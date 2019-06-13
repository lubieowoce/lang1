{-# LANGUAGE DeriveFunctor #-}
-- {-# LANGUAGE NamedFieldPuns #-}
-- {-# LANGUAGE RecordWildcards #-}
-- {-# OPTIONS_GHC -Wall #-}

import Data.Map (Map)
import qualified Data.Map as M

import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as N

import Data.Void

import Data.List (intersperse, nub)
import Data.Maybe (catMaybes, fromJust, isJust)
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Except
import Control.Monad (forM)

import Debug.Trace (trace)
-- import Data.Either.Combinators (rightToMaybe)



-- ##################
-- #    Compiler    #
-- ##################



data Definition
    = DDef FunId [VarId] [Stmt]
    deriving (Eq, Show)

data Stmt
    = SNewVar VarId Expr
    | SSetVar VarId Expr
    | SIfThenElse Expr [Stmt] [Stmt]
    | SWhile Expr [Stmt]
    | SForFromTo VarId Expr Expr [Stmt]
    | SReturn Expr
    deriving (Eq, Show)

data Expr
    = ENum Int
    | EAdd Expr Expr
    | EMul Expr Expr
    | ESub Expr Expr
    | EEqual Expr Expr
    | ENot Expr
    | EIfThenElse Expr Expr Expr
    | ELet VarId Expr Expr
    | EVar VarId
    | EApp FunId [Expr]
    deriving (Eq, Show)

eConstFalse = ENum 0
eConstTrue = ENum 1

type VarId = Char
type FunId = String

type VarIxs = Map VarId VarIx
type Procs = Map FunId Proc
type CompilerState = (VarIxs, Procs)

emptyCompilerState :: CompilerState
emptyCompilerState = (M.empty, M.empty)

type Compile a = ExceptT String (State CompilerState) a

runCompile :: Compile a -> State CompilerState (Either String a)
runCompile = runExceptT

evalCompile :: Compile a -> Either String a
evalCompile = (`evalState` emptyCompilerState) . runCompile



compileError :: String -> Compile a
compileError = throwE



getVars :: Compile VarIxs
getVars = fst <$> lift get

putVars :: VarIxs -> Compile ()
putVars vs = modifyVars (const vs)

modifyVars :: (VarIxs -> VarIxs) -> Compile ()
modifyVars f =  lift $ modify (overFst f)

newVar :: VarId -> VarIx -> Compile ()
newVar var ix = modifyVars (M.insert var ix)

getVarIx :: VarId -> Compile (Maybe VarIx)
getVarIx var = M.lookup var <$> getVars

freshVarIx :: Compile VarIx
freshVarIx = length <$> getVars

withVars :: VarIxs -> Compile a -> Compile a
withVars vs ca = do 
    old <- getVars
    putVars vs
    a <- ca
    putVars old
    pure a



getProcs :: Compile Procs
getProcs = snd <$> lift get

getProc :: FunId -> Compile (Maybe Proc)
getProc funId = M.lookup funId <$> getProcs

modifyProcs :: (Procs -> Procs) -> Compile ()
modifyProcs f =  lift $ modify (overSnd f)

newProc :: FunId -> Proc -> Compile ()
newProc funId proc = modifyProcs (M.insert funId proc)


overFst :: (a -> b) -> (a, x) -> (b, x)
overFst f (a, x) = (f a, x)
overSnd :: (a -> b) -> (x, a) -> (x, b)
overSnd f (x, a) = (x, f a)




compileProgram :: [Definition] -> Compile Program
compileProgram defs = do
    forM_ defs $ \(def@(DDef funId _ _)) -> do
        proc <- withVars M.empty $ compileDefinition def
        newProc funId proc
    mainProc <- getProc "main"
    case mainProc of
        Nothing -> compileError "No definition for 'main'"
        Just proc -> do 
            when ((nArgs proc) /= 0) $ compileError "main must take no arguments"
            ps <- getProcs
            pure $ Program {mainProc=proc, allProcs=ps}



compileDefinition :: Definition -> Compile Proc
compileDefinition (DDef funId args body) = do
    forM_ args $ \arg ->
        freshVarIx >>= newVar arg
    storeArgs <- forM args (\arg -> (Store . fromJust) <$> getVarIx arg)
    bodyCode  <- optimizeOps <$> compileBlock body
    let nArgs = length args
    nVars <- length <$> getVars
    pure $ Proc nArgs nVars (storeArgs ++ bodyCode)



compileBlock :: [Stmt] -> Compile [Op]
compileBlock = (concat <$>) . mapM compileStmt


compileStmt :: Stmt -> Compile [Op]
compileStmt (SNewVar var eVal) = do
    mix <- getVarIx var
    case mix of 
        Nothing -> do
            valCode <- compileExpr eVal
            ix <- freshVarIx
            newVar var ix
            pure $ valCode ++ [Store ix]  
        Just ix -> compileError $ "Redeclared variable: " ++ (show var) 
compileStmt (SSetVar var eVal) = do
    mix <- getVarIx var
    case mix of
        Just ix -> do
            valCode <- compileExpr eVal
            pure $ valCode ++ [Store ix]  
        Nothing -> compileError $ "Variable used before declaration: " ++ (show var) 
compileStmt (SIfThenElse eCond trueBlock falseBlock) = do
    condCode  <- compileExpr eCond
    trueCode  <- compileBlock trueBlock
    falseCode <-  (++ [JmpRel $ (length trueCode) + 1]) <$> compileBlock falseBlock
    let trueOffset = length falseCode + 1
    pure $ condCode ++ [JmpRelIf trueOffset] ++ falseCode ++ trueCode
compileStmt (SWhile eCond body) = do
    condCode  <- compileExpr eCond
    bodyCode  <- compileBlock body
    let gotoStart = [JmpRel $ negate ((length bodyCode) + (length gotoEnd) + (length condCode))]
        gotoEnd   = [Not, JmpRelIf $ (length bodyCode) + (length gotoStart) + 1]
    pure $ condCode ++ gotoEnd ++ bodyCode ++ gotoStart
compileStmt (SForFromTo var low high body) = compileBlock [
        SSetVar var low,
        SWhile (ENot (EEqual (EVar var) (EAdd high (ENum 1)))) $
            body ++ [SSetVar var (EAdd (EVar var) (ENum 1))]
    ]
compileStmt (SReturn expr) = do
    exprCode <- compileExpr expr
    pure $ exprCode ++ [Ret]
compileStmt stmt = compileError $ "Statement not implemented: " ++ (show stmt)


simplifyExpr :: Expr -> Expr
-- constant folding
simplifyExpr (EAdd (ENum x) (ENum y)) = (ENum (x+y))
simplifyExpr (EMul (ENum x) (ENum y)) = (ENum (x*y))
simplifyExpr (ESub (ENum x) (ENum y)) = (ENum (x-y))
-- neutral element
simplifyExpr (EAdd x        (ENum 0)) = x
simplifyExpr (EAdd (ENum 0) x       ) = x
simplifyExpr (EMul x        (ENum 1)) = x
simplifyExpr (EMul (ENum 1) x       ) = x
-- annihilating element
simplifyExpr (EMul x        (ENum 0)) = ENum 0
simplifyExpr (EMul (ENum 0) x       ) = ENum 0
-- cancellation
simplifyExpr e@(EAdd (ESub x y) y')
    | y == y' = x
    | otherwise = (EAdd (ESub (simplifyExpr x) (simplifyExpr y)) (simplifyExpr y'))
simplifyExpr e@(EAdd y' (ESub x y))
    | y == y' = x
    | otherwise = (EAdd (simplifyExpr y') (ESub (simplifyExpr x) (simplifyExpr y)))
-- reflexivity
simplifyExpr e@(EEqual (ENum a) (ENum b))
    | a == b    = eConstTrue
    | otherwise = eConstFalse
simplifyExpr e@(EEqual a b)
    | a == b  =  eConstTrue
    | otherwise  =  EEqual (simplifyExpr a) (simplifyExpr b)
simplifyExpr (EAdd a b)   = (EAdd (simplifyExpr a) (simplifyExpr b))
simplifyExpr (EMul a b)   = (EMul (simplifyExpr a) (simplifyExpr b))
simplifyExpr (ESub a b)   = (ESub (simplifyExpr a) (simplifyExpr b))
simplifyExpr (ENot x)     = (ENot (simplifyExpr x))
simplifyExpr (EApp f exprs) = (EApp f (map simplifyExpr exprs))
simplifyExpr x = x


compileExpr = compileExpr' . simplifyExpr
-- trace' s x = trace (s ++ " " ++ (show x)) x 
-- compileExpr = compileExpr' . (trace' "simplified: ") . simplifyExpr . (trace' "original:   " )

compileExpr' :: Expr -> Compile [Op]
compileExpr' (ENum n)   = pure [Push n]
compileExpr' (EAdd a        (ENum 1)) = concat <$> sequence [compileExpr' a, pure [Incr]]
compileExpr' (EAdd (ENum 1) a       ) = concat <$> sequence [compileExpr' a, pure [Incr]]
compileExpr' (EAdd a b) = concat <$> sequence [compileExpr' a, compileExpr' b, pure [Add]]
compileExpr' (EMul a b) = concat <$> sequence [compileExpr' a, compileExpr' b, pure [Mul]]
compileExpr' (ESub a (ENum 1)) = concat <$> sequence [compileExpr' a, pure [Decr]]
compileExpr' (ESub a b) = concat <$> sequence [compileExpr' a, compileExpr' b, pure [Sub]]
compileExpr' (ENot x)   = concat <$> sequence [compileExpr' x, pure [Not]]
compileExpr' (EEqual a b) = concat <$> sequence [compileExpr' a, compileExpr' b, pure [Equal]]
compileExpr' (EIfThenElse cond etrue efalse) = do
    condCode  <- compileExpr' cond
    trueCode  <- compileExpr' etrue
    falseCode <-  (++ [JmpRel $ (length trueCode) + 1]) <$> compileExpr' efalse
    let trueOffset = length falseCode + 1
    pure $ condCode ++ [JmpRelIf trueOffset] ++ falseCode ++ trueCode
compileExpr' (EVar var) = do 
    mix <- getVarIx var
    case mix of
        Just ix -> pure [Load ix]
        Nothing -> compileError $ "Use of undefined variable: " ++ (show var) 
compileExpr' (EApp f exprs) = do 
    mproc <- getProc f
    when (not . isJust $ mproc) $ do
        compileError $ "Use of undefined function: " ++ (show f)
    argsCode <- concat <$> sequence (compileExpr' <$> exprs)
    pure $ argsCode ++ [Call f (length exprs)]


optimizeOps :: [Op] -> [Op]
optimizeOps = id
-- optimizeOps (x      : Push 0 : Mul : rest) = optimizeOps $ Push 0   : rest
-- optimizeOps (Push 0 : x      : Mul : rest) = optimizeOps $ Push 0   : rest
-- optimizeOps (x      : Push 1 : Mul : rest) = optimizeOps $ x        : rest
-- optimizeOps (Push 1 : x      : Mul : rest) = optimizeOps $ x        : rest
-- optimizeOps (x      : Push 0 : Add : rest) = optimizeOps $ x        : rest
-- optimizeOps (Push 0 : x      : Add : rest) = optimizeOps $ x        : rest
-- optimizeOps (x      : Push 1 : Add : rest) = optimizeOps $ x : Incr : rest
-- optimizeOps (Push 1 : x      : Add : rest) = optimizeOps $ x : Incr : rest
-- optimizeOps (x      : Push 0 : Sub : rest) = optimizeOps $ x        : rest
-- optimizeOps (x      : Push 1 : Sub : rest) = optimizeOps $ x : Decr : rest
-- optimizeOps (Incr : Decr : rest) = optimizeOps rest
-- optimizeOps (Decr : Incr : rest) = optimizeOps rest
-- optimizeOps (Not  : Not  : rest) = optimizeOps rest
-- optimizeOps (op : rest) = op : optimizeOps rest
-- optimizeOps [] = []



isUnique xs = (length xs) == (length $ nub xs)




-- ##################
-- #       VM       #
-- ##################


type InstructionIx = Int
type InstructionOffset = Int
type StackIx = Int
type IntVal = Int
type ProcId = String


data VM = VM {
        procedures :: Map ProcId Proc,
        frames :: [VMFrame]
    } deriving (Eq, Show)

data VMFrame = VMFrame {
        instructionPointer :: InstructionIx,
        instructions :: [Op],
        vars  :: [IntVal],
        stack :: [IntVal]
    } deriving (Eq, Show)

data Proc = Proc {
        nArgs :: Int,
        nVars :: Int,
        code :: [Op]
    } deriving (Eq, Show)

type VarIx = Int


empty = VM {
    procedures = M.empty,
    frames = []
}

emptyVM = empty

emptyFrame = VMFrame {
    instructionPointer = 0,
    instructions = [],
    stack = [],
    vars = []
}

data Program = Program {mainProc :: Proc, allProcs :: Map FunId Proc}

execProgram :: Program -> VM
execProgram p = emptyVM { frames = [procFrame (mainProc p)] , procedures=allProcs p}


procFrame :: Proc -> VMFrame
procFrame proc = emptyFrame { instructions=(code proc),
                              vars=(replicate (nVars proc) 0) }


data Op
    = Nop
    | Push IntVal | Pop | Dup
    -- | Get StackIx | Set StackIx
    | Load VarIx | Store VarIx
    | Add | Mul | Sub | Incr | Decr
    | Equal | Not
    | Jmp   InstructionIx  | JmpRel   InstructionOffset
    | JmpIf InstructionIx  | JmpRelIf InstructionOffset
    | Call ProcId Int | Ret
    deriving (Eq, Show)



data Running e r f a
    = Error e
    | Stop r
    | Next a
    | Request (f a)
    deriving Functor

data VMRequest a
    = Print String (()     -> a)
    | Read  ()     (String -> a)
    | Exit  ()     (Void   -> a)
    deriving Functor

instance Show (VMRequest a) where
    show (Print s _) = "Print " ++ (show s) ++ " (_ :: () -> a)"
    show (Read  _ _) = "Read () (_ :: String -> a)"
    show (Exit  _ _) = "Exit () (_ :: Void -> a)"

type Running' f a = Running String String f a


step :: VM -> Running' VMRequest VM 
step (VM {frames=[]}) =  Stop "No frames remaining, halting"
step vm@(VM {frames=frame@(VMFrame {instructionPointer=ip, instructions=ops, stack=st, vars=vs}) : outerFrames, procedures=procs})
    | ip >= length ops = Error $ "instruction pointer out of bounds, stack: " ++ (show st)
    | otherwise = (\fr -> vm {frames = fr}) <$> frames'
       where
        frame' = frame {instructionPointer = ip+1}
        frames' = case (ops !! ip, st) of 
            (Nop,           _           ) -> Next $ frame' : outerFrames
            (Push val,      stack'      ) -> Next $ frame' {stack = val : stack'}     : outerFrames
            (Pop,           (_:stack')  ) -> Next $ frame' {stack = stack'}           : outerFrames
            (Dup,           (x:stack')  ) -> Next $ frame' {stack = (x : x : stack')} : outerFrames
            -- (Get ix,        (stack')    ) -> Next $ frame' {stack = (stack' !! ix) : stack'} : outerFrames
            -- (Set ix,        (x:stack')  ) -> Next $ frame' {stack = setAt (ix-1) x stack'} : outerFrames
            (Load  ix,      stack'      ) -> Next $ frame' {stack = ((vs !! ix) : stack')}        : outerFrames
            (Store ix,      (x:stack')  ) -> Next $ frame' {stack = stack', vars=setAt (ix) x vs} : outerFrames
            (Add,           (a:b:stack')) -> Next $ frame' {stack = a+b : stack'} : outerFrames
            (Sub,           (a:b:stack')) -> Next $ frame' {stack = b-a : stack'} : outerFrames
            (Mul,           (a:b:stack')) -> Next $ frame' {stack = a*b : stack'} : outerFrames
            (Incr,          (x:stack')  ) -> Next $ frame' {stack = x+1 : stack'} : outerFrames
            (Decr,          (x:stack')  ) -> Next $ frame' {stack = x-1 : stack'} : outerFrames
            (Equal,         (a:b:stack')) -> Next $ frame' {stack = (boolToInt $ a==b) : stack'} : outerFrames
            (Not,           (b:stack')  ) -> Next $ frame' {stack = (boolToInt . not . intToBool $ b) : stack'} : outerFrames
            (Jmp ip',       _           ) -> Next $ frame' {instructionPointer=ip'}    : outerFrames
            (JmpRel off,    _           ) -> Next $ frame' {instructionPointer=ip+off} : outerFrames

            (JmpIf ip',     (c:stack')  ) -> Next $ if intToBool c
                                                       then frame' {instructionPointer=ip',    stack=stack'} : outerFrames
                                                       else frame' {stack=stack'} : outerFrames

            (JmpRelIf off,  (c:stack')  ) -> Next $ if intToBool c
                                                       then frame' {instructionPointer=ip+off, stack=stack'} : outerFrames
                                                       else frame' {stack=stack'} : outerFrames
            (Call procId nArgsPassed, stack')
                | length stack' < nArgsPassed -> Error $ (
                    "Not enough arguments to call " ++ (show procId) ++
                    " with stack " ++ (show stack') ++
                    "(expected" ++ (show nArgsPassed) ++ ")")
                | otherwise -> case M.lookup procId procs of
                    Nothing   -> Error $ "Undefined procedure " ++ (show procId)
                    Just proc@Proc{nArgs=nArgs}
                        | nArgsPassed /= nArgs -> Error $
                            "Arity mismatch: " ++ (show procId) ++ " requires " ++ (show nArgs) ++" arguments, " ++
                            " but was called with " ++ (show nArgsPassed)
                        | otherwise -> Next $ functionFrame {stack = args} : frame {stack = stack''} : outerFrames
                            where functionFrame = (procFrame proc)
                                  (args, stack'') = splitAt nArgsPassed stack' 

            (Ret, (x:stack')) -> case outerFrames of
                [] -> Stop $ "main returned " ++ (show x)
                (outer@VMFrame{stack=outerStack, instructionPointer=outerIp} : outerFrames') ->
                    Next $ outer {stack = x:outerStack, instructionPointer=outerIp+1} : outerFrames'

            (op, stack') -> Error $
                "Cannot execute " ++ (show op) ++ " with stack " ++ (show stack')

intToBool :: Int -> Bool
intToBool = (/= 0)
boolToInt :: Bool -> Int
boolToInt x = if x then 1 else 0 

setAt :: Int -> a -> [a] -> [a]
setAt i x =  map (\(j,y) -> if j==i then x else y) . zip [0..]




-- ##################
-- #     Main       #
-- ##################


prettyShowVM :: VM -> String
prettyShowVM (VM {frames=[]}) =  "<no stack frames>"
prettyShowVM vm@(VM {frames = frames}) =
    prettyShowVMStack . reverse $ frames

prettyShowVMStack :: [VMFrame] -> String
prettyShowVMStack [frame] = unlines $ prettyShowVMFrame frame
prettyShowVMStack (VMFrame {instructionPointer=ip, instructions=ops} : innerFrames) = 
    "-------\n" ++ op' ++ "\n-------\n" ++ (indent . prettyShowVMStack $ innerFrames) ++ "-------\n...\n"
    where
        indent = unlines. map ("    "++) . lines
        op' = (show ip) ++ "  " ++ (show $ ops !! ip)



prettyShowVMFrame :: VMFrame -> [String]
prettyShowVMFrame VMFrame {instructionPointer=ip, instructions=ops, stack=stack, vars=vars} =
    [separate "|" vars' stack', "-------"] ++ ops'
    where
        vars' = (joinWith " " vars)
        stack' = joinWith " " $ reverse stack
        ops' = catMaybes . map (\i -> showOp i <$> (ops !? i)) $ [ip, ip+1, ip+2]
        showOp i op = (show i) ++ "  " ++ (show op) ++ (if i == ip then "  <--- " else "")


separate sep s1 s2 = s1' ++ sep ++ s2'
    where
        s1' = if null s1 then s1 else s1 ++ " "
        s2' = if null s2 then s2 else " " ++ s2

joinWith sep = concat . intersperse sep . map show

(!?) :: [a] -> Int -> Maybe a
xs !? i = if (i >= 0) && (i < length xs) then Just $ xs !! i else Nothing 






iterVM :: VM -> [Either String VM]
iterVM vm = (Right vm) : case step vm of
                            Error e   -> [Left $ "Error: "    ++ e]
                            Stop  r   -> [Left $ "Stopped. "  ++ r]
                            Next  vm' -> iterVM vm'
                            Request f -> [Left $ "Request: " ++ (show f)]


e1 = (EAdd
        (ENum 3)
        (EMul
            (ENum 2)
            (ENum 2)))


e2 = (EAdd
        (ENum 3)
        (EIfThenElse (EEqual (ENum 1) (ENum 2))
            (EMul (ENum 2) (ENum 2))
            (EMul (ENum 3) (ENum 3))))

e3 = (EAdd
        (ENum 1)
        (ELet 'x' (EMul (ENum 2) (ENum 2))
            (ELet 'y' (EMul (ENum 3) (ENum 3))
                (EAdd (EVar 'x') (EVar 'y')) )))


p2 = [

        DDef "add1" ['a'] [
            SReturn (EAdd (EVar 'a') (ENum 1))
        ],

        DDef "main" [] [
            SNewVar 'x' (ENum 5),
            SNewVar 'y' (ENum 10),
            SWhile (ENot (EEqual (EVar 'x') (EVar 'y'))) [
                SSetVar 'x' (EApp "add1" [(EVar 'x')])
            ],
            SReturn (EVar 'x')
        ]
    
    ]


p3 = [
        {-
        def fib(i) {
            j := 0;
            a := 1; b := 1; c := 0;
            while (not (j == i))) {
                c = a + b;
                a = b;
                b = c;
                j = j + 1;
            }
            return a;
        }
        -}

        -- DDef "fib" ['i'] [
        --     SNewVar 'j' (ENum 0),
        --     SNewVar 'a' (ENum 1), SNewVar 'b' (ENum 1), SNewVar 'c' (ENum 0),
        --     SWhile (ENot (EEqual (EVar 'j') (EVar 'i'))) [
        --         SSetVar 'c' (EAdd (EVar 'a') (EVar 'b')),
        --         SSetVar 'a' (EVar 'b'),
        --         SSetVar 'b' (EVar 'c'),
        --         SSetVar 'j' (EAdd (EVar 'j') (ENum 1))
        --     ],
        --     SReturn (EVar 'a')
        -- ],

        {-
        def fib(i) {
            j := 0;
            a := 1; b := 1; c := 0;
            for j from 0 to (i-1) {
                c = a + b;
                a = b;
                b = c;
            }
            return a;
        }
        -}

        DDef "fib" ['i'] [
            SNewVar 'j' (ENum 0),
            SNewVar 'a' (ENum 1), SNewVar 'b' (ENum 1), SNewVar 'c' (ENum 0),
            SForFromTo 'j' (ENum 0) (ESub (EVar 'i') (ENum 1)) [
                SSetVar 'c' (EAdd (EVar 'a') (EVar 'b')),
                SSetVar 'a' (EVar 'b'),
                SSetVar 'b' (EVar 'c')
            ],
            SReturn (EVar 'a')
        ],

        {-
        def main() {
            return fib(5);
        }
        -}

        DDef "main" [] [
            SReturn (EApp "fib" [ENum 5])
        ]

    ]

main = do
    -- let DDef funId args body = defAdd1 in
    --     print $ evalCompile $ compileDef funId args body
    case evalCompile . compileProgram $ p3 of

        Left msg -> do
            print msg

        Right prog -> do
            forM_ (M.toList . allProcs $ prog) $ \(funId, proc) -> do
                print $ funId ++ ":"
                printCode . code $ proc
                blank
            blank
            let vm = execProgram prog
            forM_ (iterVM vm) $ either putStrLn (\x -> putStrLn (prettyShowVM x) >> blank)

    where
        print' x = print x >> blank 
        blank = putStrLn ""
        printCode = mapM putStrLn . map (uncurry showLine) . zip [0..]
        showLine n c = show n ++ "\t" ++ show c

-- main = do
--     let proc = compile e3
--     mapM putStrLn $ map (uncurry showLine) $ zip [0..] $ code proc
--     putStrLn ""
--     mapM print $ unfold1E step (empty {frames = [procFrame proc]})
--     where
--         showLine n c = show n ++ "\t" ++ show c

-- main = mapM print $ unfold1E step (empty {instructions=(code p2), vars=(replicate (nVars p2) 0)})
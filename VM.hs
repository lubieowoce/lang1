{-# LANGUAGE DeriveFunctor #-}
-- {-# LANGUAGE NamedFieldPuns #-}
-- {-# LANGUAGE RecordWildcards #-}
-- {-# OPTIONS_GHC -Wall #-}

import Data.Map (Map)
import qualified Data.Map as M

import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as N

import Data.List (nub)
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Identity
import Control.Monad (forM)
-- import Data.Either.Combinators (rightToMaybe)


data Stmt
    = SNewVar VarId Expr
    | SSetVar VarId Expr
    | SIfThenElse Expr [Stmt] [Stmt]
    | SWhile Expr [Stmt]
    -- | SForIn VarId Expr Expr [Stmt]
    | SPrint Expr
    -- | SReturn Expr

data Expr
    = ENum Int
    | EAdd Expr Expr
    | EMul Expr Expr
    | EEqual Expr Expr
    | ENot Expr
    | EIfThenElse Expr Expr Expr
    | ELet VarId Expr Expr
    | EVar    VarId
    | EApp FunId [Expr]
    deriving (Eq, Show)


type VarId = Char
type FunId = String

type CompilerState = Map VarId VarIx

newtype Compile a = Compile {runCompile :: State CompilerState (Either String a)}
    deriving Functor

instance Applicative Compile where
    pure a = Compile $ pure . pure $ a
    (Compile sef) <*> (Compile sea) = Compile $ do
        ef <- sef
        ea  <- sea
        pure $ do {f <- ef; a <- ea; pure (f a)}  

instance Monad Compile where
    return = pure
    (Compile sea) >>= k = Compile $
        StateT $ \s -> Identity $ 
            let (ea, s') = runState sea s in
            case ea of
                Left msg -> (Left msg, s')
                Right a  -> runState (runCompile (k a)) s'


getVars :: Compile (Map VarId VarIx)
getVars = Compile $ Right <$> get

modifyVars :: ((Map VarId VarIx) -> (Map VarId VarIx)) -> Compile ()
modifyVars f = Compile $ Right <$> modify f

compileError :: String -> Compile a
compileError msg = Compile $ pure (Left msg)




compileFull :: [Stmt] -> Either String Proc
compileFull stmts =
    let (eops, vars) = (`runState` M.empty) . runCompile$ compile stmts in
    Proc (length vars) <$> eops

compile :: [Stmt] -> Compile [Op]
compile = (concat <$>) . mapM compile' 
    where
        compile' :: Stmt -> Compile [Op]
        compile' stmt = case stmt of
            SNewVar var eVal -> do
                mix <- getVarIx var
                case mix of 
                    Nothing -> do
                        valCode <- compileExpr eVal
                        ix <- freshVarIx
                        newVar var ix
                        pure $ valCode ++ [Store ix]  
                    Just ix -> compileError $ "Redeclared variable: " ++ (show var) 
            SSetVar var eVal -> do
                mix <- getVarIx var
                case mix of
                    Just ix -> do
                        valCode <- compileExpr eVal
                        pure $ valCode ++ [Store ix]  
                    Nothing -> compileError $ "Variable used before declaration: " ++ (show var) 
            SIfThenElse eCond trueBlock falseBlock -> do
                condCode  <- compileExpr eCond
                trueCode  <- compile trueBlock
                falseCode <-  (++ [JmpRel $ (length trueCode) + 1]) <$> compile falseBlock
                let trueOffset = length falseCode + 1
                pure $ condCode ++ [JmpRelIf trueOffset] ++ falseCode ++ trueCode
            SWhile eCond body -> do
                condCode  <- compileExpr eCond
                bodyCode  <- compile body
                let gotoStart = [JmpRel $ negate ((length bodyCode) + (length gotoEnd) + (length condCode))]
                    gotoEnd   = [Not, JmpRelIf $ (length bodyCode) + (length gotoStart) + 1]
                pure $ condCode ++ gotoEnd ++ bodyCode ++ gotoStart


            -- SPrint eVal ->

getVarIx :: VarId -> Compile (Maybe VarIx)
getVarIx var = M.lookup var <$> getVars

freshVarIx :: Compile VarIx
freshVarIx = length <$> getVars

newVar :: VarId -> VarIx -> Compile ()
newVar var ix = modifyVars (M.insert var ix)


isUnique xs = (length xs) == (length $ nub xs)



compileExpr :: Expr -> Compile [Op]
compileExpr (ENum n)     = pure [Push n]
compileExpr (EAdd a b)   = concat <$> sequence [compileExpr a, compileExpr b, pure [Add]  ]
compileExpr (EMul a b)   = concat <$> sequence [compileExpr a, compileExpr b, pure [Mul]  ]
compileExpr (EEqual a b) = concat <$> sequence [compileExpr a, compileExpr b, pure [Equal]]
compileExpr (ENot x) = concat <$> sequence [compileExpr x, pure [Not]]
compileExpr (EIfThenElse cond etrue efalse) = do
    condCode  <- compileExpr cond
    trueCode  <- compileExpr etrue
    falseCode <-  (++ [JmpRel $ (length trueCode) + 1]) <$> compileExpr efalse
    let trueOffset = length falseCode + 1
    pure $ condCode ++ [JmpRelIf trueOffset] ++ falseCode ++ trueCode
compileExpr (EVar var) = do 
    mix <- getVarIx var
    case mix of
        Just ix -> pure [Load ix]
        Nothing -> compileError $ "Variable used before declaration: " ++ (show var) 
compileExpr (EApp f exprs) = do 
    argsCode <- concat <$> sequence (compileExpr <$> exprs)
    pure $ argsCode ++ [Call f (length exprs)]




findVars :: Expr -> [VarId]
findVars (ELet v expr2 body) = v : ((findVars expr2) ++ (findVars body))
findVars (EVar v) = []
findVars (EAdd   a b) = (findVars a) ++ (findVars b)
findVars (EMul   a b) = (findVars a) ++ (findVars b)
findVars (EEqual a b) = (findVars a) ++ (findVars b)
findVars (EIfThenElse cond etrue efalse) =
    (findVars cond) ++ (findVars etrue) ++ (findVars efalse)
findVars (EApp _ exprs) = concat $ findVars <$> exprs
findVars (ENum _) = []


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
        nVars :: Int,
        code :: [Op]
    } deriving (Eq, Show)

type VarIx = Int


empty = VM {
    procedures = M.empty,
    frames = []
}

emptyFrame = VMFrame {
    instructionPointer = 0,
    instructions = [],
    stack = [],
    vars = []
}

procFrame :: Proc -> VMFrame
procFrame proc = emptyFrame { instructions=(code proc),
                              vars=(replicate (nVars proc) 0) }

data Op
    = Nop
    | Push IntVal | Pop | Dup
    -- | Get StackIx | Set StackIx
    | Load VarIx | Store VarIx
    | Add | Mul | Incr | Decr
    | Equal | Not
    | Jmp    InstructionIx  | JmpRel   InstructionOffset
    | JmpIf  InstructionIx  | JmpRelIf InstructionOffset
    | Call ProcId Int | Ret
    deriving (Eq, Show)

data Ple r a = Error String | Done r | More a

step :: VM -> Either String VM
step (VM {frames=[]}) = Left "No frames remaining, halting"
step vm@(VM {frames=frame@(VMFrame {instructionPointer=ip, instructions=ops, stack=st, vars=vs}) : outerFrames, procedures=procs})
    | ip >= length ops = Left $ "instruction pointer out of bounds, stack: " ++ (show st)
    | otherwise = do
        frames' <- case (ops !! ip, st) of 
            (Nop,           _           ) -> Right $ frame' : outerFrames
            (Push val,      stack'      ) -> Right $ frame' {stack = val : stack'}     : outerFrames
            (Pop,           (_:stack')  ) -> Right $ frame' {stack = stack'}           : outerFrames
            (Dup,           (x:stack')  ) -> Right $ frame' {stack = (x : x : stack')} : outerFrames
            -- (Get ix,        (stack')    ) -> Right $ frame' {stack = (stack' !! ix) : stack'} : outerFrames
            -- (Set ix,        (x:stack')  ) -> Right $ frame' {stack = setAt (ix-1) x stack'} : outerFrames
            (Load  ix,      stack'      ) -> Right $ frame' {stack = ((vs !! ix) : stack')}        : outerFrames
            (Store ix,      (x:stack')  ) -> Right $ frame' {stack = stack', vars=setAt (ix) x vs} : outerFrames
            (Add,           (a:b:stack')) -> Right $ frame' {stack = a+b : stack'} : outerFrames
            (Mul,           (a:b:stack')) -> Right $ frame' {stack = a*b : stack'} : outerFrames
            (Incr,          (x:stack')  ) -> Right $ frame' {stack = x+1 : stack'} : outerFrames
            (Decr,          (x:stack')  ) -> Right $ frame' {stack = x-1 : stack'} : outerFrames
            (Equal,         (a:b:stack')) -> Right $ frame' {stack = (boolToInt $ a==b) : stack'} : outerFrames
            (Not,           (b:stack')  ) -> Right $ frame' {stack = (boolToInt . not . intToBool $ b) : stack'} : outerFrames
            (Jmp ip',       _           ) -> Right $ frame' {instructionPointer=ip'}    : outerFrames
            (JmpRel off,    _           ) -> Right $ frame' {instructionPointer=ip+off} : outerFrames

            (JmpIf ip',     (c:stack')  ) -> Right $ if intToBool c
                                                       then frame' {instructionPointer=ip',    stack=stack'} : outerFrames
                                                       else frame' {stack=stack'} : outerFrames

            (JmpRelIf off,  (c:stack')  ) -> Right $ if intToBool c
                                                       then frame' {instructionPointer=ip+off, stack=stack'} : outerFrames
                                                       else frame' {stack=stack'} : outerFrames
            (Call procId nArgs, stack')
                | length stack' < nArgs -> Left $ (
                    "Not enough arguments to call " ++ (show procId) ++
                    " with stack " ++ (show stack') ++
                    "(expected" ++ (show nArgs) ++ ")")
                | otherwise -> case M.lookup procId procs of
                    Nothing   -> Left $ "Undefined procedure " ++ (show procId)
                    Just proc -> Right $ functionFrame {stack = args} : frame' {stack = stack''} : outerFrames
                        where functionFrame = (procFrame proc)
                              (args, stack'') = splitAt nArgs stack' 

            (Ret, (x:stack')) -> case outerFrames of
                [] -> Left $
                    "No outer frame to return to. value: " ++ (show x) ++ ", stack: " ++ (show stack')
                (outer@VMFrame{stack=outerStack} : outerFrames') ->
                    Right $ outer {stack = x:outerStack} : outerFrames'

            (op, stack') -> Left $
                "Cannot execute " ++ (show op) ++ " with stack " ++ (show stack')

        pure $ vm {frames = frames'}

      where frame' = frame {instructionPointer = ip+1}

intToBool :: Int -> Bool
intToBool = (/= 0)
boolToInt :: Bool -> Int
boolToInt x = if x then 1 else 0 

setAt :: Int -> a -> [a] -> [a]
setAt i x =  map (\(j,y) -> if j==i then x else y) . zip [0..]



runVM :: VM -> ([VM], String)
runVM vm = go [] vm where
    go past vm = case step vm of
                    Right vm' -> go (vm : past) vm' 
                    Left  msg -> (reverse (vm : past), msg)



_swap = Proc 2 $ [  -- y x
    Store 0,        -- y
    Store 1,        --
    Load 0,         -- x
    Load 1          -- x y
    ]

p1 = Proc 0 $ [
    Push 10,       -- 10
    Push 5,        -- 10 5 
    Add,           -- 15
    Push 8,        -- 15 8
    Equal,         -- 0
    Not,           -- 1
    JmpRelIf 3,    --
    Push 1000,     -- 1000 
    JmpRel 2,
    Push 1111,     -- 1111
    Nop
    ]

p2 = Proc (nVars _swap) $ [
    Push 3,
    Push 5
    ] ++ code _swap


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

add1 = Proc 0 [
    Incr,
    Ret
    ]

-- e4 = [(SPrint (EApp "add1" [e3]))]

e4 = [
    SNewVar 'x' (ENum 5),
    SNewVar 'y' (ENum 10),
    (SWhile (ENot (EEqual (EVar 'x') (EVar 'y')))
        [SSetVar 'x' (EAdd (ENum 1) (EVar 'x'))])
    ]

main = do
    case compileFull e4 of

        Left msg -> do
            print msg

        Right proc -> do
            showCode $ code proc
            blank
            let (states, msg) = runVM $  empty { frames = [procFrame proc],
                                                 procedures = M.fromList [("add1", add1)] }
            mapM print' $ states
            blank
            putStrLn msg

    where
        print' x = print x >> blank 
        blank = putStrLn ""
        showCode = mapM putStrLn . map (uncurry showLine) . zip [0..]
        showLine n c = show n ++ "\t" ++ show c

-- main = do
--     let proc = compile e3
--     mapM putStrLn $ map (uncurry showLine) $ zip [0..] $ code proc
--     putStrLn ""
--     mapM print $ unfold1E step (empty {frames = [procFrame proc]})
--     where
--         showLine n c = show n ++ "\t" ++ show c

-- main = mapM print $ unfold1E step (empty {instructions=(code p2), vars=(replicate (nVars p2) 0)})
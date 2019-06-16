module Compiler where
import VM
-- import Graph

import Data.Map (Map)
import qualified Data.Map as M

import Data.List (nub)
import Data.Maybe (fromJust, isJust)

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Except
import Control.Monad (forM)

import Debug.Trace (trace)


-- ##################
-- #    Compiler    #
-- ##################



data Definition
    = DDef FunId [VarId] [Stmt]
    deriving (Eq, Show)

data Stmt
    = SPass
    | SNewVar VarId Expr
    | SSetVar VarId Expr
    | SIfThenElse Expr [Stmt] [Stmt]
    | SWhile Expr [Stmt]
    | SForFromTo VarId Expr Expr [Stmt]
    | SBreak
    | SContinue
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

newtype Label = Label {unLabel :: Int} deriving (Eq, Ord)
underLabel f = Label . f . unLabel
newLabel :: Label -> Label
newLabel = underLabel (+1)
instance Show Label where show (Label l) = "label_" ++ (show l)

type CompilerState = (VarIxs, Procs, Label)

emptyCompilerState :: CompilerState
emptyCompilerState = (M.empty, M.empty, (Label 0))

type Compile a = ExceptT String (State CompilerState) a

runCompile :: Compile a -> State CompilerState (Either String a)
runCompile = runExceptT

evalCompile :: Compile a -> Either String a
evalCompile = (`evalState` emptyCompilerState) . runCompile



compileError :: String -> Compile a
compileError = throwE



getVars :: Compile VarIxs
getVars = fst' <$> lift get

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
getProcs = snd' <$> lift get

getProc :: FunId -> Compile (Maybe Proc)
getProc funId = M.lookup funId <$> getProcs

modifyProcs :: (Procs -> Procs) -> Compile ()
modifyProcs f =  lift $ modify (overSnd f)

newProc :: FunId -> Proc -> Compile ()
newProc funId proc = modifyProcs (M.insert funId proc)



modifyLabel :: (Label -> Label) -> Compile ()
modifyLabel f =  lift $ modify (overThrd f)

getLabel :: Compile Label
getLabel =  thrd <$> lift get

freshLabel :: Compile Label
freshLabel = do {l <- getLabel; modifyLabel newLabel; pure l}



overFst :: (a -> b) -> (a, x, y) -> (b, x, y)
overFst f (a, x, y) = (f a, x, y)
overSnd :: (a -> b) -> (x, a, y) -> (x, b, y)
overSnd f (x, a, y) = (x, f a, y)
overThrd :: (a -> b) -> (x, y, a) -> (x, y, b)
overThrd f (x, y, a) = (x, y, f a)


fst' (a, _, _) = a
snd' (_, a, _) = a
thrd (_, _, a) = a



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


data FlowGraph l = FlowGraph {nodes :: Map l (FlowNode l)} deriving (Eq, Show)
overNodes f (g @ FlowGraph {nodes=ns}) = g { nodes = f ns}
emptyFlowGraph = FlowGraph {nodes=M.empty}

getNode :: (Ord l) => l -> FlowGraph l -> FlowNode l
getNode l = (M.! l) . nodes

insertNode :: (Ord l) => l -> FlowNode l -> FlowGraph l -> FlowGraph l
insertNode l n = overNodes (M.insert l n)

insertNodes :: (Ord l) => [(l, FlowNode l)] -> FlowGraph l -> FlowGraph l
insertNodes ns = overNodes (M.union (M.fromList ns))

deleteNode :: (Ord l) => l -> FlowGraph l -> FlowGraph l
deleteNode l = overNodes (M.delete l)



data FlowNode l
    = Begin {funId :: FunId, next :: l}
    | BasicBlock {body :: [BasicStmt], next :: l}
    | IfThenElse {cond :: Expr, ifTrue, ifFalse :: l}
    | Return {expr :: Expr, next :: l}
    | End 
    deriving (Eq, Show)

data BasicStmt
    = BPass
    | BSetVar VarId Expr
    deriving (Eq, Show)

data Ctx l
    = FuncCtx  {end :: l}
    | BlockCtx {end :: l}
    | LoopCtx  {cont, end :: l}

snoc :: [a] -> a -> [a]
snoc xs x = xs ++ [x]

flowGraph :: Definition -> Compile (Label, FlowGraph Label)
flowGraph (DDef funId _ body) = do
    begin <- freshLabel
    ret   <- freshLabel
    let graph = insertNode ret End emptyFlowGraph
        ctx   = [FuncCtx {end=ret}]
    (first, graph') <- go ctx graph body
    pure $ (begin, insertNode begin (Begin funId first) graph') where

    go :: [Ctx Label] -> (FlowGraph Label) -> [Stmt] -> Compile (Label, FlowGraph Label)
    go ctx graph [] = do
        when (null ctx) $ compileError "no context"
        case head ctx of
            LoopCtx {cont=s} -> pure $ (s, graph)
            _ -> pure $ (end $ ctx !! 0, graph)
    go ctx graph (stmt:stmts) =
        case stmt of
            SPass -> do
                l <- freshLabel
                (entry, graph') <- go ctx graph stmts
                let node = BasicBlock [BPass] entry
                pure $ (l, insertNode l node graph')
            SNewVar var expr -> do
                l <- freshLabel
                (entry, graph') <- go ctx graph stmts
                let node = BasicBlock [BSetVar var expr] entry
                pure $ (l, insertNode l node graph')
            SSetVar var expr -> do
                l <- freshLabel
                (entry, graph') <- go ctx graph stmts
                let node = BasicBlock [BSetVar var expr] entry
                pure $ (l, insertNode l node graph')
            SIfThenElse cond trueBody falseBody -> do
                l <- freshLabel
                (next, graph') <- go ctx graph stmts
                let ctx' = BlockCtx {end=next} : ctx
                (trueEntry,  graph'')  <- go ctx' graph'  trueBody
                (falseEntry, graph''') <- go ctx' graph'' falseBody
                let node = IfThenElse {cond=cond, ifTrue=trueEntry, ifFalse=falseEntry}
                pure $ (l, insertNode l node graph''')
            SWhile cond body -> do
                l <- freshLabel
                (next, graph') <- go ctx graph stmts
                let ctx' = LoopCtx {cont=l, end=next} : ctx
                (bodyEntry,  graph'') <- go ctx' graph' body
                let node = IfThenElse {cond=cond, ifTrue=bodyEntry, ifFalse=next}
                pure $ (l, insertNode l node graph'')
            SForFromTo var low high body -> do
                loopInit <- freshLabel
                loopIf   <- freshLabel
                loopIncr <- freshLabel
                (next, graph') <- go ctx graph stmts
                let ctx' = LoopCtx {cont=loopIncr, end=next} : ctx
                (bodyEntry,  graph'') <- go ctx' graph' body
                let incrNode = BasicBlock [BSetVar var (EAdd (EVar var) (ENum 1))] loopIf
                    ifNode   = IfThenElse {cond=(ENot (EEqual (EVar var) high)), ifTrue=bodyEntry, ifFalse=next}
                    initNode = BasicBlock [BSetVar var low] loopIf
                pure $ (loopInit, insertNodes [(loopInit, initNode), (loopIf, ifNode), (loopInit, initNode)] graph'')
            SBreak -> case findLoopEnd ctx of
                Just end -> pure $ (end, graph)
                Nothing -> compileError "break outside of loop"
            SContinue -> case findLoopCont ctx of
                Just cont -> pure $ (cont, graph)
                Nothing -> compileError "continue outside of loop"
            SReturn expr -> do
                when (null ctx) $ compileError "no context"
                case last ctx of
                    FuncCtx {end=end} -> do
                        l <- freshLabel
                        let node = Return expr end
                        pure $ (l, insertNode l node graph)
                    _ -> compileError "return outside function"
    findLoopEnd [] = Nothing
    findLoopEnd (ctx:ctxs) =
        case ctx of
            LoopCtx {end=e} -> Just e
            _                -> findLoopEnd ctxs
    findLoopCont [] = Nothing
    findLoopCont (ctx:ctxs) =
        case ctx of
            LoopCtx {cont=c} -> Just c
            _                 -> findLoopCont ctxs


findPredecessors :: Label -> FlowGraph Label -> [Label]
findPredecessors l g = map fst . filter ((continuesTo l) . snd) .  M.toList . nodes $ g

continuesTo :: Label -> FlowNode Label -> Bool
continuesTo target n = case n of
    Begin {next=next} -> next == target
    BasicBlock {next=next} -> next == target
    IfThenElse {ifTrue=ifTrue, ifFalse=ifFalse} -> ifTrue == target || ifFalse == target
    Return {next=next} -> next == target
    End -> False


joinBasics :: FlowGraph Label -> FlowGraph Label
joinBasics g = (`execState` g) $ do
    forM_ (M.toList . nodes $ g) $ \(label, node) ->
        case node of
            BasicBlock body next -> do
                g <- get
                case findPredecessors label g of
                    [pre] -> case getNode pre g of
                        BasicBlock body' _ -> do
                            modify (deleteNode label)
                            modify (insertNode pre $ BasicBlock (body'++body) next)
                        _ -> pure () 
                    _ -> pure () 
            _ -> pure ()




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
compileBlock = ((trace' "block: ") . concat <$>) . mapM compileStmt


compileStmt :: Stmt -> Compile [Op]
compileStmt (SPass) = pure $ [Nop]
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
trace' s x = trace (s ++ " " ++ (show x)) x 
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



p1 = [
        SIfThenElse (EEqual (EVar 'x') (EVar 'y')) [
            SSetVar 'x' (EAdd (EVar 'x') (ENum 1)),
            SSetVar 'x' (EAdd (EVar 'x') (ENum 1))
        ] [
            SReturn (EVar 'y')
        ],
        SReturn (EVar 'x')
    ]



p2 = DDef "fib" ['i'] [
        SNewVar 'j' (ENum 0),
        SNewVar 'a' (ENum 1), SNewVar 'b' (ENum 1), SNewVar 'c' (ENum 0),
        SForFromTo 'j' (ENum 0) (ESub (EVar 'i') (ENum 1)) [
            SSetVar 'c' (EAdd (EVar 'a') (EVar 'b')),
            SSetVar 'a' (EVar 'b'),
            SSetVar 'b' (EVar 'c')
        ],
        SReturn (EVar 'a')
    ]


main = do
    let (start, g1) = fromRight . evalCompile $ flowGraph p2
        g2 = joinBasics g1

    print start
    mapM print $ M.toList . nodes $ g1
    blank
    mapM print $ M.toList . nodes $ g2
    where
        blank = putStrLn "\n" 
        fromRight (Right x) = x 

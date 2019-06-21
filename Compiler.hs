{-# LANGUAGE DeriveFunctor #-}

module Compiler where
import VM
-- import Graph

import Data.Map (Map)
import qualified Data.Map as M

import Data.Set (Set)
import qualified Data.Set as S

import Data.List (nub, intersperse, elemIndex)
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
    deriving (Eq)

instance Show Definition where
    show (DDef funId vars body) =
        "func " ++ funId ++ (parens . joinWith ", " . map showVarId $ vars) ++ " " ++ (showBlock body)


showBlock :: [Stmt] -> String
showBlock b = "{\n" ++ (joinWith "" . map indent' . map show $ b) ++ "}\n"


indent' = unlines . map indent . lines

joinWith :: String -> [String] -> String
joinWith sep = concat . intersperse sep
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
    deriving (Eq)

instance Show Stmt where
    show (SPass) = "pass"
    show (SNewVar var expr) = (showVarId var) ++ " := " ++ (show expr)
    show (SSetVar var expr) = (showVarId var) ++=++ (show expr)
    show (SIfThenElse cond trueBody falseBody) = 
        "if " ++ (show cond) ++ " " ++ (showBlock trueBody) ++ "else " ++ (showBlock falseBody)
    show (SWhile cond body) = 
        "while " ++ (show cond) ++ " " ++ (showBlock body)
    show (SForFromTo var low high body) = 
        "for " ++ (showVarId var) ++ " in [" ++ (show low) ++ " .. " ++ (show high) ++ "] " ++ (showBlock body)
    show (SBreak) = "break"
    show (SContinue) = "continue"
    show (SReturn expr) = "return " ++ (show expr)

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
    deriving (Eq)

instance Show Expr where
    show (ENum n) = show n
    show (EAdd a b)   = parens $ (show a) ++ " + "  ++ (show b)
    show (EMul a b)   = parens $ (show a) ++ " * "  ++ (show b)
    show (ESub a b)   = parens $ (show a) ++ " - "  ++ (show b)
    show (EEqual a b) = parens $ (show a) ++ " == " ++ (show b)
    show (ENot (EEqual a b)) = parens $ (show a) ++ " != " ++ (show b)
    show (ENot x) = parens $ "!" ++ (show x)
    show (EVar v) = showVarId v 
    show (EApp fun exprs) = fun ++ (parens . concat . intersperse ", " . map show $ exprs)

parens s = "(" ++ s ++ ")"
showVarId v = v


eConstFalse = ENum 0
eConstTrue = ENum 1

type VarId = String
type FunId = String


type VarIxs = Map VarId VarIx
type Procs = Map FunId Proc

newtype Label = Label {unLabel :: Int} deriving (Eq, Ord)
underLabel f = Label . f . unLabel
asLabel f = unLabel . f . Label
newLabel :: Label -> Label
newLabel = underLabel (+1)
instance Show Label where show (Label l) = "L" ++ (show l)

type CompilerState = (VarIxs, Procs, Int)

emptyCompilerState :: CompilerState
emptyCompilerState = (M.empty, M.empty, 0)

type Compile a = ExceptT String (State CompilerState) a

runCompile :: Compile a -> State CompilerState (Either String a)
runCompile = runExceptT

evalCompile :: Compile a -> Either String a
evalCompile = (`evalState` emptyCompilerState) . runCompile



compileError :: String -> Compile a
compileError = throwE

orError :: Maybe a -> String -> Compile a
(Just a) `orError` _   = pure a
_        `orError` msg = throwE msg


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


getFresh :: Compile Int
getFresh = thrd <$> lift get

modifyFresh :: (Int -> Int) -> Compile ()
modifyFresh f = modify (overThrd f) 

fresh :: Compile Int
fresh = do {x <- getFresh; modifyFresh (+1); pure x}


freshLabel :: Compile Label
freshLabel = Label <$> fresh


toVarId :: Int -> VarId
toVarId = ("_t_" ++) . show

freshVarId :: Compile VarId
freshVarId = toVarId <$> fresh



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

graphLabels :: FlowGraph l -> [l]
graphLabels = map fst . M.toList . nodes



data Ctx l
    = BlockCtx {end :: l}
    | LoopCtx  {cont, end :: l}


data FlowNode l
    = Block {body :: [BasicStmt], next :: l}
    | IfThenElse {cond :: BasicExpr, ifTrue, ifFalse :: l}
    | Return {expr :: BasicExpr}
    deriving (Eq, Show, Functor)

data BasicExpr
    = BVar VarId
    | BNum Int
    deriving (Eq)


instance Show BasicExpr where
    show (BVar v) = showVarId v
    show (BNum n) = show n

data BasicStmt
    = BSetVar VarId BasicExpr 
    | BAdd    VarId BasicExpr BasicExpr
    | BMul    VarId BasicExpr BasicExpr
    | BSub    VarId BasicExpr BasicExpr
    | BEqual  VarId BasicExpr BasicExpr
    | BNot    VarId BasicExpr
    | BApp    VarId FunId [BasicExpr]
    deriving (Eq)

instance Show BasicStmt where
    show (BSetVar v x) = (showVarId v) ++=++ (show x)
    show (BAdd   v a b) = (showVarId v) ++=++ (show a) ++ " + "  ++ (show b)
    show (BMul   v a b) = (showVarId v) ++=++ (show a) ++ " * "  ++ (show b)
    show (BSub   v a b) = (showVarId v) ++=++ (show a) ++ " - "  ++ (show b)
    show (BEqual v a b) = (showVarId v) ++=++ (show a) ++ " == " ++ (show b)
    show (BNot   v x)   = (showVarId v) ++=++ "!" ++ (show x)
    show (BApp    v f exprs) = (showVarId v) ++=++ (f ++ (parens . concat . intersperse ", " . map show $ exprs))


a ++=++ b = a ++ " = " ++ b


toBasicExpr :: Expr -> Compile (BasicExpr, [BasicStmt])
toBasicExpr (ENum n)     = pure (BNum n, [])
toBasicExpr (EAdd a b)   = do (v1, s1) <- toBasicExpr a; (v2, s2) <- toBasicExpr b; t <- freshVarId; pure (BVar t, s1 ++ s2 ++ [BAdd   t v1 v2])
toBasicExpr (EMul a b)   = do (v1, s1) <- toBasicExpr a; (v2, s2) <- toBasicExpr b; t <- freshVarId; pure (BVar t, s1 ++ s2 ++ [BMul   t v1 v2])
toBasicExpr (ESub a b)   = do (v1, s1) <- toBasicExpr a; (v2, s2) <- toBasicExpr b; t <- freshVarId; pure (BVar t, s1 ++ s2 ++ [BSub   t v1 v2])
toBasicExpr (EEqual a b) = do (v1, s1) <- toBasicExpr a; (v2, s2) <- toBasicExpr b; t <- freshVarId; pure (BVar t, s1 ++ s2 ++ [BEqual t v1 v2])
toBasicExpr (ENot x)     = do (v1, s1) <- toBasicExpr x; t <- freshVarId; pure (BVar t, s1 ++ [BNot t v1])
toBasicExpr (EVar v) = pure (BVar v, [])
toBasicExpr (EApp fun exprs) = do
    xs <- mapM toBasicExpr exprs
    let vars  = map fst xs
    let temps = concat $ map snd xs
    t <- freshVarId
    pure (BVar t, temps ++ [BApp t fun vars])



snoc :: [a] -> a -> [a]
snoc xs x = xs ++ [x]


flowGraph :: Definition -> Compile (Label, FlowGraph Label)
flowGraph (DDef funId _ body) = go [] emptyFlowGraph body where
    go :: [Ctx Label] -> (FlowGraph Label) -> [Stmt] -> Compile (Label, FlowGraph Label)
    go []      _     [] = compileError "missing return statement"
    go (ctx:_) graph [] = do
        case ctx of
            LoopCtx {} -> pure $ (cont ctx, graph)
            _          -> pure $ (end ctx,  graph)
    go ctxs    graph (stmt:stmts) =
        case stmt of
            SPass -> do
                go ctxs graph stmts
            SNewVar var expr -> do
                l <- freshLabel
                (expr', computeExpr, graph) <- computeBlock expr graph l
                (next, graph) <- go ctxs graph stmts
                let node = Block [BSetVar var expr'] next
                pure $ (computeExpr, insertNode l node graph)
            SSetVar var expr -> do
                l <- freshLabel
                (expr', computeExpr, graph) <- computeBlock expr graph l
                (next, graph) <- go ctxs graph stmts
                let node = Block [BSetVar var expr'] next
                pure $ (computeExpr, insertNode l node graph)
            SIfThenElse cond trueBody falseBody -> do
                ifCond <- freshLabel
                (condExpr, computeCond, graph) <- computeBlock cond graph ifCond 
                (next, graph) <- go ctxs graph stmts
                let ctxs' = BlockCtx {end=next} : ctxs
                (trueCont,  graph) <- go ctxs' graph trueBody
                (falseCont, graph) <- go ctxs' graph falseBody
                let ifCondNode      = IfThenElse {cond=condExpr, ifTrue=trueCont, ifFalse=falseCont}
                pure $ (computeCond, insertNode ifCond ifCondNode graph)
            SWhile cond body -> do
                ifCond <- freshLabel
                (condExpr, computeCond, graph) <- computeBlock cond graph ifCond 
                (next, graph) <- go ctxs graph stmts
                let ctxs' = LoopCtx {cont=computeCond, end=next} : ctxs
                (bodyCont,  graph) <- go ctxs' graph body
                let node = IfThenElse {cond=condExpr, ifTrue=bodyCont, ifFalse=next}
                pure $ (computeCond, insertNode ifCond node graph)
            SForFromTo var low high body -> do
                loopInit <- freshLabel
                (initExpr, computeInit, graph) <- computeBlock low graph loopInit 
                loopIf   <- freshLabel
                (condExpr, computeCond, graph) <- computeBlock (ENot (EEqual (EVar var) high)) graph loopIf
                loopIncr <- freshLabel
                (incrExpr, computeIncr, graph) <- computeBlock (EAdd (EVar var) (ENum 1)) graph loopIncr
                (next, graph) <- go ctxs graph stmts
                let ctxs' = LoopCtx {cont=computeIncr, end=next} : ctxs
                (bodyCont,  graph) <- go ctxs' graph body
                let incrNode = Block [BSetVar var incrExpr] computeCond
                    ifNode   = IfThenElse {cond=condExpr, ifTrue=bodyCont, ifFalse=next}
                    initNode = Block [BSetVar var initExpr] computeCond
                pure $ (computeInit, insertNodes [(loopInit, initNode), (loopIf, ifNode), (loopIncr, incrNode)] graph)
            SBreak -> do 
                end <- findLoopEnd ctxs `orError` "break outside of loop"
                pure $ (end, graph)
            SContinue -> do
                cont <- findLoopCont ctxs `orError` "continue outside of loop"
                pure $ (cont, graph)
            SReturn expr -> do
                l <- freshLabel
                (expr', computeExpr, graph) <- computeBlock expr graph l 
                let node = Return expr'
                pure $ (computeExpr, insertNode l node graph)

    computeBlock :: Expr -> FlowGraph Label -> Label -> Compile (BasicExpr, Label, FlowGraph Label)
    computeBlock expr graph next = do
        computeExpr <- freshLabel
        (expr', temps) <- toBasicExpr expr
        pure $ if not . null $ temps
                   then (expr', computeExpr, insertNode computeExpr (Block temps next) graph )
                   else (expr', next, graph)

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
    Block {next=next} -> next == target
    IfThenElse {ifTrue=ifTrue, ifFalse=ifFalse} -> ifTrue == target || ifFalse == target
    Return {} -> False



joinBlocks :: FlowGraph Label -> FlowGraph Label
joinBlocks g = (`execState` g) $ do
    forM_ (graphLabels g) $ \label -> do
        g <- get
        when (label `M.member` (nodes g)) $
            case getNode label g of
                Block body next ->
                    case findPredecessors label g of
                        [pre] -> case getNode pre g of
                            Block body' _ -> do
                                modify (deleteNode label)
                                let node' = Block (body'++body) next
                                modify (insertNode pre node')
                            _ -> pure () 
                        _ -> pure () 
                _ -> pure ()




depthFirst :: Label -> FlowGraph Label -> [Label]
depthFirst entry graph = (`evalState` S.empty) $ go entry where
    go :: Label -> State (Set Label) [Label]
    go label = do
        visited <- get
        if label `S.member` visited
            then pure $ []
            else do
                modify (S.insert label)
                case getNode label graph of
                    Block {body=body, next=next} -> do
                        ordered <- go next
                        pure $ label : ordered
                    IfThenElse {ifTrue=ifTrue, ifFalse=ifFalse} -> do
                        ordered  <- go ifTrue
                        ordered' <- go ifFalse
                        pure $ label : (ordered ++ ordered')
                    Return {expr=expr} -> do
                        pure $ [label]


depthFirstNodes :: Label -> FlowGraph Label -> [(Label, FlowNode Label)]
depthFirstNodes entry graph = map (\l -> (l, getNode l graph)) $ depthFirst entry graph



renameLabels :: [Label] -> FlowGraph Label -> FlowGraph Label
renameLabels order graph = overNodes (M.fromList . map rename . M.toList) $ graph where
    rename (label, node) = (newLabel label, fmap newLabel node)
    newLabel l = Label . fromJust $ elemIndex l order


depthFirstReorder :: Label -> FlowGraph Label -> FlowGraph Label
depthFirstReorder entry graph = let order = depthFirst entry graph in renameLabels order graph


findVars :: FlowGraph Label -> [VarId]
findVars = nub . concat . map basicStmtVars . concat . map body . filter isBlock . map snd . M.toList . nodes
    where
        basicStmtVars (BSetVar v x)  = v : basicExprVars x 
        basicStmtVars (BAdd   v a b) = v : (basicExprVars a) ++ (basicExprVars b)
        basicStmtVars (BMul   v a b) = v : (basicExprVars a) ++ (basicExprVars b)
        basicStmtVars (BSub   v a b) = v : (basicExprVars a) ++ (basicExprVars b)
        basicStmtVars (BEqual v a b) = v : (basicExprVars a) ++ (basicExprVars b)
        basicStmtVars (BNot   v x)   = v : (basicExprVars x)
        basicStmtVars (BApp   v f exprs) = v : (concat . map basicExprVars $ exprs)

        basicExprVars (BVar v) = [v]
        basicExprVars (BNum _) = []

        isBlock (Block {}) = True
        isBlock _          = False

        
     
        

compileDefinition' :: Definition -> Compile Proc
compileDefinition' def@(DDef funId args body) = do
    (entry, graph) <- flowGraph def
    forM_ (findVars graph) $ \var ->
        freshVarIx >>= newVar var
    storeArgs <- forM args (\arg -> (Store . fromJust) <$> getVarIx arg)
    bodyCode  <- compileGraph entry graph
    let nArgs = length args
    nVars <- length <$> getVars
    pure $ Proc nArgs nVars (storeArgs ++ bodyCode)


compileGraph :: Label -> FlowGraph Label -> Compile [Op]
compileGraph entry graph = do
    case getNode entry graph of
        Block {body=body, next=next} -> do
            -- bodyCode <- concat <$> mapM compileBasicStmt body
            -- pure $ bodyCode `snoc` Jmp next
            undefined
        IfThenElse {cond=cond, ifTrue=ifTrue, ifFalse=ifFalse} -> do
            -- condCode <- compileBasicExpr cond
            undefined
        Return {expr=expr} -> do
            undefined


-- compileBasicStmt :: BasicStmt -> Compile [Op]
-- compileBasicStmt (BSetVar v x)  = do ix <- getVarIx v; pure [compileBasicExpr x, Store ix]
-- compileBasicStmt (BAdd   v a b) = do ix <- getVarIx v; pure [compileBasicExpr a, compileBasicExpr b, Add,   Store ix]
-- compileBasicStmt (BMul   v a b) = do ix <- getVarIx v; pure [compileBasicExpr a, compileBasicExpr b, Mul,   Store ix]
-- compileBasicStmt (BSub   v a b) = do ix <- getVarIx v; pure [compileBasicExpr a, compileBasicExpr b, Sub,   Store ix]
-- compileBasicStmt (BEqual v a b) = do ix <- getVarIx v; pure [compileBasicExpr a, compileBasicExpr b, Equal, Store ix]
-- compileBasicStmt (BNot   v x)   = do ix <- getVarIx v; pure [compileBasicExpr x, Not, Store ix]
-- compileBasicStmt (BApp   v f exprs) = do ecode <- mapM_ compileBasicExpr exprs; ix <- getVarIx v; pure $ ecode ++ [Call f (length exprs), Store ix]

-- compileBasicExpr :: BasicExpr -> Compile Op
-- compileBasicExpr (BVar v) = Load <$> (getVarIx v `orError` "undefined variable" ++ (showVarId v))
-- compileBasicExpr (BNum n) = pure $ Push n





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



e1 = (EAdd
        (ENum 3)
        (EMul
            (ENum 2)
            (ENum 2)))


p1 = [
        SIfThenElse (EEqual (EVar "x") (EVar "y")) [
            SSetVar "x" (EAdd (EVar "x") (ENum 1)),
            SSetVar "x" (EAdd (EVar "x") (ENum 1))
        ] [
            SReturn (EVar "y")
        ],
        SReturn (EVar "x")
    ]



p2 = DDef "fib" ["i"] [
        SNewVar "j" (ENum 0),
        SNewVar "a" (ENum 1), SNewVar "b" (ENum 1), SNewVar "c" (ENum 0),
        SForFromTo "j" (ENum 0) (ESub (EVar "i") (ENum 1)) [
            SSetVar "c" (EAdd (EVar "a") (EVar "b")),
            SSetVar "a" (EVar "b"),
            SSetVar "b" (EVar "c")
        ],
        SReturn (EVar "a")
    ]


p3 = DDef "ple" [] [
        SNewVar "x" (ENum 0),
        SNewVar "i" (ENum 0), SNewVar "j" (ENum 0),
        SForFromTo "i" (ENum 1) (ENum 10) [
            SForFromTo "j" (ENum 1) (ENum 10) [
                SSetVar "x" (EAdd (EVar "x") (EAdd (EVar "i") (EVar "j")))
            ]
        ],
        SReturn (EVar "x")
    ]


main = either (putStrLn . ("Error: "++)) pure  =<<  (runExceptT mainE)

mainE :: ExceptT String IO ()
mainE = do
    (_, vars) <- ExceptT . pure $ evalCompile (toBasicExpr e1)
    lift $ mapM_ print vars
    lift $ blank
    let prog = p2
    lift $ print $ prog
    lift $ blank
    (start, g1) <- ExceptT . pure $ evalCompile (flowGraph prog)
    let g2 = joinBlocks g1
    -- lift $ putStrLn $ "-> " ++ (show start)
    lift $ mapM_ (uncurry printNode) . M.toList . nodes . depthFirstReorder start $ g1
    lift $ blank >> blank
    -- lift $ putStrLn $ "-> " ++ (show start)
    lift $ mapM_ (uncurry printNode) . M.toList . nodes . depthFirstReorder start $ g2
    lift $ blank
    where
        blank = putStrLn "\n" 
        fromRight (Right x) = x 
        printNode l (IfThenElse {cond=cond, ifTrue=ifTrue, ifFalse=ifFalse}) = do
            putStrLn $ (show l) ++ ": " ++ " if " ++ (show cond) ++ ""
            putStrLn . indent $ "then -> " ++ (show ifTrue)
            putStrLn . indent $ "else -> " ++ (show ifFalse)
        printNode l (Return {expr=expr}) =
            putStrLn $ (show l) ++ ": " ++"return " ++ (show expr)
        printNode l (Block {body=body, next=next}) = do 
            putStrLn $ (show l) ++ ":"
            mapM_ (putStrLn . indent . show) body
            putStrLn $ "  -> " ++ (show next) 


indent = ("  "++)

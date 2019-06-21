{-# LANGUAGE DeriveFunctor #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Compiler where

import VM hiding (Proc (..), Op (..))
import qualified VM
-- import Graph

import Data.Map (Map)
import qualified Data.Map as M

import Data.Set (Set)
import qualified Data.Set as S

import Data.List (nub, intersperse, elemIndex)
import Data.Maybe (fromJust, isJust, listToMaybe)

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Except
import Control.Monad (forM)

import Data.Bifunctor (Bifunctor, bimap, first, second)

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
    | ELess Expr Expr
    | EGreater Expr Expr
    | ELessEqual Expr Expr
    | EGreaterEqual Expr Expr
    | ENot Expr
    | EVar VarId
    | EApp FunId [Expr]
    -- | EIfThenElse Expr Expr Expr
    -- | ELet VarId Expr Expr
    deriving (Eq)

instance Show Expr where
    show (ENum n) = show n
    show (EAdd a b)   = parens $ (show a) ++ " + "  ++ (show b)
    show (EMul a b)   = parens $ (show a) ++ " * "  ++ (show b)
    show (ESub a b)   = parens $ (show a) ++ " - "  ++ (show b)
    show (EEqual a b)        = parens $ (show a) ++ " == " ++ (show b)
    show (ELess a b)         = parens $ (show a) ++ " <" ++ (show b)
    show (EGreater a b)      = parens $ (show a) ++ " > " ++ (show b)
    show (ELessEqual a b)    = parens $ (show a) ++ " <= " ++ (show b)
    show (EGreaterEqual a b) = parens $ (show a) ++ " >= " ++ (show b)
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
type Procs = Map FunId VM.Proc

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

getProc :: FunId -> Compile (Maybe VM.Proc)
getProc funId = M.lookup funId <$> getProcs

modifyProcs :: (Procs -> Procs) -> Compile ()
modifyProcs f =  lift $ modify (overSnd f)

newProc :: FunId -> VM.Proc -> Compile ()
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
    | BEqual         VarId BasicExpr BasicExpr
    | BLess          VarId BasicExpr BasicExpr
    | BGreater       VarId BasicExpr BasicExpr
    | BLessEqual     VarId BasicExpr BasicExpr
    | BGreaterEqual  VarId BasicExpr BasicExpr
    | BNot    VarId BasicExpr
    | BApp    VarId FunId [BasicExpr]
    deriving (Eq)

instance Show BasicStmt where
    show (BSetVar v x) = (showVarId v) ++=++ (show x)
    show (BAdd   v a b) = (showVarId v) ++=++ (show a) ++ " + "  ++ (show b)
    show (BMul   v a b) = (showVarId v) ++=++ (show a) ++ " * "  ++ (show b)
    show (BSub   v a b) = (showVarId v) ++=++ (show a) ++ " - "  ++ (show b)
    show (BEqual        v a b) = (showVarId v) ++=++ (show a) ++ " == " ++ (show b)
    show (BLess         v a b) = (showVarId v) ++=++ (show a) ++ " < "  ++ (show b)
    show (BGreater      v a b) = (showVarId v) ++=++ (show a) ++ " > "  ++ (show b)
    show (BLessEqual    v a b) = (showVarId v) ++=++ (show a) ++ " <= " ++ (show b)
    show (BGreaterEqual v a b) = (showVarId v) ++=++ (show a) ++ " >= " ++ (show b)
    show (BNot   v x)   = (showVarId v) ++=++ "!" ++ (show x)
    show (BApp    v f exprs) = (showVarId v) ++=++ (f ++ (parens . concat . intersperse ", " . map show $ exprs))


a ++=++ b = a ++ " = " ++ b


toBasicExpr :: Expr -> Compile (BasicExpr, [BasicStmt])
toBasicExpr (ENum n)     = pure (BNum n, [])
toBasicExpr (EAdd a b)   = do (v1, s1) <- toBasicExpr a; (v2, s2) <- toBasicExpr b; t <- freshVarId; pure (BVar t, s1 ++ s2 ++ [BAdd   t v1 v2])
toBasicExpr (EMul a b)   = do (v1, s1) <- toBasicExpr a; (v2, s2) <- toBasicExpr b; t <- freshVarId; pure (BVar t, s1 ++ s2 ++ [BMul   t v1 v2])
toBasicExpr (ESub a b)   = do (v1, s1) <- toBasicExpr a; (v2, s2) <- toBasicExpr b; t <- freshVarId; pure (BVar t, s1 ++ s2 ++ [BSub   t v1 v2])
toBasicExpr (EEqual        a b) = do (v1, s1) <- toBasicExpr a; (v2, s2) <- toBasicExpr b; t <- freshVarId; pure (BVar t, s1 ++ s2 ++ [BEqual        t v1 v2])
toBasicExpr (ELess         a b) = do (v1, s1) <- toBasicExpr a; (v2, s2) <- toBasicExpr b; t <- freshVarId; pure (BVar t, s1 ++ s2 ++ [BLess         t v1 v2])
toBasicExpr (EGreater      a b) = do (v1, s1) <- toBasicExpr a; (v2, s2) <- toBasicExpr b; t <- freshVarId; pure (BVar t, s1 ++ s2 ++ [BGreater      t v1 v2])
toBasicExpr (ELessEqual    a b) = do (v1, s1) <- toBasicExpr a; (v2, s2) <- toBasicExpr b; t <- freshVarId; pure (BVar t, s1 ++ s2 ++ [BLessEqual    t v1 v2])
toBasicExpr (EGreaterEqual a b) = do (v1, s1) <- toBasicExpr a; (v2, s2) <- toBasicExpr b; t <- freshVarId; pure (BVar t, s1 ++ s2 ++ [BGreaterEqual t v1 v2])
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
                (highExpr, computeHigh, graph) <- computeBlock high graph loopInit
                (lowExpr, computeLow, graph) <- computeBlock low graph computeHigh
                loopIf   <- freshLabel
                (condExpr, computeCond, graph) <- computeBlock (ELessEqual (EVar var) (toExpr highExpr)) graph loopIf
                loopIncr <- freshLabel
                (incrExpr, computeIncr, graph) <- computeBlock (EAdd (EVar var) (ENum 1)) graph loopIncr
                (next, graph) <- go ctxs graph stmts
                let ctxs' = LoopCtx {cont=computeIncr, end=next} : ctxs
                (bodyCont,  graph) <- go ctxs' graph body
                let incrNode = Block [BSetVar var incrExpr] computeCond
                    ifNode   = IfThenElse {cond=condExpr, ifTrue=bodyCont, ifFalse=next}
                    initNode = Block [BSetVar var lowExpr] computeCond
                pure $ (computeLow, insertNodes [(loopInit, initNode), (loopIf, ifNode), (loopIncr, incrNode)] graph)
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


toExpr :: BasicExpr -> Expr
toExpr (BVar v) = EVar v
toExpr (BNum n) = ENum n

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




someOrder :: Label -> FlowGraph Label -> [Label]
someOrder entry graph = snd $ (`evalState` S.empty) $ go entry where
    go :: Label -> State (Set Label) (Maybe Label, [Label])
    go label = do
        visited <- get
        if label `S.member` visited
            then pure $ (Just label, [])
            else do
                modify (S.insert label)
                case getNode label graph of
                    Block {body=body, next=next} -> do
                        (stopped, ordered) <- go next
                        pure $ (stopped, label : ordered)
                    IfThenElse {ifTrue=ifTrue, ifFalse=ifFalse} -> do
                        (stopped, ordered)  <- go ifTrue
                        (joined,  ordered') <- go ifFalse
                        let rest = case joined of
                                        Nothing -> ordered ++ ordered'
                                        Just j  -> truePart ++ ordered' ++ afterJoin
                                            where (truePart, afterJoin) = break (==j) ordered
                        pure $ (stopped, label : rest)
                    Return {expr=expr} -> do
                        pure $ (Nothing, [label])


joinPoint :: (Ord a) => [a] -> [a] -> Maybe a
joinPoint xs ys = listToMaybe . filter (`S.member` xs') $ ys
    where xs' = S.fromList xs


orderedNodes :: Label -> FlowGraph Label -> [(Label, FlowNode Label)]
orderedNodes entry graph = map (\l -> (l, getNode l graph)) $ someOrder entry graph



renameLabels :: [Label] -> FlowGraph Label -> FlowGraph Label
renameLabels order graph = overNodes (M.fromList . map rename . M.toList) $ graph where
    rename (label, node) = (newLabel label, fmap newLabel node)
    newLabel l = Label . fromJust $ elemIndex l order


reorder :: Label -> FlowGraph Label -> FlowGraph Label
reorder entry graph = let order = someOrder entry graph in renameLabels order graph


findVars :: FlowGraph Label -> [VarId]
findVars = nub . concat . map basicStmtVars . concat . map body . filter isBlock . map snd . M.toList . nodes
    where
        basicStmtVars (BSetVar v x)  = v : basicExprVars x 
        basicStmtVars (BAdd   v a b) = v : (basicExprVars a) ++ (basicExprVars b)
        basicStmtVars (BMul   v a b) = v : (basicExprVars a) ++ (basicExprVars b)
        basicStmtVars (BSub   v a b) = v : (basicExprVars a) ++ (basicExprVars b)
        basicStmtVars (BEqual        v a b) = v : (basicExprVars a) ++ (basicExprVars b)
        basicStmtVars (BLess         v a b) = v : (basicExprVars a) ++ (basicExprVars b)
        basicStmtVars (BGreater      v a b) = v : (basicExprVars a) ++ (basicExprVars b)
        basicStmtVars (BLessEqual    v a b) = v : (basicExprVars a) ++ (basicExprVars b)
        basicStmtVars (BGreaterEqual v a b) = v : (basicExprVars a) ++ (basicExprVars b)
        basicStmtVars (BNot   v x)   = v : (basicExprVars x)
        basicStmtVars (BApp   v f exprs) = v : (concat . map basicExprVars $ exprs)

        basicExprVars (BVar v) = [v]
        basicExprVars (BNum _) = []

        isBlock (Block {}) = True
        isBlock _          = False

        

data OpIR label var
    = Nop
    | Push IntVal | Pop | Dup
    | Load var | Store var
    | Add | Mul | Sub | Incr | Decr
    | Equal | Less | Greater | LessEqual | GreaterEqual
    | Not
    | Jmp   label
    | JmpIf label
    | Call ProcId Int
    | Ret
    deriving (Eq, Show)

mapLabel :: (l1 -> l2) -> OpIR l1 var -> OpIR l2 var
mapLabel f (Jmp   label) = (Jmp   (f label)) 
mapLabel f (JmpIf label) = (JmpIf (f label))
mapLabel _ (Nop)       = Nop
mapLabel _ (Push val)  = Push val
mapLabel _ (Pop)       = Pop
mapLabel _ (Dup)       = Dup
mapLabel _ (Load var)  = Load var
mapLabel _ (Store var) = Store var
mapLabel _ (Add )      = Add 
mapLabel _ (Mul )      = Mul 
mapLabel _ (Sub )      = Sub 
mapLabel _ (Incr )     = Incr 
mapLabel _ (Decr)      = Decr
mapLabel _ (Equal       ) = Equal 
mapLabel _ (Less        ) = Less 
mapLabel _ (Greater     ) = Greater 
mapLabel _ (LessEqual   ) = LessEqual 
mapLabel _ (GreaterEqual) = GreaterEqual 
mapLabel _ (Not)       = Not
mapLabel _ (Call id n) = Call id n
mapLabel _ (Ret)       = Ret


mapVar :: (v1 -> v2) -> OpIR label v1 -> OpIR label v2
mapVar f (Load var)  = Load (f var)
mapVar f (Store var) = Store (f var)
mapVar _ (Nop)       = Nop
mapVar _ (Push val)  = Push val
mapVar _ (Pop)       = Pop
mapVar _ (Dup)       = Dup
mapVar _ (Add )      = Add 
mapVar _ (Mul )      = Mul 
mapVar _ (Sub )      = Sub 
mapVar _ (Incr )     = Incr 
mapVar _ (Decr)      = Decr
mapVar _ (Equal       ) = Equal 
mapVar _ (Less        ) = Less 
mapVar _ (Greater     ) = Greater 
mapVar _ (LessEqual   ) = LessEqual 
mapVar _ (GreaterEqual) = GreaterEqual 
mapVar _ (Not)       = Not
mapVar _ (Jmp   label) = Jmp   label 
mapVar _ (JmpIf label) = JmpIf label
mapVar _ (Call id n) = Call id n
mapVar _ (Ret)       = Ret

-- typ OpIR' = OpIR Label VarId
-- typ OpIR'' = OpIR Int VarIx


data ProcIR label var = ProcIR {
        funId :: FunId,
        params :: [var],
        vars :: [var],
        code :: [(Label, [OpIR Label VarId])]
    }
    deriving (Eq, Show)
        
-- fix syntax highlighting after the definition of ProcIR ?
blah :: Bool
blah = False

compileDefinition :: Definition -> Compile (ProcIR Label VarId)
compileDefinition def@(DDef funId params body) = do
    (entry, _graph) <- flowGraph def
    let graph = joinBlocks _graph
    let storeArgs = [(Label (-1), Store <$> params)]
    let bodyCode = compileGraph graph (someOrder entry graph)
    let vars = nub $ params ++ findVars graph
    pure $ ProcIR funId params vars (storeArgs ++ bodyCode)


compileDefinition' def = (overCode $ map (second optimizeOps) . removeRedundantJumps) <$> compileDefinition def
    where overCode f p = p {code = f (code p)}

compileGraph :: FlowGraph Label -> [Label] -> [(Label, [OpIR Label VarId])]
compileGraph graph order = map (\l -> c l (getNode l graph)) order where
    c :: Label -> FlowNode Label -> (Label, [OpIR Label VarId])
    c label node = (label, code) where
        code = case node of
            Block {body=body, next=next} ->
                (concat . map compileBasicStmt $ body) ++ [Jmp next]
            IfThenElse {cond=cond, ifTrue=ifTrue, ifFalse=ifFalse} ->
                (compileBasicExpr cond) : [Not, JmpIf ifFalse, Jmp ifTrue]
            Return {expr=expr} -> do
                (compileBasicExpr expr) : [Ret]



compileBasicStmt :: BasicStmt -> [OpIR Label VarId]
compileBasicStmt (BSetVar v x)  = [compileBasicExpr x, Store v]
compileBasicStmt (BAdd   v a b) = [compileBasicExpr a, compileBasicExpr b, Add,   Store v]
compileBasicStmt (BMul   v a b) = [compileBasicExpr a, compileBasicExpr b, Mul,   Store v]
compileBasicStmt (BSub   v a b) = [compileBasicExpr a, compileBasicExpr b, Sub,   Store v]
compileBasicStmt (BEqual        v a b) = [compileBasicExpr a, compileBasicExpr b, Equal,        Store v]
compileBasicStmt (BLess         v a b) = [compileBasicExpr a, compileBasicExpr b, Less,         Store v]
compileBasicStmt (BGreater      v a b) = [compileBasicExpr a, compileBasicExpr b, Greater,      Store v]
compileBasicStmt (BLessEqual    v a b) = [compileBasicExpr a, compileBasicExpr b, LessEqual,    Store v]
compileBasicStmt (BGreaterEqual v a b) = [compileBasicExpr a, compileBasicExpr b, GreaterEqual, Store v]
compileBasicStmt (BNot   v x)   = [compileBasicExpr x, Not, Store v]
compileBasicStmt (BApp   v f exprs) = let ecode = compileBasicExpr <$> exprs in ecode ++ [Call f (length exprs), Store v]

compileBasicExpr :: BasicExpr -> OpIR Label VarId
compileBasicExpr (BVar v) = Load v
compileBasicExpr (BNum n) = Push n



labelsToOffsets :: [(Label, [OpIR Label var])] -> [OpIR Int var]
labelsToOffsets blocks = concat . map (\(label, block) -> map (mapLabel (labelToOffset M.!)) block) $ blocks where
    labelToOffset :: Map Label Int
    labelToOffset = M.fromList $ zip labelsOnly (init . scanl (+) 0 . map length $ codeOnly)
    labelsOnly = map fst blocks   
    codeOnly   = map snd blocks   


removeRedundantJumps :: (Eq var, Show var) => [(Label, [OpIR Label var])] -> [(Label, [OpIR Label var])]
removeRedundantJumps = (trace' "\nafter removing jumps: ") . mapWithNext removeJumpToNext . (trace' "\nbefore removing jumps: ") where

    removeJumpToNext b1@(l1, n1) (Just b2@(l2, n2)) = if (not . null  $ n1) && (last n1 == (Jmp l2)) then (l1, init n1) else b1
    removeJumpToNext b1 _ = b1

    mapWithNext :: (a -> Maybe a -> b) -> [a] -> [b]
    mapWithNext f (x : rest@(y:xs)) = (f x $ Just y) : mapWithNext f rest
    mapWithNext f [x] = [f x Nothing]
    mapWithNext _ [] = []


toVMProc :: ProcIR Label VarId -> Compile (VM.Proc)
toVMProc (ProcIR funId params vars code) = do
    let nParams = length params
    forM_ vars $ \var ->
        freshVarIx >>= newVar var
    vs <- getVars
    let code' = toVMOp . mapVar (vs M.!) <$> labelsToOffsets code
    nVars <- length <$> getVars
    pure $ VM.Proc nParams nVars code'


toVMOp :: OpIR Int VarIx -> VM.Op
toVMOp (Load ix)   = VM.Load ix
toVMOp (Store ix)  = VM.Store ix
toVMOp (Nop)       = VM.Nop
toVMOp (Push val)  = VM.Push val
toVMOp (Pop)       = VM.Pop
toVMOp (Dup)       = VM.Dup
toVMOp (Add )      = VM.Add 
toVMOp (Mul )      = VM.Mul 
toVMOp (Sub )      = VM.Sub 
toVMOp (Incr )     = VM.Incr 
toVMOp (Decr)      = VM.Decr
toVMOp (Equal       ) = VM.Equal
toVMOp (Less        ) = VM.Less
toVMOp (Greater     ) = VM.Greater
toVMOp (LessEqual   ) = VM.LessEqual
toVMOp (GreaterEqual) = VM.GreaterEqual
toVMOp (Not)       = VM.Not
toVMOp (Jmp   off) = VM.Jmp   off 
toVMOp (JmpIf off) = VM.JmpIf off
toVMOp (Call id n) = VM.Call id n
toVMOp (Ret)       = VM.Ret

compileProgram :: [Definition] -> Compile VM.Program
compileProgram defs = do
    forM_ defs $ \(def@(DDef funId _ _)) -> do
        proc <- withVars M.empty $ do 
            procIR <- compileDefinition' def
            toVMProc procIR 
        newProc funId proc
    mainProc <- getProc "main"
    case mainProc of
        Nothing -> compileError "No definition for 'main'"
        Just proc -> do 
            when ((VM.nArgs proc) /= 0) $ compileError "main must take no arguments"
            ps <- getProcs
            pure $ VM.Program {mainProc=proc, allProcs=ps}


trace' s x = trace (s ++ " " ++ (show x)) x 



simplifyExpr :: Expr -> Expr
-- constant folding
simplifyExpr (EAdd (ENum x) (ENum y)) = (ENum (x+y))
simplifyExpr (EMul (ENum x) (ENum y)) = (ENum (x*y))
simplifyExpr (ESub (ENum x) (ENum y)) = (ENum (x-y))
simplifyExpr (EEqual        (ENum a) (ENum b)) = boolToExpr $ a == b
simplifyExpr (ELess         (ENum a) (ENum b)) = boolToExpr $ a <  b
simplifyExpr (EGreater      (ENum a) (ENum b)) = boolToExpr $ a >  b
simplifyExpr (ELessEqual    (ENum a) (ENum b)) = boolToExpr $ a <= b
simplifyExpr (EGreaterEqual (ENum a) (ENum b)) = boolToExpr $ a >= b
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
-- boring
simplifyExpr (EEqual        a b) = EEqual (simplifyExpr a) (simplifyExpr b)
simplifyExpr (ELess         a b) = ELess (simplifyExpr a) (simplifyExpr b)
simplifyExpr (EGreater      a b) = EGreater (simplifyExpr a) (simplifyExpr b)
simplifyExpr (ELessEqual    a b) = ELessEqual (simplifyExpr a) (simplifyExpr b)
simplifyExpr (EGreaterEqual a b) = EGreaterEqual (simplifyExpr a) (simplifyExpr b)
simplifyExpr (EAdd a b)   = (EAdd (simplifyExpr a) (simplifyExpr b))
simplifyExpr (EMul a b)   = (EMul (simplifyExpr a) (simplifyExpr b))
simplifyExpr (ESub a b)   = (ESub (simplifyExpr a) (simplifyExpr b))
simplifyExpr (ENot x)     = (ENot (simplifyExpr x))
simplifyExpr (EApp f exprs) = (EApp f (map simplifyExpr exprs))
simplifyExpr x = x

boolToExpr :: Bool -> Expr
boolToExpr b = if b then eConstTrue else eConstFalse



optimizeOps :: [OpIR Label var] -> [OpIR Label var]
-- TODO: optimize comparisons
optimizeOps (x      : Push 0 : Mul : rest) = optimizeOps $ Push 0   : rest
optimizeOps (Push 0 : x      : Mul : rest) = optimizeOps $ Push 0   : rest
optimizeOps (x      : Push 1 : Mul : rest) = optimizeOps $ x        : rest
optimizeOps (Push 1 : x      : Mul : rest) = optimizeOps $ x        : rest
optimizeOps (x      : Push 0 : Add : rest) = optimizeOps $ x        : rest
optimizeOps (Push 0 : x      : Add : rest) = optimizeOps $ x        : rest
optimizeOps (x      : Push 1 : Add : rest) = optimizeOps $ x : Incr : rest
optimizeOps (Push 1 : x      : Add : rest) = optimizeOps $ x : Incr : rest
optimizeOps (x      : Push 0 : Sub : rest) = optimizeOps $ x        : rest
optimizeOps (x      : Push 1 : Sub : rest) = optimizeOps $ x : Decr : rest
optimizeOps (Incr : Decr : rest) = optimizeOps rest
optimizeOps (Decr : Incr : rest) = optimizeOps rest
optimizeOps (Not  : Not  : rest) = optimizeOps rest
optimizeOps (op : rest) = op : optimizeOps rest
optimizeOps [] = []



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


p4 = DDef "pred" ["x"] [
        SNewVar "res" (ENum 0),
        SIfThenElse (EEqual (EVar "x") (ENum 0)) [
            SSetVar "res" (EVar "x")
        ] [
            SSetVar "res" (ESub (EVar "x") (ENum 1))
        ],
        SReturn (EVar "res")
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
    lift $ putStrLn "raw graph:"
    lift $ mapM_ (uncurry printNode) . M.toList . nodes $ g2
    lift $ blank
    lift $ putStrLn "ordered graph:"
    lift $ mapM_ (uncurry printNode) . orderedNodes start $ g2
    lift $ blank
    lift $ putStrLn "renamed labels:"
    lift $ mapM_ (uncurry printNode) . M.toList . nodes . reorder start $ g2
    lift $ blank >> blank
    cprog <- ExceptT . pure $ evalCompile (compileDefinition prog)
    lift $ putStrLn "compiled, IR1:"
    lift $ printCode $ code cprog 
    lift $ blank
    cprog2 <- ExceptT . pure $ evalCompile (compileDefinition' prog)
    lift $ putStrLn "compiled, IR1: (removed redundant jumps, optimized bytecode)"
    lift $ printCode $ code cprog2
    lift $ blank
    lift $ putStrLn "compiled, IR2:"
    lift $ printCode $ labelsToOffsets $ code cprog2 
    lift $ blank
    lift $ putStrLn "compiled, result:"
    result <- ExceptT . pure $ evalCompile (toVMProc cprog2)
    lift $ printCode $ VM.code result
    where
        blank = putStrLn "\n" 
        fromRight (Right x) = x 
        printCode :: (Show a) => [a] -> IO ()
        printCode = mapM_ putStrLn . map (uncurry showLine) . zip [0..]
        showLine n c = show n ++ "\t" ++ show c

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


-- NOTE: converting instructions:
--
--          sub dst x y  =  mov dst x
--                          sub dst y 
--
--          sub x x y    =  sub x y 
--
--       HOWEVER
--       this transformation isn't necessarily valid for instructions like
--
--          add R0 [R0] [R0]
--
--       because the first translated instruction modifies R0.
--       in that case, we would have to do
--
--          mov R1 [R0]
--          add R1 [R0]
--          mov R0 R1

{-# LANGUAGE DeriveFunctor #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module RegisterCompiler where

import qualified RegisterVM
import Util

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
import Data.Semigroup

import Debug.Trace (trace)


-- ##################
-- #    Compiler    #
-- ##################

data Module = Module [Definition]

data Definition
    = DDef FunId [(VarId, TypeId)] TypeId [Stmt]
    deriving (Eq)


data Stmt
    = SPass
    | SNewVar VarId TypeId Expr
    | SSetVar VarId Expr
    | SIfThenElse Expr [Stmt] [Stmt]
    | SWhile Expr [Stmt]
    | SForFromTo VarId TypeId Expr Expr [Stmt]
    | SBreak
    | SContinue
    | SReturn Expr
    deriving (Eq)


data Expr
    = ENum Int NumType
    | EVar VarId
    | E1 Op1 Expr
    | E2 Op2 Expr Expr
    | EApp FunId [Expr]
    -- | ECast Expr TypeId
    -- | EIfThenElse Expr Expr Expr
    -- | ELet VarId Expr Expr
    deriving (Eq)


type VarId  = String
type FunId  = String

data TypeId
    = SimpleType String
    | ParametrizedType String [TypeId]
    deriving (Eq)

instance Show TypeId where
    show (SimpleType name) = name
    show (ParametrizedType name params) = name ++ (brackets . joinWith ", " $ params)


type StackFrameOffset = Int
type RegisterId = Int

data VarLoc
    = VarLocRegister RegisterId
    | VarLocStack StackFrameOffset
    deriving (Eq, Show)


data TType
    = TBool
    | TChar
    | TPtr TType
    | TNum NumType
    | TUnit
    | TNoReturn
    deriving (Eq)

instance Show TType where
    show TBool         = "bool"
    show TChar         = "char"
    show (TNum TInt)   = "int" 
    show (TNum TUInt)  = "uint"
    show TUnit         = "()"  
    show TNoReturn     = "!"   
    show (TPtr typ)    = "ptr[" ++ (show typ) ++ "]" 

data NumType
    = TInt
    | TUInt
    deriving (Eq, Show)

data FunType = FunType [TType] TType deriving (Eq, Show)


instance Show Definition where
    show (DDef funId varsAndTypes retTypeId body) =
        "func " ++ funId
        ++ (parens . joinWith' ", " . map (
            \(varId, typeId) -> showVarId varId ++ ": " ++ (show typeId)) $ varsAndTypes
        )
        ++ " -> " ++ (show retTypeId) ++ " "
        ++ (showBlock body)

showBlock :: [Stmt] -> String
showBlock b = "{\n" ++ (joinWith' "" . map indent' . map show $ b) ++ "}\n"


instance Show Stmt where
    show (SPass) = "pass"
    show (SNewVar var typeId expr) = (showVarId var) ++ ": " ++ (show typeId) ++ " <- " ++ (show expr)
    show (SSetVar var expr) = (showVarId var) +=+ (show expr)
    show (SIfThenElse cond trueBody falseBody) = 
        "if " ++ (show cond) ++ " " ++ (showBlock trueBody) ++ "else " ++ (showBlock falseBody)
    show (SWhile cond body) = 
        "while " ++ (show cond) ++ " " ++ (showBlock body)
    show (SForFromTo var typeId low high body) = 
        "for " ++ (showVarId var) ++ ": " ++ (show typeId) ++ " in [" ++ (show low) ++ " .. " ++ (show high) ++ "] " ++ (showBlock body)
    show (SBreak) = "break"
    show (SContinue) = "continue"
    show (SReturn expr) = "return " ++ (show expr)


instance Show Expr where
    show (ENum n t) = showNum n t
    show (EVar v) = showVarId v
    show (E1 op x) = parens ((show op) ++ (show x))
    show (E2 op a b) = parens ((show a) +|+ (show op) +|+ (show b))
    show (EApp fun exprs) = fun ++ (parens . concat . intersperse ", " . map show $ exprs)

showNum :: (Show a, Num a) => a -> NumType -> String
showNum n t = (show n) ++ (case t of TInt -> ""; TUInt -> "u")


data Op1
    = OpNot
    deriving (Eq)


data Op2
    = OpAdd
    | OpMul
    | OpSub
    | OpEqual
    | OpLess
    | OpGreater
    | OpLessEqual
    | OpGreaterEqual
    deriving (Eq)

instance Show Op1 where
    show OpNot = "!"

instance Show Op2 where
    show OpAdd          = "+"
    show OpMul          = "*"
    show OpSub          = "-"
    show OpEqual        = "=="
    show OpLess         = "<"
    show OpGreater      = ">"
    show OpLessEqual    = "<="
    show OpGreaterEqual = ">="


showVarId v = v
showTypeId t = t

eConstFalse = ENum 0
eConstTrue = ENum 1





type Compile a = ExceptT String (State CompilerState) a

data CompilerState = CompilerState
    { varTypes  :: VarTypes
    , funTypes  :: FunTypes
    , varLocs   :: VarLocs
    -- , procs     :: Procs
    , uniqueGen :: Int
    }

type VarLocs  = Map VarId VarLoc
type VarTypes = Map VarId TType
type FunTypes = Map VarId FunType

-- type Procs = Map FunId RegisterVM.Proc

emptyCompilerState :: CompilerState
emptyCompilerState = CompilerState {varTypes=M.empty, funTypes=M.empty, varLocs=M.empty, {-procs=M.empty,-} uniqueGen=0}

runCompile :: Compile a -> State CompilerState (Either String a)
runCompile = runExceptT

evalCompile :: Compile a -> Either String a
evalCompile = (`evalState` emptyCompilerState) . runCompile



-- operatorSignature :: Compile


compileError :: String -> Compile a
compileError = throwE

orError' :: Compile (Maybe a) -> String -> Compile a
orError' cma msg = cma >>= (`orError` msg) 

orError :: Maybe a -> String -> Compile a
(Just a) `orError` _   = pure a
_        `orError` msg = throwE msg



declFunType :: FunId -> FunType -> Compile ()
declFunType fun typ = modifyFunTypes (M.insert fun typ)

modifyFunTypes :: (FunTypes -> FunTypes) -> Compile ()
modifyFunTypes f =  lift $ modify (overFunTypes f)

getFunType :: FunId -> Compile (Maybe FunType)
getFunType fun = M.lookup fun <$> getFunTypes

getFunTypes :: Compile FunTypes
getFunTypes = funTypes <$> lift get



declVarType :: VarId -> TType -> Compile ()
declVarType var typ = modifyVarTypes (M.insert var typ)

modifyVarTypes :: (VarTypes -> VarTypes) -> Compile ()
modifyVarTypes f =  lift $ modify (overVarTypes f)

getVarType :: VarId -> Compile (Maybe TType)
getVarType var = M.lookup var <$> getVarTypes

getVarTypes :: Compile VarTypes
getVarTypes = varTypes <$> lift get



getVars :: Compile VarLocs
getVars = varLocs <$> lift get

putVars :: VarLocs -> Compile ()
putVars vs = modifyVars (const vs)

modifyVars :: (VarLocs -> VarLocs) -> Compile ()
modifyVars f =  lift $ modify (overVarLocs f)

newVar :: VarId -> VarLoc -> Compile ()
newVar var ix = modifyVars (M.insert var ix)

getVarLoc :: VarId -> Compile (Maybe VarLoc)
getVarLoc var = M.lookup var <$> getVars

freshStackVar :: Compile VarLoc
-- freshStackVar = length <$> getVars
freshStackVar = undefined

withVars :: VarLocs -> Compile a -> Compile a
withVars vs ca = do 
    old <- getVars
    putVars vs
    a <- ca
    putVars old
    pure a


resolveType :: TypeId -> Compile TType
resolveType (SimpleType name) = case name of
    "bool" -> pure TBool
    "char" -> pure TChar
    "int"  -> pure $ TNum TInt
    "uint" -> pure $ TNum TUInt
    "()"   -> pure TUnit
    "!"    -> pure TNoReturn
    _      -> throwE $ "undefined type" ++ name
resolveType (ParametrizedType name params) = case name of
    "ptr" -> case params of
        [pname] -> TPtr <$> resolveType pname
        _       -> throwE $ "too many parameters for " ++ name ++ ": " ++ (show params) 
    _      -> throwE $ "undefined type" ++ name





-- getProcs :: Compile Procs
-- getProcs = procs <$> lift get

-- getProc :: FunId -> Compile (Maybe RegisterVM.Proc)
-- getProc funId = M.lookup funId <$> getProcs

-- modifyProcs :: (Procs -> Procs) -> Compile ()
-- modifyProcs f =  lift $ modify (overProcs f)

-- newProc :: FunId -> RegisterVM.Proc -> Compile ()
-- newProc funId proc = modifyProcs (M.insert funId proc)


getFresh :: Compile Int
getFresh = uniqueGen <$> lift get

modifyFresh :: (Int -> Int) -> Compile ()
modifyFresh f = modify (overUniqueGen f) 

fresh :: Compile Int
fresh = do {x <- getFresh; modifyFresh (+1); pure x}


freshLabel :: Compile Label
freshLabel = Label <$> fresh


toVarId :: Int -> VarId
toVarId = ("_t_" ++) . show

freshVarId :: Compile VarId
freshVarId = toVarId <$> fresh


overVarTypes  f state = state { varTypes  = f $ varTypes  state}
overFunTypes  f state = state { funTypes  = f $ funTypes  state}
overVarLocs   f state = state { varLocs   = f $ varLocs   state}
-- overProcs     f state = state { procs     = f $ procs     state}
overUniqueGen f state = state { uniqueGen = f $ uniqueGen state}


newtype Label = Label {unLabel :: Int} deriving (Eq, Ord)

underLabel f = Label . f . unLabel
asLabel f = unLabel . f . Label

newLabel :: Label -> Label
newLabel = underLabel (+1)

instance Show Label where show (Label l) = "L" ++ (show l)



data FlowGraph x l = FlowGraph {nodes :: Map l (FlowNode x l)} deriving (Eq, Show)

data FlowNode x l
    = Block      {extra :: x, body :: [BasicStmt], next :: l}
    | IfThenElse {extra :: x, cond :: BasicExpr, ifTrue, ifFalse :: l}
    | Return     {extra :: x, expr :: BasicExpr}
    deriving (Eq, Show, Functor)

data BasicStmt
    = BSetVar TType VarId BasicExpr 
    | B1 TType VarId Op1 BasicExpr
    | B2 TType VarId Op2 BasicExpr BasicExpr
    | BApp TType VarId FunId [BasicExpr]
    deriving (Eq)

data BasicExpr
    = BVar TType VarId 
    | BNum NumType Int 
    deriving (Eq)


type FlowGraph' l = FlowGraph () l
type FlowNode'  l = FlowNode  () l
block'      = Block ()
ifThenElse' = IfThenElse ()
return'     = Return ()

overNodes f (g @ FlowGraph {nodes=ns}) = g { nodes = f ns }
emptyFlowGraph = FlowGraph {nodes=M.empty}
overExtra f n = n {extra = f (extra n)}

getNode :: (Ord l) => l -> FlowGraph x l -> FlowNode x l
getNode l = (M.! l) . nodes

insertNode :: (Ord l) => l -> FlowNode x l -> FlowGraph x l -> FlowGraph x l
insertNode l n = overNodes (M.insert l n)

insertNodes :: (Ord l) => [(l, FlowNode x l)] -> FlowGraph x l -> FlowGraph x l
insertNodes ns = overNodes (M.union (M.fromList ns))

deleteNode :: (Ord l) => l -> FlowGraph x l -> FlowGraph x l
deleteNode l = overNodes (M.delete l)

graphLabels :: FlowGraph x l -> [l]
graphLabels = map fst . M.toList . nodes


instance Show BasicExpr where
    show (BVar typ v) = (showVarId v) -- ++ ": " ++ (show typ) 
    show (BNum ntyp n) = showNum n ntyp

instance Show BasicStmt where
    show (BSetVar _ v x)       = (showVarId v) +=+ (show x)
    show (B1 _ v op x)         = (showVarId v) +=+ (show op) ++ (show x)
    show (B2 _ v op a b)       = (showVarId v) +=+ ((show a) +|+ (show op) +|+ (show b))
    show (BApp _ v f exprs)    = (showVarId v) +=+ (f ++ (parens . concat . intersperse ", " . map show $ exprs))



data Ctx l
    = BlockCtx {end :: l}
    | LoopCtx  {cont, end :: l}



flowGraph :: Definition -> Compile (Label, FlowGraph' Label)
flowGraph (DDef funId argsAndTypes retTypeId body) = do
    forM_ argsAndTypes $ \(arg, typeId) -> do
        resolveType typeId >>= declVarType arg
    go [] emptyFlowGraph body
    where
    go :: [Ctx Label] -> (FlowGraph' Label) -> [Stmt] -> Compile (Label, FlowGraph' Label)
    go []      _     [] = compileError "missing return statement"
    go (ctx:_) graph [] = do
        case ctx of
            LoopCtx {} -> pure $ (cont ctx, graph)
            _          -> pure $ (end ctx,  graph)
    go ctxs    graph (stmt:stmts) =
        case stmt of
            SPass -> do
                go ctxs graph stmts
            SNewVar var typeId expr -> do
                v <- getVarLoc var
                when (isJust $ v) $
                    throwE $ "duplicate variable or argument: " ++ (showVarId var)
                l <- freshLabel
                typ <- resolveType typeId
                declVarType var typ
                (expr', computeExpr, graph) <- computeBlock expr typ graph l
                (next, graph) <- go ctxs graph stmts
                let node = block' [BSetVar typ var expr'] next
                pure $ (computeExpr, insertNode l node graph)
            SSetVar var expr -> do
                l <- freshLabel
                typ <- getVarType var `orError'` ("undefined variable: " ++ var)
                (expr', computeExpr, graph) <- computeBlock expr typ graph l
                (next, graph) <- go ctxs graph stmts
                let node = block' [BSetVar typ var expr'] next
                pure $ (computeExpr, insertNode l node graph)
            SIfThenElse cond trueBody falseBody -> do
                ifCond <- freshLabel
                (condExpr, computeCond, graph) <- computeBlock cond TBool graph ifCond 
                (next, graph) <- go ctxs graph stmts
                let ctxs' = BlockCtx {end=next} : ctxs
                (trueCont,  graph) <- go ctxs' graph trueBody
                (falseCont, graph) <- go ctxs' graph falseBody
                let ifCondNode = IfThenElse {extra=(), cond=condExpr, ifTrue=trueCont, ifFalse=falseCont}
                pure $ (computeCond, insertNode ifCond ifCondNode graph)
            SWhile cond body -> do
                ifCond <- freshLabel
                (condExpr, computeCond, graph) <- computeBlock cond TBool graph ifCond 
                (next, graph) <- go ctxs graph stmts
                let ctxs' = LoopCtx {cont=computeCond, end=next} : ctxs
                (bodyCont,  graph) <- go ctxs' graph body
                let node = IfThenElse {extra=(), cond=condExpr, ifTrue=bodyCont, ifFalse=next}
                pure $ (computeCond, insertNode ifCond node graph)
            SForFromTo var typeId low high body -> do
                loopInit <- freshLabel
                typ <- resolveType typeId
                numType <- assertIsNumericType typ
                declVarType var typ
                (highExpr, computeHigh, graph) <- computeBlock high typ graph loopInit
                (lowExpr, computeLow, graph) <- computeBlock low typ graph computeHigh
                loopIf   <- freshLabel
                (condExpr, computeCond, graph) <- computeBlock (E2 OpLessEqual (EVar var) (toExpr highExpr)) TBool graph loopIf
                loopIncr <- freshLabel
                (incrExpr, computeIncr, graph) <- computeBlock (E2 OpAdd (EVar var) (ENum 1 numType)) typ graph loopIncr
                (next, graph) <- go ctxs graph stmts
                let ctxs' = LoopCtx {cont=computeIncr, end=next} : ctxs
                (bodyCont,  graph) <- go ctxs' graph body
                let incrNode = block' [BSetVar typ var incrExpr] computeCond
                    ifNode   = IfThenElse {extra=(), cond=condExpr, ifTrue=bodyCont, ifFalse=next}
                    initNode = block' [BSetVar typ var lowExpr] computeCond
                pure $ (computeLow, insertNodes [(loopInit, initNode), (loopIf, ifNode), (loopIncr, incrNode)] graph)
            SBreak -> do 
                end <- findLoopEnd ctxs `orError` "break outside of loop"
                pure $ (end, graph)
            SContinue -> do
                cont <- findLoopCont ctxs `orError` "continue outside of loop"
                pure $ (cont, graph)
            SReturn expr -> do
                l <- freshLabel
                retTyp <- resolveType retTypeId
                (expr', computeExpr, graph) <- computeBlock expr retTyp graph l 
                let node = return' expr'
                pure $ (computeExpr, insertNode l node graph)


    computeBlock :: Expr -> TType -> FlowGraph' Label -> Label -> Compile (BasicExpr, Label, FlowGraph' Label)
    computeBlock expr typ graph next = do
        computeExpr <- freshLabel
        (expr', temps) <- toBasicExpr expr typ
        pure $ if not . null $ temps
                   then (expr', computeExpr, insertNode computeExpr (block' temps next) graph )
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


exprType :: Expr -> Compile TType
exprType e@(ENum n ntyp) = pure $ TNum ntyp
exprType (EVar v) = getVarType v `orError'` ("undefined variable: " ++ v)
exprType (E1 op x) = case op of
    OpNot -> do
        assertType x TBool
        pure TBool
exprType (E2 op a b) = case op of
    OpAdd -> do assertSameType a b; exprType a
    OpMul -> do assertSameType a b; exprType a
    OpSub -> do assertSameType a b; exprType a
    OpEqual        -> do assertSameType a b; pure $ TBool
    OpLess         -> do assertSameType a b; pure $ TBool
    OpGreater      -> do assertSameType a b; pure $ TBool
    OpLessEqual    -> do assertSameType a b; pure $ TBool
    OpGreaterEqual -> do assertSameType a b; pure $ TBool
exprType (EApp fun exprs) = do 
    FunType argTypes retTyp <- getFunType fun `orError'` ("undefined function: " ++ fun)
    let nExpected = length argTypes
        nGot      = length exprs
    when (nExpected /= nGot) $ throwE $
        "function " ++ fun ++ " expects "
        ++ (show nExpected) ++ " arguments, but got " ++ (show nGot)
    sequence $ zipWith assertType exprs argTypes
    pure retTyp

assertType :: Expr -> TType -> Compile TType
assertType expr expected = do
    actual <- exprType expr
    when (actual /= expected) $ throwE $
        "expression " ++ (show expr) ++ " should have type "
        ++ (show expected) ++ ", but has type " ++ (show actual)
    pure actual


assertIsNumericExpr :: Expr -> Compile NumType
assertIsNumericExpr e = do
    t <- exprType e
    case t of 
        TNum nt -> pure nt 
        _      -> throwE $
            "expression " ++ (show e) ++ " should be numeric, "
            ++ "but has type " ++ (show t)

assertIsNumericType :: TType -> Compile NumType
assertIsNumericType t =
    case t of 
        TNum nt -> pure nt 
        _      -> throwE $
            "type " ++ (show t) ++ " is invalid here, "
            ++ "numeric type expected "

assertSameType :: Expr -> Expr -> Compile TType
assertSameType a b = do
    ta <- exprType a
    tb <- exprType b
    when (ta /= tb) $ throwE $
        "expressions " ++ (show a) ++ " and " ++ (show b)
        ++ " should be of the same type, but "
        ++ (show a) ++ " has type " ++ (show ta)
        ++" and " ++ (show b) ++ " has type " ++ (show tb)
    pure ta



toBasicExpr :: Expr -> TType -> Compile (BasicExpr, [BasicStmt])
toBasicExpr expr typ = do 
    assertType expr typ
    toBasicExpr' expr typ 

toBasicExpr' :: Expr -> TType -> Compile (BasicExpr, [BasicStmt])
toBasicExpr' (ENum n ntyp) _ = pure (BNum ntyp n, [])
toBasicExpr' (EVar v) typ = pure (BVar typ v, [])
toBasicExpr' e@(E1 op x) typ  = do
    -- need type signature of op!!!!
    xt <- exprType x
    (v1, s1) <- toBasicExpr x xt
    r <- freshVarId
    declVarType r typ
    pure (BVar typ r, s1 ++ [B1 typ r op v1])
toBasicExpr' e@(E2 op a b) typ = do
    -- need type signature of op!!!!
    at <- exprType a
    bt <- exprType b
    (v1, s1) <- toBasicExpr a at
    (v2, s2) <- toBasicExpr b bt
    r <- freshVarId
    declVarType r typ
    pure (BVar typ r, s1 ++ s2 ++ [B2 typ r op v1 v2])
toBasicExpr' (EApp fun exprs) typ = do
    -- need type signature of fun!!!!
    FunType argTypes _ <- getFunType fun `orError'` ("undefined function: " ++ fun)
    xs <- sequence $ zipWith toBasicExpr exprs argTypes
    let vars  = map fst xs
    let temps = concat $ map snd xs
    r <- freshVarId
    declVarType r typ
    pure (BVar typ r, temps ++ [BApp typ r fun vars])


toExpr :: BasicExpr -> Expr
toExpr (BVar _ v) = EVar v
toExpr (BNum ntyp n) = ENum n ntyp


findPredecessors :: Label -> FlowGraph x Label -> [Label]
findPredecessors l g = map fst . filter ((continuesTo l) . snd) .  M.toList . nodes $ g

continuesTo :: Label -> FlowNode x Label -> Bool
continuesTo target n = case n of
    Block {next=next} -> next == target
    IfThenElse {ifTrue=ifTrue, ifFalse=ifFalse} -> ifTrue == target || ifFalse == target
    Return {} -> False



joinBlocks :: (Semigroup x) => FlowGraph x Label -> FlowGraph x Label
joinBlocks g = (`execState` g) $ do
    forM_ (graphLabels g) $ \label -> do
        g <- get
        when (label `M.member` (nodes g)) $
            case getNode label g of
                Block x2 body2 next ->
                    case findPredecessors label g of
                        [pre] -> case getNode pre g of
                            Block x1 body1 _ -> do
                                modify (deleteNode label)
                                let node' = Block (x1 <> x2) (body1++body2) next
                                modify (insertNode pre node')
                            _ -> pure () 
                        _ -> pure () 
                _ -> pure ()




someOrder :: Label -> FlowGraph x Label -> [Label]
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


orderedNodes :: Label -> FlowGraph x Label -> [(Label, FlowNode x Label)]
orderedNodes entry graph = map (\l -> (l, getNode l graph)) $ someOrder entry graph



renameLabels :: [Label] -> FlowGraph x Label -> FlowGraph x Label
renameLabels order graph = overNodes (M.fromList . map rename . M.toList) $ graph where
    rename (label, node) = (newLabel label, fmap newLabel node)
    newLabel l = Label . fromJust $ elemIndex l order


reorder :: Label -> FlowGraph x Label -> FlowGraph x Label
reorder entry graph = let order = someOrder entry graph in renameLabels order graph


findVars :: FlowGraph x Label -> [VarId]
findVars = nub . concat . map basicStmtVars . concat . map body . filter isBlock . map snd . M.toList . nodes




nodeVars (Block {body=body})      = concat . map basicStmtVars $ body
nodeVars (IfThenElse {cond=cond}) = basicExprVars cond
nodeVars (Return {expr=expr})     = basicExprVars expr

basicStmtVars (BSetVar _ v x)    = v : basicExprVars x 
basicStmtVars (B1 _ v _ x)       = v : (basicExprVars x)
basicStmtVars (B2 _ v _ a b)     = v : (basicExprVars a) ++ (basicExprVars b)
basicStmtVars (BApp _ v f exprs) = v : (concat . map basicExprVars $ exprs)

basicExprVars (BVar _ v) = [v]
basicExprVars (BNum _ _) = []


isBlock (Block {}) = True
isBlock _          = False

isReturn (Return {}) = True
isReturn _           = False

isIfThenElse (IfThenElse {}) = True
isIfThenElse _               = False


data BlockVars = BlockVars {inVars, outVars :: Set VarId}
    deriving (Eq)

instance Semigroup BlockVars where
    bv1 <> bv2 = BlockVars {inVars  = (inVars  bv1) `S.union` (inVars  bv2),
                            outVars = (outVars bv1) `S.union` (outVars bv2)}
instance Monoid BlockVars where
    mempty = BlockVars {inVars = S.empty, outVars = S.empty}
    mappend = (<>)
instance Show BlockVars where
    show b = parens $ "in: " ++ (showVarSet . inVars $ b) ++ ", out: " ++ (showVarSet . outVars $ b)
                where showVarSet = braces . concat . intersperse ", " . map showVarId . S.toList


liveness :: FlowGraph x Label -> FlowGraph BlockVars Label
liveness graph = (`execState` graph') $ mapM_ (go S.empty) endLabels where
        endLabels = map fst . filter (isReturn . snd) . M.toList . nodes $ graph
        graph'    = overNodes (overExtra (const mempty) <$>) $ graph
        go :: Set VarId -> Label -> State (FlowGraph BlockVars Label) () 
        go successorInVars label = do
            node <- getNode label <$> get
            let vars @ BlockVars {inVars=inv, outVars=outv} = extra node
                (read, written) = nodeVars' node
                outv' = outv `S.union` successorInVars
                inv'  = inv  `S.union` (read    `S.union` (successorInVars `S.difference` written))
                vars' = BlockVars {inVars = inv', outVars=outv'}
                node' = node {extra = BlockVars {inVars  = inv', outVars = outv' } }
            when (vars /= vars') $ do
                modify $ insertNode label node'
                mapM_ (go inv') $ findPredecessors label graph

        nodeVars' :: FlowNode x l -> (Set VarId, Set VarId)
        nodeVars' (Block {body=body}) = go S.empty body where
            go local (stmt:rest) = let (extRead, written) = basicStmtVars' stmt 
                                       extRead' = extRead `S.difference` local
                                    in  (extRead', S.singleton written)  `pairwiseUnion`  go (S.insert written local) rest
            go local [] = (S.empty, local)
            -- go _ [] = (S.empty, S.empty)
            pairwiseUnion (a, b) (c, d) = (a `S.union` c, b `S.union` d)
        nodeVars' (IfThenElse {cond=cond}) = (basicExprVars' cond, S.empty)
        nodeVars' (Return {expr=expr})     = (basicExprVars' expr, S.empty)

        basicStmtVars' (BSetVar _ v x)  = (basicExprVars' x,                                v)
        basicStmtVars' (B1 _ v _ x)       = (basicExprVars' x,                                v)
        basicStmtVars' (B2 _ v _ a b)     = ((basicExprVars' a) `S.union` (basicExprVars' b), v)
        basicStmtVars' (BApp _ v f exprs) = (S.unions . map basicExprVars' $ exprs,           v)

        basicExprVars' = S.fromList . basicExprVars

        -- startLabels = map fst . filter (null . (`findPredecessors` graph) . fst) . M.toList . nodes $ graph




eNot = E1 OpNot
eAdd          = E2 OpAdd
eMul          = E2 OpMul
eSub          = E2 OpSub
eEqual        = E2 OpEqual
eLess         = E2 OpLess
eGreater      = E2 OpGreater
eLessEqual    = E2 OpLessEqual
eGreaterEqual = E2 OpGreaterEqual
tt = SimpleType

uu = (`ENum` TUInt)
ii = (`ENum` TInt)

e1 = (eAdd
        (uu 3)
        (eMul
            (uu 2)
            (uu 2)))


p1 = [
        SIfThenElse (eEqual (EVar "x") (EVar "y")) [
            SSetVar "x" (eAdd (EVar "x") (ii 1)),
            SSetVar "x" (eAdd (EVar "x") (ii 1))
        ] [
            SReturn (EVar "y")
        ],
        SReturn (EVar "x")
    ]



p2 = DDef "fib" [("i", tt "uint")] (tt "uint") [
        SNewVar "a" (tt "uint") (uu 1),
        SNewVar "b" (tt "uint") (uu 2),
        SNewVar "c" (tt "uint") (uu 0),
        SForFromTo "j" (tt "uint") (uu 0) (eSub (EVar "i") (uu 3)) [
            SSetVar "c" (eAdd (EVar "a") (EVar "b")),
            SSetVar "a" (EVar "b"),
            SSetVar "b" (EVar "c")
        ],
        SReturn (EVar "a")
    ]


p3 = DDef "ple" [] (tt "int") [
        SNewVar "x" (tt "int") (ii 0),
        SForFromTo "i" (tt "int") (ii 1) (ii 10) [
            SForFromTo "j" (tt "int") (ii 1) (ii 10) [
                SSetVar "x" (eAdd (EVar "x") (eAdd (EVar "i") (EVar "j")))
            ]
        ],
        SReturn (EVar "x")
    ]


p4 = DDef "pred" [("x", tt "uint")] (tt "uint") [
        SNewVar "res" (tt "uint") (uu 0),
        SIfThenElse (eEqual (EVar "x") (uu 0)) [
            SSetVar "res" (EVar "x")
        ] [
            SSetVar "res" (eSub (EVar "x") (uu 1))
        ],
        SReturn (EVar "res")
    ]



main = either (putStrLn . ("Error: "++)) pure  =<<  (runExceptT mainE)

mainE :: ExceptT String IO ()
mainE = do
    -- (_, vars) <- ExceptT . pure $ evalCompile (toBasicExpr e1)
    -- lift $ mapM_ print vars
    -- lift $ blank
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
    let g3 = reorder start $ g2
    lift $ putStrLn "renamed labels:"
    lift $ mapM_ (uncurry printNode) . M.toList . nodes $ g3
    lift $ blank >> blank
    lift $ putStrLn "liveness:"
    lift $ mapM_ (uncurry printNode) . M.toList . nodes $ liveness g3
    lift $ blank >> blank
    -- cprog <- ExceptT . pure $ evalCompile (compileDefinition prog)
    -- lift $ putStrLn "compiled, IR1:"
    -- lift $ printCode $ code cprog 
    -- lift $ blank
    -- cprog2 <- ExceptT . pure $ evalCompile (compileDefinition' prog)
    -- lift $ putStrLn "compiled, IR1: (removed redundant jumps, optimized bytecode)"
    -- lift $ printCode $ code cprog2
    -- lift $ blank
    -- lift $ putStrLn "compiled, IR2:"
    -- lift $ printCode $ labelsToOffsets $ code cprog2 
    -- lift $ blank
    -- lift $ putStrLn "compiled, result:"
    -- result <- ExceptT . pure $ evalCompile (toVMProc cprog2)
    -- lift $ printCode $ RegisterVM.code result
    where
        blank = putStrLn "\n" 
        fromRight (Right x) = x 
        fromRight (Left y) = error $ "fromRight: " ++ (show y)  
        printCode :: (Show a) => [a] -> IO ()
        printCode = mapM_ putStrLn . map (uncurry showLine) . zip [0..]
        showLine n c = show n ++ "\t" ++ show c

        printNode l n = do
            putStrLn $ (show l) ++ ": " ++ (show . extra $ n)
            case n of 
                IfThenElse {cond=cond, ifTrue=ifTrue, ifFalse=ifFalse} -> do
                    putStrLn $ "if " ++ (show cond)
                    putStrLn . indent $ "then -> " ++ (show ifTrue)
                    putStrLn . indent $ "else -> " ++ (show ifFalse)
                Return {expr=expr} -> do
                    putStrLn $ "return " ++ (show expr)
                Block {body=body, next=next} -> do 
                    mapM_ (putStrLn . indent . show) body
                    putStrLn $ "  -> " ++ (show next) 



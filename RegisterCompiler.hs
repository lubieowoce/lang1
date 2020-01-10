
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

{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE KindSignatures, StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}




module RegisterCompiler where

import Control.Lens
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Bifunctor.TH

import qualified RegisterVM
import Util

import Data.Map (Map)
import qualified Data.Map as M

import Data.Set (Set)
import qualified Data.Set as S

import Data.Tree (Tree) 
import qualified Data.Tree as T

import Data.List (nub, intersperse, elemIndex)
import Data.Maybe (fromJust, isJust, listToMaybe, maybe)
import Data.Char (ord)

import Control.Monad.Reader
import Control.Monad.Writer hiding ((<>))
import Control.Monad.State
import Control.Monad.Trans.Except
import Control.Monad (forM)

import Data.Bifunctor (Bifunctor, bimap, first, second)
import Data.Semigroup

import Data.Void (Void, absurd)
import Data.Functor.Const (Const (..))

import Data.Coerce (coerce)
import Debug.Trace (trace)

-- ##################
-- #    Compiler    #
-- ##################




data ModuleG typ var = Module [DefinitionG typ var] 
    deriving (Eq)

data DefinitionG typ var
    = DDef FunId [(var, typ)] typ [StmtG typ var]
    deriving (Eq)


data StmtG typ var
    = SPass
    | SNewVar var typ (ExprG typ var)
    | SSetVar var (ExprG typ var)
    | SSetIndex var (ExprG typ var) (ExprG typ var)
    | SIfThenElse (ExprG typ var) [StmtG typ var] [StmtG typ var]
    | SWhile (ExprG typ var) [StmtG typ var]
    | SForFromTo var typ (ExprG typ var) (ExprG typ var) [StmtG typ var]
    | SBreak
    | SContinue
    | SReturn (ExprG typ var)
    deriving (Eq)


data ExprG typ var
    = ENum Int NumType
    | EChar Char
    | EVar var
    | E1 Op1 (ExprG typ var)
    | E2 Op2 (ExprG typ var) (ExprG typ var)
    | EApp FunId [(ExprG typ var)]
    | EIndex (ExprG typ var) (ExprG typ var)
    | EArrayLiteral typ [(ExprG typ var)]
    | ECast (ExprG typ var) typ
    | EAddressOf (ExprG typ var) -- &x, &x[y], &x.foo
    -- | EIfThenElse (ExprG typ) (ExprG typ) (ExprG typ)
    -- | ELet var (ExprG typ) (ExprG typ)
    deriving (Eq)

data Op1
    = OpNot
    deriving (Eq)

data Op2
    = OpAdd
    | OpSub
    | OpMul
    | OpDiv
    | OpMod
    | OpEqual
    | OpLess
    | OpGreater
    | OpLessEqual
    | OpGreaterEqual
    deriving (Eq)


type Module     = ModuleG     TypeId VarId
type Definition = DefinitionG TypeId VarId
type Stmt       = StmtG       TypeId VarId
type Expr       = ExprG       TypeId VarId


newtype VarId = VarId {unVarId :: String}
    deriving (Eq, Ord)

instance Show VarId where
    show = unVarId

type FunId  = String

data TypeId
    = SimpleType String
    | ParametrizedType String [TypeId]
    | ArrayType TypeId Int
    deriving (Eq)

instance Show TypeId where
    show (SimpleType name) = name
    show (ParametrizedType name params) = name ++ (brackets . joinWith ", " $ params)
    show (ArrayType elType size) = brackets $ (show elType) ++ ", " ++ (show size)



data TType
    = TBool
    | TChar
    | TPtr TType
    | TArray TType Int
    | TNum NumType
    | TUnit
    | TEmpty
    deriving (Eq)

instance Show TType where
    show TBool         = "bool"
    show TChar         = "char"
    show (TNum TInt)   = "int" 
    show (TNum TUInt)  = "uint"
    show TUnit         = "()"  
    show TEmpty     = "!"   
    show (TPtr typ)    = "ptr[" ++ (show typ) ++ "]"
    show (TArray typ size)    = "[" ++ (show typ) ++ ", " ++ (show size) ++ "]"

data NumType
    = TInt
    | TUInt
    deriving (Eq, Show)

data FunType = FunType [TType] TType
    deriving (Eq, Show)

$(deriveBifoldable ''ModuleG)
$(deriveBifunctor ''ModuleG)
$(deriveBitraversable ''ModuleG)

$(deriveBifoldable ''DefinitionG)
$(deriveBifunctor ''DefinitionG)
$(deriveBitraversable ''DefinitionG)

$(deriveBifoldable ''StmtG)
$(deriveBifunctor ''StmtG)
$(deriveBitraversable ''StmtG)

$(deriveBifoldable ''ExprG)
$(deriveBifunctor ''ExprG)
$(deriveBitraversable ''ExprG)


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
    show (SSetIndex var ix expr) = (showVarId var) ++ (brackets . show $ ix) ++ " = " ++ (show expr) 
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
    show (EChar c) = show c
    show (EArrayLiteral t elems) = show elems
    show (EIndex expr ix) = (parens . show $ expr) ++ (brackets . show $ ix)
    show (EVar v) = showVarId v
    show (E1 op x) = parens ((show op) ++ (show x))
    show (E2 op a b) = parens ((show a) +|+ (show op) +|+ (show b))
    show (EApp fun exprs) = fun ++ (parens . concat . intersperse ", " . map show $ exprs)
    show (ECast expr typeId) = parens $ (show expr) ++ " as " ++ (show typeId)
    show (EAddressOf expr) = "&" ++ (show expr)

showNum :: (Show a, Num a) => a -> NumType -> String
showNum n t = (show n) ++ (case t of TInt -> ""; TUInt -> "u")


instance Show Op1 where
    show OpNot = "!"

instance Show Op2 where
    show OpAdd          = "+"
    show OpSub          = "-"
    show OpMul          = "*"
    show OpDiv          = "/"
    show OpMod          = "%"
    show OpEqual        = "=="
    show OpLess         = "<"
    show OpGreater      = ">"
    show OpLessEqual    = "<="
    show OpGreaterEqual = ">="


showVarId = unVarId
showTypeId t = t

eConstFalse = ENum 0
eConstTrue = ENum 1





type Compile a = ExceptT String (State CompilerState) a

data CompilerState = CompilerState
    { _varTypes  :: VarTypes
    , _funTypes  :: FunTypes
    , _funLabels :: FunLabels
    , _varLocs   :: VarLocs
    , _uniqueGen :: Int
    }
    deriving (Show)

type VarLocs  = Map VarId VarLoc
type VarTypes = Map VarId TType
type FunTypes = Map FunId FunType
type FunLabels = Map FunId Label


data VarLoc
    = VarLocRegister RegisterId
    | VarLocStack StackFrameOffset
    deriving (Eq)

type StackFrameOffset = Int
type RegisterId = Int

instance Show VarLoc where
    show (VarLocRegister r) = showRef' ("R" ++ (show r)) 0
    show (VarLocStack off)  = showRef' "EBP" off

showRef' :: String -> Int -> String
showRef' a off = "[" ++ a ++ (showOffset off) ++ "]"

showOffset :: Int -> String
showOffset off = case compare off 0 of
                    LT -> show off
                    EQ -> ""
                    GT -> "+" ++ (show off)
    

newtype Label = Label {unLabel :: Int} deriving (Eq, Ord)

underLabel f = Label . f . unLabel
asLabel f = unLabel . f . Label

newLabel :: Label -> Label
newLabel = underLabel (+1)

instance Show Label where show (Label l) = "L" ++ (show l)


$(makeLenses ''CompilerState)




-- type Procs = Map FunId RegisterVM.Proc

emptyCompilerState :: CompilerState
emptyCompilerState = CompilerState {_varTypes=M.empty, _funTypes=M.empty, _varLocs=M.empty, _funLabels=M.empty, _uniqueGen=0}

runCompile :: Compile a -> State CompilerState (Either String a)
runCompile = runExceptT

evalCompile :: Compile a -> Either String a
evalCompile = (`evalState` emptyCompilerState) . runCompile

withCompilerState :: CompilerState -> Compile a -> Compile a
withCompilerState = withTmp id 

-- operatorSignature :: Compile


compileError :: String -> Compile a
compileError = throwE

orError' :: Compile (Maybe a) -> String -> Compile a
orError' cma msg = cma >>= (`orError` msg) 

orError :: Maybe a -> String -> Compile a
(Just a) `orError` _   = pure a
_        `orError` msg = throwE msg



declFunType :: FunId -> FunType -> Compile ()
declFunType fun typ = funTypes . at fun .= Just typ

getFunType :: FunId -> Compile (Maybe FunType)
getFunType fun = use $ funTypes . at fun



newFun :: FunId -> Compile Label
newFun fun = do label <- freshLabel; funLabels . at fun .= Just label; pure label

getFunLabel :: FunId -> Compile (Maybe Label)
getFunLabel fun = use $ funLabels . at fun




declVarType :: VarId -> TType -> Compile ()
declVarType var typ = varTypes . at var .= Just typ

getVarType :: VarId -> Compile (Maybe TType)
getVarType var = use $ varTypes . at var




newVarLoc :: VarId -> VarLoc -> Compile ()
newVarLoc var loc = do
    prev <- use (varLocs.(at var))
    when (isJust $ prev) $ throwE $
        "Internal Error: duplicate location for variable " ++ (showVarId var)
        ++ " (was: " ++ (show . fromJust $ prev) ++ ", got: " ++ (show loc)
    varLocs.(at var) .= Just loc

getVarLoc :: VarId -> Compile (Maybe VarLoc)
getVarLoc var = M.lookup var <$> use varLocs


withVars :: VarLocs -> Compile a -> Compile a
withVars = withTmp varLocs


withTmp :: MonadState s m => Lens' s s' -> s' -> m a -> m a
withTmp l tmp ca = do
    old <- use l
    l .= tmp
    a <- ca
    l .= old
    pure a


resolveType :: TypeId -> Compile TType
resolveType (ArrayType elTypeId size) = TArray <$> resolveType elTypeId <*> pure size
resolveType (SimpleType name) = case name of
    "bool" -> pure TBool
    "char" -> pure TChar
    "int"  -> pure $ TNum TInt
    "uint" -> pure $ TNum TUInt
    "()"   -> pure TUnit
    "!"    -> pure TEmpty
    _      -> throwE $ "undefined type" ++ name
resolveType (ParametrizedType name params) = case name of
    "ptr" -> case params of
        [pname] -> TPtr <$> resolveType pname
        _       -> throwE $ "too many parameters for " ++ name ++ ": " ++ (show params) 
    _      -> throwE $ "undefined type" ++ name





-- getProcs :: Compile Procs
-- getProcs = use rocs

-- getProc :: FunId -> Compile (Maybe RegisterVM.Proc)
-- getProc funId = M.lookup funId <$> getProcs

-- modifyProcs :: (Procs -> Procs) -> Compile ()
-- modifyProcs f =  lift $ modify (overProcs f)

-- newProc :: FunId -> RegisterVM.Proc -> Compile ()
-- newProc funId proc = modifyProcs (M.insert funId proc)


getFresh :: Compile Int
getFresh = use uniqueGen

modifyFresh :: (Int -> Int) -> Compile ()
modifyFresh f = modify (overUniqueGen f)

putFresh :: Int -> Compile ()
putFresh = modifyFresh . const

fresh :: Compile Int
fresh = do {x <- getFresh; modifyFresh (+1); pure x}


freshLabel :: Compile Label
freshLabel = Label <$> fresh


toVarId :: Int -> VarId
toVarId = VarId . ("$" ++) . show 

freshVarId :: Compile VarId
freshVarId = toVarId <$> fresh


overVarTypes   f state = state { _varTypes  = f $ _varTypes  state}
overFunTypes   f state = state { _funTypes  = f $ _funTypes  state}
overFunLabels  f state = state { _funLabels = f $ _funLabels  state}
overVarLocs    f state = state { _varLocs   = f $ _varLocs   state}
-- overProcs     f state = state { procs   = f $ procs     state}
overUniqueGen  f state = state { _uniqueGen = f $ _uniqueGen state}






type FlowGraph' l = FlowGraph () l
type FlowNode'  l = FlowNode  () l

block'      = Block ()
ifThenElse' = IfThenElse ()
return'     = Return ()

type FlowGraph x l = FlowGraphG BasicExpr BasicStmt x l
type FlowNode  x l = FlowNodeG  BasicExpr BasicStmt x l


data FlowGraphG expr stmt x l =
    FlowGraphG {_nodes :: Map l (FlowNodeG expr stmt x l)}
    deriving (Eq)

data FlowNodeG expr stmt x l
    = Block      {_extra :: x, _body :: [stmt], _next :: l}
    | IfThenElse {_extra :: x, _cond :: expr, _ifTrue, _ifFalse :: l}
    | Return     {_extra :: x, _expr :: expr}
    deriving (Eq, Functor)



type BasicStmt    = BasicStmtG (Const2_Void) VarId VarId
type BasicExpr    = BasicExprG VarId

data BasicStmtG (con :: * -> * -> *) varW varR
    = BSetVar       {_typ :: TType, _target :: varW, _val :: (BasicExprG varR)}

    | BGetAddressOf {_typ :: TType,  _target :: varW, _var :: varR}
    | BWriteAddress {_typ :: TType,  _target :: varW, _val :: (BasicExprG varR)}
    | BReadAddress  {_typ :: TType,  _target :: varW, _var :: varR}

    | BSetIndex     {_typ :: TType, _target :: varW, _index :: (BasicExprG varR), _val :: (BasicExprG varR) }
    | BGetIndex     {_typ :: TType, _target :: varW, _var :: varR, _index :: (BasicExprG varR)}
    
    | B1            {_typ :: TType, _target :: varW, _op1 :: Op1, _val :: (BasicExprG varR)}
    | B2            {_typ :: TType, _target :: varW, _op2 :: Op2, _val1, _val2 :: (BasicExprG varR)}
    | BApp          {_typ :: TType, _target :: varW, _fun :: FunId, _args :: [(BasicExprG varR)]}
    | BOther        {_other :: (con varW varR)}
    deriving (Eq)


data BasicExprG var
    = BVar  {_etyp   :: TType,   _evar :: var}
    | BNum  {_numtyp :: NumType, _int :: Int}
    | BChar {_char :: Char}
    deriving (Eq, Functor, Foldable, Traversable)

-- data Place
--     = PVar VarId
--     | POffsetBy Place Int
--     | PDescribedBy Place

newtype Const2_Void a b = Const2_Void {unConst2 :: Void}

instance Show (Const2_Void a b) where
    show = absurd . unConst2


-- data BPhi var = BPhi var [(var, Label)]
data BPhi varW varR = BPhi {_bpTyp :: TType, _bpVar :: varW, _bpVarsAndLabels :: [(varR, Label)]}
    deriving (Eq, Functor, Foldable, Traversable)

instance (Show a, Show b) => Show (BPhi a b) where
    show (BPhi _ v vars) = (show v) +|+ "= phi" +|+ (joinWith' ", " $ map (\(v, l) -> (show v) ++ "|" ++ (show l)) $ vars)

$(makeLenses ''FlowGraphG)

$(makeLenses ''FlowNodeG)
$(makeLensesFor [("_next","nodeCont"),("_ifTrue","nodeCont"),("_ifFalse","nodeCont")] ''FlowNodeG)
$(makeLensesFor [("_expr","nodeExpr"),("_cond","nodeExpr")] ''FlowNodeG)
$(makePrisms ''FlowNodeG)


$(makeLenses ''BasicExprG)

$(deriveBifunctor ''BasicStmtG)
$(deriveBifoldable ''BasicStmtG)
$(deriveBitraversable ''BasicStmtG)
$(makeLenses ''BasicStmtG)
$(makePrisms ''BasicStmtG)

$(deriveBifunctor ''BPhi)
$(deriveBifoldable ''BPhi)
$(deriveBitraversable ''BPhi)
$(makeLenses ''BPhi)

$(deriveBifunctor ''Const2_Void)
$(deriveBifoldable ''Const2_Void)
$(deriveBitraversable ''Const2_Void)


overNodes f (g @ FlowGraphG {_nodes=ns}) = g { _nodes = f ns }
emptyFlowGraph = FlowGraphG {_nodes=M.empty}
overExtra f n = n {_extra = f (_extra n)}

getNode :: (Ord l) => l -> FlowGraphG e s x l -> FlowNodeG e s x l
getNode l = (M.! l) . _nodes

insertNode :: (Ord l) => l -> FlowNodeG e s x l -> FlowGraphG e s x l -> FlowGraphG e s x l
insertNode l n = overNodes (M.insert l n)

insertNodes :: (Ord l) => [(l, FlowNodeG e s x l)] -> FlowGraphG e s x l -> FlowGraphG e s x l
insertNodes ns = overNodes (M.union (M.fromList ns))

deleteNode :: (Ord l) => l -> FlowGraphG e s x l -> FlowGraphG e s x l
deleteNode l = overNodes (M.delete l)

graphLabels :: FlowGraphG e s x l -> [l]
graphLabels = map fst . M.toList . _nodes


instance (Show a) => Show (BasicExprG a) where
    show (BVar typ v) = (show v) -- ++ ": " ++ (show typ) 
    show (BNum ntyp n) = showNum n ntyp
    show (BChar c) = show c

    -- show (BIndex _ v ix) = (showVarId v) ++ (brackets . show $ ix)


instance (Show a, Show b, Show (f a b)) => Show (BasicStmtG f a b) where
    show (BSetVar _ v x)       = (show v) +=+ (show x)

    show (BGetAddressOf _ v v2) = (show v) +=+ "&" ++ (show v2)
    show (BReadAddress  _ v v2) = (show v) +=+ "*" ++ (show v2)
    show (BWriteAddress _ v expr) = "*" ++ (show v) +=+ (show expr)

    show (BSetIndex _ v ix expr) = (show v) ++ (brackets . show $ ix) +=+ (show expr)
    show (BGetIndex _ v v2 ix)    = (show v) +=+ (show v2) ++ (brackets . show $ ix)

    show (B1 _ v op x)         = (show v) +=+ (show op) ++ (show x)
    show (B2 _ v op a b)       = (show v) +=+ ((show a) +|+ (show op) +|+ (show b))
    show (BApp _ v f exprs)    = (show v) +=+ (f ++ (parens . concat . intersperse ", " . map show $ exprs))
    show (BOther fvv) = show fvv




data Ctx l
    = BlockCtx {end :: l}
    | LoopCtx  {cont, end :: l}



flowGraph :: Definition -> Compile (Label, FlowGraph' Label)
flowGraph (DDef funId argsAndTypes retTypeId body) = do
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
                typ <- getVarType var `orError'` ("undefined variable: " ++ (showVarId var))
                -- FIXME: types that don't fit in registers?
                (expr', computeExpr, graph) <- computeBlock expr typ graph l
                (next, graph) <- go ctxs graph stmts
                let node = block' [BSetVar typ var expr'] next
                pure $ (computeExpr, insertNode l node graph)
            SSetIndex var ix expr -> do
                l <- freshLabel
                typ <- getVarType var `orError'` ("undefined variable: " ++ (showVarId var))
                elType <- assertIsArrayLikeType typ
                (expr', computeExpr, graph) <- computeBlock expr elType       graph l
                (ix',   computeIx,   graph) <- computeBlock ix   (TNum TUInt) graph computeExpr
                (next, graph) <- go ctxs graph stmts
                let node = block' [BSetIndex elType var ix' expr'] next
                pure $ (computeIx, insertNode l node graph)
            SIfThenElse cond trueBody falseBody -> do
                ifCond <- freshLabel
                (condExpr, computeCond, graph) <- computeBlock cond TBool graph ifCond 
                (next, graph) <- go ctxs graph stmts
                let ctxs' = BlockCtx {end=next} : ctxs
                (trueCont,  graph) <- go ctxs' graph trueBody
                (falseCont, graph) <- go ctxs' graph falseBody
                let ifCondNode = IfThenElse {_extra=(), _cond=condExpr, _ifTrue=trueCont, _ifFalse=falseCont}
                pure $ (computeCond, insertNode ifCond ifCondNode graph)
            SWhile cond body -> do
                ifCond <- freshLabel
                (condExpr, computeCond, graph) <- computeBlock cond TBool graph ifCond 
                (next, graph) <- go ctxs graph stmts
                let ctxs' = LoopCtx {cont=computeCond, end=next} : ctxs
                (bodyCont,  graph) <- go ctxs' graph body
                let node = IfThenElse {_extra=(), _cond=condExpr, _ifTrue=bodyCont, _ifFalse=next}
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
                    ifNode   = IfThenElse {_extra=(), _cond=condExpr, _ifTrue=bodyCont, _ifFalse=next}
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
        -- FIXME: types that don't fit in registers?
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
exprType (ECast expr typeId) = do
    te <- exprType expr
    te' <- resolveType typeId
    assertSameRepresentation te te'
    pure te'
exprType (EAddressOf e) = do
    TPtr <$> exprType e
exprType (ENum _ ntyp) = pure $ TNum ntyp
exprType (EChar _) = pure $ TChar
exprType (EArrayLiteral typ elems) = TArray <$> resolveType typ <*> pure (length elems)
exprType (EIndex expr ix) = do
    te <- exprType expr
    assertIsNumericExpr ix
    elType <- assertIsArrayLikeType te
    pure elType
exprType (EVar v) = getVarType v `orError'` ("undefined variable: " ++ (showVarId v))
exprType (E1 op x) = case op of
    OpNot -> do
        assertType x TBool
        pure TBool
exprType (E2 op a b) = case op of
    OpAdd -> do assertSameType a b; exprType a
    OpSub -> do assertSameType a b; exprType a
    OpMul -> do assertSameType a b; exprType a
    OpDiv -> do assertSameType a b; exprType a
    OpMod -> do assertSameType a b; exprType a
    OpEqual        -> do assertSameType a b; pure $ TBool
    OpLess         -> do assertSameType a b; pure $ TBool
    OpGreater      -> do assertSameType a b; pure $ TBool
    OpLessEqual    -> do assertSameType a b; pure $ TBool
    OpGreaterEqual -> do assertSameType a b; pure $ TBool
exprType (EApp fun exprs) = do 
    FunType argTypes retTyp <- getFunType fun `orError'` ("undefined function (no type found in `exprType`): " ++ fun)
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

assertIsArrayLikeType :: TType -> Compile TType
assertIsArrayLikeType (TArray elType _) = pure $ elType
assertIsArrayLikeType (TPtr   elType)   = pure $ elType
assertIsArrayLikeType t = throwE $ "type " ++ (show t) ++ " is not indexable" 

assertSameRepresentation :: TType -> TType -> Compile ()
assertSameRepresentation (TNum _) (TNum _) = pure ()
assertSameRepresentation (TNum _) (TPtr _) = pure ()
assertSameRepresentation (TPtr _) (TNum _) = pure ()
assertSameRepresentation ta tb
    | ta == tb  = pure ()
    | otherwise = throwE $ "cannot cast " ++ (show ta) ++ " to " ++ (show tb)




toBasicExpr :: Expr -> TType -> Compile (BasicExpr, [BasicStmt])
toBasicExpr expr typ = do 
    assertType expr typ
    toBasicExpr' expr typ 

toBasicExpr' :: Expr -> TType -> Compile (BasicExpr, [BasicStmt])
toBasicExpr' (ECast expr typeId) _ = do
    tFrom <- exprType expr
    tTo <- resolveType typeId
    assertSameRepresentation tFrom tTo
    toBasicExpr' expr tTo
toBasicExpr' (EAddressOf (EVar v)) t = do
    t' <- assertIsPtrType t
    -- (e', eInit) <- toBasicExpr expr t
    -- v <- assertIsBVar e'
    r <- freshVarId
    declVarType r t
    pure $ (BVar t r, [BGetAddressOf t' r v])
toBasicExpr' (EAddressOf (EVar v `EIndex` ENum 0 TUInt)) t = do
    t' <- assertIsPtrType t
    -- assertIsArrayLikeType
    r <- freshVarId
    declVarType r t
    pure $ (BVar t r, [BGetAddressOf t' r v])
toBasicExpr' (EAddressOf e) t = throwE $ "Can't take address of " ++ (show e)
toBasicExpr' (ENum n ntyp) _ = pure (BNum ntyp n, [])
toBasicExpr' (EChar c) _ = pure (BChar c, [])
toBasicExpr' (EArrayLiteral elTypeId elems) _ = do
    elType <- resolveType elTypeId 
    arr <- freshVarId
    let arrType = TArray elType (length elems)
    declVarType arr $ arrType
    elemInits <- forM (zip [0..] elems) $ \(i, expr) -> do
        (val, valInit) <- toBasicExpr' expr elType
        let setIVal = BSetIndex elType arr (BNum TUInt i) val
        pure $ valInit ++ [setIVal]
    pure (BVar arrType arr, concat elemInits)
toBasicExpr' (EIndex expr ix) _ = do
    ti <- exprType ix
    numType <- assertIsNumericType ti
    (ix', ixInit) <- toBasicExpr ix ti

    te <- exprType expr
    elType <- assertIsArrayLikeType te
    (expr', exprInit) <- toBasicExpr expr te
    (_, v) <- assertIsBVar expr'

    r <- freshVarId
    declVarType r elType
    let getIntoR = BGetIndex elType r v ix'

    pure (BVar elType r, ixInit ++ exprInit ++ [getIntoR])
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
    -- pure (BVar typ r, s1 ++ s2 ++ [B2 typ r op v1 v2])
    pure (BVar typ r, s1 ++ s2 ++ [B2 at r op v1 v2])
toBasicExpr' (EApp fun exprs) typ = do
    -- need type signature of fun!!!!
    FunType argTypes _ <- getFunType fun `orError'` ("undefined function (no type found in `toBasicExpr`): " ++ fun)
    xs <- sequence $ zipWith toBasicExpr exprs argTypes
    let vars  = map fst xs
    let temps = concat $ map snd xs
    r <- freshVarId
    declVarType r typ
    pure (BVar typ r, temps ++ [BApp typ r fun vars])


assertIsBVar (BVar t v) = pure (t, v)
assertIsBVar e = throwE $ "Internal Error: expected variable, got " ++ (show e) 

assertIsPtrType (TPtr t) = pure t
assertIsPtrType t = throwE $ "expected ptr, got " ++ (show t) 


toExpr :: BasicExpr -> Expr
toExpr (BVar _ v) = EVar v
toExpr (BNum ntyp n) = ENum n ntyp
toExpr (BChar c) = EChar c


findPredecessors :: Label -> FlowGraphG expr stmt x Label -> [Label]
findPredecessors l g = map fst . filter ((continuesTo l) . snd) .  M.toList . _nodes $ g

continuesTo :: Label -> FlowNodeG expr stmt x Label -> Bool
continuesTo target n = case n of
    Block {_next=next} -> next == target
    IfThenElse {_ifTrue=_ifTrue, _ifFalse=_ifFalse} -> _ifTrue == target || _ifFalse == target
    Return {} -> False



joinBlocks :: (Semigroup x) => FlowGraphG expr stmt x Label -> FlowGraphG expr stmt x Label
joinBlocks g = (`execState` g) $ do
    forM_ (graphLabels g) $ \label -> do
        g <- get
        when (label `M.member` (_nodes g)) $
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




someOrder :: Label -> FlowGraphG expr stmt x Label -> [Label]
someOrder entry graph = snd $ (`evalState` S.empty) $ go entry where
    go :: Label -> State (Set Label) (Maybe Label, [Label])
    go label = do
        visited <- get
        if label `S.member` visited
            then pure $ (Just label, [])
            else do
                modify (S.insert label)
                case getNode label graph of
                    Block {_body=body, _next=next} -> do
                        (stopped, ordered) <- go next
                        pure $ (stopped, label : ordered)
                    IfThenElse {_ifTrue=_ifTrue, _ifFalse=_ifFalse} -> do
                        (stopped, ordered)  <- go _ifTrue
                        (joined,  ordered') <- go _ifFalse
                        let rest = case joined of
                                        Nothing -> ordered ++ ordered'
                                        Just j  -> truePart ++ ordered' ++ afterJoin
                                            where (truePart, afterJoin) = break (==j) ordered
                        pure $ (stopped, label : rest)
                    Return {_expr=expr} -> do
                        pure $ (Nothing, [label])


joinPoint :: (Ord a) => [a] -> [a] -> Maybe a
joinPoint xs ys = listToMaybe . filter (`S.member` xs') $ ys
    where xs' = S.fromList xs


orderedNodes :: Label -> FlowGraphG expr stmt x Label -> [(Label, FlowNodeG expr stmt x Label)]
orderedNodes entry graph = map (\l -> (l, getNode l graph)) $ someOrder entry graph



renameLabels :: [Label] -> FlowGraphG expr stmt x Label -> FlowGraphG expr stmt x Label
renameLabels order graph = overNodes (M.fromList . map rename . M.toList) $ graph where
    rename (label, node) = (newLabel label, fmap newLabel node)
    newLabel l = Label . fromJust $ elemIndex l order


reorder :: Label -> FlowGraphG expr stmt x Label -> FlowGraphG expr stmt x Label
reorder entry graph = let order = someOrder entry graph in renameLabels order graph



data VarIdSSA = VarIdSSA VarId Int
    deriving (Eq, Ord)

type BasicExprSSA = BasicExprG VarIdSSA
type BasicStmtSSA = BasicStmtG BPhi VarIdSSA VarIdSSA


getSSAVarName :: VarIdSSA -> VarId
getSSAVarName (VarIdSSA var _) = var

sameVar :: VarIdSSA -> VarIdSSA -> Bool
sameVar (VarIdSSA a _) (VarIdSSA b _) = a == b

showVarIdSSA :: VarIdSSA -> String
showVarIdSSA (VarIdSSA var i) = (showVarId var) ++ "_" ++ (show i)

instance Show VarIdSSA where
    show = showVarIdSSA



injectConst2_Void :: BasicStmtG Const2_Void varW varR -> BasicStmtG con varW varR
injectConst2_Void = changeStmtFunctor (\(Const2_Void void) -> absurd void)

changeStmtFunctor :: (forall a b. f a b -> g a b) -> BasicStmtG f varW varR -> BasicStmtG g varW varR
changeStmtFunctor h = other %~ h





-- https://en.wikipedia.org/wiki/Dominator_(graph_theory)

-- A node `d` dominates a node `n` if every path from the entry node to `n` must go
-- through `d`. By definition, every node dominates itself.

dominators :: FlowGraphG expr stmt x Label -> FlowGraphG expr stmt (Set Label) Label
dominators graph = (`execState` graph') $ go where
    graph'  = overNodes (M.mapWithKey initDoms) $ graph
    initDoms l n = overExtra (const $ f l) $ n
        where f l = if l == startLabel
                      then S.singleton l
                      else allLabels
    allLabels = S.fromList . graphLabels $ graph
    startLabel = case starts of
        [l] -> l
        []  -> error $ "no start node"
        xs  -> error $ "multiple start nodes: " ++ (show xs)
        where
            starts = filter (\l -> null $ findPredecessors l graph) . graphLabels $ graph

    nonStartLabels = S.toList $ S.delete startLabel allLabels

    doms :: FlowNodeG expr stmt (Set Label) Label -> (Set Label)
    doms = _extra

    go = do
        changed <- forM (nonStartLabels) $ \label -> do
            graph <- get
            let node = getNode label graph
                ds = doms node
                preds = findPredecessors label graph
                predDoms = map doms . map (`getNode` graph) $ preds
                ds' = S.singleton label `S.union` foldl1 S.intersection predDoms
            if ds /= ds'
             then do
                let node' = overExtra (const ds') node
                modify $ insertNode label node'
                pure True
             else
                pure False
        when (any id changed) $
            go

-- A node `d` strictly dominates a node `n` if `d` dominates `n` and `d` does not equal `n`.

strictDominators :: FlowGraphG expr stmt x Label -> FlowGraphG expr stmt (Set Label) Label
strictDominators graph =
    overNodes (M.mapWithKey (\l n -> overExtra (S.delete l) n)) . dominators $ graph

strictlyDominates :: FlowGraphG expr stmt (Set Label) Label -> Label -> Label -> Bool
strictlyDominates graph a b =
    a /= b  &&  dominates graph a b

dominates :: FlowGraphG expr stmt (Set Label) Label -> Label -> Label -> Bool
dominates graph a b = 
    let domsB = _extra $ getNode b graph
     in a == b  ||  a `S.member` domsB 


-- The immediate dominator of a node `n` is the unique node that strictly dominates `n`
-- but does not strictly dominate any other node that strictly dominates `n`.
-- Every node, except the entry node, has an immediate dominator.

-- It is said that a block M immediately dominates block N if M dominates N, and
-- there is no intervening block P such that M dominates P and P dominates N. In
-- other words, M is the last dominator on all paths from entry to N. Each block
-- has a unique immediate dominator.

immediateDominators :: FlowGraphG expr stmt x Label -> FlowGraphG expr stmt (Maybe Label) Label
immediateDominators graph =
    overNodes (M.mapWithKey immDom') sDomGraph
    where
        sDomGraph = strictDominators $ graph
        strictlyDominates' = strictlyDominates sDomGraph
        immDom' label node = overExtra (const $ immDom label node) node
        immDom label node = 
            let sDoms = S.toList $ _extra node in
            case filter (\sDom -> not $ any (sDom `strictlyDominates'`) sDoms) $ sDoms of
                []  -> Nothing
                [x] -> Just x
                xs  -> error $ "Internal error: node " ++ (show label)
                              ++ " should have 0 or 1 immediate dominators, but has " ++ (show xs)


-- A dominator tree is a tree where each node's children are those nodes it immediately dominates.
-- Because the immediate dominator is unique, it is a tree. The start node is the root of the tree.

dominatorTree :: FlowGraphG expr stmt x Label -> Tree Label
dominatorTree graph = 
    let immDoms = fmap _extra . _nodes . immediateDominators $ graph
        startLabel = head . M.keys . M.filter (not . isJust) $ immDoms
        dominatorTree' :: Label -> Tree Label
        dominatorTree' label = 
            T.Node label (map dominatorTree' children)
            where 
                children = M.keys . M.filterWithKey (\l d -> d == (Just label)) $ immDoms
     in dominatorTree' startLabel


dominated :: FlowGraphG expr stmt x Label -> FlowGraphG expr stmt (Set Label) Label
dominated graph =
    let doms = dominators $ graph
        dominatedNodes :: Label -> Set Label
        dominatedNodes label = M.keysSet $ M.filterWithKey (\l2 n -> label `S.member` _extra n) $ _nodes doms
    in
        overNodes (M.mapWithKey $ \label node -> overExtra (const $ dominatedNodes label) node) $ doms


-- The dominance frontier of a node `d` is
-- the set of all nodes `n` such that
--    `d` dominates an immediate predecessor of `n`,
--     but `d` does not strictly dominate `n`.
-- It is the set of nodes where `d`'s dominance stops.


dominanceFrontiers :: FlowGraphG expr stmt x Label -> FlowGraphG expr stmt (Set Label) Label
dominanceFrontiers graph =
    let domGraph = dominators $ graph
        dominates'         = dominates         domGraph
        strictlyDominates' = strictlyDominates domGraph
        predecessors label = findPredecessors label graph
        frontier d =
            M.keysSet
                $ M.filterWithKey (\n _ -> (any (d `dominates'`) $ predecessors n) && (not $ d `strictlyDominates'` n) )
                    $ _nodes graph 

     in overNodes (M.mapWithKey $ \label node -> overExtra (const $ frontier label) node) graph
        

extras :: (Ord l) => FlowGraphG expr stmt x l -> Map l x
extras = fmap _extra . _nodes  


isBlock (Block {}) = True
isBlock _          = False

isReturn (Return {}) = True
isReturn _           = False

isIfThenElse (IfThenElse {}) = True
isIfThenElse _               = False



varLocToOpLoc :: VarLoc -> OpLoc
varLocToOpLoc (VarLocRegister n) = OpLocReg Val . GeneralRegister . GeneralRegisterId $ n
varLocToOpLoc (VarLocStack offset) = OpLocReg (Ref offset) . SpecialRegister $ StackBase

varLocToOpVal :: VarLoc -> OpVal
varLocToOpVal (VarLocRegister n)   = OpValReg Val . GeneralRegister . GeneralRegisterId $ n
varLocToOpVal (VarLocStack offset) = OpValReg (Ref offset) . SpecialRegister $ StackBase

basicExprToOpVal :: BasicExpr -> Compile OpVal
basicExprToOpVal (BNum _ n) = pure $ OpValConst Val n
basicExprToOpVal (BChar c) = pure  $ OpValConst Val (ord c)
basicExprToOpVal (BVar _ v) = varLocToOpVal <$> getVarLoc v `orError'` ("undefined variable: " ++ (showVarId v))

basicExprToOpLoc :: BasicExpr -> Compile OpLoc
basicExprToOpLoc (BVar _ v) = varLocToOpLoc <$> getVarLoc v `orError'` ("undefined variable: " ++ (showVarId v))
basicExprToOpLoc e = throwE $ "Internal error: Cannot convert BasicExpr `" ++ (show e) ++ "` to OpLoc" 

varToOpLoc :: VarId -> Compile OpLoc
varToOpLoc v = varLocToOpLoc <$> getVarLoc v `orError'` ("undefined variable: " ++ (showVarId v))

varToOpVal :: VarId -> Compile OpVal
varToOpVal v = varLocToOpVal <$> getVarLoc v `orError'` ("undefined variable: " ++ (showVarId v))




compileModule :: Module -> Compile [OpIR3]
compileModule (Module defs) = do
    -- allDefs :: [(Label, [OpIR2])]
    printLabel <- newFun "print"
    declFunType "print" (FunType [TPtr TChar, TNum TUInt] TBool)

    forM_ defs $ \(def@(DDef funId paramsAndTypeIds retTypeId body)) -> do
            argTypes <- forM paramsAndTypeIds $ \(arg, typeId) -> do
                           resolveType typeId
            retType <- resolveType retTypeId
            declFunType funId (FunType argTypes retType)
            funLabel <- newFun funId
            pure ()

    allDefs <- forM defs $ \(def@(DDef funId _ _ _)) -> do
        u        <- getFresh
        (labeledOps, (u', st)) <- withCompilerState (emptyCompilerState {_uniqueGen=u} ) $ do 
            labeledOps <- compileDefinition $ def
            u' <- getFresh
            st <- get
            pure (labeledOps, (u', st))
        putFresh u'
        pure $
            trace' ("\n\n"++funId++" types\n") (_varTypes st) `seq` 
            trace' ("\n\n"++funId++" locs\n")  (_varLocs st) `seq`
            labeledOps
    mainLabel <- getFunLabel "main" `orError'` ("missing definition for main()")
    bootstrapLabel <- freshLabel

    sizeof_Ptr <- typeSizeBytes $ TPtr TChar
    sizeof_InstrAddr <- typeSizeBytes $ TNum TUInt
    let
        bootstrap :: [(Label, [OpIR2])]
        bootstrap =
            [(bootstrapLabel, [Call mainLabel,
                              Push (TNum TInt) (OpValReg Val (GeneralRegister . GeneralRegisterId $ 0)),
                              SyscallExit ])]
        print :: [(Label, [OpIR2])]
        print =
            let
            _ebp offset  = (OpLocReg (Ref offset) . SpecialRegister $ StackBase)
            _ebpv offset = (OpValReg (Ref offset) . SpecialRegister $ StackBase)
            esp  = (OpLocReg Val . SpecialRegister $ StackTop)
            espv = (OpValReg Val . SpecialRegister $ StackTop)
            ebp  = (OpLocReg Val . SpecialRegister $ StackBase)
            ebpv = (OpValReg Val . SpecialRegister $ StackBase)
            _TByte = TChar
            _TInstrAddr = TNum TUInt
            in
            [(printLabel, [
                Push (TPtr _TByte) ebpv,
                Mov (TPtr _TByte) ebp espv,
                Push (TNum TUInt) (_ebpv $ sizeof_Ptr + sizeof_InstrAddr + sizeof_Ptr), -- len
                Push (TPtr TChar) (_ebpv $ sizeof_Ptr + sizeof_InstrAddr), -- ptr
                SyscallPrint,
                Mov (TPtr _TByte) esp ebpv,
                Pop (TPtr _TByte) ebp,
                Ret ] )
            ]
    pure . labelsToOffsets . concat $ (bootstrap : print : allDefs)  





{-

STACK FRAME LAYOUT

<low>

Local3                <-- EBP - (sizeof Local1 + sizeof Local2 + sizeof Local 3)
Local2                <-- EBP - (sizeof Local1 + sizeof Local2)
Local1                <-- EBP - (sizeof Local1)
CallerEBP :: Ptr      <-- EBP                 [points to the start of CallerEBP, i.e. the right behind Local1]
RetAddr :: InstrAddr  <-- EBP + sizeof Ptr
Arg1                  <-- EBP + sizeof Ptr + sizeof InstrAddr
Arg2                  <-- EBP + sizeof Ptr + sizeof InstrAddr + sizeof Arg1
Arg3                  <-- EBP + sizeof Ptr + sizeof InstrAddr + sizeof Arg1 + sizeof Arg2

<high>

-}


compileDefinition' def@(DDef funId paramsAndTypeIds retTypeId body) = do
    argTypes <- forM paramsAndTypeIds $ \(arg, typeId) -> do
                   resolveType typeId
    retType <- resolveType retTypeId
    declFunType funId (FunType argTypes retType)
    funLabel <- newFun funId

    -- FunType argTypes retType <- getFunType funId `orError'` ("Internal Error: " ++ funId ++ " should be declared by now")
    -- funLabel <- getFunLabel funId `orError'` ("Internal Error: " ++ funId ++ " should have a label by now")

    fits <- fitsInRegister retType
    when (not fits) $
        throwE $ (show retType) ++ " is too big to be returned by value"

    let params = zipWith (\(arg, _) t -> (arg, t)) paramsAndTypeIds argTypes
    mapM_ (uncurry declVarType) params

    (entry, _graph) <- flowGraph def
    pure $ joinBlocks _graph



compileDefinition :: Definition -> Compile [(Label, [OpIR2])]
compileDefinition def@(DDef funId paramsAndTypeIds _ body) = do
    FunType argTypes retType <- getFunType funId `orError'` ("Internal Error: " ++ funId ++ " should be declared by now")
    funLabel <- getFunLabel funId `orError'` ("Internal Error: " ++ funId ++ " should have a label by now")

    fits <- fitsInRegister retType
    when (not fits) $
        throwE $ (show retType) ++ " is too big to be returned by value"

    let params = zipWith (\(arg, _) t -> (arg, t)) paramsAndTypeIds argTypes
    mapM_ (uncurry declVarType) params

    (entry, _graph) <- flowGraph def
    let graph = log $ joinBlocks _graph
                where
                    log g =
                        trace ("=============\n" ++ funId ++ "\n\n" ++ (showGraph . dominanceFrontiers $ g)  ++ "\n" ++  (showTree . dominatorTree $ g) ++ "\n\n")
                        $ g

    localsAndParams <- use varTypes;
    let locals = S.toList $ (M.keysSet localsAndParams) `S.difference` (S.fromList . map fst $ params)

    stackBasePtrSize <- typeSizeBytes (TPtr $ TNum TUInt)
    retAddrSize      <- typeSizeBytes (TPtr $ TNum TUInt)

    paramSizes <-  mapM (typeSizeBytes . snd) params
    let paramOffsets = init $ scanl (+) (stackBasePtrSize + retAddrSize) paramSizes
    forM_ (zip params paramOffsets) $ \((param, _), offset) -> do
        newVarLoc param (VarLocStack offset)

    localsSizes <- mapM (typeSizeBytes <=< (`orError` "undefined variable") <=< getVarType) locals
    let localsOffsets = tail $ scanl (+) 0 localsSizes
    forM_ (zip locals localsOffsets) $ \(var, offset) -> do
        newVarLoc var (VarLocStack $ negate offset)

    let localsSize = sum localsSizes
    let
        stackPtrT = (TPtr $ TNum TUInt)
        esp = SpecialRegister StackTop
        ebp = SpecialRegister StackBase
        setup = [ Push stackPtrT (OpValReg Val ebp)
                , Mov  stackPtrT (OpLocReg Val ebp) (OpValReg Val esp)
                , Sub  stackPtrT (OpLocReg Val esp) (OpValReg Val esp) (OpValConst Val localsSize)
                , Jmp entry]
    bodyCode <- compileGraph graph (someOrder entry graph)
    pure .  removeRedundantJumps $ (funLabel, setup) : bodyCode


compileGraph :: FlowGraph x Label -> [Label] -> Compile [(Label, [OpIR2])]
compileGraph graph order = mapM (\l -> comp l (getNode l graph)) order where
    comp :: Label -> FlowNode x Label -> Compile (Label, [OpIR2])
    comp label node = do code' <- code; pure (label, code') where
        code :: Compile [OpIR2]
        code = case node of
            Block {_body=body, _next=next} -> do
                body' <- concat <$> mapM compileBasicStmt body
                pure $ body' ++ [Jmp next]
            IfThenElse {_cond=cond, _ifTrue=_ifTrue, _ifFalse=_ifFalse} -> do
                cond' <- basicExprToOpVal cond
                pure $ [JmpIf cond' _ifTrue, Jmp _ifFalse]
            Return {_expr=expr} -> do
                let
                    retType = basicExprType expr
                    stackPtrT = (TPtr $ TNum TUInt)
                    esp = SpecialRegister StackTop
                    ebp = SpecialRegister StackBase
                    res = GeneralRegister . GeneralRegisterId $ 0
                    cleanup = [ Mov stackPtrT (OpLocReg Val esp) (OpValReg Val ebp)
                              , Pop stackPtrT (OpLocReg Val ebp)]
                expr' <- basicExprToOpVal expr
                pure $ [Mov retType (OpLocReg Val res) expr'] ++ cleanup ++ [Ret]



compileBasicStmt :: BasicStmt -> Compile [OpIR2]
compileBasicStmt (BSetVar t v x)  = do
    v' <- varToOpLoc v
    x' <- basicExprToOpVal x
    fits <- fitsInRegister t
    if fits
    then do 
        pure [Mov t v' x']
    else do
        memcpy t v' x'

compileBasicStmt (BSetIndex elType ref i x)  = do
    i' <- basicExprToOpVal i
    x' <- basicExprToOpVal x
    addr   <- pure $ GeneralRegister . GeneralRegisterId $ 1 -- FIXME - temp location
    offset <- pure $ GeneralRegister . GeneralRegisterId $ 2 -- FIXME - temp location
    elSize <- typeSizeBytes elType
    let 
        addrV = OpValReg Val addr
        addrL = OpLocReg Val addr
        _addrV = OpValReg (Ref 0) addr
        _addrL = OpLocReg (Ref 0) addr
        offsetV = OpValReg Val offset
        offsetL = OpLocReg Val offset
    reft <- getVarType ref `orError'` ("undefined variable " ++ (show ref))
    ref' <- varToOpVal ref
    let
        pre = case reft of
                TArray _ _ -> [Lea addrL ref']
                TPtr _     -> [Mov (TPtr elType) addrL ref']
        get = [ Mul (TNum TUInt) offsetL i' (OpValConst Val $ elSize)
              , Add (TPtr elType) addrL addrV offsetV
              , Mov elType _addrL x' ]
    pure $ pre ++ get
compileBasicStmt (BGetIndex elType v ref i)  = do
    v' <- varToOpLoc v
    ref' <- varToOpVal ref
    i' <- basicExprToOpVal i
    elSize <- typeSizeBytes elType
    let 
        addr   = GeneralRegister . GeneralRegisterId $ 1 -- FIXME - temp location
        offset = GeneralRegister . GeneralRegisterId $ 2 -- FIXME - temp location
        addrV = OpValReg Val addr
        addrL = OpLocReg Val addr
        _addrV = OpValReg (Ref 0) addr
        offsetV = OpValReg Val offset
        offsetL = OpLocReg Val offset
    reft <- getVarType ref `orError'` ("undefined variable " ++ (show ref))
    ref' <- varToOpVal ref
    let
        pre = case reft of
                TArray _ _ -> [Lea addrL ref']
                TPtr _     -> [Mov (TPtr elType) addrL ref']
        get = [ Mul (TNum TUInt) offsetL i' (OpValConst Val $ elSize)
              , Add (TPtr elType) addrL addrV offsetV
              , Mov elType v' _addrV]

    pure $ pre ++ get
               
               
compileBasicStmt (BGetAddressOf _ v u)  = do
    v' <- varToOpLoc v
    u' <- varToOpVal u
    pure $ [Lea v' u']
compileBasicStmt (B1 t v op x)   = do
    v' <- varToOpLoc v
    x' <- basicExprToOpVal x
    pure [opcode  t v' x']
    where opcode = case op of
                      OpNot -> Not
compileBasicStmt (B2 t v op a b) = do
    v' <- varToOpLoc v
    a' <- basicExprToOpVal a
    b' <- basicExprToOpVal b
    pure [opcode t v' a' b']
    where opcode =
            case op of
                OpAdd          -> Add
                OpSub          -> Sub
                OpMul          -> Mul
                OpDiv          -> Div
                OpMod          -> Mod
                OpEqual        -> Equal
                OpLess         -> Less
                OpGreater      -> Greater
                OpLessEqual    -> LessEqual
                OpGreaterEqual -> GreaterEqual
compileBasicStmt (BApp t v f args) = do
    f' <- getFunLabel f `orError'` ("undefined function (no label found): " ++ f)
    args' <- mapM (\e -> do e' <- basicExprToOpVal e; pure (basicExprType e, e')) $ reverse args
    argsSize <- sum <$> mapM (typeSizeBytes . fst) args'
    v' <- varToOpLoc v
    setups <- forM args' $ \(t, loc) -> do
        size <- typeSizeBytes t
        fits <- fitsInRegister t
        if fits
        then pure $ [Push t loc]
        else do
            let
                _esp = (OpLocReg (Ref 0) . SpecialRegister $ StackTop)
                esp  = (OpLocReg Val . SpecialRegister $ StackTop)
                espv = (OpValReg Val . SpecialRegister $ StackTop)
            ([Sub (TPtr $ TNum TUInt) esp espv (OpValConst Val size)] ++) <$> (memcpy t _esp loc)
    let
        setup  = concat setups
        esp = SpecialRegister StackTop
        res = GeneralRegister . GeneralRegisterId $ 0
        argCleanup = [Add (TPtr $ TNum TUInt) (OpLocReg Val esp) (OpValReg Val esp) (OpValConst Val argsSize)] 
    -- FIXME: is it safe to store the result BEFORE arg cleanup?
    pure $ setup ++ [Call f', Mov t v' (OpValReg Val res)] ++ argCleanup
compileBasicStmt (BOther (Const2_Void void)) = absurd void


fitsInRegister :: TType -> Compile Bool
fitsInRegister t = (<=8) <$> typeSizeBytes t

memcpy :: TType -> OpLoc -> OpVal -> Compile [OpIR2]
memcpy t dst src = do
    tSize <- typeSizeBytes t 
    pure $
        (\off -> Mov TChar (offsetOpLocBy off dst) (offsetOpValBy off src)) <$> [0..tSize-1] 
    where
        offsetOpLocBy off (OpLocReg (Ref off') reg) = (OpLocReg (Ref $ off'+off) reg) 
        offsetOpLocBy off (OpLocAddr addr)          = (OpLocAddr $ addr+off)
        offsetOpLocBy _   x                         = error $ "cannot offset loc " ++ (show x)
        offsetOpValBy off (OpValReg   (Ref off') reg)  = (OpValReg   (Ref $ off'+off) reg) 
        offsetOpValBy off (OpValConst (Ref off') addr) = (OpValConst (Ref $ off'+off) addr)
        offsetOpValBy _   x                            = error $ "cannot offset val " ++ (show x)



basicExprType :: BasicExpr -> TType
basicExprType (BNum ntyp _) = TNum ntyp
basicExprType (BChar _) = TChar
basicExprType (BVar t _) = t


funLabel :: FunId -> Compile Label
funLabel fun = freshLabel

typeSizeBytes :: TType -> Compile Int
typeSizeBytes TUnit         = pure 0
typeSizeBytes TEmpty        = pure 0
typeSizeBytes TBool         = pure 1
typeSizeBytes TChar         = pure 1
typeSizeBytes (TNum TInt)   = pure 8
typeSizeBytes (TNum TUInt)  = pure 8
typeSizeBytes (TPtr _)      = pure 8
typeSizeBytes (TArray elType size) = (size *) <$> typeSizeBytes elType





data OpVal
    = OpValReg   Ref Register
    | OpValConst Ref Int
    deriving (Eq)

data Ref = Val | Ref Int deriving (Eq, Show)


instance Show OpVal where
    show (OpValReg Val r) = show r
    show (OpValConst Val r) = show r
    show (OpValReg (Ref off) r)   = showRef r off
    show (OpValConst (Ref off) n) = showRef n off

showRef :: (Show a) => a -> Int -> String
showRef = showRef' . show


data OpLoc
    = OpLocReg  Ref Register
    | OpLocAddr     Int
    deriving (Eq)

instance Show OpLoc where
    show (OpLocReg Val r) = show r
    show (OpLocReg (Ref off) r)   = showRef r off
    show (OpLocAddr n) = showRef n 0

data Register
    = SpecialRegister SpecialRegisterId
    | GeneralRegister GeneralRegisterId
    deriving (Eq)


instance Show Register where
    show (SpecialRegister r) = case r of 
                                ProgramCounter -> "PC"
                                StackBase      -> "EBP"
                                StackTop       -> "ESP"
    show (GeneralRegister (GeneralRegisterId i)) = "R"++(show i)

data SpecialRegisterId
    = ProgramCounter
    | StackBase
    | StackTop
    deriving (Eq, Show)

newtype GeneralRegisterId = GeneralRegisterId Int
    deriving (Eq, Show)

type OpIR1 = OpIR Label (Either VarId Register) (Either BasicExpr Register)
type OpIR2 = OpIR Label OpLoc OpVal
type OpIR3 = OpIR Int   OpLoc OpVal

data OpIR label loc val
    = Nop
    | Mov TType loc val
    | Lea loc val

    | Push TType val
    | Pop  TType loc

    | Add TType loc val val
    | Sub TType loc val val
    | Mod TType loc val val
    | Mul TType loc val val
    | Div TType loc val val

    | Incr TType loc
    | Decr TType loc

    | Equal        TType loc val val 
    | Less         TType loc val val 
    | Greater      TType loc val val 
    | LessEqual    TType loc val val 
    | GreaterEqual TType loc val val
    
    | Not TType loc val

    | Jmp       label
    | JmpIf val label

    | Call label
    | Ret

    | SyscallExit 
    | SyscallPrint

    deriving (Eq, Show)


eFalse = eEqual (uu 3) (uu 5)
eTrue  = eEqual (uu 3) (uu 3)

eNot = E1 OpNot
eAdd          = E2 OpAdd
eMul          = E2 OpMul
eSub          = E2 OpSub
eDiv          = E2 OpDiv
eMod          = E2 OpMod
eEqual        = E2 OpEqual
eLess         = E2 OpLess
eGreater      = E2 OpGreater
eLessEqual    = E2 OpLessEqual
eGreaterEqual = E2 OpGreaterEqual

newVar    = SNewVar    . VarId
setVar    = SSetVar    . VarId
forFromTo = SForFromTo . VarId
setIndex  = SSetIndex  . VarId
def fn = DDef fn . map (_1 %~ VarId)

tt = SimpleType
uu = (`ENum` TUInt)
ii = (`ENum` TInt)
ch = EChar
vv = EVar . VarId
ptr = ParametrizedType "ptr" . pure

e1 = (eAdd
        (uu 3)
        (eMul
            (uu 2)
            (uu 2)))


p1 = [
        SIfThenElse (eEqual (vv "x") (vv "y")) [
            setVar "x" (eAdd (vv "x") (ii 1)),
            setVar "x" (eAdd (vv "x") (ii 1))
        ] [
            SReturn (vv "y")
        ],
        SReturn (vv "x")
    ]



p2 = def "fib" [("i", tt "uint")] (tt "uint") [
        newVar "a" (tt "uint") (uu 1),
        newVar "b" (tt "uint") (uu 1),
        newVar "tmp" (tt "uint") (uu 0),
        forFromTo "j" (tt "uint") (uu 0) (eSub (vv "i") (uu 1)) [
            setVar "tmp" (eAdd (vv "a") (vv "b")),
            setVar "a" (vv "b"),
            setVar "b" (vv "tmp")
        ],
        SReturn (vv "a")
    ]

p2' = def "fib'" [("i", tt "uint")] (tt "uint") [
        SIfThenElse (eLessEqual (vv "i") (uu 1)) [
            SReturn (uu 1)
        ] [ ],
        SReturn $
            eAdd
                (EApp "fib'" [eSub (vv "i") (uu 2)] )
                (EApp "fib'" [eSub (vv "i") (uu 1)] )
    ]


p2main = def "main" [] (tt "bool") [
        -- SReturn (eEqual (uu 21) (EApp "fib'" [uu 7]))
        SReturn (eEqual (uu 21) (EApp "fib" [uu 7]))
    ]

m2 = Module [p2, p2', p2main]




p3 = def "ple" [] (tt "int") [
        newVar "x" (tt "int") (ii 0),
        forFromTo "i" (tt "int") (ii 1) (ii 10) [
            forFromTo "j" (tt "int") (ii 1) (ii 10) [
                setVar "x" (eAdd (vv "x") (eAdd (vv "i") (vv "j")))
            ]
        ],
        SReturn (vv "x")
    ]


p4 = def "pred" [("x", tt "uint")] (tt "uint") [
        newVar "res" (tt "uint") (uu 0),
        SIfThenElse (eEqual (vv "x") (uu 0)) [
            setVar "res" (vv "x")
        ] [
            setVar "res" (eSub (vv "x") (uu 1))
        ],
        SReturn (vv "res")
    ]



p5_str_rev = def "str_rev" [("str", ptr (tt "char")), ("len", (tt "uint"))] (tt "bool") [
        newVar "i_front" (tt "uint") (uu 0),
        newVar "i_back" (tt "uint") (vv "len" `eSub` uu 1),
        newVar "tmp" (tt "char") (ch '_'),
        SWhile (vv "i_front" `eLess` vv "i_back") [
            setVar "tmp" $ (vv "str") `EIndex` (vv "i_back"),
            setIndex "str" (vv "i_back")
                $ (vv "str") `EIndex` (vv "i_front"),
            setIndex "str" (vv "i_front") (vv "tmp"),
            setVar "i_front" (vv "i_front" `eAdd` uu 1),
            setVar "i_back" (vv "i_back" `eSub` uu 1)
        ],
        SReturn eTrue
    ]



p5_sum = def "sum" [("xs", ptr (tt "int")), ("len", (tt "uint"))] (tt "int") [
        newVar "res" (tt "int") (ii 0),
        forFromTo "i" (tt "uint") (uu 0) (vv "len" `eSub` uu 1) [
            setVar "res" $ eAdd (vv "res") ((vv "xs") `EIndex` (vv "i")) 
        ],
        SReturn (vv "res")
    ]


p5_str = def "str" [("n", (tt "int")), ("out", ptr (tt "char"))] (tt "uint") [
        newVar "i" (tt "uint") (uu 0),
        newVar "was_negative" (tt "bool") eFalse,
        SIfThenElse (vv "n" `eEqual` (ii 0)) [
            setIndex "out" (uu 0) (EChar '0'),
            setVar "i" $ (vv "i") `eAdd` (uu 1),
            SReturn $ vv "i"
        ] [],
        SIfThenElse (vv "n" `eLess` (ii 0)) [
            setIndex "out" (uu 0) (EChar '-'),
            setVar "was_negative" eTrue,
            setVar "n" $ (vv "n") `eMul` (ii (-1))
        ] [],
        SWhile (eNot $ (vv "n") `eEqual` (ii 0)) [
            setIndex "out" (vv "i") (
                EApp "digit" [(vv "n" `ECast` (tt "uint")) `eMod` (uu 10)]
            ),
            setVar "i" $ (vv "i") `eAdd` (uu 1),
            setVar "n" $ (vv "n") `eDiv` (ii 10)
        ],
        SIfThenElse (vv "was_negative") [
            setIndex "out" (vv "i") (EChar '-'),
            setVar "i" $ (vv "i") `eAdd` (uu 1)
        ] [],

        newVar "_" (tt "bool") $ EApp "str_rev" [(vv "out"), (vv "i")],
        SReturn (vv "i")
    ]

p5_digit = def "digit" [("n", (tt "uint"))] (tt "char") [
        SIfThenElse (vv "n" `eEqual` (uu 0)) [SReturn (ch '0')] [],
        SIfThenElse (vv "n" `eEqual` (uu 1)) [SReturn (ch '1')] [],
        SIfThenElse (vv "n" `eEqual` (uu 2)) [SReturn (ch '2')] [],
        SIfThenElse (vv "n" `eEqual` (uu 3)) [SReturn (ch '3')] [],
        SIfThenElse (vv "n" `eEqual` (uu 4)) [SReturn (ch '4')] [],
        SIfThenElse (vv "n" `eEqual` (uu 5)) [SReturn (ch '5')] [],
        SIfThenElse (vv "n" `eEqual` (uu 6)) [SReturn (ch '6')] [],
        SIfThenElse (vv "n" `eEqual` (uu 7)) [SReturn (ch '7')] [],
        SIfThenElse (vv "n" `eEqual` (uu 8)) [SReturn (ch '8')] [],
        SIfThenElse (vv "n" `eEqual` (uu 9)) [SReturn (ch '9')] [],
        SReturn (ch '?')
    ]

p5_main = def "main" [] (tt "int") [
        -- SReturn (eEqual (uu 21) (EApp "fib'" [uu 7]))
        newVar "arr" (ArrayType (tt "int") 4) (
            EArrayLiteral (tt "int")
                [ (ii (-11))
                , (ii (-21))
                , (ii (-31))
                , (ii (-41)) ]
            ),
        newVar "n" (tt "int") (
            EApp "sum" [(EAddressOf $ vv "arr" `EIndex` uu 0), (uu 4)]
        ),
        newVar "s" (ArrayType (tt "char") 8) (
            EArrayLiteral (tt "char") [ch '_', ch '_', ch '_', ch '_', ch '_', ch '_', ch '_', ch '_']
        ),
        newVar "len" (tt "uint") (
            EApp "str" [(vv "n"), (EAddressOf $ vv "s" `EIndex` uu 0)]
        ),
        newVar "_2" (tt "bool") (
            EApp "print" [(EAddressOf $ vv "s" `EIndex` uu 0), (vv "len")]
        ),

        SReturn (vv "n") 
        -- SReturn (eEqual (ii 10) (EApp "sum" [(vv "arr" `ECast` (ptr $ tt "int")), (uu 4)]))
        -- SReturn (foldr1 eAdd $ map (EIndex (vv "arr") . uu) [0..3])
    ]

m5 = Module [p5_main, p5_sum, p5_str, p5_digit, p5_str_rev]


m6 = Module [
    def "main" [] (tt "int") [
        newVar "arr" (ArrayType (tt "int") 2) (
            EArrayLiteral (tt "int")
                [ (ii (-11))
                , (ii (-11)) ]
        ),
        newVar "res" (tt "int") $ EApp "mul2" [vv "arr"],

        newVar "s" (ArrayType (tt "char") 8) (
            EArrayLiteral (tt "char") [ch '_', ch '_', ch '_', ch '_', ch '_', ch '_', ch '_', ch '_']
        ),
        newVar "res_len" (tt "uint") (
            EApp "str" [(vv "res"), (EAddressOf $ vv "s" `EIndex` uu 0)]
        ),
        newVar "_2" (tt "bool") (
            EApp "print" [(EAddressOf $ vv "s" `EIndex` uu 0), (vv "res_len")]
        ),

        SReturn (vv "res")
    ],

    def "mul2" [("xs", ArrayType (tt "int") 2)] (tt "int") [
        SReturn $ ((vv "xs") `EIndex` (uu 0)) `eMul` ((vv "xs") `EIndex` (uu 1))
    ],

    p5_str, p5_digit, p5_str_rev

    ]




showTree :: (Show a) => Tree a -> String
showTree = T.drawTree . fmap show

printTree :: (Show a) => Tree a -> IO ()
printTree = putStrLn . showTree

printGraph :: (Show e, Show s, Show x, Show l) => FlowGraphG e s x l -> IO ()
printGraph = mapM_ (uncurry printNode) . M.toList . _nodes

showGraph :: (Show e, Show s, Show x, Show l) => FlowGraphG e s x l -> String
showGraph = unlines . map (uncurry showNode) . M.toList . _nodes

instance (Show e, Show s, Show x, Show l) => Show (FlowGraphG e s x l) where
    show = showGraph

printNode l n = putStrLn $ showNode l n

showNode :: (Show e, Show s, Show x, Show l) => l -> FlowNodeG e s x l -> String
showNode l n = execWriter $ do
    putStrLn $ (show l) ++ ": " ++ (show . _extra $ n)
    case n of 
        IfThenElse {_cond=cond, _ifTrue=ifTrue, _ifFalse=ifFalse} -> do
            putStrLn $ "if " ++ (show cond)
            putStrLn . indent $ "then -> " ++ (show ifTrue)
            putStrLn . indent $ "else -> " ++ (show ifFalse)
        Return {_expr=expr} -> do
            putStrLn $ "return " ++ (show expr)
        Block {_body=body, _next=next} -> do 
            mapM_ (putStrLn . indent . show) body
            putStrLn $ "  -> " ++ (show next)
    where
        putStrLn = tell . (++"\n")





-- http://pages.cs.wisc.edu/~fischer/cs701.f05/lectures/Lecture22.pdf
-- page 392

testGraph :: FlowGraphG BasicExpr BasicStmt () Label
testGraph = 
    let (a:b:c:d:e:f:_) = Label <$> [0..]
        _0 = BNum TUInt 0
    in FlowGraphG . M.fromList $
        [
           (a, IfThenElse () _0  b  f),
           (b, IfThenElse () _0  c  d),
           (c, Block () []       e   ),
           (d, Block () []       e   ),
           (e, Block () []       f   ),
           (f, Return () _0          )
        ]

testGraphDominanceFrontiers =
    let (a:b:c:d:e:f:_) = Label <$> [0..]
    in M.fromList $
        [
           (a, S.fromList []),
           (b, S.fromList [f]),
           (c, S.fromList [e]),
           (d, S.fromList [e]),
           (e, S.fromList [f]),
           (f, S.fromList [])
        ]

-- http://staff.cs.upt.ro/~chirila/teaching/upt/c51-pt/aamcij/7113/Fly0142.html

testProg =
    def "test" [] (tt "uint") [
        newVar "i" (tt "uint") (uu 1),
        newVar "j" (tt "uint") (uu 1),
        newVar "k" (tt "uint") (uu 0),
        SWhile (vv "k" `eLess` (uu 100)) [
            SIfThenElse ((vv "j") `eLess` (uu 20)) [
                setVar "j" (vv "i"),
                setVar "k" $ (vv "k") `eAdd` (uu 1)
            ] [
                setVar "j" (vv "k"),
                setVar "k" $ (vv "k") `eAdd` (uu 2)
            ]
        ],
        SReturn $ vv "j"
    ]




readVarsBE ::
    Traversal
        (BasicExprG varR)
        (BasicExprG varR')
        varR
        varR'
readVarsBE = traverse

{-# INLINE readVarsBE #-}


readVarsBS ::
    (Bitraversable con) =>
    Traversal
        (BasicStmtG con varW varR)
        (BasicStmtG con varW varR')
        varR
        varR'
readVarsBS f = bitraverse pure f

{-# INLINE readVarsBS #-}


readVarsFN :: 
  (Bitraversable con) =>
  Traversal
    (FlowNodeG (BasicExprG varR)  (BasicStmtG con varW varR)  x label)
    (FlowNodeG (BasicExprG varR') (BasicStmtG con varW varR') x label)
    varR
    varR'
readVarsFN f (Block x1 x2 x3)
  = fmap
      (\y1 -> Block x1 y1 x3) ((each.readVarsBS) f x2)
readVarsFN f (IfThenElse x1 x2 x3 x4)
  = fmap
      (\y1 -> IfThenElse x1 y1 x3 x4) (readVarsBE f x2)
readVarsFN f (Return x1 x2)
  = fmap (\y1 -> Return x1 y1) (readVarsBE f x2)

{-# INLINE readVarsFN #-}



writtenVarsBS ::
    (Bitraversable con) =>
    Traversal
        (BasicStmtG con varW varR)
        (BasicStmtG con varW' varR)
        varW
        varW'
writtenVarsBS f = bitraverse f pure

{-# INLINE writtenVarsBS #-}


writtenVarsFN :: 
  (Bitraversable con) =>
  Traversal
    (FlowNodeG (BasicExprG varR) (BasicStmtG con varW varR)  x label)
    (FlowNodeG (BasicExprG varR) (BasicStmtG con varW' varR) x label)
    varW
    varW'
writtenVarsFN f (Block x1 x2 x3)
  = fmap
      (\y1 -> Block x1 y1 x3) ((each.writtenVarsBS) f x2)
writtenVarsFN _ (IfThenElse x1 x2 x3 x4)
  = pure (IfThenElse x1 x2 x3 x4)
writtenVarsFN _ (Return x1 x2)
  = pure (Return x1 x2)

{-# INLINE writtenVarsFN #-}




-- Whenever node x contains a definition of some variable a,
-- then any node z in the dominance frontier of x needs a phi-function for a.

-- http://staff.cs.upt.ro/~chirila/teaching/upt/c51-pt/aamcij/7113/Fly0142.html

ssaInsertPhis
    :: FlowGraphG BasicExpr BasicStmt x Label
    -> (FlowGraphG (BasicExprG VarId) (BasicStmtG BPhi VarId VarId) (Set Label, Map VarId [Label]) Label)
ssaInsertPhis graph = 
    over (nodes.each) h $
        (`execState` graphWithFrontiers) $
                mapM_ f $ (graphLabels graph)
    where

    graphWithFrontiers :: FlowGraphG (BasicExprG VarId) (BasicStmtG Const2_Void VarId VarId) (Set Label, Map VarId [Label]) Label
    graphWithFrontiers = dominanceFrontiers graph
                            & (nodes.each.extra) %~ (\x -> (x, mempty))

    f :: Label
      -> State
            (FlowGraphG (BasicExprG VarId) (BasicStmtG Const2_Void VarId VarId) (Set Label, Map VarId [Label]) Label)
            ()
    f label = do
        node <- getNode label <$> get
        let domFrontier = node ^. extra._1
            written = S.fromList $ toListOf writtenVarsFN node
        forM_ domFrontier $ \next -> do
            forM_ written $ \v -> do
                (nodes . ix next . extra . _2 . at v) %=
                    maybe (Just [label]) (\ds -> Just $ label:ds)

    h :: FlowNodeG (BasicExprG VarId) (BasicStmtG Const2_Void VarId VarId) (Set Label, Map VarId [Label]) Label 
      -> FlowNodeG (BasicExprG VarId) (BasicStmtG BPhi VarId VarId) (Set Label, Map VarId [Label]) Label
    h node =
        let phiVars = node^.extra._2
            phis = M.toList phiVars
                    & filter ((>1).length.snd)
                    & map (\(v, froms) ->
                                (BOther $ BPhi TUnit v $ map ((,) v) froms))
        in node
            & body.each %~ injectConst2_Void
            & body %~ (phis++) 


-- traverseDominatorTree
--     :: Traversal
--             (FlowGraphG expr  stmt  x  Label)
--             (FlowGraphG expr' stmt' x' Label)
--             (FlowNodeG expr  stmt  x  Label)
--             (FlowNodeG expr' stmt' x' Label)
-- traverseDominatorTree g
--     = g & nodes &

ssaRenameVars
    :: FlowGraphG (BasicExprG VarId)    (BasicStmtG BPhi VarId VarId)       (Set Label,          Map VarId [Label]) Label
    -> FlowGraphG (BasicExprG VarIdSSA) (BasicStmtG BPhi VarIdSSA VarIdSSA) (Map VarId VarIdSSA, Map VarId [Label]) Label
ssaRenameVars g =
    fixupPhis $
        snd $ (`execState` ((0, mempty), emptyFlowGraph)) $
            go $ dominatorTree g
    where
        fixupPhis
            :: FlowGraphG (BasicExprG VarIdSSA) (BasicStmtG BPhi VarIdSSA VarIdSSA) (Map VarId VarIdSSA, Map VarId [Label]) Label
            -> FlowGraphG (BasicExprG VarIdSSA) (BasicStmtG BPhi VarIdSSA VarIdSSA) (Map VarId VarIdSSA, Map VarId [Label]) Label
        fixupPhis g =
            let
                vs :: Map Label (Map VarId VarIdSSA)
                vs = g & _nodes & fmap (fst._extra)
                fixup :: (VarIdSSA, Label) -> (VarIdSSA, Label)
                fixup (v, l) = (vs M.! l M.! (getSSAVarName v), l) in
            g & nodes . each . body . each . _BOther . bpVarsAndLabels . each  %~ fixup
        go
            :: (Tree Label)
            -> State
                ((Int, Map VarId VarIdSSA),
                  FlowGraphG
                    (BasicExprG VarIdSSA)
                    (BasicStmtG BPhi VarIdSSA VarIdSSA)
                    (Map VarId VarIdSSA, Map VarId [Label])
                    Label)
                ()
        go (T.Node label children) = do
            let node = getNode label g
            node' <- zoom _1 $ renameFN node
            vars <- use $ _1 . renamed
            _2 %= insertNode label (node' & extra . _1 .~ vars)
            forM_ children $ \child -> do
                withTmp (_1 . renamed) vars $
                    go child


        renamed :: Lens' (a, Map VarId VarIdSSA) (Map VarId VarIdSSA)
        renamed = _2

        uniq :: Lens' (Int, a) Int
        uniq = _1

        renameFN
            :: FlowNodeG (BasicExprG VarId) (BasicStmtG BPhi VarId VarId) x Label
            -> State
                (Int, Map VarId VarIdSSA)
                (FlowNodeG (BasicExprG VarIdSSA) (BasicStmtG BPhi VarIdSSA VarIdSSA) x Label)
        renameFN (Block x body next) =
            (\body' -> Block x body' next)
                <$> (body & each %%~ renameBS)
        renameFN (Return x res) =
            (\res' -> Return x res')
                <$> (res & readVarsBE %%~ renameReadVar)
        renameFN (IfThenElse x cond t f) =
            (\cond' -> IfThenElse x cond' t f)
                <$> (cond & readVarsBE %%~ renameReadVar)


        renameBS
            :: BasicStmtG BPhi VarId VarId
            -> State
                (Int, Map VarId VarIdSSA)
                (BasicStmtG BPhi VarIdSSA VarIdSSA)
        renameBS s =
            s &   readVarsBS %%~ renameReadVar
              >>= writtenVarsBS %%~ renameWrittenVar

        renameReadVar :: VarId -> State (Int, Map VarId VarIdSSA) VarIdSSA
        renameReadVar v = do
            Just v' <- use $ renamed . at v
            pure v'

        renameWrittenVar :: VarId -> State (Int, Map VarId VarIdSSA) VarIdSSA
        renameWrittenVar v = do
            i <- zoom uniq fresh
            let v' = VarIdSSA v i
            renamed . at v  ?=  v'
            pure v'

        fresh :: State Int Int
        fresh = do
            x <- get
            modify (+1)
            pure x








removeRedundantJumps
    :: (Eq loc, Show loc, Eq val, Show val)
    => [(Label, [OpIR Label loc val])]
    -> [(Label, [OpIR Label loc val])]
removeRedundantJumps =
    {-(trace' "\nafter removing jumps: ") .-}
    mapWithNext removeJumpToNext
    {-. (trace' "\nbefore removing jumps: ")-} where

    removeJumpToNext b1@(l1, n1) (Just b2@(l2, n2)) =
        if (not . null  $ n1) && (last n1 == (Jmp l2)) then (l1, init n1) else b1
    removeJumpToNext b1 _ = b1

    mapWithNext :: (a -> Maybe a -> b) -> [a] -> [b]
    mapWithNext f (x : rest@(y:xs)) = (f x $ Just y) : mapWithNext f rest
    mapWithNext f [x] = [f x Nothing]
    mapWithNext _ [] = []



labelsToOffsets :: [(Label, [OpIR Label loc val])] -> [OpIR Int loc val]
labelsToOffsets blocks = concat . map (\(label, block) -> map (mapLabel (labelToOffset M.!)) block) $ blocks where
    labelToOffset :: Map Label Int
    labelToOffset = M.fromList $ zip labelsOnly (init . scanl (+) 0 . map length $ codeOnly)
    labelsOnly = map fst blocks   
    codeOnly   = map snd blocks


main = either (putStrLn . ("Error: "++)) pure  =<<  (runExceptT mainE)

mainE :: ExceptT String IO ()
mainE = do

    -- lift $ putStrLn "test:"
    -- lift $ printGraph $ testGraph
    -- lift $ blank
    -- lift $ printTree $ dominatorTree testGraph
    -- lift $ blank
    -- lift $ mapM_ print $ fmap extra . _nodes . dominanceFrontiers $ testGraph
    -- lift $ blank
    -- lift $ mapM_ print $ testGraphDominanceFrontiers

    -- let mod@(Module funs) = m6
    -- lift $ mapM_ print funs
    -- ops <- ExceptT . pure $
    --     evalCompile
    --         (compileModule mod
    --             `catchE` (\e -> do
    --                 state <- get
    --                 throwE $ e ++ "\nstate:\n" ++(show state)))
    -- let ops' = toVMOp <$> ops
    -- lift $ RegisterVM.run ops'

    let prog = testProg
    lift $ print $ prog
    lift $ blank
    g1 <- ExceptT . pure $ evalCompile (compileDefinition' prog)
    -- let g3 = reorder start $ g1
    -- lift $ putStrLn "graph:"
    -- lift $ printGraph $ g1
    lift $ blank

    -- lift $ mapM_ print $ fmap extra . _nodes . dominanceFrontiers $ g1
    lift $ printGraph $ dominanceFrontiers $ g1
    -- lift $ printGraph $ immediateDominators g1
    lift $ blank
    lift $ printTree $ dominatorTree g1
    lift $ printGraph $ ssaRenameVars . ssaInsertPhis $ g1


    -- lift $ blank >> blank
    -- cprog <- ExceptT . pure $ evalCompile (compileDefinition prog)
    -- lift $ putStrLn "compiled, IR2:"
    -- lift $ forM_ cprog $ \(lbl, code) -> do
    --     putStrLn ((show lbl) ++ ":")
    --     forM_ code $
    --         putStrLn . indent . show
    --
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




mapLabel :: (l1 -> l2) -> OpIR l1 loc val -> OpIR l2 loc val
mapLabel f (Jmp       label) = (Jmp       $ f label)
mapLabel f (JmpIf val label) = (JmpIf val $ f label)
mapLabel f (Call label)      = (Call $ f label)
mapLabel _ (Nop)                          = (Nop)
mapLabel _ (Mov t loc val)                = (Mov t loc val)
mapLabel _ (Lea loc val)                  = (Lea loc val)
mapLabel _ (Push t val)                   = (Push t val)
mapLabel _ (Pop  t loc)                   = (Pop  t loc)
mapLabel _ (Add t loc val1 val2)          = (Add t loc val1 val2)
mapLabel _ (Sub t loc val1 val2)          = (Sub t loc val1 val2)
mapLabel _ (Mul t loc val1 val2)          = (Mul t loc val1 val2)
mapLabel _ (Div t loc val1 val2)          = (Div t loc val1 val2)
mapLabel _ (Mod t loc val1 val2)          = (Mod t loc val1 val2)
mapLabel _ (Incr t loc)                   = (Incr t loc)
mapLabel _ (Decr t loc)                   = (Decr t loc)
mapLabel _ (Equal        t loc val1 val2) = (Equal        t loc val1 val2)
mapLabel _ (Less         t loc val1 val2) = (Less         t loc val1 val2)
mapLabel _ (Greater      t loc val1 val2) = (Greater      t loc val1 val2)
mapLabel _ (LessEqual    t loc val1 val2) = (LessEqual    t loc val1 val2)
mapLabel _ (GreaterEqual t loc val1 val2) = (GreaterEqual t loc val1 val2)
mapLabel _ (Not t loc val)                = (Not t loc val)
mapLabel _ (Ret)                          = (Ret)
mapLabel _ (SyscallExit )                 = (SyscallExit )
mapLabel _ (SyscallPrint)                 = (SyscallPrint)



toVMOp :: OpIR3 -> RegisterVM.Op
toVMOp (Jmp       label)              = (RegisterVM.Jmp       label')                  where label' = coerce label;
toVMOp (JmpIf val label)              = (RegisterVM.JmpIf val' label')                 where val' = toVMOpVal val;label' = coerce label;
toVMOp (Call label)                   = (RegisterVM.Call label')                       where label' = coerce label;
toVMOp (Nop)                          = (RegisterVM.Nop)                              where 
toVMOp (Mov t loc val)                = (RegisterVM.Mov t' loc' val')                 where t' = toVMSize t; loc' = toVMOpLoc loc; val' = toVMOpVal val;
toVMOp (Lea loc val)                  = (RegisterVM.Lea loc' val')                    where loc' = toVMOpLoc loc; val' = toVMOpVal val;
toVMOp (Push t val)                   = (RegisterVM.Push t' val')                     where t' = toVMSize t; val' = toVMOpVal val;
toVMOp (Pop  t loc)                   = (RegisterVM.Pop  t' loc')                     where t' = toVMSize t; loc' = toVMOpLoc loc;
toVMOp (Add t loc val1 val2)          = (RegisterVM.Add t' loc' val1' val2')          where t' = toVMSize t; loc' = toVMOpLoc loc; val1' = toVMOpVal val1; val2' = toVMOpVal val2; 
toVMOp (Sub t loc val1 val2)          = (RegisterVM.Sub t' loc' val1' val2')          where t' = toVMSize t; loc' = toVMOpLoc loc; val1' = toVMOpVal val1; val2' = toVMOpVal val2; 
toVMOp (Mod t loc val1 val2)          = (RegisterVM.Mod t' loc' val1' val2')          where t' = toVMSize t; loc' = toVMOpLoc loc; val1' = toVMOpVal val1; val2' = toVMOpVal val2; 
toVMOp (Mul t loc val1 val2)          = (RegisterVM.Mul t' s loc' val1' val2')        where t' = toVMSize t; s = toVMSignedness t; loc' = toVMOpLoc loc; val1' = toVMOpVal val1; val2' = toVMOpVal val2; 
toVMOp (Div t loc val1 val2)          = (RegisterVM.Div t' s loc' val1' val2')        where t' = toVMSize t; s = toVMSignedness t; loc' = toVMOpLoc loc; val1' = toVMOpVal val1; val2' = toVMOpVal val2; 
toVMOp (Incr t loc)                   = (RegisterVM.Incr t' loc')                     where t' = toVMSize t; loc' = toVMOpLoc loc;
toVMOp (Decr t loc)                   = (RegisterVM.Decr t' loc')                     where t' = toVMSize t; loc' = toVMOpLoc loc;
toVMOp (Equal        t loc val1 val2) = (RegisterVM.Equal        t' loc' val1' val2') where t' = toVMSize t; loc' = toVMOpLoc loc; val1' = toVMOpVal val1; val2' = toVMOpVal val2; 
toVMOp (Less         t loc val1 val2) = (RegisterVM.Less         t' s loc' val1' val2') where t' = toVMSize t; s = toVMSignedness t; loc' = toVMOpLoc loc; val1' = toVMOpVal val1; val2' = toVMOpVal val2; 
toVMOp (Greater      t loc val1 val2) = (RegisterVM.Greater      t' s loc' val1' val2') where t' = toVMSize t; s = toVMSignedness t; loc' = toVMOpLoc loc; val1' = toVMOpVal val1; val2' = toVMOpVal val2; 
toVMOp (LessEqual    t loc val1 val2) = (RegisterVM.LessEqual    t' s loc' val1' val2') where t' = toVMSize t; s = toVMSignedness t; loc' = toVMOpLoc loc; val1' = toVMOpVal val1; val2' = toVMOpVal val2; 
toVMOp (GreaterEqual t loc val1 val2) = (RegisterVM.GreaterEqual t' s loc' val1' val2') where t' = toVMSize t; s = toVMSignedness t; loc' = toVMOpLoc loc; val1' = toVMOpVal val1; val2' = toVMOpVal val2; 
toVMOp (Not t loc val)                = (RegisterVM.Not t' loc' val')                 where t' = toVMSize t; loc' = toVMOpLoc loc; val' = toVMOpVal val;
toVMOp (Ret)                          = (RegisterVM.Ret)                              where 
toVMOp (SyscallExit )                 = (RegisterVM.SyscallExit )                     where 
toVMOp (SyscallPrint)                 = (RegisterVM.SyscallPrint)                     where 

toVMSize  :: TType -> RegisterVM.Size
toVMSize TBool         = RegisterVM.S8
toVMSize TChar         = RegisterVM.S8
toVMSize (TNum TInt)   = RegisterVM.S64
toVMSize (TNum TUInt)  = RegisterVM.S64
toVMSize TUnit         = undefined
toVMSize TEmpty        = undefined
toVMSize (TPtr _)      = RegisterVM.S64
toVMSize (TArray t _)  = toVMSize (TPtr t)

toVMSignedness  :: TType -> RegisterVM.Signedness
toVMSignedness TBool         = RegisterVM.Unsigned
toVMSignedness TChar         = RegisterVM.Unsigned
toVMSignedness (TNum TInt)   = RegisterVM.Signed
toVMSignedness (TNum TUInt)  = RegisterVM.Unsigned
toVMSignedness TUnit         = undefined
toVMSignedness TEmpty        = undefined
toVMSignedness (TPtr _)      = RegisterVM.Unsigned
toVMSignedness (TArray t _)  = toVMSignedness (TPtr t)

toVMOpLoc :: OpLoc -> RegisterVM.OpLoc
toVMOpLoc (OpLocReg ref reg) = (RegisterVM.OpLocReg ref' reg') where ref' = toVMRef ref; reg' = toVMRegister reg; 
toVMOpLoc (OpLocAddr addr)   = (RegisterVM.OpLocAddr addr)     where 

toVMOpVal :: OpVal -> RegisterVM.OpVal
toVMOpVal (OpValReg ref reg)  = (RegisterVM.OpValReg ref' reg') where ref' = toVMRef ref; reg' = toVMRegister reg; 
toVMOpVal (OpValConst ref n)  = (RegisterVM.OpValConst ref' n)  where ref' = toVMRef ref;

toVMRegister :: Register -> RegisterVM.Register
toVMRegister (SpecialRegister r) = RegisterVM.SpecialRegister r' where r' = case r of 
                                                                            ProgramCounter -> RegisterVM.ProgramCounter
                                                                            StackBase      -> RegisterVM.StackBase     
                                                                            StackTop       -> RegisterVM.StackTop      
toVMRegister (GeneralRegister (GeneralRegisterId i)) = (RegisterVM.GeneralRegister (coerce i))

toVMRef :: Ref -> RegisterVM.Ref
toVMRef Val     = RegisterVM.Val
toVMRef (Ref n) = RegisterVM.Ref n
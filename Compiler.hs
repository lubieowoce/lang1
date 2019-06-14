module Compiler where
import VM

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

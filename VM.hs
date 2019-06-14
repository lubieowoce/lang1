{-# LANGUAGE DeriveFunctor #-}
-- {-# LANGUAGE NamedFieldPuns #-}
-- {-# LANGUAGE RecordWildcards #-}
-- {-# OPTIONS_GHC -Wall #-}
module VM where

import Data.Map (Map)
import qualified Data.Map as M

import Data.Void


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
type FunId = String



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

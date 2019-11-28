{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric, DeriveAnyClass, StandaloneDeriving #-}

module RegisterVM where

import StackVM (Running (..), Running', VMRequest (..), setAt, intToBool, boolToInt)

import Data.Map (Map)
import qualified Data.Map as M

import Data.Vector (Vector)
import qualified Data.Vector as V

import qualified Data.Word as W 

import Data.Char (chr, ord)

import Data.Coerce
import Debug.Trace (trace)

import Control.Monad (forM, forM_)
import Data.Maybe (catMaybes)
import Data.List (intersperse)

import Control.Exception (SomeException, try, evaluate)
-- import System.IO.Unsafe (unsafePerformIO, unsafeInterleaveIO)
import System.IO.Unsafe
import GHC.Generics (Generic)
import Control.DeepSeq (force, NFData)

import Data.Bifunctor (first, second)
import Data.List (mapAccumL)


newtype InstructionIx     = InstructionIx Int     deriving (Eq, Show)
newtype InstructionOffset = InstructionOffset Int deriving (Eq, Show)

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

data SpecialRegisters = SpecialRegisters {
        programCounter :: InstructionIx,
        stackBase      :: Int,
        stackTop       :: Int
    } deriving (Eq, Show)


newtype GeneralRegisterId = GeneralRegisterId Int deriving (Eq, Show)

type GeneralRegisters = [IntVal]


type IntVal = Int


data Ref = Val | Ref Int deriving (Eq, Show)

-- data Address
--     = StackAddress Int
--     | HeapAddress  Int
--     deriving (Eq, Show)

data OpVal
    = OpValReg   Ref Register
    | OpValConst Ref IntVal
    deriving (Eq)


instance Show OpVal where
    show (OpValReg Val r) = show r
    show (OpValConst Val r) = show r
    show (OpValReg (Ref off) r)   = showRef r off
    show (OpValConst (Ref off) n) = showRef n off

showRef :: (Show a) => a -> Int -> String
showRef a off = "[" ++ (show a) ++ off' ++ "]"
    where off' = case compare off 0 of
                    LT -> show off
                    EQ -> ""
                    GT -> "+" ++ (show off)

data OpLoc
    = OpLocReg  Ref Register
    | OpLocAddr     IntVal
    deriving (Eq)

instance Show OpLoc where
    show (OpLocReg Val r) = show r
    show (OpLocReg (Ref off) r)   = showRef r off
    show (OpLocAddr n) = showRef n 0

data Size
    = S8
    | S16
    | S32
    | S64
    deriving (Eq, Ord, Enum, Show)

sizeToBytes :: Size -> Int
sizeToBytes S8  = 1
sizeToBytes S16 = 2
sizeToBytes S32 = 4
sizeToBytes S64 = 8


data Op
    = Nop
    | Mov Size OpLoc OpVal
    | Lea OpLoc OpVal

    | Push Size OpVal
    | Pop  Size OpLoc

    | Add OpLoc OpVal OpVal
    | Sub OpLoc OpVal OpVal
    | Mul OpLoc OpVal OpVal
    | Div OpLoc OpVal OpVal
    | Mod OpLoc OpVal OpVal

    | Incr OpLoc
    | Decr OpLoc

    | Equal        OpLoc OpVal OpVal 
    | Less         OpLoc OpVal OpVal 
    | Greater      OpLoc OpVal OpVal 
    | LessEqual    OpLoc OpVal OpVal 
    | GreaterEqual OpLoc OpVal OpVal
    
    | Not OpLoc OpVal

    | Jmp         InstructionIx
    | JmpIf OpVal InstructionIx

    | Call InstructionIx
    | Ret

    | SyscallExit 
    | SyscallPrint

    deriving (Eq, Show)


data VM = VM {
        codeMemory  :: [Op],
        stackMemory :: [IntVal],
        -- heapMemory  :: Map Address [IntVal],
        specialRegisters :: SpecialRegisters,
        generalRegisters :: GeneralRegisters
    }


step :: VM -> Running' VMRequest VM
step vm@VM{codeMemory=ops, stackMemory=stack, specialRegisters=specs@SpecialRegisters{programCounter=(InstructionIx pc)}}
    | pc >= length ops = Error $ "instruction pointer out of bounds"
    | otherwise = let vm' = vm {specialRegisters=specs{programCounter=InstructionIx $ pc+1}} in
        case ops !! pc of
            Nop                   ->  pure vm'

            Mov dst src           ->  do val <- getVal src vm
                                         setLoc dst val $ vm'
            Lea dst loc           ->  do addr <- getLoc loc vm
                                         setLoc dst addr $ vm'

            Push v                ->  push v vm'
            Pop  dst              ->  pop dst vm'

            Add dst a b           ->  binop (+) dst a b vm'
            Sub dst a b           ->  binop (-) dst a b vm'
            Mul dst a b           ->  binop (*) dst a b vm'
            Div dst a b           ->  binop (div) dst a b vm'
            Mod dst a b           ->  binop (mod) dst a b vm'

            Incr loc              ->  incrop (+ 1)        loc vm'
            Decr loc              ->  incrop (subtract 1) loc vm'
            
            Equal        dst a b  ->  binop' (==) dst a b vm' 
            Less         dst a b  ->  binop' (<)  dst a b vm'
            Greater      dst a b  ->  binop' (>)  dst a b vm' 
            LessEqual    dst a b  ->  binop' (<=) dst a b vm' 
            GreaterEqual dst a b  ->  binop' (>=) dst a b vm'

            Not dst x             ->  unop' (not) dst x vm'

            Jmp     loc           ->  jmp loc vm
            JmpIf x loc           ->  do xv <- getVal x vm
                                         if (intToBool xv) then jmp loc vm else pure vm'

            Call loc              ->  do vm2 <- push (OpValConst Val $ pc+1) vm
                                         jmp loc vm2
            Ret                   ->  do (retLoc, vm2) <- pop' vm
                                         setLoc (OpLocReg Val . SpecialRegister $ ProgramCounter) retLoc vm2
            SyscallExit           ->  do (exitVal, _) <- pop' vm
                                         Stop $ show exitVal
            SyscallPrint          ->  do (ptr, vm2) <- pop' vm'
                                         (len, vm3) <- pop' vm2
                                         let str = map chr . take len . drop ptr . stackMemory $ vm3
                                         if (length str) /= len
                                            then Error "bad print syscall"
                                            else Request (Print str (\_ -> pure vm3))
        where
            binop' f = binop (\a b -> boolToInt $ f a b)
            binop f dst a b vm = do
                av <- getVal a vm
                bv <- getVal b vm
                let res = {-trace' ((show av) ++ " `op` " ++ (show bv) ++ " -> ")-} (av `f` bv)
                setLoc dst res $ vm
            incrop f loc vm = do 
                v <- getVal (toVal loc) vm
                setLoc loc (f v) $ vm
            unop' f = unop (boolToInt . f . intToBool)
            unop f dst x vm = do
                v <- getVal x vm
                setLoc dst (f v) $ vm
            jmp loc vm = pure $ vm {specialRegisters=(specialRegisters vm){programCounter=loc}}
            push v vm = do
                val <- getVal v vm
                let stackTopIx' = 1 + (stackTop . specialRegisters $ vm)
                stack' <- (fromMaybe $ "bad stackTop: " ++ (show stackTopIx')) $ setAt' stackTopIx' val (stackMemory vm)
                pure $ vm {stackMemory = stack', specialRegisters = (specialRegisters vm) {stackTop=stackTopIx'}}
            pop dst vm = do
                (val, vm2) <- pop' vm
                setLoc dst val vm2
            pop' vm = do
                let stackTopIx = stackTop (specialRegisters vm)
                val <- (fromMaybe $ "bad stackTop: " ++ (show stackTopIx)) $ (stackMemory vm) !? stackTopIx
                let vm2 = vm {specialRegisters=(specialRegisters vm){stackTop=stackTopIx-1}}
                pure (val, vm2)


            getVal :: (Functor r) => OpVal -> VM -> Running' r IntVal
            getVal (OpValConst Val n) vm = pure n
            getVal (OpValReg   Val (GeneralRegister (GeneralRegisterId i))) vm = (fromMaybe "invalid register") . (!? i) . generalRegisters $ vm
            getVal (OpValReg   Val (SpecialRegister r)) vm = pure . getR . specialRegisters $ vm where
                getR :: SpecialRegisters -> IntVal
                getR = case r of
                        ProgramCounter -> coerce . programCounter
                        StackBase -> stackBase
                        StackTop -> stackTop
            getVal (OpValConst (Ref offset) addr) vm = (fromMaybe  "invalid stack address") . (!? (addr + offset)) . stackMemory $ vm
            getVal (OpValReg   (Ref offset) r   ) vm = do addr <- getVal (OpValReg Val r) vm; getVal (OpValConst (Ref offset) addr) vm


            setLoc :: (Functor r) => OpLoc -> IntVal -> VM -> Running' r VM 
            setLoc (OpLocReg Val (GeneralRegister (GeneralRegisterId i))) val vm = do
                grs <- (fromMaybe "invalid register") . (setAt' i val) . generalRegisters $ vm
                pure $ vm {generalRegisters=grs}
            setLoc (OpLocReg Val (SpecialRegister r)) val vm =
                let srs = setR val . specialRegisters $ vm
                 in pure $ vm {specialRegisters=srs} where
                setR val srs = case r of
                                ProgramCounter -> srs {programCounter=InstructionIx val}
                                StackBase -> srs {stackBase=val}
                                StackTop -> srs {stackTop=val}
            setLoc (OpLocReg (Ref offset) r) val vm = do
                addr <- getVal (OpValReg Val r) vm
                setLoc (OpLocAddr (addr + offset)) val vm
            setLoc (OpLocAddr addr) val vm = do
                smem <- (fromMaybe  "invalid stack address") . (setAt' addr val) . stackMemory $ vm
                pure $ vm {stackMemory=smem}
            -- setLoc (OpLocAddr (HeapAddress addr))  val vm = undefined
            -- setLoc (OpLocAddr (HeapAddress addr))  val vm = do hmem <- (fromMaybe  "invalid heap address")  . (M.insert addr val) . heapMemory $ vm; pure vm {heapMemory=hmem}

            getLoc :: (Functor r) => OpVal -> VM -> Running' r IntVal
            getLoc (OpValConst (Ref offset) addr) vm = pure (addr + offset)
            getLoc (OpValReg   (Ref offset) r   ) vm = do addr <- getVal (OpValReg Val r) vm; getLoc (OpValConst (Ref offset) addr) vm
            getLoc x _ = Error $ "invalid operand for LEA: " ++ (show x)


            fromMaybe :: (Functor r) => String -> Maybe a -> Running' r a
            fromMaybe msg Nothing = Error msg
            fromMaybe _   (Just a) = Next a

            takeLast n xs = drop ((length xs) - n) xs
            dropLast n xs = take ((length xs) - n) xs

            toVal :: OpLoc -> OpVal
            toVal (OpLocAddr addr) = OpValConst (Ref 0) addr
            toVal (OpLocReg r reg)  = OpValReg r reg

            safeLast [] = Nothing
            safeLast xs = Just $ last xs

            safeInit [] = Nothing
            safeInit xs = Just $ init xs

            setAt' :: Int -> a -> [a] -> Maybe [a]
            setAt' i x xs
                | i < 0 || i >= (length xs) = Nothing
                | otherwise = Just $ setAt i x xs


            snoc xs x = xs ++ [x]

(!?) :: [a] -> Int -> Maybe a
xs !? i 
    | (i >= 0) && (i < length xs) = Just $ xs !! i
    | otherwise = Nothing 


trace' s x = trace (s ++ " " ++ (show x)) x 



prettyShowVM :: VM -> String
prettyShowVM VM {codeMemory=ops, stackMemory=stack, generalRegisters = regs, specialRegisters = specs @ SpecialRegisters {programCounter = InstructionIx pc, stackTop = stackTopIx, stackBase = stackBaseIx}} =
    unlines $ [specs', separate "|" regs' stack', "-------"] ++ ops'
    where
        specs' = "ESP:" ++ (show stackTopIx) ++ " " ++ "EBP:" ++ (show stackBaseIx)
        regs' = (joinWith " " regs)
        stack' = joinWith " " $ take (stackTopIx+1) stack
        -- stack' = joinWith " " $ stack
        ops' = catMaybes . map (\i -> showOp i <$> (ops !? i)) $ [pc, pc+1, pc+2]
        showOp i op = (show i) ++ "  " ++ (show op) ++ (if i == pc then "  <--- " else "")


separate sep s1 s2 = s1' ++ sep ++ s2'
    where
        s1' = if null s1 then s1 else s1 ++ " "
        s2' = if null s2 then s2 else " " ++ s2

joinWith sep = concat . intersperse sep . map show


execProgram :: [Op] -> VM
execProgram ops = VM { codeMemory = ops
                     , stackMemory = replicate 40 0
                     , generalRegisters = replicate 10 0
                     , specialRegisters = SpecialRegisters {programCounter = InstructionIx 0
                                                           , stackBase = -1
                                                           , stackTop = -1}}

iterVM :: VM -> [Either String VM]
iterVM vm = (Right vm) : (iterVM' $ step vm) where

    iterVM' (Error e  ) = [Left $ "Error: "    ++ e]
    iterVM' (Stop  r  ) = [Left $ "Stopped. "  ++ r]
    iterVM' (Next  vm') = iterVM vm'
    iterVM' (Request f) = (Left . highlight $ "Request: " ++ (show f)) : rest where
        rest = case f of
                Read  _ k  -> iterVM' (k exampleInput)
                Print s k  -> iterVM' (k ())
                Exit  _ _  -> []
    exampleInput = "hello"
    highlight s = unlines $ [stars, s, stars] where stars = replicate 40 '#'


esp       = OpLocReg Val       (SpecialRegister StackTop)
espv      = OpValReg Val       (SpecialRegister StackTop)
ebp       = OpLocReg Val       (SpecialRegister StackBase)
ebpv      = OpValReg Val       (SpecialRegister StackBase)
_ebp off  = OpLocReg (Ref off) (SpecialRegister StackBase)
_ebpv off = OpValReg (Ref off) (SpecialRegister StackBase)
_espv off = OpValReg (Ref off) (SpecialRegister StackTop)
reg  i    = OpLocReg Val       (GeneralRegister . GeneralRegisterId $ i)
regv i    = OpValReg Val       (GeneralRegister . GeneralRegisterId $ i)
_reg  i   = OpLocReg (Ref 0)   (GeneralRegister . GeneralRegisterId $ i)
_regv i   = OpValReg (Ref 0)   (GeneralRegister . GeneralRegisterId $ i)
int n    = OpValConst Val n

type Block = (String, [Op])
type Procedure = (String -> InstructionIx) -> [Block]
type Program = [Procedure]

resolveLabels :: Program -> Either String [Op]
resolveLabels procs =
    let dummyProg = concat . map ($ dummy) $ procs
        labelOffsets = M.fromList . snd  .  mapAccumL (\off (lbl, len) -> (off+len, (lbl, off))) 0  .  map (second length) $ dummyProg
    in concat . map snd . concat <$> mapM (tryResolve labelOffsets) procs
    where
        dummy = const (InstructionIx (-1))
        tryResolve :: Map String Int -> Procedure -> Either String [Block]
        tryResolve labelOffsets proc = maybe (Left "undefined label") Right $ try_ $ proc $ (InstructionIx . (labelOffsets M.!))

try_ :: (NFData a) => a -> Maybe a
try_ x = unsafeDupablePerformIO $ do
            x' <- try $ evaluate (force x)
            pure . eToMaybe . (first dropException) $ x'

    where
        dropException :: SomeException -> ()
        dropException = const ()

        eToMaybe = either (const Nothing) Just
{-# NOINLINE try_ #-}

deriving instance Generic InstructionIx
deriving instance NFData  InstructionIx
deriving instance Generic InstructionOffset
deriving instance NFData  InstructionOffset
deriving instance Generic Register
deriving instance NFData  Register
deriving instance Generic SpecialRegisterId
deriving instance NFData  SpecialRegisterId
deriving instance Generic GeneralRegisterId
deriving instance NFData  GeneralRegisterId
deriving instance Generic Ref
deriving instance NFData  Ref
deriving instance Generic OpVal
deriving instance NFData  OpVal
deriving instance Generic OpLoc
deriving instance NFData  OpLoc
deriving instance Generic Op
deriving instance NFData  Op


p0 :: Program
p0 = [bootstrap, ptostr, parrrev, parrsum, pmain]

bootstrap lbl = [
    ("_bootstrap", [
        Push ebpv,
        Mov ebp espv,
        Call (lbl "main"),
        Mov esp ebpv,
        Pop ebp,
        Push (regv 0),
        SyscallExit ])
    ]
    where


pmain lbl = [
    -- main() -> int
    ("main", [
        Nop,
        Push (int (-10000)), 
        Push (int 0), -- out_str: [int, 5]
        Push (int 0),
        Push (int 0),
        Push (int 0),
        Push (int 0),
        Push (int (-10000)), 
        Push (int 1200), -- arr: [int, 4]
        Push (int 40),
        Push (int 20),
        Push (int 10),
        Push (int (-10000)),
        Lea (reg rtemp) (_ebpv $ 2+7), -- arr
        Push ebpv,
        Mov ebp espv,
        Push (int 4),      -- len(arr)
        Push (regv rtemp), -- arr
        Call (lbl "arrsum"),
        Mov esp ebpv,
        Pop ebp,
        Lea (reg rtemp) (_ebpv $ 2+1), -- out_str
        Push (regv rtemp),
        Push ebpv,
        Mov ebp espv,
        Push (regv rtemp),  -- out_str
        Push (regv 0),      -- num
        Call (lbl "tostr"),
        Mov esp ebpv,
        Pop ebp,
        Pop (reg rtemp),
        Push (regv 0),
        Push (regv rtemp),
        SyscallPrint,
        Push (_ebpv 1),
        Ret ])
    ]
    where
        rsum  = 0
        rtemp = 1

parrrev lbl = [
    -- arrrev(ptr: *int, len: int) -> int
    ("arrrev", [
        Mov (reg rdst) (_ebpv 2),
        Add (reg rdstback) (regv rdst) (_ebpv 1),
        Decr (reg rdstback) ]),
    ("arrev_loop", [
        Less (reg rtemp) (regv rdst) (regv rdstback),
        Not (reg rtemp) (regv rtemp),
        JmpIf (regv rtemp) (lbl "arrev_end"),
        Mov (reg rtemp) (_regv rdstback),
        Mov (_reg rdstback) (_regv rdst),
        Mov (_reg rdst) (regv rtemp),
        Incr (reg rdst),
        Decr (reg rdstback),
        Jmp (lbl "arrev_loop") ]),
    ("arrev_end", [
        Ret ])
    ]
    where
        rdst     = 0
        rdstback = 1
        rtemp    = 2

ptostr lbl = [
    -- tostr(n: int, out: *int) -> int
    ("tostr", [
        Mov (reg rnum) (_ebpv 2),
        Mov (reg rdst) (_ebpv 1),
        Mov (reg rlen) (int 0),
        Greater (reg rtemp) (regv rnum) (int 0),
        JmpIf (regv rtemp) (lbl "tostr_loop"),
        Mov (_reg rdst) (int 48),
        Mov (reg 0) (int 1),
        Ret ]),
    ("tostr_loop", [
        LessEqual (reg rtemp) (regv rnum) (int 0),
        JmpIf (regv rtemp) (lbl "tostr_end"),
        Mod (reg rtemp) (regv rnum) (int 10),
        Add (reg rtemp) (regv rtemp) (int 48),
        Mov (_reg rdst) (regv rtemp),
        Div (reg rnum) (regv rnum) (int 10),
        Incr (reg rdst),
        Incr (reg rlen),
        Jmp (lbl "tostr_loop") ]),
    ("tostr_end", [
        Push (regv rlen),
        Mov (reg rdst) (_ebpv 1),
        Push ebpv,
        Mov ebp espv,
        Push (regv rlen),
        Push (regv rdst),
        Call (lbl "arrrev"),
        Mov esp ebpv,
        Pop ebp,
        Pop (reg rlen),
        Mov (reg 0) (regv rlen), 
        Ret ])
    ]
    where
        rnum     = 0
        rlen     = 1
        rdst     = 2
        rtemp    = 3

parrsum lbl = [
    -- arrsum(ptr: *int, len: int) -> int
    ("arrsum", [
        Mov (reg rptr) (_ebpv 2),
        Mov (reg rres) (int 0),
        Mov (reg ri)   (int 0) ]),
    ("arrsum_loop", [
        Less (reg rtemp) (regv ri) (_ebpv 1),
        Not (reg rtemp) (regv rtemp),
        -- JmpIf (regv rtemp) (lbl "undefined"),
        JmpIf (regv rtemp) (lbl "arrsum_end"),
        Add (reg rres) (regv rres) (_regv rptr),
        Incr (reg ri),
        Incr (reg rptr),
        Jmp (lbl "arrsum_loop") ]),
    ("arrsum_end", [
        Mov (reg 0) (regv rres),
        Ret ])
    ]
     where
        rptr  = 0
        rres  = 1
        ri    = 2
        rtemp = 3




main = do
    -- let DDef funId args body = defAdd1 in
    --     print $ evalCompile $ compileDef funId args body
    case resolveLabels p0 of

        Left msg -> do
            putStrLn $ "Compilation error: " ++ msg

        Right prog -> do
            printCode prog
            blank
            blank
            let vm = execProgram prog
            forM_ (iterVM vm) $ either putStrLn (\x -> putStrLn (prettyShowVM x) >> blank)

    where
        print' x = print x >> blank 
        blank = putStrLn ""
        printCode = mapM putStrLn . map (uncurry showLine) . zip [0..]
        showLine n c = show n ++ "\t" ++ show c

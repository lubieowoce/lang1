-- TODO: make the stack grow downwards (because then ESP can point to the top value instead of one-past, and it makes push/pop easy)

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric, DeriveAnyClass, StandaloneDeriving #-}

module RegisterVM where

import StackVM (Running (..), Running', VMRequest (..), setAt, intToBool, boolToInt)

import Data.Map (Map)
import qualified Data.Map as M

import Data.Vector (Vector)
import qualified Data.Vector as V

import qualified Data.Word as W
import Data.Bits

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

type GeneralRegisters = [W.Word64]


type IntVal = Int


data Ref = Val | Ref Int deriving (Eq, Show)

-- data Address
--     = StackAddress Int
--     | HeapAddress  Int
--     deriving (Eq, Show)

data OpVal
    = OpValReg   Ref Register
    | OpValConst Ref Int
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

regSize :: Size
regSize = S64


data WordVal
    = W8  W.Word8
    | W16 W.Word16
    | W32 W.Word32
    | W64 W.Word64
    deriving (Show)

wordValSize :: WordVal -> Size
wordValSize (W8  _) = S8 
wordValSize (W16 _) = S16
wordValSize (W32 _) = S32
wordValSize (W64 _) = S64

castWordVal :: Size -> WordVal -> WordVal
castWordVal size val =
    case (val, size) of
        (x@(W8 _), S8) -> x 
        (x@(W16 _), S16) -> x 
        (x@(W32 _), S32) -> x 
        (x@(W64 _), S64) -> x

        (W8  x, S16) -> W16 . integral $ x 
        (W8  x, S32) -> W32 . integral $ x 
        (W8  x, S64) -> W64 . integral $ x
         
        (W16 x, S8 ) -> W8  . integral $ x 
        (W16 x, S32) -> W32 . integral $ x 
        (W16 x, S64) -> W64 . integral $ x
         
        (W32 x, S8 ) -> W8  . integral $ x 
        (W32 x, S16) -> W16 . integral $ x 
        (W32 x, S64) -> W64 . integral $ x
         
        (W64 x, S8 ) -> W8  . integral $ x 
        (W64 x, S16) -> W16 . integral $ x 
        (W64 x, S32) -> W32 . integral $ x 

wordValFromBytes :: [W.Word8] -> Maybe WordVal
wordValFromBytes x = case x of 
     [x0] ->
        Just $ W8 x0
     [x8, x0] ->
        Just $ W16 $ ((to16 x8) `shiftL` 8) .|. (to16 x0)
     [x24, x16, x8, x0] -> Just $ W32 $
        (    (to32 x24) `shiftL` 24)
        .|. ((to32 x16) `shiftL` 16)
        .|. ((to32  x8) `shiftL`  8)
        .|.   (to32 x0) 
     [x56, x48, x40, x32, x24, x16, x8, x0] -> Just $ W64 $
        (    (to64 x56) `shiftL` 56)
        .|. ((to64 x48) `shiftL` 48)
        .|. ((to64 x40) `shiftL` 40)
        .|. ((to64 x32) `shiftL` 32)
        .|. ((to64 x24) `shiftL` 24)
        .|. ((to64 x16) `shiftL` 16)
        .|. ((to64  x8) `shiftL`  8)
        .|.   (to64 x0) 
     _ -> Nothing
    where
      to16 :: W.Word8 -> W.Word16
      to16 = integral
      to32 :: W.Word8 -> W.Word32
      to32 = integral
      to64 :: W.Word8 -> W.Word64
      to64 = integral

wordValToBytes :: WordVal -> [W.Word8] 
wordValToBytes x = case x of 
    W8 x -> [x]
    W16 x -> [(to8 $ x `shiftR` 8), (to8 x)]
    W32 x -> 
        [ (to8 $ x `shiftR` 24)
        , (to8 $ x `shiftR` 16)
        , (to8 $ x `shiftR`  8)
        , (to8 x) ]
    W64 x -> 
        [ (to8 $ x `shiftR` 56)
        , (to8 $ x `shiftR` 48)
        , (to8 $ x `shiftR` 40)
        , (to8 $ x `shiftR` 32)
        , (to8 $ x `shiftR` 24)
        , (to8 $ x `shiftR` 16)
        , (to8 $ x `shiftR`  8)
        , (to8 x) ]
    where
      to8 :: (Integral a) => a -> W.Word8
      to8 = integral

wordValToInt :: WordVal -> Int
wordValToInt (W8  x) = integral x
wordValToInt (W16 x) = integral x
wordValToInt (W32 x) = integral x
wordValToInt (W64 x) = integral x


leastCommonSize :: WordVal -> WordVal -> Size
leastCommonSize a b = max (wordValSize a) (wordValSize b)

promoteSize :: WordVal -> WordVal -> (WordVal, WordVal)
promoteSize a b = let size = leastCommonSize a b
                   in (castWordVal size a, castWordVal size b)

-- overCommon :: (forall a r. (Integral a) => a -> a -> r) -> (WordVal -> WordVal -> r)
-- overCommon f a b = case promoteSize a b of
--                     (W8  a, W8  b) -> W8  $ f a b
--                     (W16 a, W16 b) -> W16 $ f a b
--                     (W32 a, W32 b) -> W32 $ f a b
--                     (W64 a, W64 b) -> W64 $ f a b
                     

integral :: (Integral a, Integral b) => a -> b
integral = fromIntegral . toInteger






data Op
    = Nop
    | Mov Size OpLoc OpVal
    | Lea OpLoc OpVal

    | Push Size OpVal
    | Pop  Size OpLoc

    | Add Size OpLoc OpVal OpVal
    | Sub Size OpLoc OpVal OpVal
    | Mul Size OpLoc OpVal OpVal
    | Div Size OpLoc OpVal OpVal
    | Mod Size OpLoc OpVal OpVal

    | Incr Size OpLoc
    | Decr Size OpLoc

    | Equal        Size OpLoc OpVal OpVal 
    | Less         Size OpLoc OpVal OpVal 
    | Greater      Size OpLoc OpVal OpVal 
    | LessEqual    Size OpLoc OpVal OpVal 
    | GreaterEqual Size OpLoc OpVal OpVal
    
    | Not Size OpLoc OpVal

    | Jmp         InstructionIx
    | JmpIf OpVal InstructionIx

    | Call InstructionIx
    | Ret

    | SyscallExit 
    | SyscallPrint

    deriving (Eq, Show)


data VM = VM {
        codeMemory  :: [Op],
        stackMemory :: [W.Word8],
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

            Mov size dst src      ->  do val <- getVal size src vm
                                         setLoc size dst val $ vm'
            Lea dst loc           ->  do addr <- getLoc S64 loc vm
                                         setLoc S64 dst addr $ vm'

            Push size v           ->  push size v   vm'
            Pop  size dst         ->  pop  size dst vm'

            Add size dst a b           ->  binop size (+) dst a b vm'
            Sub size dst a b           ->  binop size (-) dst a b vm'
            Mul size dst a b           ->  binop size (*) dst a b vm'
            Div size dst a b           ->  binop size (div) dst a b vm'
            Mod size dst a b           ->  binop size (mod) dst a b vm'

            Incr size loc              ->  incrop size (+ 1)        loc vm'
            Decr size loc              ->  incrop size (subtract 1) loc vm'
            
            Equal        size dst a b  ->  binop' size (==) dst a b vm' 
            Less         size dst a b  ->  binop' size (<)  dst a b vm'
            Greater      size dst a b  ->  binop' size (>)  dst a b vm' 
            LessEqual    size dst a b  ->  binop' size (<=) dst a b vm' 
            GreaterEqual size dst a b  ->  binop' size (>=) dst a b vm'

            Not size dst x             ->  unop' size (not) dst x vm'

            Jmp     loc           ->  jmp loc vm
            JmpIf x loc           ->  do W64 xv <- getVal S64 x vm
                                         if (intToBool . integral $ xv) then jmp loc vm else pure vm'

            Call loc              ->  do vm2 <- push S64 (OpValConst Val $ pc+1) vm
                                         jmp loc vm2
            Ret                   ->  do (retLoc, vm2) <- pop' S64 vm
                                         setLoc S64 (OpLocReg Val $ SpecialRegister ProgramCounter) retLoc vm2
            SyscallExit           ->  do (exitVal, _) <- pop' S64 vm
                                         Stop $ show exitVal
            SyscallPrint          ->  do (W64 ptr, vm2) <- pop' S64 vm'
                                         (W64 len, vm3) <- pop' S64 vm2
                                         let str = map chr . map integral . slice (integral ptr) (integral len) . stackMemory $ vm3
                                         if (length str) /= (integral len)
                                            then Error "bad print syscall"
                                            else Request (Print str (\_ -> pure vm3))
        where
            binop' size (f :: forall a . Integral a => a -> a -> Bool) = binop size (\a b -> if f a b then a*0 + 1 else a*0)
            binop size (f :: forall a . Integral a => a -> a -> a) dst a b vm = do
                av <- getVal size a vm
                bv <- getVal size b vm
                let res = case promoteSize av bv of
                            (W8  a, W8  b) -> W8  $ f a b
                            (W16 a, W16 b) -> W16 $ f a b
                            (W32 a, W32 b) -> W32 $ f a b
                            (W64 a, W64 b) -> W64 $ f a b
                setLoc size dst res $ vm
            incrop size (f :: forall a . Integral a => a -> a) loc vm = do 
                v <- getVal size (toVal loc) vm
                let res = case v of
                            (W8  a) -> W8  $ f a
                            (W16 a) -> W16 $ f a
                            (W32 a) -> W32 $ f a
                            (W64 a) -> W64 $ f a
                setLoc size loc res $ vm
            unop' size f = unop size (integral . boolToInt . f . intToBool . integral)
            unop size (f :: forall a . Integral a => a -> a) dst x vm = do
                v <- getVal size x vm
                let res = case v of
                            (W8  a) -> W8  $ f a
                            (W16 a) -> W16 $ f a
                            (W32 a) -> W32 $ f a
                            (W64 a) -> W64 $ f a
                setLoc size dst res $ vm
            jmp loc vm = pure $ vm {specialRegisters=(specialRegisters vm){programCounter=loc}}
            push size v vm = do
                val <- getVal size v vm
                -- let (!val, x) = trace' "push :: " $ (_val, wordValToBytes _val)
                let stackTopIx = stackTop . specialRegisters $ vm
                let stackTopIx' = (sizeToBytes size) + stackTopIx
                stack' <- (fromMaybe $ "bad stackTop: " ++ (show stackTopIx')) $
                            pasteAt stackTopIx (wordValToBytes val) (stackMemory vm)
                pure $ vm {stackMemory = stack', specialRegisters = (specialRegisters vm) {stackTop=stackTopIx'}}
            pop size dst vm = do
                (val, vm2) <- pop' size vm
                setLoc size dst val vm2
            pop' size vm = do
                let stackTopIx = stackTop (specialRegisters vm)
                    valSize = sizeToBytes size
                    stackTopIx' = stackTopIx - valSize
                val <- (fromMaybe $ "bad stackTop: " ++ (show stackTopIx)) $
                            wordValFromBytes $ slice stackTopIx' valSize (stackMemory vm)
                let vm2 = vm {specialRegisters=(specialRegisters vm){stackTop=stackTopIx'}}
                pure (val, vm2)


            getVal :: (Functor r) => Size -> OpVal -> VM -> Running' r WordVal
            getVal size (OpValConst Val n) vm = pure . (castWordVal size) . W64 . integral $ n
            getVal size (OpValReg   Val (GeneralRegister (GeneralRegisterId i))) vm =
                (fromMaybe "invalid register") . (fmap $ castWordVal size . W64) . (!? i) . generalRegisters $ vm
            getVal size (OpValReg   Val (SpecialRegister r)) vm = pure . W64 . integral . getR . specialRegisters $ vm where
                getR :: SpecialRegisters -> Int
                getR = case r of
                        ProgramCounter -> coerce . programCounter
                        StackBase -> stackBase
                        StackTop -> stackTop
            getVal size (OpValConst (Ref offset) addr) vm =
                (fromMaybe  "invalid stack address or operand size") . wordValFromBytes . (slice (addr + offset) (sizeToBytes size)) . stackMemory $ vm
            getVal size (OpValReg   (Ref offset) r   ) vm = do W64 addr <- getVal S64 (OpValReg Val r) vm
                                                               getVal size (OpValConst (Ref offset) (integral addr)) vm


            setLoc :: (Functor r) => Size -> OpLoc -> WordVal -> VM -> Running' r VM 
            setLoc size (OpLocReg Val (GeneralRegister (GeneralRegisterId i))) val vm = do
                grs <- (fromMaybe "invalid register") . (setAt' i (let W64 x = castWordVal S64 val in x)) . generalRegisters $ vm
                pure $ vm {generalRegisters=grs}
            setLoc size (OpLocReg Val (SpecialRegister r)) val vm =
                let srs = setR (wordValToInt val) . specialRegisters $ vm
                 in pure $ vm {specialRegisters=srs} where
                setR val srs = case r of
                                ProgramCounter -> srs {programCounter=InstructionIx val}
                                StackBase -> srs {stackBase=val}
                                StackTop -> srs {stackTop=val}
            setLoc size (OpLocReg (Ref offset) r) val vm = do
                W64 addr <- getVal S64 (OpValReg Val r) vm
                setLoc size (OpLocAddr ((integral addr) + offset)) val vm
            setLoc size (OpLocAddr addr) val vm = do
                smem <- (fromMaybe  "invalid stack address") . (pasteAt addr (wordValToBytes . castWordVal size $ val)) . stackMemory $ vm
                pure $ vm {stackMemory=smem}
            -- setLoc size (OpLocAddr (HeapAddress addr))  val vm = undefined
            -- setLoc size (OpLocAddr (HeapAddress addr))  val vm = do hmem <- (fromMaybe  "invalid heap address")  . (M.insert addr val) . heapMemory $ vm; pure vm {heapMemory=hmem}

            getLoc :: (Functor r) => Size -> OpVal -> VM -> Running' r WordVal
            getLoc size (OpValConst (Ref offset) addr) vm = pure . W64 . fromIntegral . toInteger $ (addr + offset)
            getLoc size (OpValReg   (Ref offset) r   ) vm = do W64 addr <- getVal size (OpValReg Val r) vm;
                                                               getLoc size (OpValConst (Ref offset) (integral addr)) vm
            getLoc _ x _ = Error $ "invalid operand for LEA: " ++ (show x)


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

            pasteAt :: Int -> [a] -> [a] -> Maybe [a]
            pasteAt i xs ys
                | i < 0 || i >= (length ys) || i+(length xs) >= (length ys) = Nothing
                | otherwise = Just $ (take i ys) ++ xs ++ (drop (i+(length xs)) ys) 

            snoc xs x = xs ++ [x]

            slice start len = take len . drop start 

(!?) :: [a] -> Int -> Maybe a
xs !? i 
    | (i >= 0) && (i < length xs) = Just $ xs !! i
    | otherwise = Nothing 


trace' s x = trace (s ++ " " ++ (show x)) x 



prettyShowVM :: VM -> String
prettyShowVM VM {codeMemory=ops, stackMemory=stack, generalRegisters = regs, specialRegisters = specs @ SpecialRegisters {programCounter = InstructionIx pc, stackTop = stackTopIx, stackBase = stackBaseIx}} =
    unlines $ [specs', regs'] ++ ["-------"] ++ stack' ++ ["-------"] ++ ops'
    where
        specs' = "ESP:" ++ (show stackTopIx) ++ " " ++ "EBP:" ++ (show stackBaseIx)
        regs' = (joinWith " " regs)
        stack' = (joinWith " " <$>) . chunks 8 . take (stackTopIx) $ stack
        -- stack' = joinWith " " $ stack
        ops' = catMaybes . map (\i -> showOp i <$> (ops !? i)) $ [pc, pc+1, pc+2]
        showOp i op = (show i) ++ "  " ++ (show op) ++ (if i == pc then "  <--- " else "")
        chunks :: Int -> [a] -> [[a]]
        chunks n xs
            | (length xs) <= n = [xs]
            | otherwise = (take n xs) : (chunks n $ drop n xs) 


separate sep s1 s2 = s1' ++ sep ++ s2'
    where
        s1' = if null s1 then s1 else s1 ++ " "
        s2' = if null s2 then s2 else " " ++ s2

joinWith sep = concat . intersperse sep . map show


execProgram :: [Op] -> VM
execProgram ops = VM { codeMemory = ops
                     , stackMemory = replicate stackSize 0
                     , generalRegisters = replicate 10 0
                     , specialRegisters = SpecialRegisters {programCounter = InstructionIx 0
                                                           , stackBase = 0
                                                           , stackTop  = 0}}
    where stackSize = 400

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

sizeof = sizeToBytes
_Char = S8
_Int  = S64
_Ptr  = S64

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
deriving instance Generic Size
deriving instance NFData  Size


p0 :: Program
p0 = [bootstrap, ptostr, pstrrev, parrsum, pmain]

bootstrap lbl = [
    ("_bootstrap", [
        Push _Ptr ebpv,
        Mov _Ptr ebp espv,
        Call (lbl "main"),
        Mov _Ptr esp ebpv,
        Pop _Ptr ebp,
        Push _Int (regv 0),
        SyscallExit ])
    ]
    where


pmain lbl = [
    -- main() -> int
    ("main", [
        Nop,
        Push _Char (int 1), 
        Push _Char (int 0), -- out_str: [char, 5]
        Push _Char (int 0),
        Push _Char (int 0),
        Push _Char (int 0),
        Push _Char (int 0),
        Push _Char (int 1), 
        Push _Char (int 1), 
        Push _Int  (int 1200), -- arr: [int, 4]
        Push _Int  (int 40),
        Push _Int  (int 20),
        Push _Int  (int 10),
        Push _Int  (int (-1)),
        Lea (reg rtemp) (_ebpv $ (sizeof _Ptr) + 8*(sizeof _Char)), -- arr
        Push _Ptr ebpv,
        Mov _Ptr ebp espv,
        Push _Int (int 4),      -- len(arr)
        Push _Ptr (regv rtemp), -- arr
        Call (lbl "arrsum"),
        Mov _Ptr esp ebpv,
        Pop _Ptr ebp,
        Lea (reg rtemp) (_ebpv $ (sizeof _Ptr) + (sizeof _Char)), -- out_str
        Push _Ptr (regv rtemp),
        Push _Ptr ebpv,
        Mov _Ptr ebp espv,
        Push _Ptr (regv rtemp),  -- out_str
        Push _Int (regv 0),      -- num
        Call (lbl "tostr"),
        Mov _Ptr esp ebpv,
        Pop _Ptr ebp,
        Pop _Ptr (reg rtemp),
        Push _Int (regv 0),
        Push _Ptr (regv rtemp),
        SyscallPrint,
        Push _Int (_ebpv 0),
        Ret ])
    ]
    where
        rsum  = 0
        rtemp = 1

pstrrev lbl = [
    -- strrev(ptr: *char, len: int) -> int
    ("strrev", [
        Mov _Ptr (reg rdst) (_ebpv $ sizeof _Int),
        Add _Ptr (reg rdstback) (regv rdst) (_ebpv 0),
        Decr _Ptr (reg rdstback) ]),
    ("strrev_loop", [
        Less _Ptr (reg rtemp) (regv rdst) (regv rdstback),
        Not _Int (reg rtemp) (regv rtemp),
        JmpIf (regv rtemp) (lbl "strrev_end"),
        Mov _Char (reg rtemp) (_regv rdstback),
        Mov _Char (_reg rdstback) (_regv rdst),
        Mov _Char (_reg rdst) (regv rtemp),
        Incr _Ptr (reg rdst),
        Decr _Ptr (reg rdstback),
        Jmp (lbl "strrev_loop") ]),
    ("strrev_end", [
        Ret ])
    ]
    where
        rdst     = 0
        rdstback = 1
        rtemp    = 2

ptostr lbl = [
    -- tostr(n: int, out: *char) -> int
    ("tostr", [
        Mov _Int (reg rnum) (_ebpv $ sizeof _Ptr),
        Mov _Ptr (reg rdst) (_ebpv 0),
        Mov _Int (reg rlen) (int 0),
        Greater _Int (reg rtemp) (regv rnum) (int 0),
        JmpIf (regv rtemp) (lbl "tostr_loop"),
        Mov _Char (_reg rdst) (int 48),
        Mov _Int (reg 0) (int 1),
        Ret ]),
    ("tostr_loop", [
        LessEqual _Int (reg rtemp) (regv rnum) (int 0),
        JmpIf (regv rtemp) (lbl "tostr_end"),
        Mod _Int (reg rtemp) (regv rnum) (int 10),
        Add _Int (reg rtemp) (regv rtemp) (int 48),
        Mov _Char (_reg rdst) (regv rtemp),
        Div _Int (reg rnum) (regv rnum) (int 10),
        Incr _Ptr (reg rdst),
        Incr _Int (reg rlen),
        Jmp (lbl "tostr_loop") ]),
    ("tostr_end", [
        Push _Int (regv rlen),
        Mov _Ptr (reg rdst) (_ebpv 0),
        Push _Ptr ebpv,
        Mov _Ptr ebp espv,
        Push _Int (regv rlen),
        Push _Ptr (regv rdst),
        Call (lbl "strrev"),
        Mov _Ptr esp ebpv,
        Pop _Ptr ebp,
        Pop _Int (reg rlen),
        Mov _Int (reg 0) (regv rlen), 
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
        Mov _Ptr (reg rptr) (_ebpv $ (sizeof _Int)),
        Mov _Int (reg rres) (int 0),
        Mov _Int (reg ri)   (int 0) ]),
    ("arrsum_loop", [
        Less _Int (reg rtemp) (regv ri) (_ebpv $ 0),
        Not _Int (reg rtemp) (regv rtemp),
        -- JmpIf (regv rtemp) (lbl "undefined"),
        JmpIf (regv rtemp) (lbl "arrsum_end"),
        Add _Int (reg rres) (regv rres) (_regv rptr),
        Incr _Int (reg ri),
        Add _Ptr (reg rptr) (regv rptr) (int $ sizeof _Int),
        Jmp (lbl "arrsum_loop") ]),
    ("arrsum_end", [
        Mov _Int (reg 0) (regv rres),
        Ret ])
    ]
     where
        rptr  = 0
        rres  = 1
        ri    = 2
        rtemp = 3




main = do
    -- forM_ (W64 <$> [0..16] ++ [255] ++ [256, 512, 1024, maxBound]) $ \x@(W64 xv) -> do
    --     let Just x'@(W64 x'v) = wordValFromBytes . wordValToBytes $ x
    --     putStrLn $ (show x) ++ " " ++ (show x') ++ " " ++ (if xv == x'v then "OK" else "FAILED") 

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
            forM_ (iterVM vm) $
                either putStrLn (\x -> putStrLn (prettyShowVM x) >> blank)

    where
        print' x = print x >> blank 
        blank = putStrLn ""
        printCode = mapM putStrLn . map (uncurry showLine) . zip [0..]
        showLine n c = show n ++ "\t" ++ show c

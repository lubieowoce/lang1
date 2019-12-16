-- TODO: make the stack grow downwards (because then ESP can point to the top value instead of one-past, and it makes push/pop easy)

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric, DeriveAnyClass, StandaloneDeriving #-}

module RegisterVM where

import Util

import Data.Map (Map)
import qualified Data.Map as M

import Data.Vector (Vector)
import qualified Data.Vector as V

import qualified Data.Word as W
import qualified Data.Int  as I
import Data.Bits

import Data.Char (chr, ord)

import Data.Coerce

import Control.Monad (forM, forM_, when)
import Data.Maybe (catMaybes)

import Control.Exception (SomeException, try, evaluate)
-- import System.IO.Unsafe (unsafePerformIO, unsafeInterleaveIO)
import System.IO.Unsafe
import GHC.Generics (Generic)
import Control.DeepSeq (force, NFData)
import Debug.Trace (trace)

import Data.Bifunctor (first, second)
import Data.List (mapAccumL, mapAccumR)


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
data Signedness = Signed | Unsigned deriving (Eq, Show)
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

sizeNumBytes :: Size -> Int
sizeNumBytes S8  = 1
sizeNumBytes S16 = 2
sizeNumBytes S32 = 4
sizeNumBytes S64 = 8

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
     [x0, x8] ->
        Just $ W16 $ (to16 x0) .|. ((to16 x8) `shiftL` 8)
     [x0, x8, x16, x24] -> Just $ W32 $
        (    (to32  x0) 
        .|. ((to32  x8) `shiftL`  8)
        .|. ((to32 x16) `shiftL` 16)
        .|. ((to32 x24) `shiftL` 24) )
     [x0, x8, x16, x24, x32, x40, x48, x56] -> Just $ W64 $
        (    (to64  x0) 
        .|. ((to64  x8) `shiftL`  8)
        .|. ((to64 x16) `shiftL` 16)
        .|. ((to64 x24) `shiftL` 24)
        .|. ((to64 x32) `shiftL` 32)
        .|. ((to64 x40) `shiftL` 40)
        .|. ((to64 x48) `shiftL` 48)
        .|. ((to64 x56) `shiftL` 56) )
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
    W16 x -> [(to8 x), (to8 $ x `shiftR` 8)]
    W32 x -> 
        [ (to8 x)
        , (to8 $ x `shiftR`  8)
        , (to8 $ x `shiftR` 16)
        , (to8 $ x `shiftR` 24) ]
    W64 x -> 
        [ (to8 x)
        , (to8 $ x `shiftR`  8)
        , (to8 $ x `shiftR` 16)
        , (to8 $ x `shiftR` 24)
        , (to8 $ x `shiftR` 32)
        , (to8 $ x `shiftR` 40)
        , (to8 $ x `shiftR` 48)
        , (to8 $ x `shiftR` 56) ]
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
    | Mod Size OpLoc OpVal OpVal
    | Mul Size Signedness OpLoc OpVal OpVal
    | Div Size Signedness OpLoc OpVal OpVal

    | Incr Size OpLoc
    | Decr Size OpLoc

    | Equal        Size OpLoc OpVal OpVal 
    | Less         Size Signedness OpLoc OpVal OpVal 
    | Greater      Size Signedness OpLoc OpVal OpVal 
    | LessEqual    Size Signedness OpLoc OpVal OpVal 
    | GreaterEqual Size Signedness OpLoc OpVal OpVal
    
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

            Add size dst a b           ->  binop size Unsigned (+)   dst a b vm'
            Sub size dst a b           ->  binop size Unsigned (-)   dst a b vm'
            Mod size dst a b           ->  binop size Unsigned (mod) dst a b vm'
            Mul size sign dst a b      ->  binop size sign     (*)   dst a b vm'
            Div size sign dst a b      ->  binop size sign     (div) dst a b vm'

            Incr size loc              ->  incrop size (+ 1)        loc vm'
            Decr size loc              ->  incrop size (subtract 1) loc vm'
            
            Equal        size      dst a b  ->  boolop size Unsigned (==) dst a b vm' 
            Less         size sign dst a b  ->  boolop size sign     (<)  dst a b vm'
            Greater      size sign dst a b  ->  boolop size sign     (>)  dst a b vm' 
            LessEqual    size sign dst a b  ->  boolop size sign     (<=) dst a b vm' 
            GreaterEqual size sign dst a b  ->  boolop size sign     (>=) dst a b vm'

            Not size dst x             ->  unop' size (not) dst x vm'

            Jmp     loc           ->  jmp loc vm
            JmpIf x loc           ->  do W8 xv <- getVal S8 x vm
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
            boolop size sign (f :: forall a . Integral a => a -> a -> Bool) dst a b vm = do
                av <- getVal size a vm
                bv <- getVal size b vm
                let  f' :: forall a . Integral a => a -> a -> W.Word8
                     f' = \a b -> if f a b then 1 else 0 
                let res = case (promoteSize av bv, sign) of
                            ((W8  a, W8  b), Unsigned) -> W8 $ f' a b
                            ((W16 a, W16 b), Unsigned) -> W8 $ f' a b
                            ((W32 a, W32 b), Unsigned) -> W8 $ f' a b
                            ((W64 a, W64 b), Unsigned) -> W8 $ f' a b
                            ((W8  a, W8  b), Signed  ) -> W8 $ integral $ f' (integral a :: I.Int8 ) (integral b :: I.Int8 )
                            ((W16 a, W16 b), Signed  ) -> W8 $ integral $ f' (integral a :: I.Int16) (integral b :: I.Int16)
                            ((W32 a, W32 b), Signed  ) -> W8 $ integral $ f' (integral a :: I.Int32) (integral b :: I.Int32)
                            ((W64 a, W64 b), Signed  ) -> W8 $ integral $ f' (integral a :: I.Int64) (integral b :: I.Int64)
                setLoc S8 dst res $ vm
            binop size sign (f :: forall a . Integral a => a -> a -> a) dst a b vm = do
                av <- getVal size a vm
                bv <- getVal size b vm
                let res = case (promoteSize av bv, sign) of
                            ((W8  a, W8  b), Unsigned) -> W8  $ f a b
                            ((W16 a, W16 b), Unsigned) -> W16 $ f a b
                            ((W32 a, W32 b), Unsigned) -> W32 $ f a b
                            ((W64 a, W64 b), Unsigned) -> W64 $ f a b
                            ((W8  a, W8  b), Signed  ) -> W8  $ integral $ f (integral a :: I.Int8 ) (integral b :: I.Int8 )
                            ((W16 a, W16 b), Signed  ) -> W16 $ integral $ f (integral a :: I.Int16) (integral b :: I.Int16)
                            ((W32 a, W32 b), Signed  ) -> W32 $ integral $ f (integral a :: I.Int32) (integral b :: I.Int32)
                            ((W64 a, W64 b), Signed  ) -> W64 $ integral $ f (integral a :: I.Int64) (integral b :: I.Int64)
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
                    valSize = sizeNumBytes size
                    stackTopIx' = stackTopIx - valSize
                when (stackTopIx < 0) $
                    Error $ "stack overflow when pushing " ++ (show val)
                    ++ "(" ++ (show valSize) ++ "bytes)"
                stack' <- (fromMaybe $ "bad ESP " ++ (show stackTopIx') ++ " when pushing " ++ (show val)) $
                            pasteAt stackTopIx' (wordValToBytes val) (stackMemory vm)
                pure $ vm { stackMemory = stack'
                          , specialRegisters = (specialRegisters vm) {stackTop=stackTopIx'}
                          }
            pop size dst vm = do
                (val, vm2) <- pop' size vm
                setLoc size dst val vm2
            pop' size vm = do
                let stackTopIx = stackTop (specialRegisters vm)
                    valSize = sizeNumBytes size
                    stackTopIx' = stackTopIx + valSize
                when (stackTopIx' > (length $ stackMemory vm)) $
                    Error $ "stack underflow when popping " ++ (show valSize) ++ " bytes"
                val <- (fromMaybe $ "bad ESP " ++ (show stackTopIx) ++ " when popping " ++ (show valSize) ++ " bytes") $
                            wordValFromBytes $ slice stackTopIx valSize (stackMemory vm)
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
                (fromMaybe  "invalid stack address or operand size") . wordValFromBytes . (slice (addr + offset) (sizeNumBytes size)) . stackMemory $ vm

            getVal size (OpValReg   (Ref offset) r   ) vm = do
                W64 addr <- getVal S64 (OpValReg Val r) vm
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
            getLoc size (OpValConst (Ref offset) addr) vm = pure . W64 . integral $ (addr + offset)
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
                | i < 0 || i >= (length ys) || i+(length xs)-1 >= (length ys) = Nothing
                | otherwise = Just $ (take i ys) ++ xs ++ (drop (i+(length xs)) ys) 

            snoc xs x = xs ++ [x]

            slice start len = take len . drop start 



prettyShowVM :: VM -> String
prettyShowVM VM {codeMemory=ops, stackMemory=stack, generalRegisters = regs, specialRegisters = specs @ SpecialRegisters {programCounter = InstructionIx pc, stackTop = stackTopIx, stackBase = stackBaseIx}} =
    unlines $ [specs', regs'] ++ ["-------"] ++ stack' ++ ["-------"] ++ ops'
    where
        specs' = "ESP:" ++ (show stackTopIx) ++ " " ++ "EBP:" ++ (show stackBaseIx)
        regs' = (joinWith " " regs)
        stack' = snd . mapAccumR (\n line -> (n-8, (show n) ++ " | " ++ line)) ((length stack)-8) . map (joinWith' " ") . map (pad "_" 8) . map reverse . reverse . chunks 8 . reverse . map show . drop (stackTopIx) $ stack
        -- stack' = joinWith " " $ stack
        ops' = catMaybes . map (\i -> showOp i <$> (ops !? i)) $ [pc, pc+1, pc+2]
        showOp i op = (show i) ++ "  " ++ (show op) ++ (if i == pc then "  <--- " else "")
        chunks :: Int -> [a] -> [[a]]
        chunks n xs
            | (length xs) <= n = [xs]
            | otherwise = (take n xs) : (chunks n $ drop n xs) 
        pad x len xs
            | xslen < len = replicate (len - xslen) x ++ xs
            | otherwise  = xs
            where xslen = length xs



execProgram :: [Op] -> VM
execProgram ops = VM { codeMemory = ops
                     , stackMemory = replicate stackSize 0
                     , generalRegisters = replicate 10 0
                     , specialRegisters = SpecialRegisters {programCounter = InstructionIx 0
                                                           , stackBase = stackSize
                                                           , stackTop  = stackSize}}
    where stackSize = 800

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

neg = negate
sizeof = sizeNumBytes
_Char = S8
_UInt = S64
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
deriving instance Generic Signedness
deriving instance NFData  Signedness
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
        Call (lbl "main"),
        Push _Int (regv 0),
        SyscallExit ])
    ]
    where


-- main() -> uint
pmain lbl = let
        offset_out_str = neg $ (1+5)   * (sizeof _Char) 
        offset_arr     = neg $ (1+5+2) * (sizeof _Char) + 4 * (sizeof _Int)
    in [
    ("main", [
        Push _Ptr ebpv,
        Mov _Ptr ebp espv,

        Push _Char (int 1), 
        Sub _Ptr esp espv (int $ 5 * sizeof _Char), -- out_str: [char, 5] 
        Mov _Char (_ebp $ offset_out_str + 0 * (sizeof _Char)) (int 0),
        Mov _Char (_ebp $ offset_out_str + 1 * (sizeof _Char)) (int 1),
        Mov _Char (_ebp $ offset_out_str + 2 * (sizeof _Char)) (int 2),
        Mov _Char (_ebp $ offset_out_str + 3 * (sizeof _Char)) (int 3),
        Mov _Char (_ebp $ offset_out_str + 4 * (sizeof _Char)) (int 4),
        Push _Char (int 1),
        Push _Char (int 1),

        Sub _Ptr esp espv (int $ 4 * sizeof _Int),  -- arr: [int, 4]
        Mov _Int (_ebp $ offset_arr + 0 * (sizeof _Int)) (int (-1200)),
        Mov _Int (_ebp $ offset_arr + 1 * (sizeof _Int)) (int   40),
        Mov _Int (_ebp $ offset_arr + 2 * (sizeof _Int)) (int   20),
        Mov _Int (_ebp $ offset_arr + 3 * (sizeof _Int)) (int   10),
        Push _Int (int (-1)),

        Push _Int (int 4),      -- len(arr)
        Lea (reg rtemp) (_ebpv $ offset_arr),
        Push _Ptr (regv rtemp), -- arr
        Call (lbl "arrsum"),
        Add _Ptr esp espv (int $ (sizeof _Ptr) + (sizeof _Int)), -- arg cleanup

        Lea (reg rtemp) (_ebpv $ offset_out_str),
        Push _Ptr (regv rtemp), -- out_str
        Push _Int (regv 0),     -- num
        Call (lbl "tostr"),
        Add _Ptr esp espv (int $ (sizeof _Int) + (sizeof _Ptr)), -- arg cleanup

        Push _Int (regv 0),
        Lea (reg rtemp) (_ebpv $ offset_out_str),
        Push _Ptr (regv rtemp),
        SyscallPrint,

        Mov _Ptr esp ebpv,
        Pop _Ptr ebp,
        Ret ])
    ]
    where
        rsum  = 0
        rtemp = 1

-- strrev(ptr: *char, len: uint) -> ()
pstrrev lbl = let
    offset_ptr = (sizeof _Ptr) + (sizeof _Int)
    offset_len = (sizeof _Ptr) + (sizeof _Int) + (sizeof _Ptr)
    in [
    ("strrev", [
        Push _Ptr ebpv,
        Mov _Ptr ebp espv,
        Mov _Ptr (reg rdst) (_ebpv $ offset_ptr),
        Add _Ptr (reg rdstback) (regv rdst) (_ebpv $ offset_len),
        Decr _Ptr (reg rdstback) ]),
    ("strrev_loop", [
        Less _Ptr Unsigned (reg rtemp) (regv rdst) (regv rdstback),
        Not _Int (reg rtemp) (regv rtemp),
        JmpIf (regv rtemp) (lbl "strrev_end"),
        Mov _Char (reg rtemp) (_regv rdstback),
        Mov _Char (_reg rdstback) (_regv rdst),
        Mov _Char (_reg rdst) (regv rtemp),
        Incr _Ptr (reg rdst),
        Decr _Ptr (reg rdstback),
        Jmp (lbl "strrev_loop") ]),
    ("strrev_end", [
        Mov _Ptr esp ebpv,
        Pop _Ptr ebp,
        Ret ])
    ]
    where
        rdst     = 0
        rdstback = 1
        rtemp    = 2

-- tostr(n: int, out: *char) -> uint
ptostr lbl = let
    offset_num = (sizeof _Ptr) + (sizeof _Int)
    offset_out = (sizeof _Ptr) + (sizeof _Int) + (sizeof _Int)
    offset_was_signed = neg $ (sizeof _Int)
    in [
    
    ("tostr", [
        Push _Ptr ebpv,
        Mov _Ptr ebp espv,

        Sub _Ptr esp espv (int $ sizeof _Int), -- was_signed: int
        Mov _Int (_ebp $ offset_was_signed) (int 0),

        Mov _Int (reg rnum) (_ebpv $ offset_num),
        Mov _Ptr (reg rdst) (_ebpv $ offset_out),
        Mov _Int (reg rlen) (int 0),

        Equal _Int (reg rtemp) (regv rnum) (int 0),
        Not _Int (reg rtemp) (regv rtemp),
        JmpIf (regv rtemp) (lbl "tostr_signed"),
        Mov _Char (_reg rdst) (int 48),
        Mov _Int (reg 0) (int 1),
        Ret ]),
    ("tostr_signed", [
        Less _Int Signed (reg rtemp) (regv rnum) (int 0),
        Not _Int (reg rtemp) (regv rtemp),
        JmpIf (regv rtemp) (lbl "tostr_loop"),
        Mul _Int Signed (reg rnum) (int (-1)) (regv rnum), 
        Mov _Int (_ebp $ offset_num) (regv rnum),
        Mov _Int (_ebp $ offset_was_signed) (int 1) ]),
    ("tostr_loop", [
        LessEqual _Int Unsigned (reg rtemp) (regv rnum) (int 0),
        JmpIf (regv rtemp) (lbl "tostr_end"),
        Mod _Int (reg rtemp) (regv rnum) (int 10),
        Add _Int (reg rtemp) (regv rtemp) (int 48),
        Mov _Char (_reg rdst) (regv rtemp),
        Div _Int Unsigned (reg rnum) (regv rnum) (int 10),
        Incr _Ptr (reg rdst),
        Incr _Int (reg rlen),
        Jmp (lbl "tostr_loop") ]),
    ("tostr_end", [
        Not _Int (reg rtemp) (_ebpv $ offset_was_signed),
        JmpIf (regv rtemp) (lbl "tostr_end2"),
        Mov _Char (_reg rdst) (int 45), -- '-'
        Incr _Int (reg rlen) ]),
    ("tostr_end2", [
        Push _Int (regv rlen),

        Push _Int (regv rlen),
        Mov _Ptr (reg rdst) (_ebpv $ offset_out),
        Push _Ptr (regv rdst),
        Call (lbl "strrev"),
        Add _Ptr esp espv (int $ (sizeof _Ptr) + (sizeof _Int)), -- arg cleanup

        Pop _Int (reg rlen),
        Mov _Int (reg 0) (regv rlen),

        Mov _Ptr esp ebpv,
        Pop _Ptr ebp,
        Ret ])
    ]
    where
        rnum     = 0
        rlen     = 1
        rdst     = 2
        rtemp    = 3

-- arrsum(ptr: *int, len: uint) -> int
parrsum lbl = let
    offset_ptr = (sizeof _Ptr) + (sizeof _Int) 
    offset_len = (sizeof _Ptr) + (sizeof _Int) + (sizeof _Ptr)
    in [
    
    ("arrsum", [
        Push _Ptr ebpv,
        Mov _Ptr ebp espv,

        Mov _Ptr (reg rptr) (_ebpv $ offset_ptr),
        Mov _Int (reg rres) (int 0),
        Mov _Int (reg ri)   (int 0) ]),
    ("arrsum_loop", [
        Less _Int Unsigned (reg rtemp) (regv ri) (_ebpv $ offset_len),
        Not _Int (reg rtemp) (regv rtemp),
        -- JmpIf (regv rtemp) (lbl "undefined"),
        JmpIf (regv rtemp) (lbl "arrsum_end"),
        Add _Int (reg rres) (regv rres) (_regv rptr),
        Incr _Int (reg ri),
        Add _Ptr (reg rptr) (regv rptr) (int $ sizeof _Int),
        Jmp (lbl "arrsum_loop") ]),
    ("arrsum_end", [
        Mov _Int (reg 0) (regv rres),

        Mov _Ptr esp ebpv,
        Pop _Ptr ebp,
        Ret ])
    ]
     where
        rptr  = 0
        rres  = 1
        ri    = 2
        rtemp = 3



main = resolveAndrun p0

resolveAndrun prog = do
    -- forM_ (W64 <$> [0..16] ++ [255] ++ [256, 512, 1024, maxBound]) $ \x@(W64 xv) -> do
    --     let Just x'@(W64 x'v) = wordValFromBytes . wordValToBytes $ x
    --     putStrLn $ (show x) ++ " " ++ (show x') ++ " " ++ (if xv == x'v then "OK" else "FAILED") 

    -- let DDef funId args body = defAdd1 in
    --     print $ evalCompile $ compileDef funId args body
    case resolveLabels prog of
        Left msg -> putStrLn $ "Compilation error: " ++ msg
        Right prog -> run prog

run :: [Op] -> IO ()
run prog = do
    printCode prog
    blank
    blank
    let vm = execProgram prog
    forM_ (iterVM vm) $
        either putStrLn (\x -> putStrLn (prettyShowVM x) >> blank)
    where
        blank = putStrLn ""
        printCode = mapM putStrLn . map (uncurry showLine) . zip [0..]
        showLine n c = show n ++ "\t" ++ show c

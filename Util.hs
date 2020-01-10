{-# LANGUAGE DeriveFunctor #-}

module Util where

import Data.List (nub, intersperse)
import Debug.Trace (trace)
import System.IO.Unsafe (unsafePerformIO)

import Data.Bifunctor

import Data.Void
import Control.Monad (ap)



debugIO :: (a -> IO b) -> a -> a
debugIO f a = (unsafePerformIO $ f a) `seq` a
{-# NOINLINE debugIO #-}

a +=+ b = a ++ " = " ++ b
a +|+ b = a ++ " " ++ b

separate sep s1 s2 = s1' ++ sep ++ s2'
    where
        s1' = if null s1 then s1 else s1 ++ " "
        s2' = if null s2 then s2 else " " ++ s2

joinWith sep = joinWith' sep . map show
joinWith' sep = concat . intersperse sep

indent = ("  "++)
indent' = unlines . map indent . lines

parens s = "(" ++ s ++ ")"
braces s = "{" ++ s ++ "}"
brackets s = "[" ++ s ++ "]"

(!?) :: [a] -> Int -> Maybe a
xs !? i 
    | (i >= 0) && (i < length xs) = Just $ xs !! i
    | otherwise = Nothing 

snoc xs x = xs ++ [x]
isUnique xs = (length xs) == (length $ nub xs)


trace' s x = trace (s ++ " " ++ (show x)) x 

intToBool :: Int -> Bool
intToBool = (/= 0)
boolToInt :: Bool -> Int
boolToInt x = if x then 1 else 0 

setAt :: Int -> a -> [a] -> [a]
setAt i x =  map (\(j,y) -> if j==i then x else y) . zip [0..]

data Running e r f a
    = Error e
    | Stop r
    | Next a
    | Request (f (Running e r f a))
    deriving Functor

instance (Functor f) => Applicative (Running e r f) where
    pure = Next
    (<*>) = ap
    -- (Next f) <*> (Next a)     = Next $ f a
    -- (Next f)     <*> (Request ra) = Request $ fmap (fmap f) ra
    -- (Request rf) <*> (Next a)     = Request $ fmap (fmap ($ a)) rf
    -- (Request rf) <*> (Request ra) = Request $ rf <*> ra
        -- rf :: VMR (Running e r VMR (a -> b))
        -- ra :: VMR (Running e r VMR a)
    -- (Error e) <*> _ = Error e
    -- (Stop r) <*> _ = Stop r

instance (Functor f) => Monad (Running e r f) where
    return = pure
    (Next a) >>= k = k a
    (Request ra) >>= k = Request $ fmap (>>= k) ra
        -- ra :: VMR a
        -- k  :: a -> Request e r VMR b
    (Error e) >>= _ = Error e
    (Stop r)  >>= _ = Stop r


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

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}

import Data.Functor.Const
import Data.Functor.Identity

type Lens' s a = forall f. Functor f => (a -> f a) -> (s -> f s)


get :: Lens' s a -> s -> a
get l s = getConst $ l Const s

put :: Lens' s a -> a -> s -> s
put l a s = runIdentity $ l (Identity . const a) s

over :: Lens' s a -> (a -> a) -> s -> s
over l f s = put l (f $ get l s) s

-- ((x -> f x) -> (s -> f s)) ->
-- ((a -> f a) -> (x -> f x)) ->
-- ((a -> f a) -> (s -> f s))


(.>) :: Lens' s x -> Lens' x a -> Lens' s a
(.>) = (.)




class (Functor f) => Costrong f where
    costrength :: f (Either a b) -> Either a (f b)

instance (Functor f, Traversable f) => Costrong f where
    costrength = sequenceA

class (Functor f) => Pointed f where
    point :: a -> f a

instance (Functor f, Applicative f) => Pointed f where
    point = pure



type Prism' s a = forall g f. (Costrong g, Pointed f) => (g a -> f a) -> (g s -> f s)


preview :: Prism' s a -> s -> Either s a
preview p s = flipE . costrength . getConst $ p (Const . runIdentity) $ (Identity s)
    -- g ~ Identity _
    -- f ~ Const (Either a x) _

review :: Prism' s a -> a -> s
review = undefined

data Zap = One Int | Two String
    deriving (Eq, Show)

(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) = flip (<$>)

flipE (Left a) = Right a
flipE (Right b) = Left b

_One :: Prism' Zap Int
_One f = undefined
_One f = \gs -> costrength gs 
    where
        match (One i) = (Right i)
        match x       = (Left x)
_Two :: Prism' Zap String
_Two f = undefined


-- preview _One (One i) === Right i 
-- preview _One (Two s) === Left (Two s)  
-- preview _Two (One i) === Left (One i)  
-- preview _Two (Two s) === Right s
-- review _One === One
-- review _Two === Two



data Foo = Foo {_a :: Int, _b :: String}
    deriving (Eq, Show)

a :: Lens' Foo Int
a f = \s -> (\_a' -> s {_a = _a'}) <$> f (_a s)

b :: Lens' Foo String
b f = \s -> (\_b' -> s {_b = _b'}) <$> f (_b s)

data Bar = Bar {_foo :: Foo}
    deriving (Eq, Show)

foo :: Lens' Bar Foo
foo f = \s -> (\_foo' -> s {_foo = _foo'}) <$> f (_foo s)

main = print $ over (foo . a) (+2) $ Bar (Foo 3 "abc")
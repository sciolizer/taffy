{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
module Appl where

import Control.Applicative
import Control.Monad.RWS
import Data.IORef
import Data.Unique

data Abstract
data Instance

group :: New Abstract c a -> Init c (New Instance c a)
group = undefined

make :: New Instance c a -> Init c a
make = undefined

data Var c a
data UntypedInstanceVar c
data Constraint l c

class Level l where
  newVar :: [a] -> New l c (Var c a)
  newConstraint :: ReadAssign l c Bool -> New l c ()
  readVar :: Var c a -> ReadAssign l c [a]
  writeVar :: Var c a -> [a] -> ReadAssign l c ()

instance Level Instance where

instance Level Abstract where

-- probably new should not be a pair: instead of the
-- instance case being built up separately, it should be the
-- OUTPUT of the first being run
type AbstractInner c = RWST (IORef Int) [Constraint Abstract c] () IO
type InstanceInner c = RWST NewContext ([UntypedInstanceVar c], [Constraint Instance c]) () IO
data New l c a where
  NewAbstract
    :: AbstractInner c (a, New Instance c a)
    -> New Abstract c a
  NewInstance
    :: InstanceInner c a
    -> New Instance c a

data NewContext = NewContext {
  instantiation :: Maybe Instantiation,
  counter :: IORef Int }

newtype Instantiation = Instantiation { unInstantiation :: Unique }

instance Functor (New Instance c)
instance Applicative (New Instance c)
instance Monad (New Instance c)

instance Functor (New Abstract c) where
  fmap f (NewAbstract m) = NewAbstract (fmap g m) where
    g (x, y) = (f x, fmap f y)
instance Applicative (New Abstract c) where
  pure x = NewAbstract (pure (x, pure x))
  (NewAbstract f) <*> (NewAbstract x) = NewAbstract (q f x) -- where
    {-
    f' :: AbstractInner c ((a, New Instance c a) -> (b, New Instance c b))
    f' = pure g
    g :: (a, New Instance c a) -> (b, New Instance c b)
    g (a, b) = (f <*> a, undefined)
    -}
    -- x' :: AbstractInner c (a, New Instance c a)
    -- x' = x
q
  :: AbstractInner c (a -> b, New Instance c (a -> b))
  -> AbstractInner c (a, New Instance c a)
  -> AbstractInner c (b, New Instance c b)
q f x = (,) <$> g1 f (h1 x) <*> g2 f (h2 x)

g1
  :: AbstractInner c (a -> b, New Instance c (a -> b))
  -> AbstractInner c a
  -> AbstractInner c b
g1 f x = q <*> x where
  q = fst <$> f

h1 :: AbstractInner c (a, New Instance c a) -> AbstractInner c a
h1 = (fst <$>)

g2
  :: AbstractInner c (a -> b, New Instance c (a -> b))
  -> AbstractInner c (New Instance c a)
  -> AbstractInner c (New Instance c b)
g2 f x = something q x where
  q = snd <$> f

something
  :: AbstractInner c (New Instance c (a -> b))
  -> AbstractInner c (New Instance c a)
  -> AbstractInner c (New Instance c b)
something f x = generic f x

generic
  :: (Applicative f, Applicative g)
  => f (g (a -> b))
  -> f (g a)
  -> f (g b)
generic f x = qeh f <*> x

qeh :: (Applicative f, Applicative g) => f (g (a -> b)) -> f (g a -> g b)
qeh = fmap quux

quux :: (Applicative g) => g (a -> b) -> g a -> g b
quux = (<*>)

{-
quux
  :: (Applicative f, Applicative g)
  => f (g (a -> b))
  -> (g (a -> b) -> f (g a -> g b))
  -> f (g a -> g b)
quux = undefined

bar
  :: (Applicative g)
  => g (a -> b) -> g a -> g b
bar = (<*>)
-}
{-
s2 :: AbstractInner c (New Instance c (a -> b))
   -> AbstractInner c (New Instance c a -> New Instance c b)
s2 f = (s3 f <*>)

s3 :: AbstractInner c (New Instance c (a -> b))
   -> New Instance c (a -> b)
s3 = undefined
-}

h2 :: AbstractInner c (a, New Instance c a) -> AbstractInner c (New Instance c a)
h2 = (snd <$>)


{-
f'
  :: AbstractInner c (a -> b, New Instance c (a -> b))
  -> AbstractInner c ((a, New Instance c a) -> (b, New Instance c b))
f' f = pure (g f)

g :: AbstractInner c (a -> b, New Instance c (a -> b))
  -> (a, New Instance c a) -> (b, New Instance c b)
g = undefined
-}

{-
instance Monad (New Abstract c) where
  return x = NewAbstract (return (x, return x))
  (NewAbstract x) >>= f = foo x f

foo :: AbstractInner c (a, New Instance c a)
    -> (a -> New Abstract c b)
    -> New Abstract c b
foo x f = NewAbstract (x >>= g f)

-- f :: a -> New Abstract c b
-- x :: AbstractInner c (a, New Instance c a)
-- x >>= q -> q :: (a, New Instance c a)
g :: (a -> New Abstract c b)
  -> (a, New Instance c a) -> AbstractInner c (b, New Instance c b)
g f (y, z) = unwrap1 (f y) {- do
  (q,s) <- unwrap1 (f y)
  r <- unwrap2 f s z
  return (q, r)
  -}
  -- how is it ok to drop the z?

unwrap1 :: New Abstract c b -> AbstractInner c (b, New Instance c b)
unwrap1 (NewAbstract q) = q

unwrap2
  :: (a -> New Abstract c b) -- produces b and New Instance c b
  -> New Instance c b
  -> New Instance c a
  -> AbstractInner c (New Instance c b)
unwrap2 = undefined
-}

data ReadAssign l c a
instance Functor (ReadAssign Abstract c)
instance Applicative (ReadAssign Abstract c)
instance Monad (ReadAssign Abstract c)
instance Functor (ReadAssign Instance c)
instance Applicative (ReadAssign Instance c)
instance Monad (ReadAssign Instance c)

data Init c a
instance Functor (Init c)
instance Applicative (Init c)
instance Monad (Init c)

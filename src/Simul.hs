{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
module Simul where

import Control.Applicative
import Control.Monad.Writer

{-
data Simul t a = Simul a (t a)

instance (Applicative t) => Monad (Simul t) where
  return x = Simul x (pure x)
  x >>= f = go x f

go :: (Applicative t) => Simul t a -> (a -> Simul t b) -> Simul t b
go (Simul x y) = undefined

simul_
  :: (Applicative t)
  => a
  -> t a
  -> Simul t a
simul_ = undefined

simul
  :: (Applicative t)
  => (a -> Simul t a)
  -> t a
  -> Simul t a
simul = undefined
-}

data Abstract
data Instance
data Var l c a where
  InstanceVar :: Int -> Maybe (Var Abstract c a) -> Var Instance c a
  AbstractVar :: Int -> Var Abstract c a

data Constraint c = Constraint c
type Thing l c a = Either (New l c a) (Constraint c)
type Inner l c a = WriterT [Thing l c a] IO a
data New l c a where
  Abstract :: Inner Abstract c a -> New Instance c a -> New Abstract c a
  Instance :: Inner Instance c a -> New Instance c a

newAbstractConstraint :: c -> New Abstract c ()
newAbstractConstraint c = undefined 

newAbstractVar :: Int -> New Abstract c (Var Abstract c a)
newAbstractVar = undefined

newInstanceConstraint :: Int -> New Instance c ()
newInstanceConstraint = undefined

newInstanceVar :: Int -> New Instance c (Var Instance c a)
newInstanceVar = undefined

instance Monad (New Abstract c)
instance Monad (New Instance c)

runNewAbstract
  :: New Abstract c a
  -> IO (a, New Instance c a, [Var Abstract c a], [Constraint c])
runNewAbstract = undefined

runNewInstance :: New Instance c a -> IO (a, [Var Instance c a], [Constraint c])
runNewInstance = undefined

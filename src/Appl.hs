{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
module Appl where

import Control.Applicative
import Control.Exception
import Control.Monad.IO.Class
import Control.Monad.RWS
import Data.IORef
import Data.Unique

data Abstract
data Instance

group :: New Abstract c a -> Init c (New Instance c a)
group m = do
  ref <- Init ask
  (_, ret, cs) <- liftIO $ runNewAbstract m ref

make :: New Instance c a -> Init c a
make = undefined

newtype AbstractVarId = AbstractVarId { unAbstractVarId :: Unique }
data Var c a where
  AbstractVar :: [a] -> AbstractVarId -> Var c a
  InstanceVar :: [a] -> Unique -> Maybe (Instantiation, AbstractVarId) {- parent abstract var -} -> Var c a

data UntypedInstanceVar c
data Constraint l c = Constraint Unique

class (Applicative m) => ApplicativeIO m where
  applicativeIO :: IO a -> m a

class Level l where
  newVar :: [a] -> New l c (Var c a)
  newConstraint :: ReadAssign l c Bool -> New l c ()
  -- readVar :: Var c a -> ReadAssign l c [a]
  -- writeVar :: Var c a -> [a] -> ReadAssign l c ()

instance Level Instance where

instance Level Abstract where
  newVar vals = NewAbstract ret where
    ret = do
      u <- AbstractVarId <$> liftIO newUnique
      let av = AbstractVar vals u
      let iv = do
            u' <- liftIO $ newUnique
            mbInst <- NewInstance (asks instantiation)
            i <- case mbInst of
                   Nothing -> liftIO . throwIO . userError . internalBug $ "patterned instance var created, but no instantiation in context"
                   Just i -> return i
            return (InstanceVar vals u' (Just (i, u)))
      return (av, iv)
  newConstraint ra = NewAbstract $ do
    u <- liftIO newUnique
    tell [Constraint u]
    return ((), return ())

internalBug = error

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
instance MonadIO (New Instance c)

instance Functor (New Abstract c) where
  fmap f (NewAbstract m) = NewAbstract (fmap g m) where
    g (x, y) = (f x, fmap f y)
instance Applicative (New Abstract c) where
  pure x = NewAbstract (pure (x, pure x))
  (NewAbstract f) <*> (NewAbstract x) = NewAbstract pair where
    pair = (,) <$> (fst <$> f <*> (fst <$> x)) <*> starstar (snd <$> f) (snd <$> x)
instance ApplicativeIO (New Abstract c) where
  applicativeIO m = NewAbstract ((,) <$> liftIO m <*> return (liftIO m))

starstar
  :: (Applicative f, Applicative g)
  => f (g (a -> b))
  -> f (g a)
  -> f (g b)
starstar f x = fmap (<*>) f <*> x

data ReadAssign l c a
instance Functor (ReadAssign Abstract c)
instance Applicative (ReadAssign Abstract c)
instance Monad (ReadAssign Abstract c)
instance Functor (ReadAssign Instance c)
instance Applicative (ReadAssign Instance c)
instance Monad (ReadAssign Instance c)

newtype Init c a = Init (RWST (IORef Int) [Constraint Abstract c] () (New Instance c) a)
  deriving (Applicative, Functor, Monad, MonadIO)
{-
instance Functor (Init c)
instance Applicative (Init c)
instance Monad (Init c)
-}

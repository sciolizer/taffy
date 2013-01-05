{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
module Simul where

import Control.Applicative
import Control.Monad.Writer
import Data.Unique

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
data Var c a = AbstractVar Unique | InstanceVar Unique (Maybe Unique)
data UntypedVar l c
data Constraint c = Constraint c
type Thing c = Either (UntypedVar Instance c) (Constraint c)
type Inner c a = WriterT [Thing c] IO a
data New l c a where
  Abstract :: Inner c a -> (a -> New Instance c a) -> New Abstract c a
  Instance :: Inner c a -> New Instance c a

unInstance :: New Instance c a -> Inner c a
unInstance (Instance x) = x

newAbstractConstraint :: c -> New Abstract c ()
newAbstractConstraint c = Abstract (tell [Right . Constraint $ c]) (\_ -> return ())

newAbstractVar :: New Abstract c (Var c a)
newAbstractVar = Abstract a i where
  a = do
    u <- liftIO newUnique
    let var = AbstractVar u
    -- tell [Left (untypeAbstract var)] -- don't care
    return var
  i a = do
    u <- liftIO newUnique
    let var = case a of
                AbstractVar u' -> InstanceVar u (Just u')
                InstanceVar _ _ -> error "internal bug"
    Instance $ tell [Left (untypeInstance var)]
    return var

untypeAbstract :: Var c a -> UntypedVar Abstract c
untypeAbstract = undefined

untypeInstance :: Var c a -> UntypedVar Instance c
untypeInstance = undefined

newInstanceConstraint :: c -> New Instance c ()
newInstanceConstraint = Instance . tell . (:[]) . Right . Constraint

newInstanceVar :: New Instance c (Var c a)
newInstanceVar = Instance $ do
  u <- liftIO newUnique
  let ret = InstanceVar u Nothing
  tell [Left (untypeInstance ret)]
  return ret

instance Monad (New Abstract c) where
  return x = Abstract (return x) (\_ -> return x)
  (Abstract x y) >>= f = Abstract q delayed where
    q = innerFst . f =<< x
    innerFst (Abstract z _) = z
    delayed b = do
      a <- y =<< Instance x
      case f a of
        Abstract _ g -> g b
instance MonadIO (New Abstract c)

instance Monad (New Instance c) where
  return x = Instance (return x)
  (Instance x) >>= f = Instance (unInstance . f =<< x)
instance MonadIO (New Instance c) where
  liftIO = Instance . liftIO

runNewAbstract
  :: New Abstract c a
  -> IO (a, New Instance c a, [Thing c])
runNewAbstract (Abstract fst snd) = do
  (a, things) <- runWriterT fst
  return (a, snd a, things)

runNewInstance :: New Instance c a -> IO (a, [Thing c])
runNewInstance (Instance m) = runWriterT m

-- the Thing type can be extended to track both instance constraints
-- and abstract constraints. Also abstract vars
-- in case that ever becomes necessary

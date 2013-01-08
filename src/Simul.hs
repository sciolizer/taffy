{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
module Simul where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.Writer
import Data.IORef
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
data Var c a = AbstractVar Unique | InstanceVar Unique (Maybe Instantiation)
newtype Instantiation = Instantiation { unInstantiation :: Unique }
  deriving (Eq, Ord)
data UntypedVar l c
data Constraint l c = Constraint c
type NewInstance c = RWST NewContext ([UntypedInstanceVar c], [Constraint Instance c]) () IO
data New l c a where
  Abstract
    :: RWST (IORef Int) [Constraint Abstract c] () IO a
    -> ReaderT Something (NewInstance c) a
    -> New Abstract c a
  Instance :: NewInstance c a -> New Instance c a

data NewContext = NewContext {
  _newContextInstantiation :: Maybe Instantiation,
  _newContextNext :: IORef Int }

data Something
data UntypedInstanceVar c

unInstance :: New Instance c a -> NewInstance c a
unInstance (Instance x) = x

newAbstractConstraint :: c -> New Abstract c ()
newAbstractConstraint c = undefined -- Abstract (tell [Right . Constraint $ c]) (\_ -> return ())

newAbstractVar :: New Abstract c (Var c a)
newAbstractVar = Abstract a i where
  a = do
    u <- liftIO newUnique
    let var = AbstractVar u
    -- tell [Left (untypeAbstract var)] -- don't care
    return var
  i = undefined {- do
    u <- liftIO newUnique
    let var = case a of
                AbstractVar u' -> InstanceVar u (Just u')
                InstanceVar _ _ -> error "internal bug"
    undefined -- Instance $ tell [Left (untypeInstance var)]
    return var
    -}

untypeAbstract :: Var c a -> UntypedVar Abstract c
untypeAbstract = undefined

untypeInstance :: Var c a -> UntypedVar Instance c
untypeInstance = undefined

newInstanceConstraint :: c -> New Instance c ()
newInstanceConstraint = undefined -- Instance . tell . (:[]) . Right . Constraint

newInstanceVar :: New Instance c (Var c a)
newInstanceVar = Instance $ do
  u <- liftIO newUnique
  let ret = InstanceVar u Nothing
  undefined -- tell [Left (untypeInstance ret)]
  return ret

instance Monad (New Abstract c) where
  return x = Abstract (return x) (return x)
  (Abstract x y) >>= f = Abstract first (second x y f) where 
    first = innerFst . f =<< x
    innerFst (Abstract z _) = z
  
  {- Abstract fst snd where
    fst = innerFst . f =<< x
    innerFst (Abstract z _) = z
    snd b = ($ b) . innerSnd . f =<< y =<< Instance x
    innerSnd (Abstract _ z) = z
    -}
second
  :: RWST (IORef Int) [Constraint Abstract c] () IO a
  -> ReaderT Something (NewInstance c) a
  -> (a -> New Abstract c b) -- contains hidden b -> ReaderT ... b and RWST...b
  -> ReaderT Something (NewInstance c) b
second x y f = undefined

instance MonadIO (New Abstract c)

instance Monad (New Instance c) where
  return x = Instance (return x)
  (Instance x) >>= f = Instance (unInstance . f =<< x)
instance MonadIO (New Instance c) where
  liftIO = Instance . liftIO

runNewAbstract
  :: New Abstract c a
  -> IO (a, New Instance c a, [Constraint Abstract c])
runNewAbstract (Abstract fst snd) = undefined {- do
  (a, things) <- runWriterT fst
  return (a, snd a, things)
  -}

runNewInstance :: New Instance c a -> IO (a, [UntypedInstanceVar c], [Constraint Instance c])
runNewInstance (Instance m) = undefined -- runWriterT m

-- the Thing type can be extended to track both instance constraints
-- and abstract constraints. Also abstract vars
-- in case that ever becomes necessary

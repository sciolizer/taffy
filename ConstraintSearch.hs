{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
module ConstraintSearch where

import Control.Monad
import Control.Monad.Trans.Class

-- data Constrained var a
data WithQueue var (m :: * -> *) a

-- instance Monad (Constrained Int)
instance (Monad m) => Monad (WithQueue var m)
instance MonadTrans (WithQueue var)

ac3 :: (Eq var, Monad m) => CSP m var -> m Bool {- false if an inconsistency found, true otherwise -}
ac3 csp = do
  arcs <- getArcs csp
  runWithQueue propagate arcs where
    propagate = do
      q <- popQueue
      case q of
        Nothing -> return True
        Just (i,j) -> do
          b <- lift $ revise csp i j
          if not b then propagate else do
          c <- lift $ domainNull csp i
          if c then return False else do
          ns <- lift $ neighbors csp i
          forM_ ns $ \k -> do
            when (k /= j) $ appendQueue (k, i)
          propagate

data CSP m var = CSP {
  vars :: m [var], -- this would be an infinite list if we were working with predicate traces
  neighbors :: var -> m [var],
  revise :: var -> var -> m Bool,
  domainNull :: var -> m Bool
  }

getArcs :: CSP m var -> m [(var,var)]
getArcs = undefined -- can be written in terms of neighbors and vars

popQueue :: WithQueue var m (Maybe (var,var))
popQueue = undefined

appendQueue :: (var, var) -> WithQueue var m ()
appendQueue = undefined

runWithQueue :: WithQueue var m a -> [(var,var)] -> m a
runWithQueue = undefined

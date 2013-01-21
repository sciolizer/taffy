{-# LANGUAGE FlexibleInstances #-}
module SatExample where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Data.Function
import Data.List
import qualified Data.Map as M
import qualified Data.Set as S

import Solver

main = do
  -- todo: change learner to resolve disjunctions, e.g.
  -- x \/ y and ~y \/ z => x \/ z
  let learner = const nop
  (success, ()) <- solve learner definition (\(a,b,c) -> mapM_ showVar [a,b,c])
  print success where
    -- showVar :: Var Disjunction Bool -> IO ()
    showVar v = liftIO . print =<< readVar v

data Disjunction = Disjunction {
  unDisjunction :: [((Bool -> Bool) {- not or id -}, Var Disjunction Bool)] }

instance Eq Disjunction where (==) = (==) `on` map snd . unDisjunction
instance Ord Disjunction where compare = compare `on` map snd . unDisjunction
instance Show Disjunction where
  show (Disjunction parts) = intercalate " \\/ " (map showPart parts) where
    showPart (f, ivar) = prefix f ++ show ivar
    prefix f = if f True then "" else "not "

instance (Show v) => Show (Var Disjunction v) where show = varName

-- problem: not a \/ b \/ c
--          a \/ not b
--          a \/ c

definition = do
  -- Since a sat solver does not need to generate new variables or constraints
  -- during the search process, true and false assignments are just nops.
  let binary = (M.fromList [(True,const nop),(False,const nop)])
  make $ do
    a <- newVar (Just "a") binary
    b <- newVar (Just "b") binary
    c <- newVar (Just "c") binary
    mkDisjunction [(not,a),(id,b),(id,c)]
    mkDisjunction [(id,a),(not,b)]
    mkDisjunction [(id,a),(id,c)]
    return (a, b, c)

mkDisjunction parts = do
  let cl = Disjunction parts
  newConstraint
    (Just (show cl))
    cl
    (resolve cl)

-- | Return true iff at least one of the variables still
-- has True as a candidate value. If all but one of the literals
-- are False, the remaining literal is set to True.
-- resolve :: Disjunction -> Assign Disjunction Bool
resolve (Disjunction parts) = z where
  z = do
    trueLiterals <- filterM isPossiblyTrue parts
    case trueLiterals of
      [] -> return False
      [(flag,var)] -> do
        setVar var (flag True) -- unit literal optimization from DPLL
        return True
      _ -> return True
  isPossiblyTrue (flip,var) = any flip . S.toList <$> readVar var

nop = return ()

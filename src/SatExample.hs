{-# LANGUAGE FlexibleInstances #-}
module SatExample where

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
  (success, (a, b, c)) <- solve learner definition
  print success
  mapM_ showVar [a,b,c] where
    showVar :: Ivar Disjunction Bool -> IO ()
    showVar v = print =<< readIvar v

data Disjunction = Disjunction {
  unDisjunction :: [((Bool -> Bool) {- not or id -}, Ivar Disjunction Bool)] }

instance Eq Disjunction where (==) = (==) `on` map snd . unDisjunction
instance Ord Disjunction where compare = compare `on` map snd . unDisjunction
instance Show Disjunction where
  show (Disjunction parts) = intercalate " \\/ " (map showPart parts) where
    showPart (f, ivar) = prefix f ++ show ivar
    prefix f = if f True then "" else "not "

instance (Show v) => Show (Ivar Disjunction v) where show = ivarName

-- problem: not a \/ b \/ c
--          not b \/ a
--          not c \/ a

definition = do
  -- Since a sat solver does not need to generate new variables or constraints
  -- during the search process, true and false assignments are just nops.
  binary <- newAvar (M.fromList [(True,const nop),(False,const nop)])
  liftNew $ do
    a <- newNamedIvar binary "a"
    b <- newNamedIvar binary "b"
    c <- newNamedIvar binary "c"
    mkDisjunction [(not,a),(id,b),(id,c)]
    mkDisjunction [(not,b),(id,a)]
    mkDisjunction [(not,c),(id,a)]
    return (a, b, c)

mkDisjunction parts = do
  let cl = Disjunction parts
  newNamedConstraint
    cl
    (S.fromList (map (ivar . snd) parts)) -- dependencies
    (resolve cl)
    (show cl)

-- | Return true iff at least one of the variables still
-- has True as a candidate value.
--
-- todo: add the unit literal optimization, by calling setIvar sometimes.
resolve :: Disjunction -> Assign Disjunction Bool
resolve (Disjunction parts) = liftIO $ do
  vals <- mapM isPos parts
  return (any id vals) where
    isPos (flip,var) = do
      candidates <- readIvar var
      return . any flip . S.toList $ candidates

nop = return ()

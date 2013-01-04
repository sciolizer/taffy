module Api where

import Data.Map
import qualified Data.Set as S

solve
  :: ([constraint] -> IO [constraint]) -- constraint learner
  -> New Abstract constraint a -- problem definition
  -> New Instance constraint a -- more of the problem definition
  -> (a -> ReadAssign Instance constraint b) -- answer reader
  -> IO (Bool, a)
solve = undefined

type Values constraint a = Map a (New Instance constraint ())

data Var l constraint a

class Level l where
  newVar :: Maybe String -> Values constraint a -> New l constraint (Var l constraint a)
  varName :: Var constraint l a -> String
  readVar :: Var l constraint a -> ReadAssign l constraint (S.Set a)
  setVar :: Var l constraint a -> a -> ReadAssign l constraint ()
  shrinkVar :: Var l constraint a -> a -> ReadAssign l constraint ()
  newConstraint
    :: constraint
    -> ReadAssign l constraint Bool
    -> New l constraint ()

data Abstract
instance Level Abstract

data Instance
instance Level Instance

instantiate :: New Abstract constraint a -> New Instance constraint a
instantiate = undefined

data New l constraint a -- monad
data ReadAssign l constraint a -- monad

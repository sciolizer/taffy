module Api where

import Data.Map
import qualified Data.Set as S

solve
  :: ([constraint] -> IO [constraint]) -- constraint learner
  -> Init constraint a -- problem definition
  -> (a -> ReadAssign Instance constraint b) -- answer reader
  -> IO (Bool, b)
solve = undefined

type Values constraint a = Map a (New Instance constraint ())

data Var constraint a

class Level l where
  newVar :: Maybe String -> Values constraint a -> New l constraint (Var constraint a)
  readVar :: Var constraint a -> ReadAssign l constraint (S.Set a)
  -- when you call set or shrink on an abstract var, you are
  -- actually doing it on a particular instance var (you just don't
  -- know which one).
  setVar :: Var constraint a -> a -> ReadAssign l constraint ()
  shrinkVar :: Var constraint a -> a -> ReadAssign l constraint ()
  newConstraint
    :: constraint
    -> ReadAssign l constraint Bool
    -> New l constraint ()

varName :: Var constraint a -> String
varName = undefined

data Abstract
instance Level Abstract

data Instance
instance Level Instance

instantiate :: Pattern constraint a -> New Instance constraint a
instantiate = undefined

group :: New Abstract constraint a -> Init constraint (Pattern constraint a)
group = undefined

make :: New Instance constraint a -> Init constraint a
make = undefined

data Init constraint a
data New l constraint a -- monad
data ReadAssign l constraint a -- monad
data Pattern constraint a -- not a monad

{-
newtype Tracker a = Tracker (IO a, IO a)

instance Monad Tracker where
  return x = Tracker (return x, return x)
  x >>= f = Tracker (x >>= f, x >>= f)

can also add a custom

differ :: IO a -> IO a -> Tracker a
differ = undefined

pretty sure I can't use any of the normal monads for this
Reader: r -> a
State: s -> (a, s)
Writer: (a, monoid)
  writer is a little bit similar, but it doesn't preserve the type, e.g.
  (a, monoid a)

see if I can make a monad transformer out of this.
Then I can layer it with the other uses of the monads.

data Simul t a = Simul (a, t a)

not sure which one:
instance Monad (Simul t)
or
instance Monad (Simul Foo)
how specific do I have to be?

data SimulT t m a = Simul (m a, t m a) -- note different kind
-- or is it (t m) a? Or is it 
-- actually I think the not transformer version is fine

-}

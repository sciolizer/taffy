module Api where

import Control.Monad
import Control.Monad.IO.Class
import Data.Monoid

data S clause a
instance Monad (S clause)
instance MonadIO (S clause)

data Init clause a
instance Monad (Init clause)
instance MonadIO (Init clause)

data Assign a
instance Monad Assign
instance MonadIO Assign

data Problem clause a = Problem {
  init :: Init clause a,
  collectable :: clause -> S clause Bool,
  resolve :: clause -> clause -> S clause (),
  implications :: clause -> Assign Bool {- false means clause has become unsatisfiable -}
  }

data Var
data IVar a
data AVar a

newClause :: clause -> [Var] -> S clause ()
newClause = undefined

newAVar :: [a] -> (a -> S clause ()) -> S clause (AVar a)
newAVar = undefined

avar :: AVar a -> Var
avar = undefined

newRequiredIVar :: AVar a -> Init clause (IVar a)
newRequiredIVar = undefined

liftS :: S clause a -> Init clause a
liftS = undefined

newIVar :: AVar a -> S clause (IVar a)
newIVar = undefined

ivar :: IVar a -> Var
ivar = undefined

readIVar :: IVar a -> IO (Maybe a)
readIVar = undefined

assigned :: Var -> IO Bool
assigned = undefined

setIVar :: IVar a -> a -> Assign ()
setIVar = undefined

solve :: Problem clause a -> IO (Bool, a)
solve p@(Problem i c r s) = do
  (ivars, ret) <- runInit i
  success <- assign (map Right ivars) p
  return (success, ret)

-- end public, begin private

runInit :: Init clause a -> IO ([Var], a)
runInit = undefined

data Clause

unassign :: Var -> IO ()
unassign = undefined

anyValue :: Var -> IO Bool -> IO Bool
anyValue = undefined

constraining :: Var -> IO [Clause]
constraining = undefined

genImplications :: Clause -> IO (Maybe [(IO (), IO ())])
genImplications = undefined

foldThing :: (a -> IO (Maybe [b])) -> [a] -> IO (Maybe [b])
foldThing = undefined

assign :: [Either (IO (), IO ()) Var] -> Problem clause a -> IO Bool
assign [] _ = return True
assign (Right v : vs) p = do
  set <- assigned v
  if set then assign vs p else do
  ret <- anyValue v $ do
    clauses <- constraining v
    implications <- foldThing genImplications clauses
    case implications of
      Nothing -> return False -- one of the constraints was violated
      Just xs -> assign (map Left xs ++ vs) p
  if ret then return True else do
  unassign v
  return False

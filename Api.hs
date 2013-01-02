{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
module Api (
  S(),
  Init(),
  Assign(),

  Var(),
  IVar(),
  AVar(),

  newClause,
  newAVar,
  avar,
  liftS,
  newIVar,
  ivar,
  readIVar,
  setIVar,
  shrinkIVar,
  solve
) where

import Control.Applicative
import Control.Lens
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.RWS
import Control.Monad.Trans.Writer
import Data.Either
import Data.Function
import Data.IORef
import Data.List
import qualified Data.Map as M
import Data.Monoid
import Data.Set (Set(..))
import qualified Data.Set as S
import Data.Unique

type ClauseMaker clause = IO clause
type IVarMaker = IO UntypedIVar
newtype S clause a = S (WriterT [Either IVarMaker (ClauseMaker clause)] IO a)
  deriving (Monad, MonadIO)

type AVarMaker = IO () -- todo: is this actually necessary?
newtype Init clause a = Init (WriterT [AVarMaker] (S clause) a)
  deriving (Monad, MonadIO)

data Assign a
instance Monad Assign
instance MonadIO Assign

data Problem clause = Problem {
  collectable :: clause -> S clause Bool,
  resolve :: clause -> clause -> S clause (),
  revise :: clause -> Assign Bool {- false means clause has become unsatisfiable -}
  }

data Var = Var Meta
data IVar a = IVar {
  ivalues :: IORef (Set a),
  icandidates :: IORef (Set a),
  ivalue :: IORef (Maybe a),
  sideEffects :: forall clause. M.Map a (S clause ()),
  imeta :: Meta }
data AVar a = AVar { newIVar :: forall clause. S clause (IVar a), ameta :: Meta }
data Meta = Meta Unique

newClause :: clause -> [Var] -> S clause ()
newClause = undefined

newAVar :: (Ord a) => [(a, S clause ())] -> Init clause (AVar a)
newAVar = undefined

avar :: AVar a -> Var
avar = undefined

liftS :: S clause a -> Init clause a
liftS = undefined

ivar :: IVar a -> Var
ivar = undefined

readIVar :: IVar a -> IO [a]
readIVar = undefined

setIVar :: (Ord a) => IVar a -> a -> Assign ()
setIVar = undefined

shrinkIVar :: (Ord a) => IVar a -> a -> Assign ()
shrinkIVar = undefined

solve :: (Ord clause) => Problem clause -> Init clause a -> IO (Bool, a)
solve p i = do
  (ret, vars, clauses) <- runInit i
  completed <- runSolve backtrack vars clauses p
  case completed of
    Nothing -> return (True, ret)
    Just () -> return (False, ret)

-- end public, begin private

runSolve :: (Ord clause) => Solve clause a -> [UntypedIVar] -> [clause] -> Problem clause -> IO (Maybe a)
runSolve (Solve m) vs cs p = do
  (e, _, _) <- runRWST (runMaybeT m) p (SolveState (S.fromList vs) (S.fromList cs))
  return e

data SolveState clause = SolveState {
  _vars :: Set UntypedIVar,
  _clauses :: Set clause }

newtype Solve clause a = Solve (MaybeT (RWST (Problem clause) () (SolveState clause) IO) a)
  deriving (Applicative, Functor, Monad, MonadIO)

data UntypedIVar = UntypedIVar {
  identity :: Unique,
  numCandidates :: IO Int,
  unset :: IO (),
  everyValue :: forall m a. (MonadIO m) => m a -> m () }

instance Eq UntypedIVar where (==) = (==) `on` identity
instance Ord UntypedIVar where compare = compare `on` identity

untype :: (Ord a) => IVar a -> UntypedIVar
untype iv = UntypedIVar i nv us ev where
  (Meta i) = imeta iv
  nv = S.size <$> readIORef csRef
  us = writeIORef (ivalue iv) Nothing
  ev m = do
    orig <- liftIO $ readIORef vRef
    list <- liftIO $ readIORef csRef
    mapM_ (switchTo m) . S.toList $ list
    liftIO $ writeIORef csRef list
    liftIO $ writeIORef vRef orig
  switchTo m v = do
    liftIO $ writeIORef vRef (Just v)
    liftIO $ writeIORef csRef (S.singleton v)
    case M.lookup v (sideEffects iv) of
      Nothing -> internalBug "malconstructed ivar"
      Just effect -> liftIO $ do
        ((), ivms, cms) <- runS effect
        sequence_ ivms
        sequence_ cms
    m
  csRef = icandidates iv
  vRef = ivalue iv

internalBug = error

backtrack :: Solve clause ()
backtrack = do
  mbVar <- selectUnassignedVariable
  case mbVar of
    Nothing -> escape
    Just var -> do
      everyValue var $ do
        (continue, undo) <- reviseAll 
        when continue backtrack
        undo
      -- todo: stick clause learning somewhere in here
      liftIO $ unset var

escape :: Solve clause a
escape = Solve (fail "escape")

vars = Solve (lift $ gets _vars)
clauses = Solve (lift $ gets _clauses)

selectUnassignedVariable :: Solve clause (Maybe UntypedIVar)
selectUnassignedVariable = do
  vs <- vars
  sizes <- mapM (\v -> (,v) <$> liftIO (numCandidates v)) . S.toList $ vs
  case sort . filter (\(x,_) -> x > 1) $ sizes of
    [] -> return Nothing
    ((_,v):_) -> return (Just v)

reviseAll :: Solve clause (Bool, Solve clause ())
reviseAll = undefined

runInit :: Init clause a -> IO (a, [UntypedIVar], [clause])
runInit (Init m) = do
  ((ret, avars), ivars, cms) <- runS (runWriterT m)
  sequence_ avars
  ivars' <- sequence ivars
  cms' <- sequence cms
  return (ret, ivars', cms')

runS :: S clause a -> IO (a, [IVarMaker], [ClauseMaker clause])
runS (S m) = do
  (ret, mix) <- runWriterT m
  let (ims, cs) = partitionEithers mix
  return (ret, ims, cs)

data Clause

{-
unassign :: Var -> IO ()
unassign = undefined
-}

{-
constraining :: Var -> IO [Clause]
constraining = undefined

genImplications :: Clause -> IO (Maybe [(IO (), IO ())])
genImplications = undefined

foldThing :: (a -> IO (Maybe [b])) -> [a] -> IO (Maybe [b])
foldThing = undefined
-}

-- runS :: S clause a -> IO ([Clause], a)

{-
propagate vs p clauses = do
  (newClauses, implications) <- foldThing genImplications clauses
  case implications of
    Nothing -> return False
    Just xs -> do
      cs <- newClauses
      if (not . null $ cs)
        then propagate (map Left xs ++ vs) p cs
        else assign (map Left xs ++ vs) p

-- ergh... propagating constraints is not enough; if a constraint just
-- slightly limits the acceptable values for a variable, then we must
-- iterate over the acceptable values
assign :: [Either (IO [Clause], IO ()) RequiredVar] -> Problem clause a -> IO Bool
assign [] _ = return True
assign (Right v : vs) p = do -- non-deterministic assignment
  set <- assigned v
  if set then assign vs p else do
  ret <- anyValue v $ do
    clauses1 <- creations v
    clauses2 <- constraining v
    propagate vs p (clauses1 ++ clauses2)
  if ret then return True else do
  unassign v
  return False
assign (Left (set, unset) : vs) p = do -- deterministic assignment
  clauses <- set -- should give both the creations and the constraints
  ret <- propagate vs p clauses
  if ret then return True else do
  unset
  return False
  -}

-- makeLenses ''SolveState

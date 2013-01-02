{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
module Api (
  -- * Solving
  Problem(..),
  solve,

  -- * Variables
  Var(),

  -- ** Abstract variables
  AVar(),
  newAVar,
  avar,
  
  -- ** Instance variables
  IVar(),
  newIVar,
  ivar,
  readIVar,
  setIVar,
  shrinkIVar,

  -- * Clauses
  newClause,

  -- * Monads
  New(),
  Init(),
  liftNew,
  Assign(),
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

data Problem clause = Problem {
  collectable :: clause -> New Bool,
  resolve :: clause -> clause -> New (),
  revise :: clause -> Assign Bool {- false means clause has become unsatisfiable -}
  }

solve :: (Ord clause) => Problem clause -> Init a -> IO (Bool, a)
solve p i = do
  (ret, vars, clauses) <- runInit i
  completed <- runSolve backtrack vars (map snd clauses) p
  case completed of
    Nothing -> return (True, ret)
    Just () -> return (False, ret)

backtrack :: Solve clause ()
backtrack = do
  mbVar <- selectUnassignedVariable
  case mbVar of
    Nothing -> escape
    Just var -> do
      everyValue var $ \newvars newclauses -> do
        appendVars newvars
        appendClauses newclauses
        (continue, undo) <- reviseAll 
        when continue backtrack
        undo
      -- todo: stick clause learning somewhere in here
      liftIO $ unset var

selectUnassignedVariable :: Solve clause (Maybe UntypedIVar)
selectUnassignedVariable = do
  vs <- vars
  sizes <- mapM (\v -> (,v) <$> liftIO (numCandidates v)) . S.toList $ vs
  case sort . filter (\(x,_) -> x > 1) $ sizes of
    [] -> return Nothing
    ((_,v):_) -> return (Just v)

reviseAll :: Solve clause (Bool, Solve clause ())
reviseAll = undefined {- do
  cs <- clauses
  consume (return ()) cs where
    consume undo [] = return (True, undo)
    consume undo (x:xs) = do
      (continue, affectedVars, undo') <- runAssign $ revise x -- should run side effects
      -- todo: need to add clauses associated with affectedVars back into queue
      if continue then do
        sideEffects
        consume (undo >> undo') xs
      else return (False, undo)
      -}

data Var = Var Meta
  deriving (Eq, Ord)

data Meta = Meta Unique
  deriving (Eq, Ord)

data AVar a = AVar { newIVar :: New (IVar a), ameta :: Meta }

newAVar :: (Ord a) => [(a, New ())] -> Init (AVar a)
newAVar = undefined

avar :: AVar a -> Var
avar = Var . ameta

data IVar a = IVar {
  ivalues :: IORef (Set a),
  icandidates :: IORef (Set a),
  ivalue :: IORef (Maybe a),
  sideEffects :: forall clause. M.Map a (New ()),
  imeta :: Meta }

ivar :: IVar a -> Var
ivar = undefined

readIVar :: IVar a -> IO [a]
readIVar = undefined

setIVar :: (Ord a) => IVar a -> a -> Assign ()
setIVar = undefined

shrinkIVar :: (Ord a) => IVar a -> a -> Assign ()
shrinkIVar = undefined

data UntypedIVar = UntypedIVar {
  identity :: Unique,
  numCandidates :: IO Int,
  unset :: IO (),
  everyValue :: forall m a. (MonadIO m) => ([UntypedIVar] -> [Clause] -> m a) -> m () }

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
    (ivs, cls) <- case M.lookup v (sideEffects iv) of
      Nothing -> internalBug "malconstructed ivar"
      Just effect -> liftIO $ do
        ((), ivms, cms) <- runNew effect
        ivs <- sequence ivms
        cls <- map snd <$> sequence cms
        return (ivs, cls)
    m ivs cls
  csRef = icandidates iv
  vRef = ivalue iv

internalBug = error

newClause :: clause -> [Var] -> New ()
newClause = undefined

data Clause = Clause [Var]
  deriving (Eq, Ord)

newtype New a = New (WriterT [Either UntypedIVar Clause] IO a)
  deriving (Monad, MonadIO)

runNew :: New a -> IO (a, [IVarMaker], [Clause])
runNew (New m) = do
  (ret, mix) <- runWriterT m
  let (ims, cs) = partitionEithers mix
  return (ret, ims, cs)

newtype Init a = Init (WriterT [AVarMaker] New a)
  deriving (Monad, MonadIO)

runInit :: Init a -> IO (a, [UntypedIVar], [Clause])
runInit (Init m) = do
  ((ret, avars), ivars, cms) <- runNew (runWriterT m)
  sequence_ avars
  ivars' <- sequence ivars
  cms' <- sequence cms
  return (ret, ivars', cms')

liftNew :: New a -> Init a
liftNew = undefined

data Assign a
instance Monad Assign
instance MonadIO Assign

-- should run side effects
runAssign = undefined -- :: Assign a -> 

newtype Solve clause a = Solve (MaybeT (RWST (Problem clause) () SolveState IO) a)
  deriving (Applicative, Functor, Monad, MonadIO)

data SolveState = SolveState {
  _vars :: Set UntypedIVar,
  _clauses :: Set Clause }

runSolve :: (Ord clause) => Solve clause a -> [UntypedIVar] -> [Clause] -> Problem clause -> IO (Maybe a)
runSolve (Solve m) vs cs p = do
  (e, _, _) <- runRWST (runMaybeT m) p (SolveState (S.fromList vs) (S.fromList cs))
  return e

escape :: Solve clause a
escape = Solve (fail "escape")

-- todo: get rid of these functions
vars = Solve (lift $ gets _vars)
clauses = Solve (lift $ gets _clauses)

-- todo: get rid of these functions; use lens, and inline
appendVars vs = Solve (lift $ modify (\(SolveState v x) -> SolveState (S.union (S.fromList vs) v) x))
appendClauses cs = Solve (lift $ modify (\(SolveState v x) -> SolveState v (S.union (S.fromList cs) x)))
----

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

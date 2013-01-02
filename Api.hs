{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
module Api (
  -- * Solving
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
import Control.Monad.RWS
import Control.Monad.Trans
import Control.Monad.Writer
{-
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.RWS
import Control.Monad.Trans.Writer
-}
import Data.Either
import Data.Function
import Data.IORef
import Data.List
import qualified Data.Map as M
import Data.Monoid
import Data.Set (Set(..))
import qualified Data.Set as S
import Data.Unique

data Var c = Var {
  varIdentity :: Unique,

  -- ^ A partial set of clauses constraining this var. Clauses not in this set
  -- but which constrain this var do not need to be revised when this var
  -- is assigned.
  -- For example, if the clause is a \/ b \/ c, then I should put the
  -- clause in two of the vars, but I do not need to put it in the
  -- third, since I can only make a deduction when there is one
  -- remaining unassigned variable.
  varClauses :: IORef (S.Set (Clause c)) }

instance Eq (Var c) where (==) = (==) `on` varIdentity
instance Ord (Var c) where compare = compare `on` varIdentity

data AVar c a = AVar {
  avarValues :: M.Map a (New c ()),
  avarVar :: (Var c) }

data IVar c a = IVar {
  ivarAvar :: AVar c a,
  ivarState :: IORef (IVarState c a) }

data IVarState c a = IVarState {
  -- ^ If empty, problem is in conflict.
  -- If singleton, then a value has been chosen.
  -- If more than one item, a choice has yet to be made.
  _ivarCandidates :: (Set a),

  -- ^ Everytime ivarCandidates is reduced to a singleton, that value is
  -- added here. If it already exist in here, then the associated (New ())
  -- in the AVar is not executed, since we know it has already been executed
  -- once. If a clause using this ivar is garbage collected, then the
  -- value is removed from here, so that future re-assignments will
  -- re-instantiate the clause.
  _ivarPreviousAssignments :: M.Map a (S.Set (Clause c)) }

data UntypedIvar = UntypedIvar {
  uivarIdentity :: Unique,
  uivarCandidates :: IO Int,

  -- ^ A sequence of calls to setIVar for each remaining candidate.
  everyValue :: IO [Reversable ()] }

instance Eq UntypedIvar where (==) = (==) `on` uivarIdentity
instance Ord UntypedIvar where compare = compare `on` uivarIdentity

data Clause c = Clause {
  clauseClause :: c,
  clauseVars :: S.Set (Var c),
  clauseCollectable :: IO Bool,
  clauseResolve :: Assign c Bool,
  clauseWatched :: IORef (S.Set (Var c))
  }

clauseIdentity :: Clause c -> (c, S.Set (Var c))
clauseIdentity c = (clauseClause c, clauseVars c)

instance (Eq c) => Eq (Clause c) where (==) = (==) `on` clauseIdentity
instance (Ord c) => Ord (Clause c) where compare = compare `on` clauseIdentity

newtype New c a = New (WriterT [Either UntypedIvar (Clause c)] IO a)
  deriving (Applicative, Functor, Monad, MonadIO)

newtype Init c a = Init (WriterT [Var c] (New c) a)
  deriving (Applicative, Functor, Monad, MonadIO)

newtype Assign c a = Assign (WriterT [(UntypedIvar, Maybe (New c ()))] IO a)
  deriving (Applicative, Functor, Monad, MonadIO)

newtype Solve c a = Solve (RWST ([c] -> New c ()) () (SolveState c) IO a)
  deriving (Applicative, Functor, Monad, MonadIO)

data SolveState c = SolveState {
  _unassignedVars :: S.Set UntypedIvar,
  _unrevisedClauses :: S.Set (Clause c),
  _learntClauses :: S.Set (Clause c) }

data Reversable a = Reversable {
  action :: IO a,
  undo :: IO () }

makeLenses ''IVarState
makeLenses ''SolveState

-- solve :: Init c a -> ([c] -> New ()) -> IO (Bool, a)
solve p i = undefined {- do
  (ret, vars, clauses) <- runInit i
  completed <- runSolve backtrack vars (map snd clauses) p
  case completed of
    Nothing -> return (True, ret)
    Just () -> return (False, ret)

backtrack :: Solve c ()
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

selectUnassignedVariable :: Solve c (Maybe UntypedIvar)
selectUnassignedVariable = do
  vs <- vars
  sizes <- mapM (\v -> (,v) <$> liftIO (numCandidates v)) . S.toList $ vs
  case sort . filter (\(x,_) -> x > 1) $ sizes of
    [] -> return Nothing
    ((_,v):_) -> return (Just v)

reviseAll :: Solve c (Bool, Solve c ())
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
-}

newVar = Var <$> newUnique <*> newIORef S.empty

-- newAVar :: M.Map a (New ()) -> Init c (AVar c a)
newAVar vs = do
  ret <- AVar vs <$> newVar
  tellVar ret
  return ret

avar :: AVar c a -> Var c
avar = Var . avarVar

newIVar :: AVar c a -> New c (IVar c a)
newIVar av = do
  ret <- IVar av <$> newIORef (IVarState (M.keys (avarValues av)) M.empty)
  tellUntypedIvar (untype ret)
  return ret

ivar :: IVar c a -> Var c
ivar = Var . avarVar . ivarAvar

readIVar :: IVar c a -> IO (S.Set a)
readIVar iv = _ivarCandidates <$> readIORef (ivarState iv)

setIVar :: (Ord a) => IVar c a -> a -> Assign c ()
setIVar iv v = do
  liftIO $ do
    let ref = ivarState iv
    candidates <- ivarCandidates <$> readIORef (ivarState iv)
    let newSet =
          case M.lookup v candidates of
            Nothing -> S.empty
            Just _ -> S.singleton v
    modifyIORef ref (set ivarCandidates newSet)
  liftIO $ modifyIORef (ivarState iv) (set ivarCandidates (S.singleton v))
  dirtyVar iv

shrinkIVar :: (Ord a) => IVar c a -> a -> Assign c ()
shrinkIVar iv v = do
  liftIO $ modifyIORef (ivarState iv) (over ivarCandidates (S.delete v))
  dirtyVar iv 

-- untype :: (Ord a) => IVar c a -> UntypedIvar
untype iv = UntypedIvar identity count setters where
  identity = varIdentity . avarVar . ivarAvar $ iv
  candidates = _ivarCandidates <$> readIORef (ivarState iv)
  count = S.size <$> candidates
  setters = do
    cs <- S.toList <$> candidates
    return (map (setIVar iv) cs)

-- ^ Revise might not fire on this clause if only one of the vars in the
-- second set is assigned. When in doubt, put all of your vars in the
-- first set.
newClause
  :: clause
  -> S.Set (Var clause) -- ^ watched vars
  -> S.Set (Var clause) -- ^ not-necessarily watched vars
  -> IO Bool -- ^ collectable
  -> Assign clause Bool -- ^ resolve; False indicates constraint is unsatisfiable. Checking for satisfiability is optional; the associated variables will be checked for emptiness. Returning False is just an opportunity to fail sooner.
  -> New clause () -- ^ clause is necessary here so that resolve can be called.
newClause c watched unwatched collectable resolve = do
  wr <- newIORef watched
  tellClause (Clause c (S.union watched unwatched) collectable resolve wr)

-- runNew :: New a -> IO (a, [UntypedIvar], [Clause])
runNew (New m) = do
  (ret, mix) <- runWriterT m
  let (ims, cs) = partitionEithers mix
  return (ret, ims, cs)

tellClause :: Clause c -> New c ()
tellClause = New . tell . (:[]) . Right

tellUntypedIvar :: UntypedIvar -> New c ()
tellUntypedIvar = New . tell . (:[]) . Left

runInit :: Init c a -> IO (a, [Var c], [UntypedIvar], [Clause c])
runInit (Init m) = do
  ((ret, avars), ivars, cs) <- runNew (runWriterT m)
  return (ret, avars, ivars, cs)

liftNew :: New c a -> Init c a
liftNew = Init . lift

tellVar :: Var c {- assumed AVar -} -> Init c ()
tellVar = Init . tell . (:[])

runAssign :: Assign c a -> IO (a, [(UntypedIvar, Maybe (New c ()))])
runAssign (Assign m) = runWriterT m

-- dirtyVar :: IVar c a -> Assign c ()
dirtyVar iv = Assign $ do
  candidates <- liftIO $ _ivarCandidates <$> readIORef (ivarState iv)
  let internalBug = error
  let effect =
        case S.toList candidates of
          [v] ->
            case M.lookup v (avarValues . ivarAvar $ iv) of
              Nothing -> internalBug "one of candidates is invalid"
              Just x -> Just x
          _ -> Nothing
  tell [(untype iv, effect)]

evalSolve :: Solve c a -> ([c] -> New c ()) -> SolveState c -> IO a
evalSolve (Solve m) resolve solveState = do
  (ret, ()) <- evalRWST m resolve solveState
  return ret

resolve :: [c] -> Solve c (New c ())
resolve xs = Solve $ do
  resolver <- ask
  return (resolver xs)

runReversable :: Reversable a -> IO (a, IO ())
runReversable (Reversable a u) = do
  ret <- a
  return (ret, u)

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

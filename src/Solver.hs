{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
module Solver (
  -- | Taffy is a general purpose constraint solver. This module only
  -- implements guessing and backjumping. Constraint testing, unit
  -- detection, and clause learning are passed in as arguments.
  --
  -- See 'SatExample' for an example of how to make a simple sat solver.

  -- * Solving
  solve,

  -- * Variables
  -- | Two kinds of variables are supported: abstract and instance.
  -- Instance variables ('IVar's) are variables in the ordinary sense
  -- of constraint problems. Abstract variables ('AVar's) track groups
  -- of similar instance variables. Every instance variable belongs to
  -- one abstract variable. Constraints can be defined on instance
  -- variables, abstract variables, or a combination. The advantage of
  -- this is that constraints can be learned over entire families of
  -- subproblems, instead of being localized to individual subproblems.
  -- By explicitly encoding the symmetry of your problem into constraints
  -- over 'AVar's, you can avoid a lot of duplicated computation.
  Var(),
  avar,
  ivar,

  -- ** Abstract variables
  AVar(),
  newAVar,
  
  -- ** Instance variables
  IVar(),
  newIvar,
  readIvar,
  setIvar,
  shrinkIvar,

  -- * Constraints
  newConstraint,

  -- * Monads
  New(),
  Init(),
  liftNew,
  Assign(),
) where

import Control.Applicative
import Control.Lens
import Control.Monad.IO.Class
import Control.Monad.RWS
import Control.Monad.Writer
import Data.Either
import Data.Function
import Data.IORef
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import Data.Unique

-- | An untyped container for both 'AVar's and 'IVar's. Use it as an argument
-- to the 'newConstraint' function.
data Var constraint = Var {
  varIdentity :: Unique,

  -- ^ A partial set of clauses constraining this var. Clauses not in this set
  -- but which constrain this var do not need to be revised when this var
  -- is assigned.
  -- For example, if the clause is a \/ b \/ c, then I should put the
  -- clause in two of the vars, but I do not need to put it in the
  -- third, since I can only make a deduction when there is one
  -- remaining unassigned variable.
  varClauses :: IORef (S.Set (Clause constraint)) }

instance Eq (Var constraint) where (==) = (==) `on` varIdentity
instance Ord (Var constraint) where compare = compare `on` varIdentity

-- | A family of instance variables.
data AVar constraint a = AVar {
  avarValues :: M.Map a (IVar constraint a -> New constraint ()),
  avar :: Var constraint -- ^ Wraps an abstract variable for use as a constraint dependency.
  }

-- | An instance variable, belonging to one abstract variable. It can
-- be constrained indirectly (through its parent 'AVar') or directly.
data IVar constraint a = IVar {
  ivarAvar :: AVar constraint a,
  ivarState :: IORef (IVarState constraint a) }

data IVarState constraint a = IVarState {
  -- | If empty, problem is in conflict.
  -- If singleton, then a value has been chosen.
  -- If more than one item, a choice has yet to be made.
  _ivarCandidates :: (S.Set a),

  -- | Everytime ivarCandidates is reduced to a singleton, that value is
  -- added here. If it already exist in here, then the associated (New ())
  -- in the AVar is not executed, since we know it has already been executed
  -- once. If a clause using this ivar is garbage collected, then the
  -- value is removed from here, so that future re-assignments will
  -- re-instantiate the clause.
  _ivarPreviousAssignments :: M.Map a (S.Set (Clause constraint)) } -- todo: this value is still not being checked

data UntypedIvar c = UntypedIvar {
  uivarVar :: Var c,

  -- ^ A sequence of calls to setIvar for each remaining candidate.
  uivarValues :: IO [Assign c ()] }

instance Eq (UntypedIvar c) where (==) = (==) `on` varIdentity . uivarVar
instance Ord (UntypedIvar c) where compare = compare `on` varIdentity . uivarVar

data Clause c = Clause {
  clauseClause :: c,
  clauseVars :: S.Set (Var c),
  clauseResolve :: Assign c Bool,
  clauseCollectable :: IO Bool }

clauseIdentity :: Clause c -> (c, S.Set (Var c))
clauseIdentity c = (clauseClause c, clauseVars c)

instance (Eq c) => Eq (Clause c) where (==) = (==) `on` clauseIdentity
instance (Ord c) => Ord (Clause c) where compare = compare `on` clauseIdentity

-- | A monad for creating 'IVar's and constraints.
newtype New constraint a = New (WriterT [Either (UntypedIvar constraint) (IO Bool -> Clause constraint)] IO a)
  deriving (Applicative, Functor, Monad, MonadIO)

-- | A special case of the 'New' monad which also allows creating 'AVar's.
newtype Init constraint a = Init (WriterT [Var constraint] (New constraint) a)
  deriving (Applicative, Functor, Monad, MonadIO)

-- | A monad for making assignments to 'IVar's, which a constraint will
-- do when it deduces an implication.
newtype Assign constraint a = Assign (WriterT [Assignment constraint] IO a)
  deriving (Applicative, Functor, Monad, MonadIO)

data Assignment c = Assignment {
  assignmentVar :: (UntypedIvar c),
  assignmentEffect :: (New c ()),
  assignmentUndo :: IO () }

newtype Solve c a = Solve (RWST ([c] -> New c ()) () (SolveState c) IO a)
  deriving (Applicative, Functor, Monad, MonadIO)

instance MonadState (SolveState c) (Solve c) where -- todo

data SolveState c = SolveState {
  _assignedVars :: [AssignmentFrame c], -- head is most recently assigned
  _unassignedVars :: S.Set (UntypedIvar c),
  _unrevisedClauses :: S.Set (Clause c),
  _learntClauses :: S.Set (Clause c) }

data AssignmentFrame c = AssignmentFrame {
  _frameUndo :: IO (),
  _frameUntriedValues :: [Assign c ()],
  _frameDecisionLevel :: Bool }

makeLenses ''IVarState
makeLenses ''SolveState
makeLenses ''AssignmentFrame

-- Attempts to find a satisfying assignment.
solve
  :: (Ord constraint)
  => ([constraint] -> New constraint ()) -- ^ Constraint learning function, for conflict-directed constraint learning. The head of the given list is the constraint which produced a contradiction.
  -> Init constraint a -- ^ Problem definition. You should return the 'IVar's that you plan on reading from (using 'readIvar') when a solution is found.
  -> IO (Bool, a) -- ^ 'False' iff no solution exists. Values returned from 'readIvar' after solve completes are 'undefined' if 'False' is returned; otherwise they will be singleton sets containing the satisfying assignment.
solve learner definition = do
  (ret, _avars, ivars, clauses) <- runInit definition
  mapM_ attach clauses
  let ss = SolveState [] (S.fromList ivars) (S.fromList clauses) S.empty
  completed <- evalSolve loop learner ss
  return (completed, ret)

attach :: (Ord c) => Clause c -> IO ()
attach c = mapM_ insert . S.toList . clauseVars $ c where
  insert v = modifyIORef (varClauses v) (S.insert c)

-- loop :: Solve c Bool
loop = do
  mbc <- pop unrevisedClauses
  case mbc of
    Nothing -> do
      mbv <- pop unassignedVars
      case mbv of
        Nothing -> return True
        Just v -> do
          vals <- liftIO $ uivarValues v
          case vals of
            [] -> do
              unassignedVars %= S.insert v
              jumpback
            [_] -> do
              assignedVars %= (AssignmentFrame nop [] False :)
              loop
            (x:xs) -> choose x xs
    Just c -> do
      (satisfiable, as) <- liftIO $ runAssign (clauseResolve c)
      if not satisfiable then jumpback else do
      -- todo: need to add a check in here to see if any of the affected
      assignedVars %= (reverse (map (\a -> AssignmentFrame (assignmentUndo a) [] False) as) ++)
      propagateEffects as
      loop

nop = return ()

jumpback :: (Ord c) => Solve c Bool
jumpback = do
  vs <- use assignedVars
  let (pop,keep) = span (not . _frameDecisionLevel) vs
  -- todo: put clause learning in here
  liftIO $ mapM_ _frameUndo pop
  stepback keep

stepback [] = return False
stepback (x:xs) = do
  liftIO $ _frameUndo x
  case _frameUntriedValues x of
    [] -> stepback xs
    (y:ys) -> choose y ys

choose x xs = do
  ((), [a]) <- liftIO $ runAssign x
  assignedVars %= (AssignmentFrame (assignmentUndo a) xs True :)
  propagateEffects [a]
  loop
      

-- propagateEffects :: [Assignment c] -> Solve c ()
propagateEffects as = do
  -- todo: jumpback if any of the assignments cause a variable's
  -- candidate list to become empty
  (newVars, newConstraints) <- liftIO $ runEffects as
  unassignedVars %= S.union (S.fromList newVars)
  unrevisedClauses %= S.union (S.fromList newConstraints)
  forM_ as $ \a -> do
    cs <- liftIO $ readIORef (varClauses . uivarVar . assignmentVar $ a)
    unrevisedClauses %= S.union cs

runEffects :: [Assignment c] -> IO ([UntypedIvar c], [Clause c])
runEffects as = do
  -- todo: change the argument to runNew to be dependent on whether
  -- the instigating variable has multiple candidate values.
  out <- mapM (flip runNew (return False) . assignmentEffect) as
  return . (\(vss,css) -> (concat vss, concat css)) . unzip . map (\((),v,c) -> (v,c)) $ out

-- For some reason ghc can't infer this type.
pop :: MonadState s m => Simple Lens s (S.Set a) -> m (Maybe a)
pop set  = do
  s <- use set
  if S.null s then return Nothing else do
  let (v, s') = S.deleteFindMin s -- todo: better variable ordering
  set .= s'
  return (Just v)

newVar = Var <$> newUnique <*> newIORef S.empty

-- | Creates an abstract variable.
--
-- Candidates values to be assigned to instance variables created from this
-- abstract variable are given as the keys of the map. The associated
-- value is any side effect you want to happen when the variable is assigned.
--
-- Although any IO action can be put into the side effect, its main
-- purpose is to create new variables and new clauses on those variables.
-- For example, if your problem has, conceptually, a variable whose value
-- is some unknown list, you can create an 'AVar' which represents the two
-- possible constructors for the list: Cons and Nil. You can define the
-- side effect for the Cons case as creating two new instance variables:
-- one for the value in the head and the other for the constructor of the
-- tail.
--
-- You should not rely on the invocation of the side effect as an indication
-- that an instance variable has actually been assigned that value. The
-- solver will sometimes do a dry run on the side effects of multiple values,
-- so that it can give priority to assignments producing fewer new variables
-- and clauses.
newAVar
  :: M.Map a (IVar constraint a -> New constraint ()) -- ^ A map from values to side effects. If you do not need a side effect, just use 'return ()'.
  -> Init constraint (AVar constraint a)
newAVar vs = do
  ret <- liftIO $ AVar vs <$> newVar
  tellAvar ret
  return ret

instance Eq (IVar constraint a) where (==) = (==) `on` varIdentity . ivar
instance Ord (IVar constraint a) where compare = compare `on` varIdentity . ivar

-- | Creates a new instance variable with the given 'AVar' as its parent.
newIvar :: (Ord a) => AVar constraint a -> New constraint (IVar constraint a)
newIvar av = do
  ret <- liftIO $ IVar av <$> newIORef (IVarState (S.fromList $ M.keys (avarValues av)) M.empty)
  tellUntypedIvar (untype ret)
  return ret

-- | Wraps an instance variable for use as a constraint dependency.
ivar :: IVar constraint a -> Var constraint
ivar = avar . ivarAvar

-- | Returns the values which are not currently in direct violation
-- of a constraint. A singleton value indicates that the variable
-- has been assigned.
--
-- This function can be called after the 'solve' function
-- has returned 'True', or inside the 'Assign' monad given to 'newConstraint'.
-- Its behavior is undefined when called from inside the 'New' monad or
-- the 'Init' monad.
readIvar :: IVar constraint a -> IO (S.Set a)
readIvar iv = _ivarCandidates <$> readIORef (ivarState iv)

-- | Removes all but the given value from the variable's set of
-- candidate values. If the given value is already in violation of
-- another constraint, the set of associated values will become empty,
-- and the solver will begin backjumping.
setIvar :: (Ord a) => IVar constraint a -> a -> Assign constraint ()
setIvar iv v = modifyIVar iv collapse where
  collapse cds | S.member v cds = S.singleton v
               | otherwise = S.empty

-- | Removes the given value from the variable's set of candidate values.
-- If the set becomes empty as a result, the solver will begin backjumping.
shrinkIvar :: (Ord a) => IVar constraint a -> a -> Assign constraint ()
shrinkIvar iv v = modifyIVar iv (S.delete v)

-- modifyIVar :: IVar c a -> (S.Set a -> S.Set a) -> Assign c ()
modifyIVar iv mod = do
  orig <- liftIO $ do
    let ref = ivarState iv
    candidates <- _ivarCandidates <$> readIORef ref
    modifyIORef ref (over ivarCandidates mod)
    return candidates
  dirtyVar iv orig

-- untype :: (Ord a) => IVar c a -> (UntypedIvar c)
untype iv = UntypedIvar identity setters where
  identity = ivar iv
  candidates = _ivarCandidates <$> readIORef (ivarState iv)
  setters = do
    cs <- S.toList <$> candidates
    return (map (setIvar iv) cs) -- todo: pick a more optimal ordering

-- | Constrains a set of variables.
newConstraint
  :: constraint
  -> S.Set (Var constraint) -- ^ The set of variables which this constraint examines.
  -> Assign constraint Bool -- ^ Constraint testing function. Should return False only when the constraint can no longer be satisfied. It should call 'setIvar' or 'shrinkIvar' when it can make a deduction.
  -> New constraint ()
newConstraint c watched resolve =
  tellClause (Clause c watched resolve)

-- runNew :: New a -> IO (a, [(UntypedIvar c)], [Clause])
runNew (New m) collectable = do
  (ret, mix) <- runWriterT m
  let (ims, cs) = partitionEithers mix
  return (ret, ims, map ($ collectable) cs)

-- tellClause :: (IO Bool -> Clause c) -> New c ()
tellClause = New . tell . (:[]) . Right

tellUntypedIvar :: (UntypedIvar c) -> New c ()
tellUntypedIvar = New . tell . (:[]) . Left

runInit :: Init c a -> IO (a, [Var c], [(UntypedIvar c)], [Clause c])
runInit (Init m) = do
  ((ret, avars), ivars, cs) <- runNew (runWriterT m) (return False)
  return (ret, avars, ivars, cs)

-- | Lift 'IVar' and constraint creation into the 'Init' monad.
liftNew :: New constraint a -> Init constraint a
liftNew = Init . lift

tellAvar :: AVar c a -> Init c ()
tellAvar = Init . tell . (:[]) . avar

-- runAssign :: Assign c a -> IO (a, [Assignment])
runAssign (Assign m) = runWriterT m

-- dirtyVar :: IVar c a -> S.Set a -> Assign c ()
dirtyVar iv orig = Assign $ do
  let ref = ivarState iv
  candidates <- liftIO $ _ivarCandidates <$> readIORef ref
  let internalBug = error
  let effect =
        case S.toList candidates of
          [v] ->
            case M.lookup v (avarValues . ivarAvar $ iv) of
              Nothing -> internalBug "one of candidates is invalid"
              Just x -> x
          _ -> const nop
  tell [Assignment (untype iv) (effect iv) (modifyIORef ref (set ivarCandidates orig))]

evalSolve :: Solve c a -> ([c] -> New c ()) -> SolveState c -> IO a
evalSolve (Solve m) learner solveState = do
  (ret, ()) <- evalRWST m learner solveState
  return ret

learn :: [c] -> Solve c (New c ())
learn xs = Solve $ do
  learner <- ask
  return (learner xs)

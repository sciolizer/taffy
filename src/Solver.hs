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
  -- Instance variables ('Ivar's) are variables in the ordinary sense
  -- of constraint problems. Abstract variables ('Avar's) track groups
  -- of similar instance variables. Every instance variable belongs to
  -- one abstract variable. Constraints can be defined on instance
  -- variables, abstract variables, or a combination. The advantage of
  -- this is that constraints can be learned over entire families of
  -- subproblems, instead of being localized to individual subproblems.
  -- By explicitly encoding the symmetry of your problem into constraints
  -- over 'Avar's, you can avoid a lot of duplicated computation.
  Var(),
  avar,
  ivar,

  -- ** Abstract variables
  Avar(),
  newAvar,
  newNamedAvar,

  -- ** Instance variables
  Ivar(),
  newIvar,
  newNamedIvar,
  ivarName,
  readIvar,
  setIvar,
  shrinkIvar,

  -- * Constraints
  newConstraint,
  newNamedConstraint,

  -- * Monads
  New(),
  Init(),
  liftNew,
  Assign(),
) where

import Control.Applicative
import Control.Exception
import Control.Lens
import Control.Monad.IO.Class
import Control.Monad.RWS
import Control.Monad.Writer
import Data.Either
import Data.Function
import Data.IORef
import Data.List
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import Data.Unique

-- | An untyped container for both 'Avar's and 'Ivar's. Use it as an argument
-- to the 'newConstraint' function.
data Var constraint = Var {
  varName :: String,
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
instance Show (Var constraint) where show = varName

-- | A family of instance variables.
data Avar constraint a = Avar {

  -- Ordered by cheapest choice, that is, if x comes before y,
  -- then the product of the sizes of x's generated variables will
  -- be no more than y's product.
  -- (constraints generated is not a factor in ordering, since they
  -- don't actually make the problem larger)
  avarValues :: [(a,Ivar constraint a -> New constraint ())],

  -- | Used by safetyCheck.
  inNewOrInitMonad :: IO Bool,

  -- | Wraps an abstract variable for use as a constraint dependency.
  avar :: Var constraint }


-- | An instance variable, belonging to one abstract variable. It can
-- be constrained indirectly (through its parent 'Avar') or directly.
data Ivar constraint a = Ivar {
  ivarAvar :: Avar constraint a,
  ivarState :: IORef (IvarState constraint a),
  ivar :: Var constraint -- ^ Wraps an instance variable for use as a constraint dependency.
  }

instance Eq (Ivar constraint a) where (==) = (==) `on` varIdentity . ivar
instance Ord (Ivar constraint a) where compare = compare `on` varIdentity . ivar

data IvarState constraint a = IvarState {
  -- | If empty, problem is in conflict.
  -- If singleton, then a value has been chosen.
  -- If more than one item, a choice has yet to be made.
  _ivarCandidates :: S.Set a,

  -- | Everytime ivarCandidates is reduced to a singleton, that value is
  -- added here. If it already exist in here, then the associated (New ())
  -- in the Avar is not executed, since we know it has already been executed
  -- once. If a clause using this ivar is garbage collected, then the
  -- value is removed from here, so that future re-assignments will
  -- re-instantiate the clause.
  _ivarPreviousAssignments :: M.Map a (S.Set (Clause constraint)) } -- todo: this value is still not being checked

data UntypedIvar c = UntypedIvar {
  uivarVar :: Var c,
  uivarAvar :: Var c,

  -- ^ A sequence of calls to setIvar for each remaining candidate.
  uivarValues :: IO [Assign c ()] }

instance Eq (UntypedIvar c) where (==) = (==) `on` varIdentity . uivarVar
instance Ord (UntypedIvar c) where compare = compare `on` varIdentity . uivarVar
instance Show (UntypedIvar c) where show = show . uivarVar

data Clause c = Clause {
  clauseName :: String,
  clauseClause :: c,
  clauseVars :: S.Set (Var c),
  clauseResolve :: Assign c Bool,
  clauseCollectable :: IO Bool }

clauseIdentity :: Clause c -> (c, S.Set (Var c))
clauseIdentity c = (clauseClause c, clauseVars c)

instance (Eq c) => Eq (Clause c) where (==) = (==) `on` clauseIdentity
instance (Ord c) => Ord (Clause c) where compare = compare `on` clauseIdentity
instance Show (Clause c) where show = clauseName

-- | A monad for creating 'Ivar's and constraints. Do not call readIvar
-- while in this monad.
newtype New constraint a = New (RWST NewContext [Either (UntypedIvar constraint) (IO Bool -> Clause constraint)] () IO a)
  deriving (Applicative, Functor, Monad, MonadIO)

newtype NewContext = NewContext {
  _newState :: IORef NewState }

data NewState = NewState {
  _nextAvarId :: Int,
  _nextIvarId :: Int,
  _nextConstraintId :: Int }

-- | A special case of the 'New' monad which also allows creating 'Avar's.
newtype Init constraint a = Init (RWST (IORef Bool) [Var constraint] () (New constraint) a)
  deriving (Applicative, Functor, Monad, MonadIO)

-- | A monad for making assignments to 'Ivar's, which a constraint will
-- do when it deduces an implication.
newtype Assign constraint a = Assign (WriterT [Assignment constraint] IO a)
  deriving (Applicative, Functor, Monad, MonadIO)

data Assignment c = Assignment {
  assignmentVar :: (UntypedIvar c),
  assignmentEffect :: (New c ()),
  assignmentUndo :: IO () }

newtype Solve c a = Solve (RWST (SolveContext c) () (SolveState c) IO a)
  deriving (Applicative, Functor, Monad, MonadIO)

data SolveState c = SolveState {
  _assignedVars :: [AssignmentFrame c], -- head is most recently assigned
  _unassignedVars :: S.Set (UntypedIvar c),
  _unrevisedClauses :: S.Set (Clause c),
  _learntClauses :: S.Set (Clause c) }

data SolveContext c = SolveContext {
  _solveNewState :: IORef NewState,
  _learner :: [c] -> New c (),
  _monadCheckRef :: IORef Bool }

instance MonadReader (SolveContext c) (Solve c) where
  -- ask :: Solve c (SolveContext c)
  ask = Solve ask
  -- local :: (SolveContext c -> SolveContext c) -> Solve c a -> Solve c a
  local f (Solve m) = Solve (local f m)

instance MonadState (SolveState c) (Solve c) where state = Solve . state

data AssignmentFrame c = AssignmentFrame {
  _frameUndo :: IO (),
  _frameUntriedValues :: [Assign c ()],
  _frameDecisionLevel :: Bool }

makeLenses ''IvarState
makeLenses ''SolveState
makeLenses ''SolveContext
makeLenses ''AssignmentFrame
makeLenses ''NewState
makeLenses ''NewContext

-- Attempts to find a satisfying assignment.
solve
  :: (Ord constraint)
  => ([constraint] -> New constraint ()) -- ^ Constraint learning function, for conflict-directed constraint learning. The head of the given list is the constraint which produced a contradiction.
  -> Init constraint a -- ^ Problem definition. You should return the 'Ivar's that you plan on reading from (using 'readIvar') when a solution is found.
  -> IO (Bool, a) -- ^ 'False' iff no solution exists. Values returned from 'readIvar' after solve completes are 'undefined' if 'False' is returned; otherwise they will be singleton sets containing the satisfying assignment.
solve learner definition = do
  (ret, check, newstate, _avars, ivars, clauses) <- runInit definition
  mapM_ attach clauses
  let ss = SolveState [] (S.fromList ivars) (S.fromList clauses) S.empty
  completed <- evalSolve loop (SolveContext newstate learner check) ss
  return (completed, ret)

attach :: (Ord c) => Clause c -> IO ()
attach c = mapM_ insert . S.toList . clauseVars $ c where
  insert v = modifyIORef (varClauses v) (S.insert c)

-- loop :: Solve c Bool
loop = do
  mbc <- pop unrevisedClauses
  debug $ "popped clause: " ++ show mbc
  case mbc of
    Nothing -> do
      mbv <- pop unassignedVars
      debug $ "popped var: " ++ show mbv
      case mbv of
        Nothing -> return True
        Just v -> do
          vals <- liftIO $ uivarValues v
          debug $ "has " ++ show (length vals) ++ " vals"
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
      assignedVars %= (reverse (map (\a -> AssignmentFrame (assignmentUndo a) [] False) as) ++)
      if not satisfiable then jumpback else do
      propagateEffects as

nop = return ()

jumpback :: (Ord c) => Solve c Bool
jumpback = do
  vs <- use assignedVars
  let (pop,keep) = span (not . _frameDecisionLevel) vs
  -- todo: put clause learning in here
  liftIO $ mapM_ _frameUndo pop
  debug $ "undid " ++ show (length pop) ++ " frames"
  stepback keep

stepback [] = return False
stepback (x:xs) = do
  debug "stepback"
  liftIO $ _frameUndo x
  case _frameUntriedValues x of
    [] -> stepback xs
    (y:ys) -> choose y ys

choose x xs = do
  ((), [a]) <- liftIO $ runAssign x
  assignedVars %= (AssignmentFrame (assignmentUndo a) xs True :)
  propagateEffects [a]

-- propagateEffects :: [Assignment c] -> Solve c ()
propagateEffects as = do
  contradiction <- any null <$> liftIO (mapM (uivarValues . assignmentVar) as)
  if contradiction then jumpback else do
  (newVars, newConstraints) <- runEffects as
  debug $ "generated " ++ show (length newVars) ++ " new vars and " ++ show (length newConstraints) ++ " new constraints"
  unassignedVars %= S.union (S.fromList newVars)
  unrevisedClauses %= S.union (S.fromList newConstraints)
  forM_ as $ \a -> do
    let getConstraints f = liftIO $ readIORef (varClauses . f . assignmentVar $ a)
    cs1 <- getConstraints uivarVar
    cs2 <- getConstraints uivarAvar
    unrevisedClauses %= S.union cs1 . S.union cs2
  loop

runEffects :: [Assignment c] -> Solve c ([UntypedIvar c], [Clause c])
runEffects as = do
  ns <- view solveNewState
  making <- view monadCheckRef
  liftIO $ do
    -- todo: change collectable to be dependent on whether
    -- the instigating variable has multiple candidate values.
    out <- mapM ((\x -> runNew x making ns (return False)) . assignmentEffect) as
    return . (\(vss,css) -> (concat vss, concat css)) . unzip . map (\((),v,c) -> (v,c)) $ out

-- For some reason ghc can't infer this type.
pop :: MonadState s m => Simple Lens s (S.Set a) -> m (Maybe a)
pop set  = do
  s <- use set
  if S.null s then return Nothing else do
  let (v, s') = S.deleteFindMin s -- todo: better variable ordering
  set .= s'
  return (Just v)

newVar name = Var name <$> newUnique <*> newIORef S.empty

-- | Creates an abstract variable.
--
-- Candidates values to be assigned to instance variables created from this
-- abstract variable are given as the keys of the map. The associated
-- value is any side effect you want to happen when the variable is assigned.
--
-- Although any IO action can be put into the side effect, its main
-- purpose is to create new variables and new clauses on those variables.
-- For example, if your problem has, conceptually, a variable whose value
-- is some unknown list, you can create an 'Avar' which represents the two
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
newAvar
  :: (Ord a) => M.Map a (Ivar constraint a -> New constraint ()) -- ^ A map from values to side effects. If you do not need a side effect, just use 'return ()'.
  -> Init constraint (Avar constraint a)
newAvar vs = do
  id <- liftNew $ query nextAvarId
  newNamedAvar ("unnamed avar " ++ show id) vs

-- | Like 'newAvar', but allows you to attach a custom name to the variable
-- for debugging purposes.
newNamedAvar name vs = z where
  z = do
    making <- Init ask
    dummy <- liftNew . newIvar . Avar (M.toList vs) (readIORef making) =<< liftIO (newVar name)
    vs' <- map snd . sortBy (compare `on` fst) <$> mapM (varCount dummy making) (M.toList vs)
    ret <- liftIO $ Avar vs' (readIORef making) <$> newVar name
    tellAvar ret
    return ret
  varCount dummy making (a, maker) = liftIO $ do
    stubState <- newIORef (NewState 0 0 0)
    ((), newVars, _newClauses) <- runNew (maker dummy) making stubState (return False)
    cost <- product <$> mapM (\x -> length <$> uivarValues x) newVars
    return (cost :: Int, (a, maker))

-- | Creates a new instance variable with the given 'Avar' as its parent.
newIvar :: (Ord a) => Avar constraint a -> New constraint (Ivar constraint a)
newIvar av = do
  id <- query nextIvarId
  newNamedIvar ("unnamed ivar " ++ show id) av

-- | Like 'newIvar', but allows you to attach a custom name to the variable
-- for debugging purposes.
newNamedIvar name av = do
  ret <- liftIO $ do
    state <- newIORef . flip IvarState M.empty . S.fromList . map fst . avarValues $ av
    var <- Var name <$> newUnique <*> newIORef S.empty
    return (Ivar av state var)
  tellUntypedIvar (untype ret)
  return ret

-- | Returns the name assigned to the given variable.
ivarName :: Ivar constraint a -> String
ivarName = varName . ivar

-- | Returns the values which are not currently in direct violation
-- of a constraint. A singleton value indicates that the variable
-- has been assigned.
--
-- This function can be called after the 'solve' function
-- has returned 'True', or inside the 'Assign' monad given to 'newConstraint'.
-- It raises an error when called from inside the New (or Init) monad, to
-- prevent misleading results. New monads are sometimes executed as dry
-- runs (undone immediately after executing), and are not a safe
-- place to infer the problem state.
readIvar :: Ivar constraint a -> IO (S.Set a)
readIvar iv = do
  safetyCheck iv
  _ivarCandidates <$> readIORef (ivarState iv)

-- | Removes all but the given value from the variable's set of
-- candidate values. If the given value is already in violation of
-- another constraint, the set of associated values will become empty,
-- and the solver will begin backjumping.
setIvar :: (Ord a) => Ivar constraint a -> a -> Assign constraint ()
setIvar iv v = modifyIvar iv collapse where
  collapse cds | S.member v cds = S.singleton v
               | otherwise = S.empty

-- | Removes the given value from the variable's set of candidate values.
-- If the set becomes empty as a result, the solver will begin backjumping.
shrinkIvar :: (Ord a) => Ivar constraint a -> a -> Assign constraint ()
shrinkIvar iv v = modifyIvar iv (S.delete v)

-- modifyIvar :: Ivar c a -> (S.Set a -> S.Set a) -> Assign c ()
modifyIvar iv mod = do
  orig <- liftIO $ do
    let ref = ivarState iv
    candidates <- _ivarCandidates <$> readIORef ref
    modifyIORef ref (over ivarCandidates mod)
    return candidates
  dirtyVar iv orig

-- untype :: (Ord a) => Ivar c a -> (UntypedIvar c)
untype iv = UntypedIvar (ivar iv) (avar . ivarAvar $ iv) setters where
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
newConstraint c watched resolve = do
  id <- query nextConstraintId
  newNamedConstraint ("unnamed constraint " ++ show id) c watched resolve

-- | Like 'newConstraint', but allows you to attach a custom name for
-- debugging purposes.
newNamedConstraint name c watched resolve =
  tellClause (Clause name c watched resolve)

runNew
  :: New c a
  -> IORef Bool
  -> IORef NewState
  -> IO Bool
  -> IO (a, [(UntypedIvar c)], [Clause c])
runNew (New m) flag newstate collectable = bracket turnOn turnOff (const z) where
  z = do
    (ret, mix) <- evalRWST m (NewContext newstate) ()
    let (ims, cs) = partitionEithers mix
    return (ret, ims, map ($ collectable) cs)
  turnOn = do
    orig <- readIORef flag
    writeIORef flag False
    return orig
  turnOff = writeIORef flag

-- tellClause :: (IO Bool -> Clause c) -> New c ()
tellClause = New . tell . (:[]) . Right

tellUntypedIvar :: (UntypedIvar c) -> New c ()
tellUntypedIvar = New . tell . (:[]) . Left

query :: (Num a) => Simple Lens NewState a -> New c a
query lens = do
  ref <- New (asks _newState)
  liftIO $ do
    ret <- view lens <$> readIORef ref
    modifyIORef ref (over lens (+1))
    return ret

safetyCheck :: Ivar c a -> IO ()
safetyCheck iv = do
  making <- inNewOrInitMonad . ivarAvar $ iv
  when making $ throwIO (userError "cannot read from ivar while in the new or init monad")

-- runInit :: Init c a -> IO (a, [Var c], [(UntypedIvar c)], [Clause c])
runInit (Init m) = do
  newstate <- newIORef (NewState 0 0 0)
  making <- newIORef False
  ((ret, avars), ivars, cs) <- runNew (evalRWST m making ()) making newstate (return False)
  return (ret, making, newstate, avars, ivars, cs)

-- | Lift 'Ivar' and constraint creation into the 'Init' monad.
liftNew :: New constraint a -> Init constraint a
liftNew = Init . lift

tellAvar :: Avar c a -> Init c ()
tellAvar = Init . tell . (:[]) . avar

-- runAssign :: Assign c a -> IO (a, [Assignment])
runAssign (Assign m) = runWriterT m

-- dirtyVar :: Ivar c a -> S.Set a -> Assign c ()
dirtyVar iv orig = Assign $ do
  let ref = ivarState iv
  candidates <- liftIO $ _ivarCandidates <$> readIORef ref
  let internalBug = error
  let effect =
        case S.toList candidates of
          [v] ->
            case lookup v (avarValues . ivarAvar $ iv) of
              Nothing -> internalBug "one of candidates is invalid"
              Just x -> x
          _ -> const nop
  tell [Assignment (untype iv) (effect iv) (modifyIORef ref (set ivarCandidates orig))]

evalSolve :: Solve c a -> SolveContext c -> SolveState c -> IO a
evalSolve (Solve m) context solveState = do
  (ret, ()) <- evalRWST m context solveState
  return ret

{-
learn :: [c] -> Solve c (New c ())
learn xs = Solve $ do
  learner <- ask
  return (learner xs)
  -}

debug = liftIO . putStrLn

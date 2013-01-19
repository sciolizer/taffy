{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
module Solver (
  -- | Taffy is a general purpose constraint solver. This module only
  -- implements guessing and backjumping. Constraint testing, unit
  -- detection, and constraint learning are passed in as arguments.
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
  Values(..),

  -- * The two levels
  Instance(),

  -- * Operations on variables and constraints.
  Level(),
  newVar,
  readVar,
  setVar,
  shrinkVar,
  varName,
  newConstraint,

  -- * Abstract variables and constraints
  Abstract(),
  group,

  -- * Monads
  ReadWrite(),
  New(),
  abstractIO,
  Init(),
  make,
) where

import Control.Applicative
import Control.Arrow (first)
import Control.Exception
import Control.Lens
import Control.Monad.IO.Class
import Control.Monad.RWS
import Control.Monad.Writer
import Data.Either
import Data.Function
import Data.IORef
import Data.List hiding (group)
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import Data.Unique

-- | Candidates values to be assigned to a variable
-- are given as the keys of the map. The associated
-- value is any side effect you want to happen when the variable is assigned.
--
-- Although any IO action can be put into the side effect, its main
-- purpose is to create new variables and new constraints on those variables.
-- For example, if your problem has, conceptually, a variable whose value
-- is some unknown list, you can create a variable which represents the two
-- possible constructors for the list: Cons and Nil. You can define the
-- side effect for the Cons case as creating two new variables:
-- one for the value in the head and the other for the constructor of the
-- tail.
--
-- You should not rely on the invocation of the side effect as an indication
-- that an instance variable has actually been assigned that value. The
-- solver will sometimes do a dry run on the side effects of multiple values,
-- so that it can give priority to assignments producing fewer new variables
-- and constraints.
type Values constraint a = M.Map a (ValueEffect constraint a)

type ValueEffect c a = Var c a -> New Instance c ()

-- | Used both for vars and constraints!
data NameAndIdentity = NameAndIdentity {
  name :: String,
  identity :: Unique }

data VarCommon c a = VarCommon {
  _varCommonIdentity :: NameAndIdentity,

  -- Ordered by cheapest choice, that is, if x comes before y,
  -- then the product of the sizes of x's generated variables will
  -- be no more than y's product.
  -- (constraints generated is not a factor in ordering, since they
  -- don't actually make the problem larger)
  _varCommonValues :: [(a, ValueEffect c a)] }

-- | An untyped container for both 'Avar's and 'Ivar's. Use it as an argument
-- to the 'newConstraint' function.
data Var (constraint :: *) a
  = VarAbstract (AbstractVar constraint a)
  | VarInstance (InstanceVar constraint a)

data AbstractVar c a = AbstractVar {
  _abstractVarInstances :: IORef (M.Map Instantiation (InstanceVar c a)),

  -- | A partial set of constraints constraining this var. Constraints not in this set
  -- but which constrain this var do not need to be revised when this var
  -- is assigned.
  -- For example, if the constraint is a \/ b \/ c, then I should put the
  -- constraint in two of the vars, but I do not need to put it in the
  -- third, since I can only make a deduction when there is one
  -- remaining unassigned variable.
  -- The collection is partial if the client's constraints exit early.
  _abstractVarAbstractConstraints :: IORef (Constraints Abstract c),

  _abstractVarCommon :: VarCommon c a }

data InstanceVar (c :: *) a = InstanceVar {
  _instanceVarAbstractVar :: Maybe (AbstractVar c a, Instantiation),

  -- | If empty, problem is in conflict.
  -- If singleton, then a value has been chosen.
  -- If more than one item, a choice has yet to be made.
  _instanceVarCandidates :: IORef (S.Set a),

  -- | Partial list, etc. See comment on _abstractConstraints
  _instanceVarConstraints :: IORef (Constraints Instance c),
  _instanceVarCommon :: VarCommon c a }

type Constraints l c = S.Set (Constraint l c)

  {-

  -- | Everytime ivarCandidates is reduced to a singleton, that value is
  -- added here. If it already exist in here, then the associated (New ())
  -- in the Avar is not executed, since we know it has already been executed
  -- once. If a constraint using this ivar is garbage collected, then the
  -- value is removed from here, so that future re-assignments will
  -- re-instantiate the constraint.
  _previousAssignments :: M.Map a (S.Set (Constraint constraint)) } -- todo: this value is still not being checked
  -}

data UntypedAbstractVar c = UntypedAbstractVar {
  untypedAbstractVarIdentity :: NameAndIdentity,
  untypedAbstractVarAbstractConstraints :: IORef (Constraints Abstract c) }

-- | An instance variable with the type stripped, so that it can
-- be stored in homogoneous collections.
data UntypedInstanceVar c = UntypedInstanceVar {
  untypedInstanceVarIdentity :: NameAndIdentity,
  -- | A sequence of calls to setVar for each remaining candidate.
  untypedInstanceVarValues :: IO [ReadWrite Instance c ()],
  untypedInstanceVarInstanceConstraints :: IORef (Constraints Instance c),
  untypedInstanceVarAbstractVar :: Maybe (UntypedAbstractVar c, Instantiation) }

-- is there a way to keep the types of the vars in this data structure?
-- maybe wrap up the uses of the Constraint somehow?
data Constraint l c = Constraint {
  constraintIdentity :: NameAndIdentity,
  constraintConstraint :: Maybe c, -- if Nothing, then this constraint is a no-good generated by the solver (not by the client). (The no-good values are embedded in the resolver.)
  constraintResolve :: ReadWrite l c Bool,

  -- | False for problem clauses, True for learnt clauses, otherwise depends
  -- on the variable which created it.
  constraintCollectable :: IO Bool,

  -- | Removes this constraint from all variables that it was previously
  -- being watched on. This should be called right before constraintResolve
  -- is run. Maybe. It probably doesn't hurt to leave the injections in,
  -- and it might make things faster to leave things as is.
  -- This resets itself everytime it is run.
  constraintUninject :: IORef (IO ()) }

type AbstractInner c = RWST (IORef Int) [Constraint Abstract c] Satisfiable IO
type InstanceInner c = RWST NewContext ([UntypedInstanceVar c], [Constraint Instance c], [Assignment c]) Satisfiable IO

data Satisfiable = Satisfiable | Contradiction
  deriving (Bounded, Enum, Eq, Ord, Read, Show)

-- | A monad for creating variables and constraints.
data New level constraint a where
  NewAbstract
    :: AbstractInner constraint (a, New Instance constraint a)
    -> New Abstract constraint a
  NewInstance
    :: InstanceInner constraint a
    -> New Instance constraint a

data NewContext = NewContext {
  _newContextCollectable :: IO Bool,
  _newContextInstantiation :: Maybe Instantiation,
  _newContextNext :: IORef Int }

newtype Instantiation = Instantiation { unInstantiation :: Unique }
  deriving (Eq, Ord)

-- | Problem definition monad.
newtype Init constraint a = Init (RWST (IORef Int) [Constraint Abstract constraint] () (New Instance constraint) a)

-- | A monad for making assignments to variables. A constraint calls 'readVar'
-- to determine if one of its variables can be deduced from the others,
-- in which case it calls 'setVar'.
--
-- Abstract constraints should only read and write abstract variables.
-- Instance constraints should only read and write instance variables.
-- Doing otherwise will raise an error.
--
-- Implementations should be idempotent. That is, if a ReadWrite monad
-- is run twice (and no variables have changed in between), it should
-- read from the same variables and leave them in the same state
-- as if it were only run once. A constraint will inject itself into
-- each variable that it reads from, so that it can be re-fired
-- when that variable changes. Failing to maintain the idempotency invariant
-- can cause the solver to return incorrect assignments.
--
-- Idempotency is not required when the read variables have been changed
-- by different constraints or the solver itself. It is permissible
-- and encouraged for the ReadWrite monad to exit early
-- when it determies that the constraint is still satisfiable.
-- For example, boolean disjunctions can exit after reading only two
-- variables, if both of their literals can still be assigned true.
-- (This is known as the 'watched literal' optimization.)
--
-- The ReadWrite monad wraps the IO monad, to make debugging easier.
-- However, the solver assumes that the ReadWrite monad is stateless.
newtype ReadWrite level constraint a = ReadWrite (RWST (ReadWriteContext level constraint) [Assignment constraint] () IO a)
  deriving (Applicative, Functor, Monad, MonadIO)
  -- if level is Instance, read context will be nothing
  -- if level is Abstract, read context with be just the instantiation.

-- | Injects current constraint into given var
type Injector untyped c = untyped c -> IO ()

data ReadWriteContext level c where
  InstanceReadWriteContext
    :: Injector UntypedInstanceVar c
    -> ReadWriteContext Instance c
  AbstractReadWriteContext
    :: Instantiation
    -> ReadWriteMode -- todo: is this necessary?
    -> Injector UntypedAbstractVar c
    -> ReadWriteContext Abstract c

data ReadWriteMode = CreatingConstraint | RevisingConstraint
  deriving (Bounded, Enum, Eq, Ord, Read, Show)

data Assignment c = Assignment {
  assignmentVar :: UntypedInstanceVar c,
  assignmentEffect :: New Instance c (),
  assignmentUndo :: IO () }

-- phantom types
data Abstract
data Instance

newtype Solve c a = Solve (RWST (SolveContext c) () (SolveState c) IO a)
  deriving (Applicative, Functor, Monad, MonadIO)

data SolveContext c = SolveContext {
  _solveNext :: IORef Int,
  _solveLearner :: [c] -> IO [c] }

data SolveState c = SolveState {
  _assignedVars :: [AssignmentFrame c], -- head is most recently assigned
  _unassignedVars :: S.Set (UntypedInstanceVar c),
  _unrevisedInstanceConstraints :: Constraints Instance c,
  _unrevisedAbstractConstraints :: S.Set (Constraint Abstract c, Instantiation),
  _learntInstanceConstraints :: S.Set (Constraint Instance c),
  _learntAbstractConstraints :: S.Set (Constraint Abstract c) }

data AssignmentFrame c = AssignmentFrame {
  _frameUndo :: IO (),
  _frameUntriedValues :: [ReadWrite Instance c ()],
  _frameDecisionLevel :: Bool }

makeLenses ''Var
makeLenses ''VarCommon
makeLenses ''SolveState
makeLenses ''SolveContext
makeLenses ''AssignmentFrame
makeLenses ''NewContext

-- todo: document why I'm not including level as a type
-- parameter on Var.

class Level level where
  getInstanceVar :: String -> Var c a -> ReadWrite level c (InstanceVar c a)

  -- | Creates an new variable.
  newVar
    :: Ord a
    => Maybe String -- ^ name of the variable, for debugging
    -> Values constraint a -- ^ candidate assignments to the variable
    -> New level constraint (Var constraint a)

  -- | Returns the values which are not currently in direct violation
  -- of a constraint. A singleton value indicates that the variable
  -- has been assigned.
  readVar :: (Ord a) => Var constraint a -> ReadWrite level constraint (S.Set a)

  -- | Constrains a set of variables.
  newConstraint
    :: (Ord constraint)
    => Maybe String
    -> constraint
    -> ReadWrite level constraint Bool -- ^ Constraint testing function. Should return False only when the constraint can no longer be satisfied. It should call 'setVar' or 'shrinkVar' when it can make a deduction.
    -> New level constraint ()

instance Eq NameAndIdentity where (==) = (==) `on` identity
instance Ord NameAndIdentity where compare = compare `on` identity
instance Show NameAndIdentity where show = name

mkName :: (IdSource m, MonadIO m) => Maybe String -> String -> m NameAndIdentity
mkName mbName s = do
  name <- case mbName of
    Nothing -> do
      id <- nextId
      return $ "unnamed " ++ s ++ " " ++ show id
    Just x -> return x
  u <- liftIO newUnique
  return (NameAndIdentity name u)

orderValues
  :: (MonadState Satisfiable m, MonadIO m, Functor m)
  => Values c a
  -> m [(a, ValueEffect c a)]
orderValues values = z where
  z = do
    (cs, amakers) <- unzip . sortBy (compare `on` fst) <$> liftIO (mapM varCount (M.toList values))
    when (contradiction (map snd cs)) $ put Contradiction
    return amakers
  varCount (a, maker) = do
    stubState <- NewContext (return False) Nothing <$> newIORef 0
    -- todo: use assgnments in consideration of order
    stubValues <- newIORef (M.keysSet values)
    stubConstraints <- newIORef S.empty
    u <- newUnique
    let stubVar = VarInstance (InstanceVar Nothing stubValues stubConstraints (VarCommon (NameAndIdentity "stub variable" u) (M.toList values)))
    ((), satisfiable, newVars, _newConstraints, _assngments) <- runNewInstance (maker stubVar) stubState
    cost <- product <$> mapM (\x -> length <$> untypedInstanceVarValues x) newVars
    return ((cost :: Int, satisfiable), (a, maker))

varCommon (VarAbstract av) = _abstractVarCommon av
varCommon (VarInstance iv) = _instanceVarCommon iv

-- | Retrieves the name of the variable.
varName :: Var constraint a -> String
varName = name . _varCommonIdentity . varCommon

instance Eq (Var c a) where (==) = (==) `on` _varCommonIdentity . varCommon
instance Ord (Var c a) where compare = compare `on` _varCommonIdentity . varCommon
-- better to let the client determine the show instance. She can use
-- varName if she wants
-- instance Show (Var c a) where show = show . _varCommonIdentity . varCommon

instance Eq (InstanceVar constraint a) where (==) = (==) `on` _varCommonIdentity . _instanceVarCommon
instance Ord (InstanceVar constraint a) where compare = compare `on` _varCommonIdentity . _instanceVarCommon

instance Eq (AbstractVar constraint a) where (==) = (==) `on` _varCommonIdentity . _abstractVarCommon
instance Ord (AbstractVar constraint a) where compare = compare `on` _varCommonIdentity . _abstractVarCommon

instance Eq (UntypedInstanceVar c) where (==) = (==) `on` untypedInstanceVarIdentity
instance Ord (UntypedInstanceVar c) where compare = compare `on` untypedInstanceVarIdentity
instance Show (UntypedInstanceVar c) where show = show . untypedInstanceVarIdentity

untypeInstanceVar :: (Ord a) => InstanceVar c a -> UntypedInstanceVar c
untypeInstanceVar iv = UntypedInstanceVar ni setters constraints parent where
  (VarCommon ni allValues) = _instanceVarCommon iv
  candidates = readIORef (_instanceVarCandidates iv)
  setters = do
    cs <- candidates
    return . map (setVar (VarInstance iv)) . filter (flip S.member cs) . map fst $ allValues
  constraints = _instanceVarConstraints iv
  parent = first untypeAbstractVar <$> _instanceVarAbstractVar iv

untypeAbstractVar :: AbstractVar c a -> UntypedAbstractVar c
untypeAbstractVar av = UntypedAbstractVar (_varCommonIdentity $ _abstractVarCommon av) (_abstractVarAbstractConstraints av)

instance Eq (UntypedAbstractVar c) where (==) = (==) `on` untypedAbstractVarIdentity
instance Ord (UntypedAbstractVar c) where compare = compare `on` untypedAbstractVarIdentity
instance Show (UntypedAbstractVar c) where show = show . untypedAbstractVarIdentity

instance (Eq c) => Eq (Constraint l c) where (==) = (==) `on` constraintIdentity
instance (Ord c) => Ord (Constraint l c) where compare = compare `on` constraintIdentity
instance Show (Constraint l c) where show = show . constraintIdentity

-- | Creates a new constraint.
newConstraint'
  :: (IdSource m, MonadIO m)
  => Maybe String -- ^ optional name
  -> c -- ^ constraint
  -> ReadWrite l c Bool -- ^ resolver
  -> m (Constraint l c)
newConstraint' mbName c resolve = do
  name <- mkName mbName "constraint"
  let collectable = return False -- todo: make depend on values of variables
  uninject <- liftIO $ newIORef (return ())
  let reset = writeIORef uninject reset
  liftIO reset
  let c' = Constraint name (Just c) resolve (return False) uninject
  -- the question is: can I add "current constraint" to the context of the
  -- ReadWrite monad? Will I always have a constraint available to put
  -- into the context?
  -- in the arg to the solve function: no. the only other place is
  -- in newConstraint, where obviously it can
  -- so... can I make a dummy constraint for use in the solve function?
  -- runDependencies c (bounded resolve) -- todo: inject constraint into relevant vars
  return c'

class IdSource m where
  idSource :: m (IORef Int)

nextId :: (IdSource m, MonadIO m) => m Int
nextId = do
  ref <- idSource
  liftIO $ do
    ret <- readIORef ref
    modifyIORef ref (+1)
    return ret

contradiction :: [Satisfiable] -> Bool
contradiction = any (== Contradiction)

instance Functor (New Instance c)
instance Applicative (New Instance c)
instance Monad (New Instance c) where
  return x = NewInstance (return x)
  (NewInstance x) >>= f = NewInstance (unNewInstance . f =<< x) where
    unNewInstance (NewInstance m) = m
instance MonadIO (New Instance c) where
  liftIO = NewInstance . liftIO
instance MonadReader NewContext (New Instance c) where
  ask = NewInstance ask
  local f (NewInstance m) = NewInstance (local f m)
instance IdSource (InstanceInner c) where
  idSource = asks _newContextNext
instance IdSource (New Instance c) where
  idSource = NewInstance $ asks _newContextNext
instance MonadState Satisfiable (New Instance c) where
  state f = NewInstance (state f)

runNewInstance
  :: New Instance c a
  -> NewContext
  -- bool indicates if problem became unsatisfiable because of a newly
  -- constructed constraint that could not be satisfied
  -- true indicates the problem is still satisfiable
  -> IO (a, Satisfiable, [UntypedInstanceVar c], [Constraint Instance c], [Assignment c])
runNewInstance (NewInstance m) c = do
  (ret, b, (vars, cs, asgns)) <- runRWST m c Satisfiable
  return (ret, b, vars, cs, asgns)

instance Functor (New Abstract c) where
  fmap f (NewAbstract m) = NewAbstract (fmap g m) where
    g (x, y) = (f x, fmap f y)
instance Applicative (New Abstract c) where
  pure x = NewAbstract (pure (x, pure x))
  (NewAbstract f) <*> (NewAbstract x) = NewAbstract pair where
    pair = (,) <$> (fst <$> f <*> (fst <$> x)) <*> starstar (snd <$> f) (snd <$> x)
    starstar :: (Applicative f, Applicative g) => f (g (a -> b)) -> f (g a) -> f (g b)
    starstar f x = fmap (<*>) f <*> x
instance IdSource (AbstractInner c) where
  idSource = ask

-- | Lifts an IO action into New Abstract. For New Instance, just
-- use 'liftIO'.
abstractIO :: IO a -> New Abstract c a
abstractIO m = NewAbstract ((,) <$> liftIO m <*> return (liftIO m))

{-
instance MonadReader NewContext (New Abstract c) where
  ask = undefined -- ask = liftAbstract . ask
  local = undefined -- local f (NewAbstract m n) = NewAbstract (local f m) (\_ -> local f n)
  -}

runNewAbstract
  :: New Abstract c a
  -> IORef Int
  -> IO (a, Satisfiable, New Instance c a, [Constraint Abstract c])
runNewAbstract (NewAbstract inner) c = do
  ((ret, inst), s, constraints) <- runRWST inner c Satisfiable -- check bool!
  let instMaker = do
        i <- Instantiation <$> liftIO newUnique
        local (set newContextInstantiation (Just i)) inst
  return (ret, s, instMaker, constraints)

deriving instance Applicative (Init c)
deriving instance Functor (Init c)
deriving instance Monad (Init c)
deriving instance MonadIO (Init c)
deriving instance MonadWriter [Constraint Abstract c] (Init c)

runInit
  :: Init c a
  -> IO (a, Satisfiable, IORef Int, [UntypedInstanceVar c], [Constraint Instance c], [Constraint Abstract c])
runInit (Init m) = do
  n <- newIORef 0
  let context = NewContext (return False) Nothing n
  ((a, cas), b, vars, cis, asgns) <- runNewInstance (evalRWST m n ()) context
  return (a, b, n, vars, cis, cas)

-- | Groups a collection of abstract vars and constraints into
-- one, so that the pattern can be instantiated multiple times.
group :: New Abstract constraint a -> Init constraint (New Instance constraint a)
group m = do
  ref <- Init ask
  -- should not break on contradiction, since this group
  -- might never be used
  (_, _satisfiable, ret, cs) <- liftIO $ runNewAbstract m ref
  tell cs
  return ret

make :: New Instance constraint a -> Init constraint a
make = Init . lift

-- runAssign :: Assign c a -> IO (a, [Assignment])
runReadWriteInstance
  :: (Ord c)
  => ReadWrite Instance c a
  -> Constraint Instance c
  -> IO (a, [Assignment c])
runReadWriteInstance (ReadWrite m) c = do
  let inject = makeInjector untypedInstanceVarInstanceConstraints c
  evalRWST m (InstanceReadWriteContext inject) ()

askInstanceInjector :: ReadWrite Instance c (Injector UntypedInstanceVar c)
askInstanceInjector = ReadWrite (asks getInjector) where
  getInjector (InstanceReadWriteContext i) = i

runReadWriteAbstract
  :: (Ord c)
  => ReadWrite Abstract c a
  -> Instantiation
  -> ReadWriteMode
  -> Constraint Abstract c
  -> IO (a, [Assignment c])
runReadWriteAbstract (ReadWrite m) i ram c = do
  let inject = makeInjector untypedAbstractVarAbstractConstraints c
  evalRWST m (AbstractReadWriteContext i ram inject) ()

makeInjector :: (Ord c) => (untyped c -> IORef (Constraints l c)) -> Constraint l c -> Injector untyped c
makeInjector getConstraints c var = do
  let modifier = modifyIORef (getConstraints var)
  modifier (S.insert c)
  modifyIORef (constraintUninject c) (modifier (S.delete c) >>)

askAbstractInjector :: ReadWrite Abstract c (Injector UntypedAbstractVar c)
askAbstractInjector = ReadWrite (asks getInjector) where
  getInjector (AbstractReadWriteContext _ _ i) = i

askInstantiation = ReadWrite (asks (\(AbstractReadWriteContext i _ _) -> i))

modifyInstanceVar
  :: (Level level, Ord a)
  => (S.Set a -> S.Set a)
  -> InstanceVar c a
  -> ReadWrite level c ()
modifyInstanceVar mod iv = do
  orig <- liftIO $ do
    let ref = _instanceVarCandidates iv
    cs <- readIORef ref
    writeIORef ref (mod cs)
    return cs
  dirtyVar iv orig

-- record (in the ReadWrite monad) that a particular assignment
-- has been made (which includes the affected variable, the undo
-- operation, and the side effect creations that come as a consequence
-- of the assignment).
-- Side effects are only recorded when the variable has been
-- reduced to a single value.
dirtyVar :: (Level level, Ord a) => InstanceVar c a -> S.Set a -> ReadWrite level c ()
dirtyVar iv orig = ReadWrite $ do
  let ref = _instanceVarCandidates iv
  cs <- liftIO $ readIORef ref
  when (cs /= orig) $ do
  let internalBug = error
  let effect =
        case S.toList cs of
          [v] -> do
            case lookup v (_varCommonValues . _instanceVarCommon $ iv) of
              Nothing -> internalBug "one of candidates is invalid"
              Just eff -> eff (VarInstance iv)
          _ -> return ()
  tell [Assignment (untypeInstanceVar iv) effect (writeIORef ref orig)]

instance MonadReader (SolveContext c) (Solve c) where
  -- ask :: Solve c (SolveContext c)
  ask = Solve ask
  -- local :: (SolveContext c -> SolveContext c) -> Solve c a -> Solve c a
  local f (Solve m) = Solve (local f m)

instance MonadState (SolveState c) (Solve c) where state = Solve . state

evalSolve :: Solve c a -> SolveContext c -> SolveState c -> IO a
evalSolve (Solve m) context solveState = do
  (ret, ()) <- evalRWST m context solveState
  return ret

-- Attempts to find a satisfying assignment.
solve
  :: (Ord constraint)
  => ([constraint] -> New Instance constraint ()) -- ^ Constraint learning function, for conflict-directed constraint learning. The head of the given list is the constraint which produced a contradiction.
  -> Init constraint a -- ^ Problem definition. You should return the 'Var's that you plan on reading from (using 'readIvar') when a solution is found.
  -> (a -> ReadWrite Instance constraint b) -- ^ solution reader
  -> IO (Bool, b) -- ^ 'False' iff no solution exists. Values returned from 'readIvar' after solve completes are 'undefined' if 'False' is returned; otherwise they will be singleton sets containing the satisfying assignment.
solve learner definition = undefined {- do
  (ret, check, newstate, _avars, ivars, constraints) <- runInit definition
  mapM_ attach constraints
  let ss = SolveState [] (S.fromList ivars) (S.fromList constraints) S.empty
  completed <- evalSolve loop (SolveContext newstate learner check) ss
  return (completed, ret)
  -}

-- actually, it probably makes more sense to do the wiring on CREATION
-- of a clause... this way, there can be a single pathway for lining things up.
-- instance constraints when they are created, abstract constraints when
-- they are created. of course this means I will need to make
-- untypedAbstractVar, but I think I would have needed to do that anyway
attach :: (Ord c) => Constraint l c -> IO ()
attach c = undefined {- mapM_ insert . S.toList . constraintVars $ c where
  insert v = modifyIORef (varConstraints v) (S.insert c)
  -}

-- loop :: Solve c Bool
loop = undefined {- do
  mbc <- pop unrevisedConstraints
  debug $ "popped constraint: " ++ show mbc
  case mbc of
    Nothing -> do
      mbv <- pop unassignedVars
      debug $ "popped var: " ++ show mbv
      case mbv of
        Nothing -> return True
        Just v -> do
          vals <- liftIO $ untypedInstanceVarValues v
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
      -- todo: uninject constraint first
      (satisfiable, as) <- liftIO $ runReadWrite (constraintResolve c)
      assignedVars %= (reverse (map (\a -> AssignmentFrame (assignmentUndo a) [] False) as) ++)
      if not satisfiable then jumpback else do
      propagateEffects as
      -}

jumpback :: (Ord c) => Solve c Bool
jumpback = do
  vs <- use assignedVars
  let (pop,keep) = span (not . _frameDecisionLevel) vs
  -- todo: put constraint learning in here
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

choose x xs = undefined {- do
  -- todo: uninject constraint first
  ((), [a]) <- liftIO $ runReadWrite x
  assignedVars %= (AssignmentFrame (assignmentUndo a) xs True :)
  propagateEffects [a]
  -}

propagateEffects :: (Ord c) => [Assignment c] -> Solve c Bool
propagateEffects as = do
  -- check to see if any variables are now empty
  contradiction <- any null <$> liftIO (mapM (untypedInstanceVarValues . assignmentVar) as)
  if contradiction then jumpback else do
  -- create new vars and constraints from the assignments made
  (sat, newVars, newConstraints) <- runEffects as
  if not sat then jumpback else do
  debug $ "generated " ++ show (length newVars) ++ " new vars and " ++ show (length newConstraints) ++ " new constraints"
  unassignedVars %= S.union (S.fromList newVars)
  unrevisedInstanceConstraints %= S.union (S.fromList newConstraints)
  -- for each assignment made, re-run the constraints (instance and abstract)
  forM_ as $ \a -> do
    let uiv = assignmentVar a
    instanceConstraints <- liftIO . readIORef . untypedInstanceVarInstanceConstraints $ uiv
    unrevisedInstanceConstraints %= S.union instanceConstraints
    case untypedInstanceVarAbstractVar uiv of
      Nothing -> return ()
      Just (uav, inst) -> do
        acs <- liftIO . readIORef $ untypedAbstractVarAbstractConstraints uav
        unrevisedAbstractConstraints %= S.union (S.mapMonotonic (,inst) acs)
  loop

runEffects :: [Assignment c] -> Solve c (Bool, [UntypedInstanceVar c], [Constraint Instance c])
runEffects as = undefined {- do
  nextIdRef <- view solveNext
  liftIO $ do
    -- todo: change collectable to be dependent on whether
    -- the instigating variable has multiple candidate values.
    let context = NewContext (return False) Nothing nextIdRef
    out <- mapM ((flip runNewInstance context) . assignmentEffect) as
    return . (\(bs,vss,css) -> (all id bs, concat vss, concat css)) . unzip3 . map (\((),b,v,c) -> (b,v,c)) $ out
    -}

-- For some reason ghc can't infer this type.
pop :: MonadState s m => Simple Lens s (S.Set a) -> m (Maybe a)
pop set  = do
  s <- use set
  if S.null s then return Nothing else do
  let (v, s') = S.deleteFindMin s -- todo: better variable ordering
  set .= s'
  return (Just v)

instance Level Abstract where
  getInstanceVar _ (VarAbstract av) = do
    inst <- askInstantiation
    liftIO $ do
      instances <- readIORef (_abstractVarInstances av)
      let croak = throwIO . userError
      case M.lookup inst instances of
        Nothing -> croak $ "attempted to read from wrong abstract var"
        Just iv ->
          case _instanceVarAbstractVar iv of
            Nothing -> croak $ "internal bug: abstract var points to instance var, but reverse relationship does not exist"
            Just (av',inst') | av' /= av -> croak "internal bug: abstract var points to instance var which points to a DIFFERENT abstract var"
                             | inst /= inst' -> croak "internal bug: abstract var points to instance var but instance var's instantiation is different"
                             | otherwise -> return iv

  newVar mbName values = NewAbstract $ do
    -- make name (shared but slightly different)
    avName <- mkName mbName "abstract var"
    -- order values (shared)
    vals <- orderValues values
    -- create instance map (unique)
    instances <- liftIO $ newIORef M.empty
    -- create empty set of constraints (shared)
    constraints <- liftIO $ newIORef S.empty
    -- tellAbstractvar ret -- don't think this is actually necessary
    let u' = AbstractVar instances constraints $ VarCommon avName vals
    let iv = do
          var <- do
            -- very different name creation
            ivName <- do
              id <- nextId
              return . (("instance " ++ show id ++ " of ") ++) . name . _varCommonIdentity . _abstractVarCommon $ u'
            identity <- liftIO newUnique
            -- shared
            candidates <- liftIO . newIORef . M.keysSet $ values
            -- create empty set of constraints (shared)
            constraints <- liftIO $ newIORef S.empty
            mbInst <- view newContextInstantiation
            inst <- liftIO $ case mbInst of
              Nothing -> throwIO . userError . internalBug $ "no instantiation for instantiated variable"
              Just inst -> return inst
            let ret = InstanceVar (Just (u', inst)) candidates constraints (set varCommonIdentity (NameAndIdentity ivName identity) (_abstractVarCommon u'))
            liftIO . modifyIORef (_abstractVarInstances u') . M.insert inst $ ret
            return ret
          NewInstance $ tell ([untypeInstanceVar var], [], [])
          return (VarInstance var)
    return (VarAbstract u', iv)

  newConstraint mbName c resolve = NewAbstract $ do
    -- what I end up doing with fixme will probably depend on whether
    -- I can successfully implement newConstraint' or not
    c' <- newConstraint' mbName c resolve
    tell [c']
    -- agh... how do I wire myself up to the relevant abstract vars?
    -- what is readVar supposed to do without a particular instantiation?
    -- I suppose if there's no instantiation, readVar can just return ALL
    -- values, and the setVar and shrinkVar are no-ops
    -- its ok to ignore when _b is False (the pattern might never
    -- be instantiated), and when _assgns is not null (the assignments
    -- are for dummy variables anyway)
    i <- Instantiation <$> liftIO newUnique
    (_b, _assgns) <- liftIO $ runReadWriteAbstract resolve i CreatingConstraint c'
    return ((), return () {- is this right? -})

  -- todo: move this outside of the type class
  readVar (VarAbstract av) = do
    inject <- askAbstractInjector
    inst <- askInstantiation
    liftIO $ do
      inject (untypeAbstractVar av)
      instances <- readIORef (_abstractVarInstances av)
      let croak = throwIO . userError
      case M.lookup inst instances of
        Nothing -> croak $ "attempted to read from wrong abstract var"
        Just iv ->
          case _instanceVarAbstractVar iv of
            Nothing -> croak $ "internal bug: abstract var points to instance var, but reverse relationship does not exist"
            Just (av',inst') | av' /= av -> croak "internal bug: abstract var points to instance var which points to a DIFFERENT abstract var"
                             | inst /= inst' -> croak "internal bug: abstract var points to instance var but instance var's instantiation is different"
                             | otherwise -> readIORef (_instanceVarCandidates iv)

-- | Removes all but the given value from the variable's set of
-- candidate values. If the given value is already in violation of
-- another constraint, the set of associated values will become empty,
-- and the solver will begin backjumping.
setVar :: (Level level, Ord a) => Var constraint a -> a -> ReadWrite level constraint ()
setVar var val = modifyInstanceVar collapse =<< getInstanceVar "set" var where
  collapse cds | S.member val cds = S.singleton val
               | otherwise = S.empty

-- | Removes the given value from the variable's set of candidate values.
-- If the set becomes empty as a result, the solver will begin backjumping.
shrinkVar :: (Level level, Ord a) => Var constraint a -> a -> ReadWrite level constraint ()
shrinkVar var val = modifyInstanceVar (S.delete val) =<< getInstanceVar "shrink" var

internalBug = error

instance Level Instance where
  -- switch to putting
  -- type parameter into Var
  getInstanceVar _ (VarInstance iv) = return iv
  getInstanceVar usage (VarAbstract va) = illegalUseOfAbstractVariable usage va

  -- todo: move this outside of the type class
  newVar mbName values = do
    -- make name (shared but slightly different)
    name <- mkName mbName "instance var"
    -- order values (shared)
    vals <- orderValues values
    ret <- liftIO $ do
      -- create starting set of candidate values (shared, sorta)
      candidates <- newIORef . M.keysSet $ values
      -- create empty set of constraints (shared)
      constraints <- newIORef S.empty
      -- construct VarCommon (slightly different)
      return $ InstanceVar Nothing candidates constraints (VarCommon name vals)
    -- tell about creation (unique)
    NewInstance $ tell ([untypeInstanceVar ret], [], [])
    return (VarInstance ret)

  -- readIvar :: Ivar constraint a -> IO (S.Set a)
  readVar (VarInstance iv) = do
    inject <- askInstanceInjector
    liftIO $ do
      -- inject current constraint into variable, so that we
      -- can refire this constraint when the variable changes
      -- next
      inject (untypeInstanceVar iv)
      readIORef . _instanceVarCandidates $ iv

  newConstraint mbName c resolve = NewInstance $ do
    -- what I end up doing with fixme will probably depend on whether
    -- I can successfully implement newConstraint' or not
    c' <- newConstraint' mbName c resolve
    -- agh... how do I wire myself up to the relevant abstract vars?
    -- what is readVar supposed to do without a particular instantiation?
    -- I suppose if there's no instantiation, readVar can just return ALL
    -- values, and the setVar and shrinkVar are no-ops
    (b, assgns) <- liftIO $ runReadWriteInstance resolve c'
    when (not b) $ put Contradiction
    tell ([], [c'], assgns)

illegalUseOfAbstractVariable action va = liftIO . throwIO . userError . illegalArgument $ "cannot " ++ action ++ " abstract variable " ++ (name . _varCommonIdentity . _abstractVarCommon $ va) ++ " when inside 'ReadWrite Instance constraint' monad" where
  illegalArgument = error

debug = liftIO . putStrLn

-- todo: make sure that readVar, setVar, and shrinkVar all look at their ReadWrite
-- context and inject constraints into themselves if they need to

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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
  Level(..),
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
  ReadAssign(),
  New(),
  abstractIO,
  Init(),
  make,
) where

import Control.Applicative
import Control.Arrow
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
  _varCommonValues :: [(a, New Instance c ())] }

-- | An untyped container for both 'Avar's and 'Ivar's. Use it as an argument
-- to the 'newConstraint' function.
data Var constraint a
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

data InstanceVar c a = InstanceVar {
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
  untypedAbstractVarAbstractConstraints :: IORef (Constraints Abstract c) }

-- | An instance variable with the type stripped, so that it can
-- be stored in homogoneous collections.
data UntypedInstanceVar c = UntypedInstanceVar {
  untypedInstanceVarIdentity :: NameAndIdentity,
  -- | A sequence of calls to setVar for each remaining candidate.
  untypedInstanceVarValues :: IO [ReadAssign Instance c ()],
  untypedInstanceVarInstanceConstraints :: IORef (Constraints Instance c),
  untypedInstanceVarAbstractVar :: Maybe (UntypedAbstractVar c, Instantiation) }

-- is there a way to keep the types of the vars in this data structure?
-- maybe wrap up the uses of the Constraint somehow?
data Constraint l c = Constraint {
  constraintIdentity :: NameAndIdentity,
  constraintConstraint :: Maybe c, -- if Nothing, then this constraint is a no-good generated by the solver (not by the client). (The no-good values are embedded in the resolver.)
  constraintResolve :: ReadAssign l c Bool, 

  -- | False for problem clauses, True for learnt clauses, otherwise depends
  -- on the variable which created it.
  constraintCollectable :: IO Bool }

type AbstractInner c = RWST (IORef Int) [Constraint Abstract c] () IO
type InstanceInner c = RWST NewContext ([UntypedInstanceVar c], [Constraint Instance c]) () IO

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
-- Implementations should be idempotent. That is, if a ReadAssign monad
-- is run twice (and no variables have changed in between), it should
-- read from the same variables and leave them in the same state
-- as if it were only run once. A constraint will inject itself into
-- each variable that it reads from, so that it can be re-fired
-- when that variable changes. Failing to maintain the idempotency invariant
-- can cause the solver to return incorrect assignments.
--
-- Idempotency is not required when the read variables have been changed
-- by different constraints or the solver itself. It is permissible
-- and encouraged for the ReadAssign monad to exit early
-- when it determies that the constraint is still satisfiable.
-- For example, boolean disjunctions can exit after reading only two
-- variables, if both of their literals can still be assigned true.
-- (This is known as the 'watched literal' optimization.)
--
-- The ReadAssign monad wraps the IO monad, to make debugging easier.
-- However, the solver assumes that the ReadAssign monad is stateless.
newtype ReadAssign level constraint a = ReadAssign (RWST (MaybeInstantiation level) [Assignment constraint] () IO a)
  deriving (Applicative, Functor, Monad, MonadIO)
  -- if level is Instance, read context will be nothing
  -- if level is Abstract, read context with be just the instantiation.

data MaybeInstantiation level where
  NothingInstantiation :: MaybeInstantiation Instance
  JustInstantiation :: Instantiation -> MaybeInstantiation Abstract

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
  _unrevisedInstanceConstraints :: S.Set (ReadAssign Instance c Bool),
  _unrevisedAbstractConstraints :: S.Set (ReadAssign Abstract c Bool, Instantiation),
  _learntInstanceConstraints :: S.Set (Constraint Instance c),
  _learntAbstractConstraints :: S.Set (Constraint Abstract c) }

data AssignmentFrame c = AssignmentFrame {
  _frameUndo :: IO (),
  _frameUntriedValues :: [ReadAssign Instance c ()],
  _frameDecisionLevel :: Bool }

makeLenses ''Var
makeLenses ''VarCommon
makeLenses ''SolveState
makeLenses ''SolveContext
makeLenses ''AssignmentFrame
makeLenses ''NewContext

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
type Values constraint a = M.Map a (New Instance constraint ())

class Level level where
  -- | Creates an new variable.
  newVar
    :: Ord a
    => Maybe String -- ^ name of the variable, for debugging
    -> Values constraint a -- ^ candidate assignments to the variable
    -> New level constraint (Var constraint a)

  -- | Returns the values which are not currently in direct violation
  -- of a constraint. A singleton value indicates that the variable
  -- has been assigned.
  readVar :: Var constraint a -> ReadAssign level constraint (S.Set a)

  -- | Removes all but the given value from the variable's set of
  -- candidate values. If the given value is already in violation of
  -- another constraint, the set of associated values will become empty,
  -- and the solver will begin backjumping.
  setVar :: (Ord a) => Var constraint a -> a -> ReadAssign level constraint ()

  -- | Removes the given value from the variable's set of candidate values.
  -- If the set becomes empty as a result, the solver will begin backjumping.
  shrinkVar :: (Ord a) => Var constraint a -> a -> ReadAssign level constraint ()

  -- | Constrains a set of variables.
  newConstraint
    :: Maybe String
    -> constraint
    -> ReadAssign level constraint Bool -- ^ Constraint testing function. Should return False only when the constraint can no longer be satisfied. It should call 'setVar' or 'shrinkVar' when it can make a deduction.
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
  :: Values c a
  -> IO [(a, New Instance c ())]
orderValues values = z where
  z = map snd . sortBy (compare `on` fst) <$> mapM varCount (M.toList values)
  varCount (a, maker) = do
    stubState <- NewContext (return False) Nothing <$> newIORef 0
    ((), newVars, _newConstraints) <- runNewInstance maker stubState
    cost <- product <$> mapM (\x -> length <$> untypedInstanceVarValues x) newVars
    return (cost :: Int, (a, maker))

varCommon (VarAbstract av) = _abstractVarCommon av
varCommon (VarInstance iv) = _instanceVarCommon iv

-- | Retrieves the name of the variable.
varName :: Var constraint a -> String
varName = name . _varCommonIdentity . varCommon

instance Eq (Var c a) where (==) = (==) `on` _varCommonIdentity . varCommon
instance Ord (Var c a) where compare = compare `on` _varCommonIdentity . varCommon
instance Show (Var c a) where show = show . _varCommonIdentity . varCommon

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
untypeAbstractVar av = UntypedAbstractVar (_abstractVarAbstractConstraints av)

instance (Eq c) => Eq (Constraint l c) where (==) = (==) `on` constraintIdentity
instance (Ord c) => Ord (Constraint l c) where compare = compare `on` constraintIdentity
instance Show (Constraint l c) where show = show . constraintIdentity

-- | Creates a new constraint.
newConstraint'
  :: (IdSource m, MonadIO m)
  => Maybe String -- ^ optional name
  -> c -- ^ constraint
  -> ReadAssign l c Bool -- ^ resolver
  -> m (Constraint l c)
newConstraint' mbName c resolve = do
  name <- mkName mbName "constraint"
  let collectable = return False -- todo: make depend on values of variables
  let c' = Constraint name (Just c) resolve (return False)
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
instance IdSource (New Instance c) where
  idSource = NewInstance (asks _newContextNext)

runNewInstance
  :: New Instance c a
  -> NewContext
  -> IO (a, [UntypedInstanceVar c], [Constraint Instance c])
runNewInstance (NewInstance m) c = do
  (ret, (vars, cs)) <- evalRWST m c ()
  return (ret, vars, cs)

tellUntypedInstanceVar :: UntypedInstanceVar c -> New Instance c ()
tellUntypedInstanceVar var = NewInstance $ tell ([var], [])

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
  -> IO (a, New Instance c a, [Constraint Abstract c])
runNewAbstract (NewAbstract inner) c = do
  ((ret, inst), constraints) <- evalRWST inner c ()
  let instMaker = do
        i <- Instantiation <$> liftIO newUnique
        local (set newContextInstantiation (Just i)) inst
  return (ret, instMaker, constraints)

deriving instance Applicative (Init c)
deriving instance Functor (Init c)
deriving instance Monad (Init c)
deriving instance MonadIO (Init c)
deriving instance MonadWriter [Constraint Abstract c] (Init c)

runInit
  :: Init c a
  -> IO (a, IORef Int, [UntypedInstanceVar c], [Constraint Instance c], [Constraint Abstract c])
runInit (Init m) = do
  n <- newIORef 0
  let context = NewContext (return False) Nothing n
  ((a, cas), vars, cis) <- runNewInstance (evalRWST m n ()) context
  return (a, n, vars, cis, cas)

-- | Groups a collection of abstract vars and constraints into
-- one, so that the pattern can be instantiated multiple times.
group :: New Abstract constraint a -> Init constraint (New Instance constraint a)
group m = do
  ref <- Init ask
  (_, ret, cs) <- liftIO $ runNewAbstract m ref
  tell cs
  return ret

make :: New Instance constraint a -> Init constraint a
make = Init . lift

-- runAssign :: Assign c a -> IO (a, [Assignment])
runReadAssignInstance :: ReadAssign Instance c a -> IO (a, [Assignment c])
runReadAssignInstance (ReadAssign m) = evalRWST m NothingInstantiation ()

runReadAssignAbstract
  :: ReadAssign Abstract c a
  -> Instantiation
  -> IO (a, [Assignment c])
runReadAssignAbstract (ReadAssign m) i = evalRWST m (JustInstantiation i) ()

modifyInstanceVar
  :: (Ord a)
  => InstanceVar c a
  -> (S.Set a -> S.Set a)
  -> ReadAssign Instance c ()
modifyInstanceVar iv mod = do
  orig <- liftIO $ do
    let ref = _instanceVarCandidates iv
    cs <- readIORef ref
    writeIORef ref (mod cs)
    return cs
  dirtyVar iv orig

dirtyVar :: (Ord a) => InstanceVar c a -> S.Set a -> ReadAssign Instance c ()
dirtyVar iv orig = ReadAssign $ do
  let ref = _instanceVarCandidates iv
  cs <- liftIO $ readIORef ref
  when (cs /= orig) $ do
  let internalBug = error
  let effect =
        case S.toList cs of
          [v] -> do
            case lookup v (_varCommonValues . _instanceVarCommon $ iv) of
              Nothing -> internalBug "one of candidates is invalid"
              Just x -> x
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
  -> Init constraint a -- ^ Problem definition. You should return the 'Ivar's that you plan on reading from (using 'readIvar') when a solution is found.
  -> IO (Bool, a) -- ^ 'False' iff no solution exists. Values returned from 'readIvar' after solve completes are 'undefined' if 'False' is returned; otherwise they will be singleton sets containing the satisfying assignment.
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
      (satisfiable, as) <- liftIO $ runReadAssign (constraintResolve c)
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
  ((), [a]) <- liftIO $ runReadAssign x
  assignedVars %= (AssignmentFrame (assignmentUndo a) xs True :)
  propagateEffects [a]
  -}

propagateEffects :: [Assignment c] -> Solve c Bool
propagateEffects as = undefined {- do
  -- check to see if any variables are now empty
  contradiction <- any null <$> liftIO (mapM (untypedInstanceVarValues . assignmentVar) as)
  if contradiction then jumpback else do
  -- create new vars and constraints from the assignments made
  (newVars, newConstraints) <- runEffects as
  debug $ "generated " ++ show (length newVars) ++ " new vars and " ++ show (length newConstraints) ++ " new constraints"
  unassignedVars %= S.union (S.fromList newVars)
  unrevisedInstanceConstraints %= S.union (S.fromList newConstraints)
  -- for each assignment made, re-run the constraints (instance and abstract)
  forM_ as $ \a -> do
    let uiv = assignmentVar a
    let getConstraints f = map (a,) <$> (liftIO $ readIORef (varConstraints . f . assignmentVar $ a))
    cs1 <- getConstraints uivarVar
    cs2 <- getConstraints $ _instanceVarAbstractVar
    cs1 <- map (a,) <$> (liftIO $ undefined)
    VarInstance x ->
      fst = _instanceConstraints . readIORef (_instanceVarState iv
      include <$> case _instanceVarAbstractVar x of
                    Nothing -> _instanceConstraints
                    Just (av, i) -> 
                    _instanceVarCommon
    unrevisedConstraints %= S.union (map (a,) cs1) . S.union cs2
  loop
  -}

runEffects :: [Assignment c] -> Solve c ([UntypedInstanceVar c], [Constraint Instance c])
runEffects as = do
  nextIdRef <- view solveNext
  liftIO $ do
    -- todo: change collectable to be dependent on whether
    -- the instigating variable has multiple candidate values.
    let context = NewContext (return False) Nothing nextIdRef
    out <- mapM ((flip runNewInstance context) . assignmentEffect) as
    return . (\(vss,css) -> (concat vss, concat css)) . unzip . map (\((),v,c) -> (v,c)) $ out

-- For some reason ghc can't infer this type.
pop :: MonadState s m => Simple Lens s (S.Set a) -> m (Maybe a)
pop set  = do
  s <- use set
  if S.null s then return Nothing else do
  let (v, s') = S.deleteFindMin s -- todo: better variable ordering
  set .= s'
  return (Just v)

instance Level Abstract where
  newVar mbName values = NewAbstract $ do
    avName <- mkName mbName "abstract var"
    vals <- liftIO $ orderValues values
    instances <- liftIO $ newIORef M.empty
    constraints <- liftIO $ newIORef S.empty
    -- tellAbstractvar ret -- don't think this is actually necessary
    let u' = AbstractVar instances constraints $ VarCommon avName vals
    let iv = do
          var <- do
            ivName <- do
              id <- nextId
              return . (("instance " ++ show id ++ " of ") ++) . name . _varCommonIdentity . _abstractVarCommon $ u'
            identity <- liftIO newUnique
            candidates <- liftIO . newIORef . M.keysSet $ values
            constraints <- liftIO $ newIORef S.empty
            mbInst <- view newContextInstantiation
            inst <- liftIO $ case mbInst of
              Nothing -> throwIO . userError . internalBug $ "no instantiation for instantiated variable"
              Just inst -> return inst
            let ret = InstanceVar (Just (u', inst)) candidates constraints (set varCommonIdentity (NameAndIdentity ivName identity) (_abstractVarCommon u'))
            liftIO . modifyIORef (_abstractVarInstances u') . M.insert inst $ ret
            return ret
          NewInstance $ tell ([untypeInstanceVar var], [])
          return (VarInstance var)
    return (VarAbstract u', iv)

  newConstraint mbName c resolve = NewAbstract z where
    z = do
      -- what I end up doing with fixme will probably depend on whether
      -- I can successfully implement newConstraint' or not
      c' <- newConstraint' mbName c resolve
      tell [c']
      return ((), return () {- is this right? -})
    -- unNewAbstract (NewAbstract x) = x

internalBug = error

instance Level Instance where
  newVar mbName values = do
    name <- mkName mbName "instance var"
    ret <- liftIO $ do
      vals <- orderValues values
      candidates <- newIORef . M.keysSet $ values
      constraints <- newIORef S.empty
      return $ InstanceVar Nothing candidates constraints (VarCommon name vals)
    tellUntypedInstanceVar (untypeInstanceVar ret)
    return (VarInstance ret)

  -- readIvar :: Ivar constraint a -> IO (S.Set a)
  readVar (VarInstance iv) = liftIO . readIORef . _instanceVarCandidates $ iv

  -- setVar :: (Ord a) => Ivar constraint a -> a -> Assign constraint ()
  setVar (VarInstance iv) v = modifyInstanceVar iv collapse where
    collapse cds | S.member v cds = S.singleton v
                 | otherwise = S.empty
  setVar (VarAbstract va) _ = illegalUseOfAbstractVariable "set" va

  -- shrinkIvar :: (Ord a) => Ivar constraint a -> a -> Assign constraint ()
  shrinkVar (VarInstance iv) v = modifyInstanceVar iv (S.delete v)
  shrinkVar (VarAbstract va) _ = illegalUseOfAbstractVariable "shrink" va

illegalUseOfAbstractVariable action va = liftIO . throwIO . userError . illegalArgument $ "cannot " ++ action ++ " abstract variable " ++ (name . _varCommonIdentity . _abstractVarCommon $ va) ++ " when inside 'ReadAssign Instance constraint' monad" where
  illegalArgument = error

debug = liftIO . putStrLn

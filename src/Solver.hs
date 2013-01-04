{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes #-}
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

  -- * Operations on variables and constraints.
  Level(..),

  -- * The two levels
  Abstract(),
  Instance(),

  instantiate,

  -- * Monads
  New(),
  ReadAssign(),
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

-- | An untyped container for both 'Avar's and 'Ivar's. Use it as an argument
-- to the 'newConstraint' function.
data Var level constraint a = Var {
  _varCommon :: VarCommon level constraint a,
  _varDistinct :: VarDistinct level constraint a }

instance Eq (Var l c a) where (==) = (==) `on` varIdentity . _varCommon
instance Ord (Var l c a) where compare = compare `on` varIdentity . _varCommon
instance Show (Var l c a) where show = show . varIdentity . _varCommon

data VarCommon c a = VarCommon {
  varIdentity :: NameAndIdentity,

  -- Ordered by cheapest choice, that is, if x comes before y,
  -- then the product of the sizes of x's generated variables will
  -- be no more than y's product.
  -- (constraints generated is not a factor in ordering, since they
  -- don't actually make the problem larger)
  _values :: [(a, New Instance c ())],

  varCommonState :: IORef (VarCommonState c a) }

-- can be used both for vars and constraints!
data NameAndIdentity = NameAndIdentity {
  name :: String,
  identity :: Unique }

instance Eq NameAndIdentity where (==) = (==) `on` identity
instance Ord NameAndIdentity where compare = compare `on` identity
instance Show NameAndIdentity where show = name

data VarCommonState c a = VarState {
  -- | A partial set of constraints constraining this var. Constraints not in this set
  -- but which constrain this var do not need to be revised when this var
  -- is assigned.
  -- For example, if the constraint is a \/ b \/ c, then I should put the
  -- constraint in two of the vars, but I do not need to put it in the
  -- third, since I can only make a deduction when there is one
  -- remaining unassigned variable.
  -- todo: actually make this a partial collection
  _abstractConstraints :: M.Map (Constraint c) (ReadAssign Abstract c Bool)
  }

data VarDistinct l c a where
  VarAbstract :: IORef (AbstractVar c a) -> VarDistinct Abstract c a
  VarInstance :: InstanceVar c a -> VarDistinct Instance c a

toInstanceVar :: Var Instance c a -> InstanceVar c a
toInstanceVar = deCons . _varDistinct where
  deCons x = case x of
               VarInstance z -> z

toAbstractVar :: Var Abstract c a -> IORef (AbstractVar c a)
toAbstractVar = deCons . _varDistinct where
  deCons x = case x of
               VarAbstract z -> z

data AbstractVar c a = AbstractVar {
  _instances :: M.Map Instantiation (Var Instance c a) }

data InstanceVar c a = InstanceVar {
  _abstractVar :: Maybe (Var Abstract c a),
  _instanceVarState :: IORef (InstanceVarState c a) }

instanceState = _instanceVarState . toInstanceVar

data InstanceVarState c a = InstanceVarState {
  -- | If empty, problem is in conflict.
  -- If singleton, then a value has been chosen.
  -- If more than one item, a choice has yet to be made.
  _candidates :: S.Set a } {- ,

  -- | Everytime ivarCandidates is reduced to a singleton, that value is
  -- added here. If it already exist in here, then the associated (New ())
  -- in the Avar is not executed, since we know it has already been executed
  -- once. If a constraint using this ivar is garbage collected, then the
  -- value is removed from here, so that future re-assignments will
  -- re-instantiate the constraint.
  _previousAssignments :: M.Map a (S.Set (Constraint constraint)) } -- todo: this value is still not being checked
  -}

-- | An instance variable with the type stripped, so that it can
-- be stored in homogoneous collections.
data UntypedVar c = UntypedVar {
  uvarIdentity :: NameAndIdentity,
  -- | A sequence of calls to setVar for each remaining candidate.
  uvarValues :: IO [ReadAssign Instance c ()] }

instance Eq (UntypedVar c) where (==) = (==) `on` uvarIdentity
instance Ord (UntypedVar c) where compare = compare `on` uvarIdentity
instance Show (UntypedVar c) where show = show . uvarIdentity

-- is there a way to keep the types of the vars in this data structure?
-- maybe wrap up the uses of the Constraint somehow?
data Constraint c = Constraint {
  constraintIdentity :: NameAndIdentity,
  constraintConstraint :: Maybe c, -- if Nothing, then this constraint is a no-good generated by the solver (not by the client).
  -- constraintResolve :: ReadAssign l c Bool, -- hmm... do I need this? I think I need it for abstract constraints: it's useful for 

  -- | False for problem clauses, True for learnt clauses, otherwise depends
  -- on the variable which created it.
  constraintCollectable :: IO Bool }

instance (Eq c) => Eq (Constraint c) where (==) = (==) `on` constraintIdentity
instance (Ord c) => Ord (Constraint c) where compare = compare `on` constraintIdentity
instance Show (Constraint c) where show = show . constraintIdentity

-- | A monad for creating variables and constraints.
newtype New level constraint a = New (RWST (NewContext level) [Either (UntypedVar constraint) (Constraint constraint)] () IO a)
  deriving (Applicative, Functor, Monad, MonadIO)

data NewContext l = NewContext {
  _collectable :: IO Bool,
  _instantiation :: MaybeInstantiation l,
  _newState :: IORef NewState }

data MaybeInstantiation l where
  JustInstantiation :: Instantiation -> MaybeInstantiation Abstract -- although you want to create an instance value, you're doing it in the context of a (New Abstract) monad
  NothingInstantiation :: MaybeInstantiation l -- both abstract and instance variables can be created without an instantiation

data NewState = NewState {
  _nextAbstractId :: Int,
  _nextInstanceId :: Int,
  _nextConstraintId :: Int }

newtype Pattern constraint a = Pattern (New Instance constraint a)
  -- NOT a monad!

newtype Init constraint a = Init (ReaderT Bool {- making or grouping -}

-- | A monad for making assignments to variables. A constraint calls 'readVar'
-- to determine if one of its variables can be deduced from the others,
-- in which case it calls 'setVar'.
newtype ReadAssign level constraint a = ReadAssign (RWST (MaybeInstantiation level) [Assignment level constraint] () IO a)
  deriving (Applicative, Functor, Monad, MonadIO)

data Assignment l c = Assignment {
  assignmentVar :: UntypedVar c,
  assignmentEffect :: New l c (),
  assignmentUndo :: IO () }

newtype Instantiation = Instantiation {
  instantiationIdentity :: Unique }
  deriving (Eq, Ord)

-- phantom types
data Abstract
data Instance

newtype Solve c a = Solve (RWST (SolveContext c) () (SolveState c) IO a)
  deriving (Applicative, Functor, Monad, MonadIO)

data SolveContext c = SolveContext {
  _solveNewState :: IORef NewState,
  _learner :: [c] -> IO [c] }

data SolveState c = SolveState {
  _assignedVars :: [AssignmentFrame c], -- head is most recently assigned
  _unassignedVars :: S.Set (UntypedVar c),
  _unrevisedInstanceConstraints :: S.Set (ReadAssign Instance c Bool),
  _unrevisedAbstractConstraints :: S.Set (ReadAssign Abstract c Bool),
  _learntConstraints :: S.Set (Constraint c) }

instance MonadReader (SolveContext c) (Solve c) where
  -- ask :: Solve c (SolveContext c)
  ask = Solve ask
  -- local :: (SolveContext c -> SolveContext c) -> Solve c a -> Solve c a
  local f (Solve m) = Solve (local f m)

instance MonadState (SolveState c) (Solve c) where state = Solve . state

data AssignmentFrame c = AssignmentFrame {
  _frameUndo :: IO (),
  _frameUntriedValues :: [ReadAssign Instance c ()],
  _frameDecisionLevel :: Bool }

makeLenses ''Var
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
  (ret, check, newstate, _avars, ivars, constraints) <- runInit definition
  mapM_ attach constraints
  let ss = SolveState [] (S.fromList ivars) (S.fromList constraints) S.empty
  completed <- evalSolve loop (SolveContext newstate learner check) ss
  return (completed, ret)

attach :: (Ord c) => Constraint c -> IO ()
attach c = mapM_ insert . S.toList . constraintVars $ c where
  insert v = modifyIORef (varConstraints v) (S.insert c)

-- loop :: Solve c Bool
loop = do
  mbc <- pop unrevisedConstraints
  debug $ "popped constraint: " ++ show mbc
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
      (satisfiable, as) <- liftIO $ runReadAssign (constraintResolve c)
      assignedVars %= (reverse (map (\a -> AssignmentFrame (assignmentUndo a) [] False) as) ++)
      if not satisfiable then jumpback else do
      propagateEffects as

nop = return ()

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

choose x xs = do
  ((), [a]) <- liftIO $ runReadAssign x
  assignedVars %= (AssignmentFrame (assignmentUndo a) xs True :)
  propagateEffects [a]

-- propagateEffects :: [Assignment c] -> Solve c ()
propagateEffects as = do
  contradiction <- any null <$> liftIO (mapM (uivarValues . assignmentVar) as)
  if contradiction then jumpback else do
  (newVars, newConstraints) <- runEffects as
  debug $ "generated " ++ show (length newVars) ++ " new vars and " ++ show (length newConstraints) ++ " new constraints"
  unassignedVars %= S.union (S.fromList newVars)
  unrevisedConstraints %= S.union (S.fromList newConstraints)
  forM_ as $ \a -> do
    let getConstraints f = map (a,) <$> (liftIO $ readIORef (varConstraints . f . assignmentVar $ a))
    cs1 <- getConstraints uivarVar
    cs2 <- getConstraints uivarAvar
    unrevisedConstraints %= S.union (map (a,) cs1) . S.union cs2
  loop

runEffects :: [Assignment c] -> Solve c ([UntypedVar c], [Constraint c])
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

class Level l where
  -- | Creates an new variable.
  newVar
    :: Maybe String -- ^ name of the variable, for debugging
    -> Values constraint a -- ^ candidate assignments to the variable
    -> New level constraint (Var level constraint a)

  -- | Returns the values which are not currently in direct violation
  -- of a constraint. A singleton value indicates that the variable
  -- has been assigned.
  readVar :: Var level constraint a -> ReadAssign level constraint (S.Set a)

  -- | Removes all but the given value from the variable's set of
  -- candidate values. If the given value is already in violation of
  -- another constraint, the set of associated values will become empty,
  -- and the solver will begin backjumping.
  setVar :: Var level constraint a -> a -> ReadAssign level constraint ()

  -- | Removes the given value from the variable's set of candidate values.
  -- If the set becomes empty as a result, the solver will begin backjumping.
  shrinkVar :: Var level constraint a -> a -> ReadAssign level constraint ()

  -- | Constrains a set of variables.
  newConstraint
    :: constraint
    -> ReadAssign level constraint Bool -- ^ Constraint testing function. Should return False only when the constraint can no longer be satisfied. It should call 'setVar' or 'shrinkVar' when it can make a deduction.
    -> New level constraint ()

  newConstraint c watched resolve = do
    id <- query nextConstraintId
    newNamedConstraint ("unnamed constraint " ++ show id) c watched resolve

  -- | Like 'newConstraint', but allows you to attach a custom name for
  -- debugging purposes.
  newNamedConstraint name c watched resolve =
    tellConstraint (Constraint name c watched resolve)

newVarCommon
  :: Maybe String
  -> String
  -> Simple Lens NewState Int
  -> Values c a
  -> New (VarCommon l c a)
newVarCommon mbName prefix lens values = z where
  z = do
    name <- case mbName of
              Nothing -> ("unnamed " ++ prefix ++ " var " ++) <$> varquery lens
              Just x -> return x
    identity <- newUnique
    values' <- map snd . sortBy (compare `on` fst) <$> mapM varCount (M.toList vs)
    state <- newIORef M.empty
    return $ VarCommon (NameAndIdentity name identity) values' 
        
  varCount (a, maker) = liftIO $ do
    stubState <- NewContext (return False) NothingInstantiation <$> newIORef (NewState 0 0 0)
    ((), newVars, _newConstraints) <- runNew maker stubState
    cost <- product <$> mapM (\x -> length <$> uvarValues x) newVars
    return (cost :: Int, (a, maker))

instance Level Abstract where
{-
newAvar
  :: (Ord a) => M.Map a (Ivar constraint a -> New constraint ()) -- ^ A map from values to side effects. If you do not need a side effect, just use 'return ()'.
  -> Init constraint (Avar constraint a)
  -}
  newVar vs = do
    id <- liftNew $ query nextAvarId
    newNamedAvar ("unnamed avar " ++ show id) vs

  newVar mbName values = z where
   -- so... the odd there here, is that if we are in an instantiation context,
   -- we need to create an instance var, instead of an abstract var (!),
   -- and tell and return that
    z = do
      inst <- view instantiation
      common <-
        case inst of
          NothingInstantiation -> newVarCommon mbName nextAbstractId "abstract" values
          JustInstantiation i -> do
            instanceVar <- newVar mbName values
            return (over varDistinct setParent
      common <- newVarCommon mbName nextAbstractId
      ret <- liftIO $ Avar vs' (readIORef making) <$> newVar name
      tellAbstractvar ret
      case inst of
        NothingInstantiation -> 
      return ret

instance Level Instance where
  newVar mbName values = do
    ret <- liftIO $ do
      common <- newVarCommon mbName nextInstanceId "instance" values
      state <- newIORef . InstanceVarState . M.keysSet $ values
      return . Var common . VarInstance . InstanceVar Nothing $ state
    tellUntypedVar (untype ret)
    return ret

  -- readIvar :: Ivar constraint a -> IO (S.Set a)
  readVar iv = _candidates <$> readIORef (instanceState iv)

  -- setVar :: (Ord a) => Ivar constraint a -> a -> Assign constraint ()
  setVar iv v = modifyIvar iv collapse where
    collapse cds | S.member v cds = S.singleton v
                 | otherwise = S.empty

  -- shrinkIvar :: (Ord a) => Ivar constraint a -> a -> Assign constraint ()
  shrinkVar iv v = modifyIvar iv (S.delete v)

modifyIvar :: Var Instance c a -> (S.Set a -> S.Set a) -> ReadAssign Instance c ()
modifyIvar iv mod = do
  orig <- liftIO $ do
    let ref = instanceState iv
    candidates <- _candidates <$> readIORef ref
    modifyIORef ref (over candidates mod)
    return candidates
  dirtyVar iv orig

-- | Retrieves the name of the variable.
varName :: Var level constraint a -> String
varName = name . _varCommon

untype :: Var Instance c a -> UntypedVar c
untype iv = UntypedVar ni setters where
  ni = varIdentity . _varCommon $ iv
  vi = toInstanceVar iv
  allValues = map head . _values . _varCommon $ iv
  candidates = _candidates <$> readIORef (instanceState iv)
  setters = do
    cs <- candidates
    return . filter (flip S.member cs) $ allValues

runNew
  :: New l c a
  -> NewContext l
  -> IO (a, [(UntypedVar c)], [Constraint c])
runNew (New m) flag newstate collectable = do
  (ret, mix) <- evalRWST m (NewContext newstate) ()
  let (ims, cs) = partitionEithers mix
  return (ret, ims, cs)

-- tellConstraint :: (IO Bool -> Constraint c) -> New c ()
tellConstraint = New . tell . (:[]) . Right

tellUntypedVar :: (UntypedVar c) -> New c ()
tellUntypedVar = New . tell . (:[]) . Left

query :: (Num a) => Simple Lens NewState a -> New c a
query lens = do
  ref <- New (asks _newState)
  liftIO $ do
    ret <- view lens <$> readIORef ref
    modifyIORef ref (over lens (+1))
    return ret

-- | Instantiates all abstract variables created in the argument as
-- instance variables, and associates them with the constraints created
-- in the argument.
instantiate :: New Abstract constraint a -> New Instance constraint a
instantiate m = do
  ns <- view newState
  liftIO $ do
    let collectable = return False -- todo: make dependent on the variables
    i <- Instantiation <$> newUnique
    (ret, utvs, cs) <- runNew m (NewContext collectable (JustInstantiation i) ns)
    New . tell . map Right $ cs
    New . tell . map Left $ utvs
    return ret

-- runAssign :: Assign c a -> IO (a, [Assignment])
runInstanceReadAssign (ReadAssign m) = evalRWST NothingInstantiation ()
runAbstractReadAssign (ReadAssign m) i = evalRWST (JustInstantiation i) ()

dirtyVar :: Var Instance c a -> S.Set a -> ReadAssign Instance c ()
dirtyVar var orig = ReadAssign $ do
  let iv = toInstanceVar var
  let ref = _instanceVarState iv
  candidates <- liftIO $ _candidates <$> readIORef ref
  when (candidates /= orig) $ do
  let internalBug = error
  let effect =
        case S.toList candidates of
          [v] -> do
            case lookup v (_values . _varCommon $ iv) of
              Nothing -> internalBug "one of candidates is invalid"
              Just x -> x
          _ -> nop
  tell [Assignment (untype iv) (effect iv) (modifyIORef ref (set candidates orig))]

evalSolve :: Solve c a -> SolveContext c -> SolveState c -> IO a
evalSolve (Solve m) context solveState = do
  (ret, ()) <- evalRWST m context solveState
  return ret

debug = liftIO . putStrLn

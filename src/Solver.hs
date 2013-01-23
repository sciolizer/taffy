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
  Values,

  -- * The two levels
  Instance(),

  -- * Operations on variables and constraints.
  Level(),
  newVar,
  readVar,
  setVar,
  shrinkVar,
  varName,
  newInstanceConstraint,
  newAbstractConstraint,

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
-- import Control.Monad.Writer
-- import Data.Either
import Data.Function
import Data.IORef
import Data.List hiding (group)
import qualified Data.Map as M
-- import Data.Maybe
import qualified Data.Set as S
import Data.Unique

import Types

-- todo: document why I'm not including level as a type
-- parameter on Var.
-- biggest reason: type of args to NewAbstract must be same
-- creating an instanceOf function just creates unnecessary complexity

class Level level where
  getInstanceVar :: (Ord a) => String -> Var c a -> ReadWrite level c (InstanceVar c a)

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
    when (mconcat (map snd cs) == Contradiction) $ put Contradiction
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
    let setTo val = do
          (_, _, assignment) <- changeInstanceVar (collapse val) iv
          return assignment
    return . map setTo . filter (flip S.member cs) . map fst $ allValues
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
  let c' = Constraint name (Just c) resolve collectable uninject
  -- the question is: can I add "current constraint" to the context of the
  -- ReadWrite monad? Will I always have a constraint available to put
  -- into the context?
  -- in the arg to the solve function: no. the only other place is
  -- in newConstraint, where obviously it can
  -- so... can I make a dummy constraint for use in the solve function?
  -- runDependencies c (bounded resolve) -- todo: inject constraint into relevant vars
  return c'

uninject :: Constraint l c -> IO ()
uninject c = do
  debug $ "uninjecting for " ++ show c
  join $ readIORef (constraintUninject c)

deriving instance (Eq c) => Eq (InstanceConstraint c)
deriving instance (Ord c) => Ord (InstanceConstraint c)
instance Show (InstanceConstraint c) where
  show (InstanceConstraint c) = show c
  show (InstantiatedConstraint c _) = show c

class IdSource m where
  idSource :: m (IORef Int)

nextId :: (IdSource m, MonadIO m) => m Int
nextId = do
  ref <- idSource
  liftIO $ do
    ret <- readIORef ref
    modifyIORef ref (+1)
    return ret

instance Monoid Satisfiable where
  mempty = Satisfiable
  mappend Contradiction _ = Contradiction
  mappend _ Contradiction = Contradiction
  mappend _ _ = Satisfiable

instance Functor (New Instance c) where
  fmap f (NewInstance m) = NewInstance (fmap f m)
instance Applicative (New Instance c) where
  pure x = NewInstance (pure x)
  (NewInstance f) <*> (NewInstance x) = NewInstance (f <*> x)
instance Monad (New Instance c) where
  return x = NewInstance (return x)
  (NewInstance x) >>= f = NewInstance (unNewInstance . f =<< x) where
    unNewInstance :: New Instance c a -> InstanceInner c a
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
  -> IO (a, Satisfiable, New Instance c a)
runNewAbstract (NewAbstract inner) c = do
  ((ret, inst), s, ()) <- runRWST inner c Satisfiable -- check bool!
  let instMaker = do
        id <- nextId
        i <- Instantiation id <$> liftIO newUnique
        local (set newContextInstantiation (Just i)) inst
  return (ret, s, instMaker)

deriving instance Applicative (Init c)
deriving instance Functor (Init c)
deriving instance Monad (Init c)
deriving instance MonadIO (Init c)
deriving instance MonadWriter [Constraint Abstract c] (Init c)
deriving instance MonadReader (IORef Int) (Init c)
instance IdSource (Init c) where idSource = ask

runInit
  :: Init c a
  -> IO (a, Satisfiable, IORef Int, [UntypedInstanceVar c], [Constraint Instance c], [Constraint Abstract c])
runInit (Init m) = do
  n <- newIORef 0
  let context = NewContext (return False) Nothing n
  -- I *think* it's ok to ignore asgns, since they are all
  -- implications of decision level zero.
  ((a, cas), b, vars, cis, _asgns) <- runNewInstance (evalRWST m n ()) context
  return (a, b, n, vars, cis, cas)

-- | Groups a collection of abstract vars and constraints into
-- one, so that the pattern can be instantiated multiple times.
group :: New Abstract constraint a -> Init constraint (a, New Instance constraint a)
group m = do
  ref <- Init ask
  -- should not break on contradiction, since this group
  -- might never be used
  (a, _satisfiable, ret) <- liftIO $ runNewAbstract m ref
  return (a, ret)

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
  getInjector :: ReadWriteContext Instance c -> Injector UntypedInstanceVar c
  getInjector (InstanceReadWriteContext i) = i

runReadWriteAbstract
  :: (Ord c)
  => ReadWrite Abstract c a
  -> ReadWriteMode
  -> Constraint Abstract c
  -> IO (a, [Assignment c])
runReadWriteAbstract (ReadWrite m) mode c = do
  let inject = makeInjector untypedAbstractVarAbstractConstraints c
  evalRWST m (AbstractReadWriteContext mode inject) ()

makeInjector :: (Show (untyped c), Ord c) => (untyped c -> IORef (Constraints l c)) -> Constraint l c -> Injector untyped c
makeInjector getConstraints c var = do
  let modifier = modifyIORef (getConstraints var)
  debug $ "injecting into " ++ show var
  modifier (S.insert c)
  modifyIORef (constraintUninject c) (modifier (S.delete c) >>)

askAbstractInjector :: ReadWrite Abstract c (Injector UntypedAbstractVar c)
askAbstractInjector = ReadWrite (asks getInjector) where
  getInjector :: ReadWriteContext Abstract c -> Injector UntypedAbstractVar c
  getInjector (AbstractReadWriteContext _ i) = i

askReadWriteMode = ReadWrite (asks (\(AbstractReadWriteContext m _) -> m))

modifyInstanceVar
  :: (Level level, Ord a)
  => (S.Set a -> S.Set a)
  -> InstanceVar c a
  -> ReadWrite level c ()
modifyInstanceVar mod iv = ReadWrite $ do
  (oldCandidates, newCandidates, assignment) <- liftIO $ changeInstanceVar mod iv
  when (oldCandidates /= newCandidates) $ tell [assignment]

changeInstanceVar
  :: (Ord a)
  => (S.Set a -> S.Set a)
  -> InstanceVar c a
  -> IO (S.Set a, S.Set a, Assignment c)
changeInstanceVar mod iv = do
  let ref = _instanceVarCandidates iv
  old <- readIORef ref
  let new = mod old
  let internalBug = error
  let effect =
        case S.toList new of
          [v] -> do
            case lookup v (varCommonValues . _instanceVarCommon $ iv) of
              Nothing -> internalBug "one of candidates is invalid"
              Just eff -> eff (VarInstance iv)
          _ -> return ()
  writeIORef ref new
  return (old, new, Assignment (untypeInstanceVar iv) effect (writeIORef ref old))

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
  -> IO (Bool, b) -- ^ 'False' iff no solution exists. Values returned from 'readIvar' after solve completes are available only for debugging purposes if 'False' is returned (no guarantees are made about their values); otherwise they will be singleton sets containing the satisfying assignment.
solve learner definition reader = do
  (a, satisfiable, idsource, ivars, iconstraints, _aconstraints) <- runInit definition
  let ss = SolveState [] (S.fromList ivars) (S.fromList (map InstanceConstraint iconstraints)) S.empty S.empty
  completed <- if satisfiable == Contradiction then return False else evalSolve loop (SolveContext idsource learner) ss
  dummyIdentity <- newUnique
  dummyUninjector <- newIORef (return ())
  let dummyConstraint = Constraint (NameAndIdentity "solution reader dummy constraint" dummyIdentity) Nothing (return True) (return False) dummyUninjector
  (ret, _assignments) <- runReadWriteInstance (reader a) dummyConstraint
  return (completed, ret)

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
          vals <- liftIO $ untypedInstanceVarValues v
          debug $ "has " ++ show (length vals) ++ " vals"
          case vals of
            [] -> do
              unassignedVars %= S.insert v
              jumpback
            [_] -> do
              assignedVars %= (AssignmentFrame (return ()) [] False :)
              loop
            (x:xs) -> choose x xs
    Just (InstantiatedConstraint _ _) -> liftIO . throwIO . userError $ "abstract constraints not yet supported"
    Just (InstanceConstraint c) -> do
      liftIO $ uninject c
      (satisfiable, as) <- liftIO $ runReadWriteInstance (constraintResolve c) c
      assignedVars %= (reverse (map (\a -> AssignmentFrame (assignmentUndo a) [] False) as) ++)
      if not satisfiable then jumpback else do
      propagateEffects as

-- jumpback :: (Ord c) => Solve c Bool
jumpback = do
  vs <- use assignedVars
  let (pop,keep) = span (not . frameDecisionLevel) vs
  -- todo: put constraint learning in here
  liftIO $ mapM_ frameUndo pop
  debug $ "undid " ++ show (length pop) ++ " frames"
  stepback keep

stepback [] = return False
stepback (x:xs) = do
  debug "stepback"
  liftIO $ frameUndo x
  case frameUntriedValues x of
    [] -> stepback xs
    (y:ys) -> choose y ys

choose x xs = do
  assignment <- liftIO x
  assignedVars %= (AssignmentFrame (assignmentUndo assignment) xs True :)
  propagateEffects [assignment]

-- propagateEffects :: (Ord c) => [Assignment c] -> Solve c Bool
propagateEffects as = do
  -- check to see if any variables are now empty
  contradiction <- any null <$> liftIO (mapM (untypedInstanceVarValues . assignmentVar) as)
  if contradiction then jumpback else do
  -- create new vars and constraints from the assignments made
  (sat, newVars, newConstraints, newAssignments) <- runEffects as
  if sat == Contradiction then jumpback else do
  debug $ "generated " ++ show (length newVars) ++ " new vars and " ++ show (length newConstraints) ++ " new constraints"
  unassignedVars %= S.union (S.fromList newVars)
  unrevisedConstraints %= S.union (S.fromList (map InstanceConstraint newConstraints))
  -- for each assignment made, re-run the constraints (instance and abstract)
  forM_ as $ \a -> do
    let uiv = assignmentVar a
    instanceConstraints <- liftIO . readIORef . untypedInstanceVarInstanceConstraints $ uiv
    unrevisedConstraints %= S.union (S.mapMonotonic InstanceConstraint instanceConstraints)
    case untypedInstanceVarAbstractVar uiv of
      Nothing -> do
        debug $ "instance var does not appear to have an abstract var"
        return ()
      Just (uav, inst) -> do
        acs <- liftIO . readIORef $ untypedAbstractVarAbstractConstraints uav
        debug $ "instance var DOES have an abstract var; adding " ++ show (S.size acs) ++ " related constraints now"
        unrevisedConstraints %= S.union (S.mapMonotonic (flip InstantiatedConstraint inst) acs)
  if null newAssignments then loop else propagateEffects newAssignments

runEffects :: [Assignment c] -> Solve c (Satisfiable, [UntypedInstanceVar c], [Constraint Instance c], [Assignment c])
runEffects as = do
  nextIdRef <- view solveNext
  liftIO $ do
    -- todo: change collectable to be dependent on whether
    -- the instigating variable has multiple candidate values.
    let context = NewContext (return False) Nothing nextIdRef
    out <- mapM ((flip runNewInstance context) . assignmentEffect) as
    return . (\(bs,vss,css,ass) -> (mconcat bs, concat vss, concat css, concat ass)) . unzip4 . map (\((),b,v,c,a) -> (b,v,c,a)) $ out

-- For some reason ghc can't infer this type.
pop :: MonadState s m => Simple Lens s (S.Set a) -> m (Maybe a)
pop set  = do
  s <- use set
  if S.null s then return Nothing else do
  let (v, s') = S.deleteFindMin s -- todo: better variable ordering
  set .= s'
  return (Just v)

instance Level Abstract where
  getInstanceVar str (VarInstance _) = liftIO . throwIO . userError $ "internal bug: tried to find instance variable while in Abstract monad: " ++ str
  getInstanceVar str (VarAbstract av) = do
    rwm <- askReadWriteMode
    case rwm of
      CreatingConstraint -> liftIO $ do
        -- todo: actually, if setVar and shrinkVar make modifications
        -- to this dummy variable, we really ought to remember the
        -- changes
        dummyInstantiation <- Instantiation (-1) <$> newUnique
        dummyCandidates <- newIORef (S.fromList . map fst . varCommonValues . _abstractVarCommon $ av)
        dummyConstraints <- newIORef S.empty
        dummyNI <- NameAndIdentity "dummy variable" <$> newUnique
        return (InstanceVar (Just (av, dummyInstantiation)) dummyCandidates dummyConstraints (VarCommon dummyNI (varCommonValues $ _abstractVarCommon av)))
      RevisingConstraint inst -> liftIO $ do
        instances <- readIORef (_abstractVarInstances av)
        let croak s = throwIO . userError $ s ++ ": " ++ str
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
            identity <- liftIO newUnique
            -- shared
            candidates <- liftIO . newIORef . M.keysSet $ values
            -- create empty set of constraints (shared)
            constraints <- liftIO $ newIORef S.empty
            mbInst <- view newContextInstantiation
            inst@(Instantiation which _) <- liftIO $ case mbInst of
              Nothing -> throwIO . userError . internalBug $ "no instantiation for instantiated variable"
              Just inst -> return inst
            ivName <- do
              return . (("instance " ++ show which ++ " of ") ++) . name . _varCommonIdentity . _abstractVarCommon $ u'
            let ret = InstanceVar (Just (u', inst)) candidates constraints (set varCommonIdentity (NameAndIdentity ivName identity) (_abstractVarCommon u'))
            liftIO . modifyIORef (_abstractVarInstances u') . M.insert inst $ ret
            return ret
          NewInstance $ tell ([untypeInstanceVar var], [], [])
          return (VarInstance var)
    return (VarAbstract u', iv)

  -- todo: move this outside of the type class
  readVar (VarInstance iv) = illegalUseOfInstanceVariable "read" iv
  readVar v@(VarAbstract av) = do
    inject <- askAbstractInjector
    iv <- getInstanceVar "readVar (abstract)" v
    liftIO $ do
      inject (untypeAbstractVar av)
      readIORef (_instanceVarCandidates iv)

-- | Constrains a set of variables.
newAbstractConstraint
  :: (Ord constraint)
  => Maybe String
  -> constraint
  -> ReadWrite Abstract constraint Bool -- ^ Constraint testing function. Should return False only when the constraint can no longer be satisfied. It should call 'setVar' or 'shrinkVar' when it can make a deduction.
  -> Init constraint ()
newAbstractConstraint mbName c resolve = do
  -- what I end up doing with fixme will probably depend on whether
  -- I can successfully implement newConstraint' or not
  c' <- newConstraint' mbName c resolve
  Init $ do
    tell [c']
    -- agh... how do I wire myself up to the relevant abstract vars?
    -- what is readVar supposed to do without a particular instantiation?
    -- I suppose if there's no instantiation, readVar can just return ALL
    -- values, and the setVar and shrinkVar are no-ops
    -- its ok to ignore when _b is False (the pattern might never
    -- be instantiated), and when _assgns is not null (the assignments
    -- are for dummy variables anyway)
    -- ok to ignore satisfiable, since the group might
    -- never be instantiated
    -- assgns should probably not be ignored, but it doesn't hurt to
    -- ignore it. It just means certain revisions will be re-run multiple times
    -- (but this is not likely to be expensive).
    (_b, _assgns) <- liftIO $ runReadWriteAbstract resolve CreatingConstraint c'
    return ()

{-
constraint
  :: (Ord constraint)
  => New level constraint (Maybe String, constraint, ReadWrite level constraint Bool)
  -> New level constraint ()
constraint ni@(NewInstance _) = (\(a,b,c) -> newConstraint a b c) =<< ni
constraint (NewAbstract _) = undefined
-}

-- | Removes all but the given value from the variable's set of
-- candidate values. If the given value is already in violation of
-- another constraint, the set of associated values will become empty,
-- and the solver will begin backjumping.
setVar :: (Level level, Ord a) => Var constraint a -> a -> ReadWrite level constraint ()
setVar var val = modifyInstanceVar (collapse val) =<< getInstanceVar "set" var where

collapse :: (Ord a) => a -> S.Set a -> S.Set a
collapse val cds | S.member val cds = S.singleton val
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
  readVar (VarAbstract av) = illegalUseOfAbstractVariable "read" av

-- | Constrains a set of variables.
newInstanceConstraint
  :: (Ord constraint)
  => Maybe String
  -> constraint
  -> ReadWrite Instance constraint Bool -- ^ Constraint testing function. Should return False only when the constraint can no longer be satisfied. It should call 'setVar' or 'shrinkVar' when it can make a deduction.
  -> New Instance constraint ()
newInstanceConstraint mbName c resolve = NewInstance $ do
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

-- todo: unify with abstract variable version, or else
-- make level a type parameter of Var
illegalUseOfInstanceVariable action va = liftIO . throwIO . userError . illegalArgument $ "cannot " ++ action ++ " instance variable " ++ (name . _varCommonIdentity . _instanceVarCommon $ va) ++ " when inside 'ReadWrite Abstract constraint' monad" where
  illegalArgument = error
illegalUseOfAbstractVariable action va = liftIO . throwIO . userError . illegalArgument $ "cannot " ++ action ++ " abstract variable " ++ (name . _varCommonIdentity . _abstractVarCommon $ va) ++ " when inside 'ReadWrite Instance constraint' monad" where
  illegalArgument = error

debug = liftIO . putStrLn

-- todo: make sure that readVar, setVar, and shrinkVar all look at their ReadWrite
-- context and inject constraints into themselves if they need to

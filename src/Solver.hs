{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
module Solver (
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
  avar :: Var c }

data IVar c a = IVar {
  ivarAvar :: AVar c a,
  ivarState :: IORef (IVarState c a) }

data IVarState c a = IVarState {
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
  _ivarPreviousAssignments :: M.Map a (S.Set (Clause c)) } -- todo: this value is still not being checked

data UntypedIvar c = UntypedIvar {
  uivarVar :: Var c,

  -- ^ A sequence of calls to setIVar for each remaining candidate.
  uivarValues :: IO [Assign c ()] }

instance Eq (UntypedIvar c) where (==) = (==) `on` varIdentity . uivarVar
instance Ord (UntypedIvar c) where compare = compare `on` varIdentity . uivarVar

data Clause c = Clause {
  clauseClause :: c,
  clauseVars :: S.Set (Var c),
  clauseCollectable :: IO Bool,
  clauseResolve :: Assign c Bool }

clauseIdentity :: Clause c -> (c, S.Set (Var c))
clauseIdentity c = (clauseClause c, clauseVars c)

instance (Eq c) => Eq (Clause c) where (==) = (==) `on` clauseIdentity
instance (Ord c) => Ord (Clause c) where compare = compare `on` clauseIdentity

newtype New c a = New (WriterT [Either (UntypedIvar c) (Clause c)] IO a)
  deriving (Applicative, Functor, Monad, MonadIO)

newtype Init c a = Init (WriterT [Var c] (New c) a)
  deriving (Applicative, Functor, Monad, MonadIO)

newtype Assign c a = Assign (WriterT [Assignment c] IO a)
  deriving (Applicative, Functor, Monad, MonadIO)

data Assignment c = Assignment {
  assignmentVar :: (UntypedIvar c),
  assignmentEffect :: Maybe (New c ()), -- todo: check to see if this maybe is actually necessary
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

-- solve :: ([c] -> New c ()) -> Init c a -> IO (Bool, a)
solve resolver definition = do
  (ret, _avars, ivars, clauses) <- runInit definition
  mapM_ attach clauses -- fill the refs of each into each other
  let ss = SolveState [] (S.fromList ivars) (S.fromList clauses) S.empty
  completed <- evalSolve loop resolver ss
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
  (newVars, newClauses) <- liftIO $ runEffects as
  unassignedVars %= S.union (S.fromList newVars)
  unrevisedClauses %= S.union (S.fromList newClauses)
  forM_ as $ \a -> do
    cs <- liftIO $ readIORef (varClauses . uivarVar . assignmentVar $ a)
    unrevisedClauses %= S.union cs

runEffects :: [Assignment c] -> IO ([UntypedIvar c], [Clause c])
runEffects as = do
  let es = catMaybes $ map assignmentEffect as
  out <- mapM runNew es
  return . (\(vss,css) -> (concat vss, concat css)) . unzip . map (\((),v,c) -> (v,c)) $ out

-- For some reason ghc can't infer this type.
pop :: MonadState s m => Simple Lens s (S.Set a) -> m (Maybe a)
pop set  = do
  s <- use set
  if S.null s then return Nothing else do
  let (v, s') = S.deleteFindMin s -- todo: better variable ordering
  set .= s'
  return (Just v)

{-
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

selectUnassignedVariable :: Solve c (Maybe (UntypedIvar c))
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
  ret <- liftIO $ AVar vs <$> newVar
  tellAvar ret
  return ret

instance Eq (IVar c a) where (==) = (==) `on` varIdentity . ivar
instance Ord (IVar c a) where compare = compare `on` varIdentity . ivar

-- newIVar :: AVar c a -> New c (IVar c a)
newIVar av = do
  ret <- liftIO $ IVar av <$> newIORef (IVarState (S.fromList $ M.keys (avarValues av)) M.empty)
  tellUntypedIvar (untype ret)
  return ret

ivar :: IVar c a -> Var c
ivar = avar . ivarAvar

readIVar :: IVar c a -> IO (S.Set a)
readIVar iv = _ivarCandidates <$> readIORef (ivarState iv)

-- setIVar :: (Ord a) => IVar c a -> a -> Assign c ()
setIVar iv v = modifyIVar iv collapse where
  collapse cds | S.member v cds = S.singleton v
               | otherwise = S.empty

-- shrinkIVar :: (Ord a) => IVar c a -> a -> Assign c ()
shrinkIVar iv v = modifyIVar iv (S.delete v)

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
    return (map (setIVar iv) cs) -- todo: pick a more optimal ordering

newClause
  :: clause
  -> S.Set (Var clause)
  -> IO Bool -- ^ collectable
  -> Assign clause Bool -- ^ resolve: makes direct assignments if it can. Returns true iff the clause is still satisfiable
  -> New clause () -- ^ clause is necessary here so that resolve can be called.
newClause c watched collectable resolve =
  tellClause (Clause c watched collectable resolve)

-- runNew :: New a -> IO (a, [(UntypedIvar c)], [Clause])
runNew (New m) = do
  (ret, mix) <- runWriterT m
  let (ims, cs) = partitionEithers mix
  return (ret, ims, cs)

tellClause :: Clause c -> New c ()
tellClause = New . tell . (:[]) . Right

tellUntypedIvar :: (UntypedIvar c) -> New c ()
tellUntypedIvar = New . tell . (:[]) . Left

runInit :: Init c a -> IO (a, [Var c], [(UntypedIvar c)], [Clause c])
runInit (Init m) = do
  ((ret, avars), ivars, cs) <- runNew (runWriterT m)
  return (ret, avars, ivars, cs)

liftNew :: New c a -> Init c a
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
              Just x -> Just x
          _ -> Nothing
  tell [Assignment (untype iv) effect (modifyIORef ref (set ivarCandidates orig))]

evalSolve :: Solve c a -> ([c] -> New c ()) -> SolveState c -> IO a
evalSolve (Solve m) resolve solveState = do
  (ret, ()) <- evalRWST m resolve solveState
  return ret

resolve :: [c] -> Solve c (New c ())
resolve xs = Solve $ do
  resolver <- ask
  return (resolver xs)

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

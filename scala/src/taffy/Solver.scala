package taffy

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 1/28/13
 * Time: 9:23 AM
 */

import scala.collection.mutable
import scala.util.control.Breaks._
import scala.None

class Solver[Constraint, Variables, Variable]( domain: Domain[Constraint, Variables, Variable],
                                               problem: Problem[Constraint, Variables, Variable],
                                               ranger: Ranger[Variables, Variable]) {
  type VarId = Int

  // private class Var(var values: Variables) {}

  private val variables: mutable.ArrayBuffer[Variables] = mutable.ArrayBuffer()
  private val watchers: mutable.ArrayBuffer[Set[Constraint]] = mutable.ArrayBuffer()

  private val unrevised: mutable.Set[Constraint] = mutable.Set()

  private val unassigned: mutable.Set[VarId] = mutable.Set()
  private val trail: mutable.Stack[(VarId, Variables /* original */, Option[Set[Variable]] /* attempts */)] = mutable.Stack()

  def solve() : Option[Read[Variables, Variable]] = {
    for (vid <- 0 until problem.numVariables) {
      variables += problem.candidateValues
      watchers += Set.empty
      unassigned += vid
    }
    unrevised ++= problem.constraints

    while (!unrevised.isEmpty || !unassigned.isEmpty) {
      var bj = false
      if (!unrevised.isEmpty) {
        val constraint = unrevised.head
        unrevised -= constraint
        val varsRead = mutable.Map[VarId, Option[Set[Variable]]]()
        val undo = mutable.Map[VarId, Variables]()
        val rw = new ReadWrite[Constraint, Variables, Variable](constraint, variables, varsRead, undo, ranger)
        if (domain.revise(rw, constraint)) {
          bj = false
          breakable {
            for ((vid, original) <- undo) {
              if (ranger.isEmpty(variables(vid))) {
                bj = true
                break()
              }
            }
          }
        } else {
          bj = true
        }
        if (bj) {
          for ((vid, original) <- undo) {
            variables(vid) = original
          }
          backjump()
          if (trail.isEmpty) return None
        } else {
          for ((vid, original) <- undo) {
            val values: Variables = variables(vid)
            if (ranger.isSingleton(values)) {
              unassigned -= vid
              trail.push((vid, /* ranger.subtraction( */ original /* , values) */, None))
              unrevised ++= watchers(vid) - constraint
            }
          }
          for ((varId, _) <- varsRead) {
            watchers(varId) += constraint // todo: only watch on particular values
          }
        }
      } else if (!unassigned.isEmpty) {
        var vid = unassigned.head // todo: better variable ordering
        unassigned -= vid
        val values: Variables = variables(vid)
        val value = ranger.pick(values) // todo: better value picking
        unassigned -= vid
        variables(vid) = ranger.toSingleton(value)
        trail.push((vid, /*ranger.subtraction(*/values/*, ranger.toSingleton(value))*/, Some(Set(value))))
        unrevised ++= watchers(vid)
      }
    }
    Some(new Read(variables, ranger))
  }

  private def backjump() { // todo: currently this is only backtracking, not backjumping
    breakable {
      while (!trail.isEmpty) {
        val (vid, original, decision) = trail.pop()
        decision match {
          case None =>
            variables(vid) = original
            unassigned += vid
          case Some(attempted) =>
            var untried = original
            for (value <- attempted) {
              untried = ranger.subtraction(untried, ranger.toSingleton(value))
            }
            if (ranger.isEmpty(untried)) {
              variables(vid) = original
              unassigned += vid
            } else {
              val value: Variable = ranger.pick(untried)
              variables(vid) = ranger.toSingleton(value)
              trail.push((vid, original, Some(attempted + value)))
              break()
            }
        }
      }
    }
  }
  /*
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
module NewSolver where

import Control.Applicative
import Control.Exception
import Control.Lens
import Control.Monad.Error
import Control.Monad.IO.Class
import Control.Monad.RWS
import Control.Monad.Writer
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.Map as M
import qualified Data.Set as S

type VarId = Int
type ConstraintId = Int

data SolveContext c v = SolveContext {
  _learn :: [c] -> IO [(c, [c])], -- fst is new constraint, snd is the constraints that were sufficient to produce the new constraint
  _revise :: c -> ReadWrite c v (),
  _coverage :: c -> [VarId]
  }

data SolveState c v = SolveState {
  _isomorphisms :: [Substitution], -- have to find a better data structure for this; this data structure stores both directions of each isomorphism
  _constraints :: IM.IntMap c,
  _vars :: S.Set Int, -- IS.IntSet, {- VarId -} -- todo: switch to IntSet
  _learnts :: IM.IntMap c,
  _watches :: IM.IntMap {- VarId -} IS.IntSet {- ConstraintId -}, -- , M.Map v (S.Set c)), -- can make this slightly faster by indexing not just on variable, but on variable,value pairs, if constraint revision functions can communicate
  _values :: IM.IntMap (S.Set v),
  _unrevised :: S.Set ConstraintId,
  _trail :: [(VarId, S.Set v {- untried values; empty for unit propagations -})],
  _reason :: IM.IntMap {- VarId -} (Maybe ConstraintId), -- Nothing for decision variables
  _level :: IM.IntMap {- VarId -} Int -- decision level
  }

type Substitution = M.Map VarId VarId

type Undo c v = Solve c v ()
instance Monoid (Undo c v)

instance Error () where
  noMsg = ()
  strMsg _ = ()

newtype ReadWrite c v a = ReadWrite (ErrorT () (RWST c ([(VarId, Maybe v)], Undo c v) () (Solve c v)) a)
  deriving (Applicative, Functor, Monad, MonadIO)

newtype Solve c v a = Solve (RWST (SolveContext c v) () (SolveState c v) IO a)
  deriving (Applicative, Functor, Monad, MonadIO)

deriving instance MonadReader (SolveContext c v) (Solve c v)
deriving instance MonadState (SolveState c v) (Solve c v)

makeLenses ''SolveContext
makeLenses ''SolveState

-- should have an either monad in here
-- quit early if we set a variable to be empty
-- question: what should the constraint be watching
-- in that case? This is easy enough if we just
-- say that watchers always grows, and never shrinks
-- (well, except for learnt constraints, which
-- can be garbage collected)
-- the given c will be injected into every variable that is examined
runReadWrite :: ReadWrite c v a -> c -> Solve c v (Maybe a, [(VarId, Maybe v)], Solve c v () {- undo -})
runReadWrite (ReadWrite m) c = do
  (ret, (), (watched, undo)) <- runRWST (runErrorT m) c ()
  return (ret, watched, undo)

runSolve :: Solve c v a -> SolveContext c v -> SolveState c v -> IO (a, SolveState c v)
runSolve = undefined

readVar :: VarId -> ReadWrite c v (S.Set v)
readVar = undefined

-- Similar to calling readVar and verifying that the returned
-- set is a singleton containing the given value. You should
-- use this function instead of readVar, if you can, since
-- it will cause fewer unnecessary propagations.
varEquals :: VarId -> v -> ReadWrite c v Bool
varEquals = undefined

setVar :: VarId -> v -> ReadWrite c v ()
setVar = undefined

intersectVar :: VarId -> S.Set v -> ReadWrite c v ()
intersectVar = undefined

shrinkVar :: VarId -> v -> ReadWrite c v ()
shrinkVar = undefined

solve
  :: forall c v. (Ord v) => [c]
  -> Int -- number of variables
  -> S.Set v -- all possible values of a variable; todo: find a more compact representation
  -> [[(VarId,VarId)]] -- isomorphisms
  -> (c -> [VarId])
  -> (c -> ReadWrite c v ())
  -> ([c] -> IO [(c, [c])])
  -> IO (Maybe [v]) -- todo: figure out how caller is supposed to read newly created variables
solve constraints numVariables values isos cov revise learn = z where
  varIds = [0..(numVariables - 1)]
  sc = SolveContext learn revise cov
  ss :: SolveState c v
  ss = SolveState
         (mkSubstitutions isos) -- isomorphisms
         (IM.fromList (zip [0..] constraints)) -- constraints
         (S.fromList varIds) -- vars
         IM.empty -- learnts
         (IM.fromList (zip varIds (repeat IS.empty))) -- watches
         (IM.fromList (zip varIds (repeat values))) -- values
         (S.fromList [0..(length constraints - 1)]) -- unrevised
         [] -- trail
         IM.empty
         IM.empty
  mkSubstitutions = map M.fromList
  solution :: SolveState c v -> [v]
  solution = map fromSingleton . zip [0..] . IM.toAscList . _values --map (fromSingleton . snd) . IM.toList . _values
  fromSingleton :: (Int, (Int, S.Set v)) -> v
  fromSingleton (i, (i', s)) | i /= i' = internalBug $ "unexpected index in IM.foldl: " ++ show i ++ " /= " ++ show i'
                             | otherwise = case S.toList s of
                                             [v] -> v
                                             _ -> internalBug $ "not a singleton: " ++ show (S.size s)
  z = do
    (satisfiable, ss') <- runSolve loop sc ss
    return $ if not satisfiable then Nothing else Just (solution ss')

loop :: (Ord v) => Solve c v Bool
loop = do
  mbc <- pop unrevised
  case mbc of
    Nothing -> do
      -- debug $ PoppedConstraint Nothing
      mbv <- pop vars
      case mbv of
        Nothing -> do
          -- debug $ PoppedVar Nothing
          return True
        Just vid -> do
          -- debug $ PoppedVar (Just $ error "popped var not implemented")
          mbVals <- use (values.at vid)
          -- debug $ CountedValues (error "counted values not implemented") (length vals)
          case S.toList <$> mbVals of
            Nothing -> liftIO . throwIO . internalBugIO $ "lookup failed"
            Just [] -> do
              vars %= S.insert vid
              jumpback
            Just (val:vals) -> do
              trail %= ((vid, S.fromList vals) :)
              reason.at vid %= just Nothing
              cs <- watchers vid val
              unrevised %= S.union cs
              loop
    Just cid -> do
      mbConstraint <- use (constraints.at cid)
      case mbConstraint of
        Nothing -> liftIO . throwIO . internalBugIO $ "could not lookup constraint by id"
      -- debug $ PoppedConstraint (Just $ error "popped constraint not implemented")
        Just c -> do
          uninject c
          reviser <- view revise
          (e, vids, undo) <- runReadWrite (reviser c) c
          case e of
            -- todo: jumpback probably needs to wipe clean the collection of
            -- constraints
            Nothing -> do
              undo
              jumpback
            Just () -> do
              -- find out if any of the vids are now singletons
              -- if so, then record the current constraint as being
              -- their "reason"
              -- also: extend trail with the new assignments
              allVals <- use values
              let appl :: (a -> b) -> Maybe a -> Maybe b
                  appl = (<$>)
              let mbVals = sequence . map (\(vid,_) -> appl (vid,) $ IM.lookup vid allVals) $ vids
              case mbVals of
                Nothing -> liftIO . throwIO . internalBugIO $ "some vids' values could not be looked up"
                Just vals -> do
                  let singletons = filter ((== 1) . S.size . snd) vals
                  let update (vid,_) = do
                        (reason.at vid) %= just (Just cid)
                        trail %= ((vid, error "not implemented") :)
                  mapM_ update singletons
                  loop
              {-
              (satisfiable, as) <- liftIO $ runReadWriteInstance (constraintResolve c) c
              assignedVars %= (reverse (map (\a -> AssignmentFrame (assignmentUndo a) [] False (untypedInstanceVarIdentity $ assignmentVar a)) as) ++)
              if not satisfiable then jumpback else do
              propagateEffects as
              -}

just :: a -> Maybe a -> Maybe a
just s Nothing = Just s
just _ (Just _) = internalBug $ "tried to update reason, but found data already there"

pop :: MonadState s m => Simple Lens s (S.Set a) -> m (Maybe a)
pop set  = do
  s <- use set
  if S.null s then return Nothing else do
  let (v, s') = S.deleteFindMin s -- todo: better variable ordering
  set .= s'
  return (Just v)

jumpback :: Solve c v Bool
jumpback = undefined

uninject :: c -> Solve c v ()
uninject _ = return () -- strictly speaking, uninjecting is only an optimization, so I'll wait until later to implement it.
internalBug = error
internalBugIO = userError

watchers :: VarId -> v -> Solve c v (S.Set ConstraintId)
watchers = undefined

-- todo: we are still missing the substituter, without which we can't
-- tell if a constraint we create is actually a valid one

class Values values value | values -> value where
  singleton :: value -> values
  fromSingleton :: values -> value
  intersection :: values -> values -> values
  subtraction :: values -> values -> values
  isEmpty :: values -> Bool

-- instance Values (S.Set a) a

{-
Internally, isomorphisms can be represented as Sides.
A side is merely an ordered collection of variable ids.
type Side = [VarId]
The transitive closure of all isomorphisms is computed
(effectively, but not actually), by creating a collection of
sides.
type AllIsomorphisms = S.Set (S.Set Side)
-- for the inner set, every side must have the same size.
-- different size . size's are allowed (but not required) for the outer set
If a side x is isomorphic to a side y, then a particular
subsequence of the side x must be isomorphic to the corresponding
subsequence of the side y. This necessarily implies that intersections
of sides are themselves sides.
It does not imply (nor is it assumed by the solver) that unions
of sides are also sides.

A side x is isomorphic to a side y only if all constraints
(both given and yet-to-be-learned) on a subsequence of x are
also constraints on the corresponding subsequence of y.

Subsequence, here, is a binary function on the indices of a side.
So, [1, 2, 4] is a valid subsequence of [1, 2, 3, 4, 5], even
though it skips a number.
-}
   */
}

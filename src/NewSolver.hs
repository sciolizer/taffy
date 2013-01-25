{-# LANGUAGE TemplateHaskell #-}
module NewSolver where

import Control.Lens

type VarId = Int
type ConstraintId = Int

data SolveContext = SolveContext {
  _learn :: [c] -> IO [(c, [c])], -- fst is new constraint, snd is the constraints that were sufficient to produce the new constraint
  _revise :: c -> ReadWrite c v ()
  }

data SolveState c v = SolveState {
  _isomorphisms :: [Substitution v], -- have to find a better data structure for this; this data structure stores both directions of each isomorphism
  _constraints :: IM.IntMap c,
  _learnts :: IM.IntMap c,
  _watches :: IM.IntMap {- VarId -} IS.IntSet {- ConstraintId -}, -- , M.Map v (S.Set c)), -- can make this slightly faster by indexing not just on variable, but on variable,value pairs, if constraint revision functions can communicate 
  _values :: IM.IntMap (S.Set v),
  _unrevised :: S.Set ConstraintId,
  _trail :: [(VarId, S.Set v {- untried values; empty for unit propagations -})],
  _reason :: IM.IntMap {- VarId -} (Maybe ConstraintId), -- Nothing for decision variables
  _level :: IM.IntMap {- VarId -} Int -- decision level
  }

type Substitution v = M.Map v v

newtype ReadWrite c v a = ReadWrite (WriterT [VarId] (Solve c v) a)
  deriving (Applicative, Functor, Monad, MonadIO)

newtype Solve c v a = Solve (RWST (SolveContext c v) () (SolveState c v) IO a)
  deriving (Applicative, Functor, Monad, MonadIO)

makeLenses ''SolveContext
makeLenses ''SolveState

runReadWrite :: ReadWrite c v a -> Solve c v (a, [VarId])
runReadWrite = undefined

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
  :: [c]
  -> Int -- number of variables
  -> S.Set v -- all possible values of a variable; todo: find a more compact representation
  -> [[(VarId,VarId)]] -- isomorphisms
  -> (c -> ReadWrite c v ())
  -> ([c] -> IO [(c, [c])])
  -> IO (Maybe [v]) -- todo: figure out how caller is supposed to read newly created variables
solve constraints numVariables values isos revise learn = z where
  varIds = [0..(numVariables - 1)]
  sc = SolveContext learn revise
  ss = SolveState
         (mkSubstitutions isos) -- isomorphisms
         (IM.fromList (zip [0..] constraints)) -- constraints
         IM.empty -- learnts
         (IM.fromList (zip varIds IS.empty)) -- watches
         (IM.fromList (zip varIds S.empty)) -- values
         (S.fromList constraints) -- unrevised
         [] -- trail
         IM.empty
         IM.empty
  solution = IM.foldl fromSingleton 0 . _values --map (fromSingleton . snd) . IM.toList . _values
  fromSingleton (i (i', s)) | i /= i' = internalBug $ "unexpected index in IM.foldl: " ++ show i ++ " /= " ++ show i'
                            | otherwise -> case S.toList s of
                                             [v] -> v
                                             _ -> internalBug $ "not a singleton: " ++ show (S.size s)
  z = do
    (satisfiable, ss') <- runSolve loop sc ss
    return $ if not satisfiable then Nothing else Just (solution ss')

loop = undefined

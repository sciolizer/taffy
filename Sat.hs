module Sat where

import Control.Monad.Trans
import Data.Function
import qualified Data.Map as M
import qualified Data.Set as S

import Api

-- problem: not a \/ b \/ c
--          not b \/ a
--          not c \/ a

main = do
  (success, (a, b, c)) <- solve (const nop) definition
  print success
  mapM_ showVar [a,b,c] where
    showVar :: IVar Clause Bool -> IO ()
    showVar v = do
      val <- readIVar v
      print val

nop = return ()

definition = do
  binary <- newAVar (M.fromList [(True,nop),(False,nop)])
  liftNew $ do
    a <- newIVar binary
    b <- newIVar binary
    c <- newIVar binary
    mkClause [(not,a),(id,b),(id,c)]
    mkClause [(not,b),(id,a)]
    mkClause [(not,c),(id,a)]
    return (a, b, c)

mkClause parts = do
  let cl = Clause parts
  newClause cl (S.fromList (map (ivar . snd) parts)) (return False) (resolve cl)

data Clause = Clause { unClause :: [((Bool -> Bool), IVar Clause Bool)] }

instance Eq Clause where (==) = (==) `on` map snd . unClause
instance Ord Clause where compare = compare `on` map snd . unClause

resolve :: Clause -> Assign Clause Bool
resolve (Clause parts) = liftIO $ do
  vals <- mapM isPos parts
  return (any id vals) where
    isPos (flip,var) = do
      candidates <- readIVar var
      return . any flip . S.toList $ candidates

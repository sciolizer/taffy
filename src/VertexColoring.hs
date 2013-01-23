{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeSynonymInstances #-}
module VertexColoring where

{-

Consider the problem of coloring the following graph
with only two colors.

  /-B-\     /-I-\
 /--C--\   /--J--\
A---D---G-H---K---N
 \--E--/   \--L--/
  \-F-/     \-M-/

The solution is straightforward enough: the columns must
alternate. e.g. A, G, I-M could be black while B-F, H, N
could be white.

Since we are working with only two colors, we
can make a learning function that combines

  a != b
  c != b

to make

  a = b

With this learning rule, the solver is likely
to discover that B=C=D=E=F. 

But we don't want it to have to learn that
I=J=K=L=M, since this is obvious from
the symmetry of the problem.

So we will make a pattern of variables and constraints,
instantiate it twice, and then connect the two
instantiations together.

-}

import Prelude hiding (mapM)

import Control.Monad.IO.Class
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Traversable

import Solver

data Color = Black | White
  deriving (Bounded, Enum, Eq, Ord, Read, Show)

data Constraint = Constraint Relationship Vertex Vertex
  deriving (Eq, Ord, Show)

instance Show Vertex where show = varName

type Vertex = Var Constraint Color

data Relationship = Equal | Unequal
  deriving (Bounded, Enum, Eq, Ord)

instance Show Relationship where
  show Equal = " == "
  show Unequal = " != "

mix Equal Equal = Equal
mix Equal Unequal = Unequal
mix Unequal Equal = Unequal
mix Unequal Unequal = Equal

main = do
  (satisfiable, ret) <- solve learner problem (\xs -> debug "reading solution" >> mapM readVar xs)
  print satisfiable
  print ret

learner :: [Constraint] -> New Instance Constraint ()
learner constraints = sequence_ [combine c1 c2 | c1 <- constraints, c2 <- constraints] where
  combine c1@(Constraint r1 x1 y1) c2@(Constraint r2 x2 y2)
    | c1 <= c2 = return ()
    | x1 == x2 = constrain newInstanceConstraint (mix r1 r2) y1 y2 -- todo: does this actually produce abstract constraints?
    | x1 == y2 = constrain newInstanceConstraint (mix r1 r2) y1 x2
    | y1 == x2 = constrain newInstanceConstraint (mix r1 r2) x1 y2
    | y1 == y2 = constrain newInstanceConstraint (mix r1 r2) x1 x2
    | otherwise = return ()

lift Equal = (==)
lift Unequal = (/=)

constrain nc rel v1 v2 = nc (Just name) c op where
  name = show v1 ++ show rel ++ show v2
  c = Constraint rel v1 v2
  -- Realistically, this would read the value of one variable, and
  -- then set the other to the opposite, which would cause
  -- the solver to run in linear time (everything but the first assignment
  -- would be an implication). However, since the point of this example
  -- is to demonstrate shared clause learning, we're going to make our
  -- revise function much dumber. It will report on whether a constraint
  -- is still satisfiable, but will make no attempt to propagate implications.
  op = do
    debug $ "first read on " ++ name
    vals1 <- readVar v1
    case S.toList vals1 of
      [] -> return False
      [_,_] -> return True
      [x] -> do
        debug $ "second read on " ++ name
        vals2 <- readVar v2
        case S.toList vals2 of
          [] -> return False
          [_,_] -> return True
          [y] -> return (lift rel x y)
          err -> error $ "vertex should never have more than 3 possible values: " ++ show err
      err -> error $ "vertex should never have more than 3 possible values: " ++ show err

problem :: Init Constraint [Vertex]
problem = do
  ([t,u,v,w,x,y,z], pattern) <- group grouped
  mapM_ (connected newAbstractConstraint t) [u,v,w,x,y]
  mapM_ (connected newAbstractConstraint z) [u,v,w,x,y]
  [a,b,c,d,e,f,g] <- make pattern
  [h,i,j,k,l,m,n] <- make pattern
  make (connected newInstanceConstraint g h)
  return [a,b,c,d,e,f,g,h,i,j,k,l,m,n]

colors = M.fromList [(Black, \_ -> return ()),(White, \_ -> return ())]

grouped :: New Abstract Constraint [Vertex]
grouped = sequenceA (map var ['A'..'G']) where
  var c = newVar (Just $ show c) colors
{-
  connectA = map
  [a,b,c,d,e,f,g] <- mapM (\c -> newVar (Just $ show c) colors) ['A'..'G']
  mapM_ (connected a) [b,c,d,e,f]
  mapM_ (connected g) [b,c,d,e,f]
  return [a,b,c,d,e,f,g]

something :: New Abstract Constraint (Vertex, Vertex)
something = somethingElse <*> newVar (Just "x") colors <*> newVar (Just "y") colors
  -}

connected nc = constrain nc Unequal

debug = liftIO . putStrLn

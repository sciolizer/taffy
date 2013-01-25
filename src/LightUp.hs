module LightUp where

data Value = Light | Lit
  deriving (Bounded, Enum, Eq, Ord, Read, Show)

data Constraint = JustOne [Var]
  deriving (Eq, Ord, Read, Show)

data Var

readVar :: Var -> [Value]
readVar = undefined

constrain :: Constraint -> IO ()
constrain (MaxOne vars) = go vars where
  go [] = contradiction
  go [v] = writeVar v [Light]
  go (v:vs) = do
    vals <- readVar v
    if (Light `elem` vals) then prohibit vs

learn :: [Constraint] -> [Constraint]
learn ...
  the only thing I can think of for this is
  a + b + c <= 1
  a + d + e <= 1
  --------------
  a + b + c + d + e <= 2

  but that doesn't really speed things up, does it?

The thing we really want to learn is stuff like:
  -- for every THREE constraint, none of the corners
  -- can be lights.
  or
  -- if two numbers are facing each other, then
  -- only their neighbors are candidates for being
  -- lights... everything else in the line of fire
  -- must be ruled out

so:

a b c
d 3 e
f g h

a + b + c = 1
a + d + f = 1

1 a
b c

a + c = 1
b + c = 1
a + b = 1
---------
First two: a - b = 0 aka a = b
combine that with a + b = 1 => a + a = 1 and you
get a contradiction, which is indeed the case
for this puzzle

How about:

1 a X
b c d
X e X

a + c + e = 1
b + c + d = 1
a + b = 1
-----
First two: a + e - b - d = 0
1st and 3rd: c + e - b = 0
2nd and 3rd: c + d - a = 0
How do I derive c = 0?
Adding 1st 2 and subtracting the last: 2c + e + d = 1
Which implies c = 0

The thing is.... ace and bcd are not abstract constraints.
Or are they?

we could do it this way:

1 a X
b c d e f
X g X
  h
  i

a + b = 1 -- abstract
a + c + rest1 = 1 -- abstract
rest1 = g + h + i
b + c + rest2 = 1 -- abstract
rest2 = d + e + f

a b c d e f
1 g h i j 1

How do we infer that b = c = d = e = h = i = 0?
a + b + rest1 + e + f = 1
g + rest2 + j = 1
a + g = 1
f + j = 1
rest1 = c + d
rest2 = h + i

so... do we follow this pattern for every pair of numbers?

How can the AI learn this automatically? Is there a similar
solution to the automatic inference of A* heuristics: by
weakening things?



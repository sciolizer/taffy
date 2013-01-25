module Loopy where

data Value = On | Off | Inside | Outside

data Constraint
  = Intersection [Var] -- 2 to x, num on must be exactly two or zero; rest must be Off
  | Parity Var {- edge -} Var Var {- holes -} -- if edge is On, then one hole must be inside and the other outside; if edge is Off, then holes must be the same.
  | IsOutside Var -- one-off constraint for declaring the outside of the puzzle; actually this might be unnecessary, since even if you LABEL it the inside, the solution will still be valid
  | Count Int [Var] -- the numbers
  | Connected [Var] -- a global constraint: traces a path from the first "On" that it finds. If a loop is found, it sets the remaining edges to Off. If it is not yet a loop, a breadth-first search is done to find a path back to the start. If no path exists, it fails immediately, otherwise is returns "still satisfiable", and it will of course be "woken up" when any of the guessed path is set to False.

What we want it to infer:

max touch max at a corner
max touch max at an edge
edge touching a max outlines the max
edges coming into a 2 cannot jump back out

harder:
max "touching" max, but separated by 2s
similarly, an edge touching a max, but separated by 2s

presumably if you've learned something about 2 squares
and three squares, then the learnings could propagate,
after at least one conflict is discovered.

This suggests a sort of "pumping lemma" for patterns...
The simpler approach is to have a static pattern
of variables.
But a more general approach is to have a, um, regular expression?,
of variables.
Probably just ab*c (an opening, a closing, with arbitrary repetitions
of something in the middle).

hm... maybe I don't want instance and abstract variables at all...
maybe I should just explicitly declare the isomorphisms
within the problem (the solver can check that my declared
isomorphisms are in fact correct... or at least to what extent
they are correct).

i.e. drop the instance/abstract distinction... just make sure
that every learned constraint is duplicated where it can
be duplicated.

How this affects things:
- Watched literals can still be inferred, but the solver still
  needs a complete listing of all related variables, so that
  it only propagates isomorphisms when they are appropriate.
- In order to check isomorphism, the solver needs to be able
  to check structural equivalence between constraints:
  - order will have to be the same
  - placement will have to be the same (same order might still be wrong
    if, for instance, the second item is on a subbranch in one case
    but level in the other case)
  - easiest way to do this is probably to have the consumer implement
    a "substitution" operation on its constraints.
    substitute :: M.Map Var Var -> constraint -> constraint
    and then the solver can just check equality on the substituted version
    can probably provide a free instance if the consumer's constraint
    is an instance of traversable, or something like that
- constraint learning function needs to be explicit about which
  constraints it actually unified to produce its output.
  If the solver gives the learning function five constraints, and the
  learning function spits out one, but it only used two of the five
  constraints, and their exists an isomorphism over the two but
  not over all five, then that will be a lost opportunity for
  extra learned clauses.

I like this. It makes problem definition much simpler.
newVar
newClause
newIsomorphism
That's all. No type trickery.

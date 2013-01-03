Taffy
=====

Taffy is a constraint solver.

It is based off the chaff algorithm, but with three important differences:

1. Constraints can be arbitrary types. You are not limited to
   boolean disjunctions.
1. Constraint learning can happen over families of variables, not just
   single variables. Thus, there is an explicit way to encode symmetry.
1. New variables and constraints can be generated during the search
   process, conditioned on variables getting particular assignments.

While taffy can serve as a general purpose constraint solver, my ultimate
purpose in creating it is to implement the
[hundred year function](http://sciolizer.com/blog/2012/09/10/the-hundred-year-function/),
and so I don't plan on adding a rich collection of constraint and data types
to the solver.

An example of how to use the constraint solver as a simple sat solver is given
in src/SatExample.hs.

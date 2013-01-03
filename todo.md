Essential
=========

* Check for empty variables in propagateEffects (do not rely only on invocation of constraint)

Performance
===========

* Unit literal optimization (in the example)
* Clause learning (solver and example)
* Better variable ordering / topology tracking
* Better value ordering
* Random restarts
* ivarPreviousAssignments

Memory
======

* Constraint garbage collection
* Smarter collectable in runEffects
* Variable garbage collection
* Constraint topology

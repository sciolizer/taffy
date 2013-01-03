Essential
=========

* Check for empty variables in propagateEffects (do not rely only on invocation of constraint)
* Better value ordering (this is essential for avoiding infinite loops)

Performance
===========

* Unit literal optimization (in the example)
* Clause learning (solver and example)
* Better variable ordering / topology tracking
* Random restarts
* ivarPreviousAssignments

Memory
======

* Constraint garbage collection
* Smarter collectable in runEffects
* Variable garbage collection
* Constraint topology

package com.sciolizer.taffy

trait Instantiator[Constraint, Value] extends ConstraintInstantiator[Constraint] with VariableInstantiator[Value]
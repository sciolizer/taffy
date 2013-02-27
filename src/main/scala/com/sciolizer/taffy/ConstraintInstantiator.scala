package com.sciolizer.taffy

trait ConstraintInstantiator[-Constraint] {

  def newConstraint(constraint: Constraint)

}

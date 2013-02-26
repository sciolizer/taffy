package com.sciolizer.taffy.domains.disjunction

import com.sciolizer.taffy

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 1/31/13
 * Time: 10:11 AM
 */
class Inference[Booleans] extends taffy.Inference[Disjunction[Booleans]] {

  // Learn function does not need to be implemented, since nogood generation already covers it.

  /** Creates a copy of the given constraint with its variables swapped out for other variables.
    *
    * @param constraint constraint to make a copy of
    * @param substitution keys will be constraint.coverage. values are the desired replacement variables
    * @return A copy of the given constraint, but with different variables.
    */
  def substitute[C <: Disjunction[Booleans]](constraint: C, substitution: Map[VarId, VarId]): Disjunction[Booleans] =
    constraint.substitute(substitution)
}


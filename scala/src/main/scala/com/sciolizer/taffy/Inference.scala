package com.sciolizer.taffy

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 1/28/13
 * Time: 9:27 AM
 */

trait Inference[Constraint] {
  type VarId = Int
//  type MixedConstraint[+C, +V] = Either[NoGood[V], C]

  /**
   * The first unique implication point might be a key in constraints if the chain of constraint revisions
   * boomeranged back to the FUIP.
   * @param constraints
   * @return
   */
//  def learn(constraints : List[(VarId, MixedConstraint[Constraint, Values])]) : List[(C /* new constraint */,List[MixedConstraint[C, V]] /* generated from */)] = List.empty

  def superSimpleLearn[C <: Constraint](vars: Set[VarId], constraints: Set[C]): Traversable[(Constraint, Set[C])] = List.empty

  /** Creates a copy of the given constraint with its variables swapped out for other variables.
    *
    * @param constraint constraint to make a copy of
    * @param substitution keys will be constraint.coverage. values are the desired replacement variables
    * @return A copy of the given constraint, but with different variables.
    */
  def substitute[C <: Constraint](constraint: C, substitution: Map[VarId, VarId]): Constraint
}

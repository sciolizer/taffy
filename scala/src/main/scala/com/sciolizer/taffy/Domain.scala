package com.sciolizer.taffy

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 1/28/13
 * Time: 9:27 AM
 */

trait Domain[Constraint, Variables, Variable] {
  type VarId = Int
  type MixedConstraint = Either[NoGood[Variables], Constraint]

  /**
   * The first unique implication point might be a key in constraints if the chain of constraint revisions
   * boomeranged back to the FUIP.
   * @param constraints
   * @return
   */
  def learn(constraints : List[(VarId, MixedConstraint)]) : List[(Constraint /* new constraint */,List[MixedConstraint] /* generated from */)] = List.empty

  def superSimpleLearn(vars: Set[VarId], constraints: Set[MixedConstraint]): List[(Constraint, List[MixedConstraint])] = List.empty

  def revise(rw : ReadWrite[Variables, Variable], c: Constraint) : Boolean

  def coverage(c : Constraint) : collection.Set[VarId]

  // Substitution will always contain keys for at least everything in coverage.
  def substitute(c: Constraint, substitution: Map[VarId, VarId]): Constraint
}

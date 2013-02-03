package taffy

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

  def revise(rw : ReadWrite[Variables, Variable], c: Constraint) : Boolean

  def coverage(c : Constraint) : collection.Set[VarId]
}

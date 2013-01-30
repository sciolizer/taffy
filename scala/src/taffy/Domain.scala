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

  def learn(firstUniqueImplicationPoint: VarId, constraints : List[(VarId, MixedConstraint)]) : List[(Constraint /* new constraint */,List[MixedConstraint] /* generated from */)] = List.empty

  def revise(rw : ReadWrite[Constraint, Variables, Variable], c: Constraint) : Boolean

  def coverage(c : Constraint) : collection.Set[VarId]
}

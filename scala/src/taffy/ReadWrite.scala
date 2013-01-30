package taffy

import taffy.ReadWrite.{Accepts, Is, Rejects, Contains}
import collection.mutable

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 1/28/13
 * Time: 9:32 AM
 */

class ReadWrite[Variables, Variable](graph: ImplicationGraph[Variables, Variable],
                                     reads: mutable.Set[Int], // var ids, for installing watchers
                                     writes: mutable.Set[Int], // var ids, for potentially removing vars from unassigned
                                     ranger: Ranger[Variables, Variable]) {
  type VarId = Int
  type AssignmentId = Int
  private val assignmentReads: mutable.Set[AssignmentId] = mutable.Set()

  // todo: do safety check with the coverage function
  def readVar(v : VarId) : Variables = {
    reads += v
    val aid = graph.mostRecentAssignment(v)
    assignmentReads += aid
    graph.values(aid)
  }

  /**
   * Similar to calling readVar and verifying that the returned set is a singleton
   * containing the given value. You should use this function, if you can,
   * instead of using readVar, since it communicates back to the solver,
   * "I am interested in this particular value", which means the solver can
   * execute a more efficient watched literal strategy.
   *
   * todo: a safety check with the coverage function
   *
   * @param v The variable you want to read
   * @param value The value you hope the variable contains.
   * @return true iff the variable is currently a singleton with the given value. Returns false
   *         if either the variable has no values (meaning the problem is in a contradictory state),
   *         or if the variable still has at least two possible values that don't violate any
   *         constraints.
   */
  def contains(v : VarId, value : Variable) : Contains = {
    val candidates: Variables = readVar(v)
    if (ranger.isEmpty(ranger.intersection(candidates, ranger.toSingleton(value)))) {
      Rejects()
    } else if (ranger.isSingleton(candidates)) {
      Is()
    } else {
      Accepts()
    }
  }

  def setVar(v : VarId, value : Variable) {
    intersectVar(v, ranger.toSingleton(value))
  }

  def intersectVar(v : VarId, values : Variables) {
    replace(v, ranger.intersection(_, values))
  }

  def shrinkVar(v : VarId, value : Variable) {
    replace(v, ranger.subtraction(_, ranger.toSingleton(value)))
  }

  private def replace(v: VarId, replacer: Variables => Variables) {
    val original = graph.readVar(v)
    val replacement = replacer(original)
    if (!ranger.isEmpty(ranger.subtraction(original, replacement))) writes += v
    val reads = Set.empty ++ assignmentReads // is there a better way? Scala collections confuse me.
    graph.implies(v, replacement, reads)
  }
}

object ReadWrite {
  abstract class Contains
  case class Accepts() extends Contains
  case class Rejects() extends Contains
  case class Is() extends Contains
}

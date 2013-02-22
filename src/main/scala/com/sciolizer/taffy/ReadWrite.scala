package com.sciolizer.taffy

import com.sciolizer.taffy.ReadWrite.{Accepts, Is, Rejects, Contains}
import collection.mutable

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 1/28/13
 * Time: 9:32 AM
 */

trait ReadWrite[Values, Value] {
  type VarId = Int

  protected def ranger: Ranger[Values, Value]

  protected def replace(v: VarId, replacer: Values => Values)

  def readVar(v: VarId): Values

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
  def contains(v : VarId, value : Value) : Contains = {
    val candidates: Values = readVar(v)
    if (ranger.isEmpty(ranger.intersection(candidates, ranger.toSingleton(value)))) {
      Rejects()
    } else if (ranger.isSingleton(candidates)) {
      Is()
    } else {
      Accepts()
    }
  }

  def setVar(v : VarId, value : Value) {
    intersectVar(v, ranger.toSingleton(value))
  }

  def intersectVar(v : VarId, values : Values) {
    replace(v, ranger.intersection(_, values))
  }

  def shrinkVar(v : VarId, value : Value) {
    replace(v, ranger.subtraction(_, ranger.toSingleton(value)))
  }
}

class ReadWriteMock[Variables, Variable](
    protected val initial: Map[Int, Variables],
    protected val r: Ranger[Variables, Variable])
  extends ReadWrite[Variables, Variable] {

  val overlay: mutable.Map[VarId, Variables] = mutable.Map.empty
  def changes = overlay

  protected def ranger: Ranger[Variables, Variable] = r

  def readVar(v: VarId): Variables = {
    overlay.get(v) match {
      case None => initial(v)
      case Some(x) => x
    }
  }

  protected def replace(v: VarId, replacer: (Variables) => Variables) {
    overlay(v) = replacer(readVar(v))
  }
}

class ReadWriteGraph[Constraint, Variables, Variable](graph: ImplicationGraph[Constraint, Variables, Variable],
                                     constraint: Either[NoGood[Variables], Constraint],
                                     reads: mutable.Set[Int], // var ids, for installing watchers
                                     writes: mutable.Set[Int], // var ids, for potentially removing vars from unassigned
                                     r: Ranger[Variables, Variable]) extends ReadWrite[Variables, Variable] {
  type AssignmentId = Int
  private val assignmentReads: mutable.Set[AssignmentId] = mutable.Set()

  protected def ranger: Ranger[Variables, Variable] = r

  // todo: do safety check with the coverage function
  def readVar(v : VarId) : Variables = {
    reads += v
    val aid = graph.mostRecentAssignment(v)
    assignmentReads += aid
    graph.values(aid)
  }

  protected def replace(v: VarId, replacer: Variables => Variables) {
    val original = graph.readVar(v)
    val replacement = replacer(original)
    if (!ranger.isEmpty(ranger.subtraction(original, replacement))) {
      writes += v
      val rs = Set.empty ++ assignmentReads // is there a better way? Scala collections confuse me.
      graph.implies(v, replacement, rs, constraint)
    }
  }
}

object ReadWrite {
  abstract class Contains
  case class Accepts() extends Contains
  case class Rejects() extends Contains
  case class Is() extends Contains
}

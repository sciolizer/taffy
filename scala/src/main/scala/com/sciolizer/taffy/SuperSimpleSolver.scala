package com.sciolizer.taffy

import scala.collection.mutable

/**
 * Algorithm taken directly from page 215 of Artifical Intelligence: A Modern approach.
 *
 *
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 2/6/13
 * Time: 2:55 PM
 */
class SuperSimpleSolver[Constraint, Variables, Variable]( domain: Domain[Constraint, Variables, Variable],
                                                          problem: Problem[Constraint, Variables, Variable],
                                                          ranger: Ranger[Variables, Variable]) {
  type VarId = Int
  type MixedConstraint = Either[NoGood[Variables], Constraint]

  type Assignment = Vector[Variable]
  type PartialAssignment = Map[VarId, Variables]

  var watchers: mutable.Map[VarId, mutable.Set[Constraint]] = mutable.Map().withDefault(_ => mutable.Set())
  val initialAssignment: PartialAssignment = (0 until problem.numVariables).map(i => (i -> problem.candidateValues)).toMap

  for (constraint <- problem.constraints) {
    val vars: mutable.Set[VarId] = mutable.Set()
    val rw = tracker(initialAssignment)
    domain.revise(rw, constraint)
    for (variable <- vars) {
      watchers(variable) += constraint
    }
  }

  def tracker(assignment: PartialAssignment): ReadWriteTracker[Variables, Variable] = {
    new ReadWriteTracker[Variables, Variable](initialAssignment ++ assignment, ranger)
  }

  /**
   * Infers from the given partial assignment as many deductions as possible, without guessing.
   *
   * @param assignment Partial assignment
   * @return
   */
  def maintainArcConsistency(assignment: PartialAssignment): Option[PartialAssignment] = {
    val constraints: mutable.Set[Constraint] = mutable.Set()
    constraints ++= problem.constraints
    var ret: PartialAssignment = assignment
    while (!constraints.isEmpty) {
      val constraint: Constraint = constraints.head
      constraints -= constraint
      revise(constraint, ret) match {
        case None => return None
        case Some(pa) =>
          for ((vid, _) <- pa) {
            constraints ++= watchers(vid)
          }
          ret = ret ++ pa
      }
    }
    Some(ret)
  }

  /**
   * Runs the constraint on the given partial assignment.
   *
   * @param constraint Constraint
   * @param assignment Current assignment
   * @return None if the constraint is unsatisfiable, or the deductions (possibly empty) if it is satisfiable.
   */
  def revise(constraint: Constraint, assignment: PartialAssignment): Option[PartialAssignment] = {
    val rw = tracker(assignment)
    if (!domain.revise(rw, constraint)) {
      None
    } else {
      Some[PartialAssignment](Map.empty[VarId, Variables] ++ rw.changes)
    }
  }

  /**
   * Finds ALL conflicting subsets for which no subset of the subset is conflicting.
   *
   * @param conflictingAssignment An assignment which violates some constraint. Behavior of this function is
   *                              undefined if the given partial assignment is arc-consistent.
   * @return All proper subsets of the given partial assignment that cannot be made smaller, along with the
   *         constraints that are violated by them. If the given partial assignment is already
   *         minimal, the empty iterator is returned.
   */
  def minimizeConflict(conflictingAssignment: PartialAssignment): Iterator[(Set[VarId], Set[Constraint])] = {
    conflictingAssignment.iterator.flatMap(x => {
      val subAssignment = conflictingAssignment - x._1
      val rejs = rejectors(subAssignment)
      if (rejs.isEmpty) List.empty[(Set[VarId], Set[Constraint])].iterator else {
        val subs: Iterator[(Set[VarId], Set[Constraint])] = minimizeConflict(subAssignment)
        if (subs.isEmpty)
          Iterator.single[(Set[VarId], Set[Constraint])]((subAssignment.keySet, rejectors(subAssignment)))
        else
          subs
      }
    })
  }

  /**
   * Returns all constraints violated by the given assignment.
   *
   * @param assignment A partial assignment.
   * @return Set of constraints which reject the assignment, or the empty set if the assignment is arc-consistent.
   */
  def rejectors(assignment: PartialAssignment): Set[Constraint] = {
    problem.constraints.filter(revise(_, assignment).isDefined)
  }

  /*
  def backtrackingSearch(assignment: Assignment): Option[Map[VarId, Variable]] = {
    if (isComplete(assignment)) {
      return Some(assignment)
    }
    val variable: VarId = selectUnassignedVariable(assignment)
    for (value <- orderDomainValues(variable, assignment)) {
      val newAssignment = assignment.updated(variable, value)
      inferences(variable, value) match {
        case None =>
        case Some(overlay) =>
          val newNewAssignment = newAssignment ++ overlay
          backtrackingSearch(newNewAssignment) match {
            case None =>
            case Some(a) => return Some(a)
          }
      }
    }
    None
  }

  def isComplete(assignment: Assignment): Boolean = {

  }

  def selectUnassignedVariable(assignment: Assignment): VarId = {

  }

  def orderDomainValues(variable: VarId, assignment: Assignment): Iterator[Variable] = {

  }

  def inferences(variable: VarId, value: Variable): Option[Map[VarId, Variable]] = {

  }
  */
}

class ReadWriteTracker[Variables, Variable](initial: Map[Int, Variables], r: Ranger[Variables, Variable]) extends ReadWriteMock(initial: Map[Int, Variables], r: Ranger[Variables, Variable]) {
  var vars: Set[VarId] = Set.empty
  def reads = vars
  override def readVar(v: VarId): Variables = {
    vars += v
    super.readVar(v)
  }
}


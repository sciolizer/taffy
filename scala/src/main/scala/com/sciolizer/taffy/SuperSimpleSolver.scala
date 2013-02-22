package com.sciolizer.taffy

import scala.collection.mutable

/**
 * Algorithm taken directly from page 215 of Artifical Intelligence: A Modern approach.
 *
 * Rather than transform this into a more efficient version, I think I'll
 * use it to test against a more efficient version. e.g. generate random
 * sat problems, and if the efficient one says "no solution", make
 * sure that the slow one also says "no solution". (If a solution is provided,
 * obviously I can just check it.)
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 2/6/13
 * Time: 2:55 PM
 */
class SuperSimpleSolver[Constraint <: Revisable[Variables, Variable], Variables, Variable](
    val domain: Inference[Constraint],
    val problem: Problem[Constraint, Variables, Variable],
    val ranger: Ranger[Variables, Variable]) {

  type VarId = Int
  type MixedConstraint = Either[NoGood[Variables], Constraint]

  type Assignment = Vector[Variable]
  type PartialAssignment = Map[VarId, Variables]

  private val _learned: mutable.Set[MixedConstraint] = mutable.Set.empty ++ problem.constraints.flatMap(x => isomorphicConstraints(Right(x)))
  def learned: Set[MixedConstraint] = Set.empty ++ _learned

  class Watchers(initialAssignment: PartialAssignment) {

    private var registered: mutable.Map[VarId, mutable.Set[MixedConstraint]] = mutable.Map()

    problem.constraints.foreach(x => watch(Right(x), initialAssignment))
    _learned.foreach(x => watch(x, initialAssignment))

    def watchers(vid: VarId): Set[MixedConstraint] = {
      registered.get(vid) match {
        case None =>
          Set.empty
        case Some(x) =>
          Set.empty ++ x
      }
    }

    def watch(constraint: MixedConstraint, assignment: PartialAssignment) {
      val rw = tracker(assignment)
      satisfiable(constraint, rw)
      for (variable <- rw.reads) {
        registered.get(variable) match {
          case None =>
            registered(variable) = mutable.Set(constraint)
          case Some(s) =>
            s += constraint
        }
      }
    }
  }

  def tracker(assignment: PartialAssignment): ReadWriteTracker[Variables, Variable] = {
    new ReadWriteTracker[Variables, Variable](assignment, ranger)
  }

  def newConsistencySustainer(assignment: PartialAssignment): ConsistencySustainer = {
    new ConsistencySustainer(assignment)
  }

  class ConsistencySustainer(assignment: PartialAssignment) {

    private var _implication: PartialAssignment = assignment
    private val _propagators: mutable.Set[MixedConstraint] = mutable.Set.empty
    def propagators: Set[MixedConstraint] = Set.empty ++ _propagators
    private val _modifiedVariables: mutable.Set[VarId] = mutable.Set.empty
    def impliedVariables: Set[VarId] = Set.empty ++ _modifiedVariables
    def implication: PartialAssignment = _implication

    val rejector: Option[MixedConstraint] = maintainArcConsistency()

    private def maintainArcConsistency(): Option[MixedConstraint] = {
      val watchers = new Watchers(assignment)
      val constraints: mutable.Set[MixedConstraint] = mutable.Set()
      constraints ++= problem.constraints.map(Right(_)) ++ _learned
      //    var implied: Map[VarId, List[(Variables, Constraint)]] = Map.empty
      while (!constraints.isEmpty) {
        val constraint = constraints.head
        constraints -= constraint
        revise(constraint, _implication) match {
          case None =>
            return Some[MixedConstraint](constraint)
          case Some(pa) =>
            if (!pa.isEmpty) {
              _propagators += constraint
              _implication = _implication ++ pa
              for ((vid, vals) <- pa) {
                _modifiedVariables += vid
                // Variable assignment changed, so we need to re-examine all constraints covering that variable.
                constraints ++= watchers.watchers(vid)
                // With new assignments, constraint might read from more variables than it did before, so we need
                // to re-watch it.
                watchers.watch(constraint, assignment ++ _implication)
                //            implied = implied.updated(vid, (vals, constraint) +: implied(vid))
              }
            }
        }
      }
      None
    }
  }

  /**
   * Runs the constraint on the given partial assignment.
   *
   * @param constraint Constraint
   * @param assignment Current assignment
   * @return None if the constraint is unsatisfiable, or the deductions (possibly empty) if it is satisfiable.
   */
  def revise(constraint: MixedConstraint, assignment: PartialAssignment): Option[PartialAssignment] = {
    val rw = tracker(assignment)
    if (!satisfiable(constraint, rw) || rw.changes.exists(x => ranger.isEmpty(x._2))) {
      None
    } else {
      val changed: PartialAssignment = rw.changes.filter(x => !ranger.equal(assignment(x._1), x._2)).toMap
      Some[PartialAssignment]((Map.empty[VarId, Variables] ++ changed))
    }
  }

  private def satisfiable(constraint: MixedConstraint, rw: ReadWrite[Variables, Variable]): Boolean = {
    constraint match {
      case Left(noGood) =>
        noGood.revise(rw, ranger)
      case Right(c) =>
        c.revise(rw)
    }
  }

  def minimize(conflictingAssignment: PartialAssignment): Set[Set[VarId]] = new ConflictMinimizer(conflictingAssignment).minimized

  class ConflictMinimizer(conflictingAssignment: PartialAssignment) {

    abstract class AcceptReject
    case class Accept() extends AcceptReject
    case class NonMinimalReject() extends AcceptReject
    case class MinimalReject() extends AcceptReject

    private val accepting: mutable.Set[Set[VarId]] = mutable.Set.empty
    private val rejecting: mutable.Set[Set[VarId]] = mutable.Set.empty

    private def rejects(vars: Set[VarId]): AcceptReject = {
      // if a proper subset rejects, then so do we
      if (rejecting.exists(x => x.subsetOf(vars) && !x.equals(vars))) return NonMinimalReject()
      if (rejecting.contains(vars)) return MinimalReject()
      // if a superset accepts, then so do we
      if (accepting.exists(x => vars.subsetOf(x))) return Accept()
      // otherwise, compute
      val sustainer = new ConsistencySustainer(conflictingAssignment ++ (conflictingAssignment.keySet -- vars).map(vid => (vid -> problem.candidateValues)))
      sustainer.rejector match {
        case None =>
          accepting += vars
          Accept()
        case Some(_) =>
          rejecting += vars
          val minimal = vars.forall(v => rejects(vars - v) match {
            case Accept() => true
            case _ => false
          })
          if (minimal) MinimalReject() else NonMinimalReject()
      }
    }
                                 /*
    private val considered: mutable.Set[Set[VarId]] = mutable.Set.empty

    private def consider(vars: Set[VarId]) {
      if (considered.contains(vars)) return
      considered += vars
      rejects(vars) match {
        case NonMinimalReject() =>
          for (vid <- vars) {
            consider(vars - vid)
          }
        case MinimalReject() =>
        case Accept() =>
      }
    }      */

    // Every set is a minimal conflict, but the outer set is not complete. (There might be minimal conflicts
    // not contained.) There will always be at least one minimal conflict.
    lazy val minimized: Set[Set[VarId]] = {
      println("considering: " + conflictingAssignment.keySet)
      rejects(conflictingAssignment.keySet) // populate accepting and rejecting
      println("considered")
      val ret = (Set.empty ++ rejecting).filter(x => rejects(x) match {
        case MinimalReject() => true
        case _ => false
      })
      println("minimals: " + ret)
      ret
    }
  }

  def backtrackingSearch(assignment: PartialAssignment, listener: AssignmentListener[Variable] = SuperSimpleSolver.nullAssignmentListener): Option[Map[VarId, Variable]] = {
    completeAssignment(assignment) collect { case Some(a: Map[VarId, Variable]) => return Some(a) }
    // todo: run MAC before picking a variable, if this is the first entrance into backtrackingSearch.
    val variable: VarId = selectUnassignedVariable(assignment)
    println("picking variable: " + variable)
    for (value <- orderDomainValues(variable, assignment)) {
      val newAssignment: PartialAssignment = assignment.updated(variable, ranger.toSingleton(value))
      val sustainer = new ConsistencySustainer(newAssignment)
      val newNewAssignment: PartialAssignment = sustainer.implication
      sustainer.rejector match {
        case None =>
          listener.assignment(variable, value)
          backtrackingSearch(newNewAssignment) collect { case Some(a: Map[VarId, Variable]) => return Some(a) }
        case Some(c) =>
          for (minimalConflict <- minimize(newNewAssignment)) {
            learn(Left(new NoGood(newNewAssignment.filterKeys(minimalConflict.contains(_)))))
            val reduced = domain.superSimpleLearn(
              sustainer.impliedVariables -- minimalConflict,
              sustainer.propagators collect { case Right(x) => x }) map { _._1 }
            println("learned: " + reduced)
            reduced.foreach(x => learn(Right(x)))
          }
      }
    }
    None
  }

  def learn(constraint: MixedConstraint) {
    _learned += constraint
    _learned ++= isomorphicConstraints(constraint)
  }

  def isomorphicConstraints(constraint: MixedConstraint): mutable.Set[MixedConstraint] = {
    val ret: mutable.Set[MixedConstraint] = mutable.Set.empty
    val covered: collection.Set[VarId] = constraint match {
      case Left(noGood) => noGood.coverage()
      case Right(c) => c.coverage
    }
    val vars = covered.toList
    for (sequence <- problem.isomorphisms.get(vars)) {
      val substitution: Map[VarId, VarId] = vars.zip(sequence).toMap
      ret += substitute(constraint, substitution)
    }
    ret
  }

  def substitute(c: MixedConstraint, subst: Map[VarId, VarId]): MixedConstraint = c match {
    case Left(noGood) => Left(noGood.substitute(subst))
    case Right(c) => Right(domain.substitute(c, subst))
  }

  def completeAssignment(assignment: PartialAssignment): Option[Map[VarId, Variable]] = {
    case class NotComplete() extends Exception
    try {
      Some((for ((vid, values) <- assignment) yield {
        if (ranger.isSingleton(values)) {
          (vid, ranger.fromSingleton(values))
        } else {
          throw new NotComplete()
        }
      }).toMap)
    } catch {
      case NotComplete() => None
    }
  }

  def selectUnassignedVariable(assignment: PartialAssignment): VarId = {
    var min = -1
    var minSize = Int.MaxValue
    for ((vid, vars) <- assignment) {
      val size = ranger.size(vars)
      if (size == 2) {
        return vid
      } else if (size < minSize && size > 1) {
        min = vid
        minSize = size
      } else if (size == 0) {
        throw new IllegalArgumentException("Assignment is conflicting.")
      }
    }
    if (min == -1) throw new IllegalArgumentException("Assignment is complete.")
    min
  }

  def orderDomainValues(variable: VarId, assignment: PartialAssignment): Iterator[Variable] = {
    var candidates = assignment.getOrElse(variable, problem.candidateValues)
    Iterator.continually {
      if (ranger.isEmpty(candidates)) {
        None
      } else {
        val ret = ranger.pick(candidates)
        candidates = ranger.subtraction(candidates, ranger.toSingleton(ret))
        Some(ret)
      }
    }.takeWhile(_.isDefined).map(_.get)
  }
}
object SuperSimpleSolver {
  type VarId = Int
  type Implications[Constraint, Variables] = Map[VarId, List[(Variables, Constraint)]]
  type PartialAssignment[Variables] = Map[VarId, Variables]
  def nullAssignmentListener[Variable]: AssignmentListener[Variable] = new AssignmentListener[Variable] {
    def assignment(vid: Int, value: Variable) { }
  }
}

class ReadWriteTracker[Variables, Variable](initial: Map[Int, Variables], r: Ranger[Variables, Variable]) extends ReadWriteMock(initial: Map[Int, Variables], r: Ranger[Variables, Variable]) {
  private var vars: Set[VarId] = Set.empty
  def reads = vars
  override def readVar(v: VarId): Variables = {
    vars += v
    super.readVar(v)
  }
}

trait AssignmentListener[Value] {
  def assignment(vid: Int, value: Value)
}
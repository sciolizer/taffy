package com.sciolizer.taffy

import scala.collection.mutable
import com.sciolizer.taffy.SuperSimpleSolver.Propagation

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
  type TPropagation = Propagation[Constraint, Variables]

  private val nogoods: mutable.Set[NoGood[Variables]] = mutable.Set.empty

  class Watchers(initialAssignment: PartialAssignment) {

    private var registered: mutable.Map[VarId, mutable.Set[Constraint]] = mutable.Map()

    problem.constraints.foreach(watch(_, initialAssignment))

    def watchers(vid: VarId): Set[Constraint] = {
      registered.get(vid) match {
        case None =>
          Set.empty
        case Some(x) =>
          Set.empty ++ x
      }
    }

    def watch(constraint: Constraint, assignment: PartialAssignment) {
      val rw = tracker(assignment)
      domain.revise(rw, constraint)
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

  /**
   * Infers from the given partial assignment as many deductions as possible, without guessing.
   *
   * @param assignment Partial assignment
   * @return
   */
  def maintainArcConsistency(assignment: PartialAssignment): TPropagation = {
    val watchers = new Watchers(assignment)
    var overlay: PartialAssignment = assignment
    val constraints: mutable.Set[Constraint] = mutable.Set()
    constraints ++= problem.constraints
    var implied: Map[VarId, List[(Variables, Constraint)]] = Map.empty.withDefaultValue(List.empty)
    while (!constraints.isEmpty) {
      val constraint: Constraint = constraints.head
      constraints -= constraint
      revise(constraint, overlay) match {
        case None =>
          return Propagation[Constraint, Variables](Some[Constraint](constraint), implied)
        case Some(pa) =>
          overlay = overlay ++ pa
          for ((vid, vals) <- pa) {
            // Variable assignment changed, so we need to re-examine all constraints covering that variable.
            constraints ++= watchers.watchers(vid)
            // With new assignments, constraint might read from more variables than it did before, so we need
            // to re-watch it.
            watchers.watch(constraint, assignment ++ overlay)
            implied = implied.updated(vid, (vals, constraint) +: implied(vid))
          }
      }
    }
    Propagation(None, implied)
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
      Some[PartialAssignment]((Map.empty[VarId, Variables] ++ rw.changes).asInstanceOf[PartialAssignment]) // ugh... why do I keep ending up with these casts?
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
      val propagation = maintainArcConsistency(conflictingAssignment ++ (conflictingAssignment.keySet -- vars).map(vid => (vid -> problem.candidateValues)))
      propagation.rejector match {
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

    private val considered: mutable.Set[Set[VarId]] = mutable.Set.empty

    private def consider(vars: Set[VarId]) {
      if (considered.contains(vars)) return
      rejects(vars) match {
        case NonMinimalReject() =>
          for (vid <- vars) {
            consider(vars - vid)
          }
        case MinimalReject() =>
        case Accept() =>
      }
    }

    lazy val minimized: Set[Set[VarId]] = {
      consider(conflictingAssignment.keySet) // populate accepting and rejecting
      (Set.empty ++ rejecting).filter(x => rejects(x) match {
        case MinimalReject() => true
        case _ => false
      })
    }
  }

  def backtrackingSearch(assignment: PartialAssignment): Option[Map[VarId, Variable]] = {
    completeAssignment(assignment) match {
      case Some(a) => return Some(a)
      case None =>
    }
    val variable: VarId = selectUnassignedVariable(assignment)
    for (value <- orderDomainValues(variable, assignment)) {
      val newAssignment: PartialAssignment = assignment.updated(variable, ranger.toSingleton(value))
      val propagation = maintainArcConsistency(newAssignment)
      val newNewAssignment: PartialAssignment = newAssignment ++ propagation.partialAssignment
      propagation match {
        case Propagation(None, implied) =>
          backtrackingSearch(newNewAssignment) match {
            case None =>
            case Some(a) => return Some(a)
          }
        case Propagation(Some(c), implied) =>
          for (minimalConflict <- minimize(newNewAssignment)) {
            // todo: make test for this
            nogoods += new NoGood(newNewAssignment.filterKeys(minimalConflict.contains(_)))
          }
      }
    }
    None
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
  case class Propagation[Constraint, Variables](rejector: Option[Constraint], implied: Implications[Constraint, Variables]) {
    lazy val partialAssignment: PartialAssignment[Variables] = implied.mapValues(_.head._1)
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


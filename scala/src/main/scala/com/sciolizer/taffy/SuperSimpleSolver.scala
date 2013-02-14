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

  private val _noGoods: mutable.Set[NoGood[Variables]] = mutable.Set.empty
  def noGoods: Set[NoGood[Variables]] = Set.empty ++ _noGoods

  class Watchers(initialAssignment: PartialAssignment) {

    private var registered: mutable.Map[VarId, mutable.Set[MixedConstraint]] = mutable.Map()

    problem.constraints.foreach(x => watch(Right(x), initialAssignment))
    _noGoods.foreach(x => watch(Left(x), initialAssignment))

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

  /**
   * Infers from the given partial assignment as many deductions as possible, without guessing.
   *
   * @param assignment Partial assignment
   * @return
   */
  def maintainArcConsistency(assignment: PartialAssignment): TPropagation = {
    val watchers = new Watchers(assignment)
    var overlay: PartialAssignment = assignment
    val constraints: mutable.Set[MixedConstraint] = mutable.Set()
    constraints ++= problem.constraints.map(Right(_)) ++ _noGoods.map(Left(_))
//    var implied: Map[VarId, List[(Variables, Constraint)]] = Map.empty
    while (!constraints.isEmpty) {
      val constraint = constraints.head
      constraints -= constraint
      revise(constraint, overlay) match {
        case None =>
          return Propagation[Constraint, Variables](Some[MixedConstraint](constraint), assignment ++ overlay)
        case Some(pa) =>
          overlay = overlay ++ pa
          for ((vid, vals) <- pa) {
            // Variable assignment changed, so we need to re-examine all constraints covering that variable.
            constraints ++= watchers.watchers(vid)
            // With new assignments, constraint might read from more variables than it did before, so we need
            // to re-watch it.
            watchers.watch(constraint, assignment ++ overlay)
//            implied = implied.updated(vid, (vals, constraint) +: implied(vid))
          }
      }
    }
    Propagation(None, assignment ++ overlay)
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
    if (!satisfiable(constraint, rw)) {
      None
    } else {
      Some[PartialAssignment]((Map.empty[VarId, Variables] ++ rw.changes).asInstanceOf[PartialAssignment]) // ugh... why do I keep ending up with these casts?
    }
  }

  private def satisfiable(constraint: MixedConstraint, rw: ReadWrite[Variables, Variable]): Boolean = {
    constraint match {
      case Left(noGood) =>
        noGood.revise(rw, ranger)
      case Right(c) =>
        domain.revise(rw, c)
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
            _noGoods += new NoGood(newNewAssignment.filterKeys(minimalConflict.contains(_)))
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
  case class Propagation[Constraint, Variables](rejector: Option[Either[NoGood[Variables], Constraint]], partialAssignment: PartialAssignment[Variables])
}

class ReadWriteTracker[Variables, Variable](initial: Map[Int, Variables], r: Ranger[Variables, Variable]) extends ReadWriteMock(initial: Map[Int, Variables], r: Ranger[Variables, Variable]) {
  private var vars: Set[VarId] = Set.empty
  def reads = vars
  override def readVar(v: VarId): Variables = {
    vars += v
    super.readVar(v)
  }
}


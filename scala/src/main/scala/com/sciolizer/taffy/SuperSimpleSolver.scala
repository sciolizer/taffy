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

  val initialAssignment: PartialAssignment = (0 until problem.numVariables).map(i => (i -> problem.candidateValues)).toMap

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
      for (variable <- rw.vars) {
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
    new ReadWriteTracker[Variables, Variable](initialAssignment ++ assignment, ranger)
  }

  /**
   * Infers from the given partial assignment as many deductions as possible, without guessing.
   *
   * @param assignment Partial assignment
   * @return
   */
  def maintainArcConsistency(assignment: PartialAssignment): TPropagation = {
    val watchers = new Watchers(initialAssignment ++ assignment)
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
                                    /*
    // the key is minimal if the value is Some
    val isMinimal: mutable.Map[Set[VarId], Option[Implications]] = mutable.Map.empty

    /**
     * Finds ALL conflicting subsets for which no subset of the subset is conflicting.
     *
     * @param conflictingAssignment An assignment which violates some constraint. Behavior of this function is
     *                              undefined if the given partial assignment is arc-consistent.
     * @return All proper subsets of the given partial assignment that cannot be made smaller, along with the
     *         constraints that are violated by them. If the given partial assignment is already
     *         minimal, the empty iterator is returned. Returns None
     */
    def minimizeConflict(ca: PartialAssignment): Iterator[(Set[VarId], Set[Constraint])] = {
      // todo: this is not right
      // In order for this to be useful, we need to find whether the assignment is conflicting AFTER
      // propagation (after arc consistency is maintained). Otherwise, the subsets we pick are
      // useless, because they already have rejecting constraints. We want to find subsets that
      // are contradictory but which no current constraint rejects.

      // Also, I should add some memoization: removing the 1st and then the 2nd is the same as removing
      // the 2nd and the 1st, but the current implementation generates both cases.

      conflictingAssignment.iterator.flatMap(x => {
        val subAssignment = conflictingAssignment - x._1
        isMinimal.get(subAssignment.keySet) match {
          case Some(_) => Iterator.empty
          case None =>
            val propagation: Propagation = maintainArcConsistency(subAssignment)
            propagation.rejector match {
              case None =>
                isMinimal(subAssignment.keySet) = None
                Iterator.empty
              case Some(rej) =>
                isMinimal(subAssignment.keySet) = Some(propagation)
            }
            val rejs = rejectors(subAssignment)
            if (rejs.isEmpty) List.empty[(Set[VarId], Set[Constraint])].iterator else {
              val subs: Iterator[(Set[VarId], Set[Constraint])] = minimizeConflict(subAssignment)
              if (subs.isEmpty)
                Iterator.single[(Set[VarId], Set[Constraint])]((subAssignment.keySet, rejs))
              else
                subs
            }
        }
      })
    }

    // shrinkable ++ fixed is assumed to be a conflicting assignment
    def minimal(shrinkable: List[VarId], fixed: List[VarId]): Iterator[List[VarId]] = {
      if (shrinkable.isEmpty) {
        Iterator.single(fixed)
      } else {
        val h = shrinkable.head
        val t = shrinkable.tail

      }
    }
                             */
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
      val propagation = maintainArcConsistency(conflictingAssignment.filterKeys(vars.contains(_)))
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
      /*
  /**
   * Returns all constraints violated by the given assignment.
   *
   * @param assignment A partial assignment.
   * @return Set of constraints which reject the assignment, or the empty set if the assignment is arc-consistent.
   */
  def rejectors(assignment: PartialAssignment): Set[Constraint] = {
    problem.constraints.filter(revise(_, assignment).isDefined)
  }
        */
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
object SuperSimpleSolver {
  type VarId = Int
  type Implications[Constraint, Variables] = Map[VarId, List[(Variables, Constraint)]]
  type PartialAssignment[Variables] = Map[VarId, Variables]
  case class Propagation[Constraint, Variables](rejector: Option[Constraint], implied: Implications[Constraint, Variables]) {
    lazy val partialAssignment: PartialAssignment[Variables] = implied.mapValues(_.head._1)
  }
}

class ReadWriteTracker[Variables, Variable](initial: Map[Int, Variables], r: Ranger[Variables, Variable]) extends ReadWriteMock(initial: Map[Int, Variables], r: Ranger[Variables, Variable]) {
  var vars: Set[VarId] = Set.empty
  def reads = vars
  override def readVar(v: VarId): Variables = {
    vars += v
    super.readVar(v)
  }
}


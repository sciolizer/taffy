package taffy

import collection.mutable.ArrayBuffer
import scala.collection.mutable
import collection.immutable.Stack

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 1/29/13
 * Time: 11:23 AM
 */
class ImplicationGraph[Variables, Variable](allValues: Variables, ranger: Ranger[Variables, Variable]) {
  type VarId = Int
  type AssignmentId = Int
  type DecisionLevel = Int
  private var dl = 0
  private val assignments: ArrayBuffer[(VarId, Variables, DecisionLevel)] = ArrayBuffer()
  private val implications: mutable.Map[AssignmentId, Set[AssignmentId]] = mutable.Map() // entry does not exist for decision variables
  private val varIndex: mutable.Map[VarId, Stack[AssignmentId]] = mutable.Map().withDefaultValue(Stack.empty)

  def implies(vid: VarId, values: Variables, because: Set[AssignmentId]): AssignmentId = {
    val ret: AssignmentId = record(vid, values)
    implications(ret) = because
    ret
  }

  def decide(vid: VarId, value: Variables) {
    dl += 1
    record(vid, value)
  }

  private def record(vid: VarId, values: Variables): Int = {
    val ret: AssignmentId = assignments.size
    assignments += ((vid, values, dl))
    varIndex(vid) = varIndex(vid).push(ret)
    ret
  }

  def decisionLevel = dl

  def isEmpty = assignments.isEmpty

  def mostRecentAssignment(vid: VarId): Option[AssignmentId] = {
    val stack: Stack[ImplicationGraph.this.type#AssignmentId] = varIndex(vid)
    if (stack.isEmpty) {
      None
    } else {
      Some(stack.top)
    }
  }

  def values(aid: AssignmentId): Variables = {
    assignments(aid)._2
  }

  def readVar(vid: VarId): Variables = {
    mostRecentAssignment(vid) match {
      case None => allValues
      case Some(aid) => values(aid)
    }
  }

  private def undoOne() {
    val i: Int = assignments.size - 1
    val vid = assignments.remove(i)._1
    implications.remove(i)
    if (assignments.isEmpty) {
      dl = 0
    } else {
      dl = assignments.last._3
    }
    varIndex(vid) = varIndex(vid).pop2._2
  }

  /*
  Calculate reason: This method is given a literal p and an empty vector.
  The constraint is the _reason_ for p being true, that is, during propagation,
  the current constraint enqueued p. The received vector is extended to include
  a set of assignments (represented as literals) implying p. The current variable
  assignments are guaranteed to be identical to that of the moment before
  the constraint propagated p. The literal p is also allowed to be the special
  constant _bottom_ in which case the reason for the clause being
  _conflicting_ should be returned through the vector.
   */
  /**
   * Adapted from the minisat paper.
   * @param confl
   */
  def fuip(): (NoGood[Variables], Set[VarId] /* rewound variables */) = {
    /*
    Ok, here's my current thoughts:
    because we have a setVar function, we can track the reasons ourselves.
    If a variable becomes unit because of shrink or intersection, and NOT because
    of setVar, then we treat the variable as a decision variable.
     */

    // var confl = conflicting
    val seen: mutable.Set[AssignmentId] = mutable.Set.empty
    var counter = 0
    var p: VarId = assignments.last._1
    val nogoods: mutable.Map[VarId, Variables] = mutable.Map()
    var out_btlevel = 0
    var lastReason: Variables = null.asInstanceOf[Variables]
    var rewound: Set[VarId] = Set.empty
//    println("starting fuip. first reason: " + firstReason)
//    println("variables: " + variables)
//    println("reasons: " + reasons)
//    printTrail()

    do {
      val p_reason: AssignmentId = mostRecentAssignment(p) match {
        case None => throw new RuntimeException("internal bug: can't find assignment for " + p)
        case Some(aid) => aid
      }
      for (aid <- implications(p_reason)) {
        if (!seen.contains(aid)) {
          seen += aid
          val assignment: (VarId, Variables, DecisionLevel) = assignments(aid)
          val vidLevel: DecisionLevel = assignment._3
          if (vidLevel == decisionLevel) { // todo: is this allowed to decrease over time?
            counter += 1
          } else if (vidLevel > 0) {
            nogoods(assignment._1) = assignment._2
            out_btlevel = math.max(out_btlevel, vidLevel)
          }
        }
      }

      do {
        val lastAssignment: (VarId, Variables, DecisionLevel) = assignments.last
        p = lastAssignment._1
        rewound = rewound + p
        lastReason = lastAssignment._2
        undoOne()
      } while (!seen.contains(p))
      counter -= 1
    } while (counter > 0)
    nogoods(p) = lastReason
    // this new constraint should be unit in the variable that is about to be tried next
    val nogood: NoGood[Variables] = new NoGood[Variables](nogoods)
    if (!nogood.isUnit[Variable](new ReadWrite(this, mutable.Set(), mutable.Set(), allValues, ranger), ranger)) {
      throw new RuntimeException("generated nogood is not unit: " + nogood)
    }
    // todo: do something with btlevel_out... I think there might be the possibility of an infinite loop if we don't
    // because if a constraint makes TWO assignments, but only one of them gets reverted, the constraint will
    // just make the same assignment again
    Tuple2(nogood, rewound)
//    println("ending fuip. nogood: " + nogood)
//    println("variables: " + variables)
//    println("reasons: " + reasons)
//    printTrail()
//    println("btlevel: " + out_btlevel) // todo: do something with this value

    /*
    First unique implication point:

void Solver.analyze(Constr confl, Vec<Lit> out_learnt, Int out_btlevel) {
Vec<Bool> seen(nVars(), False)
int counter = 0
lit p = bottom (undefined?)
Vec<Lit> p_reason

out_learnt.push() // leave room for the asserting literal
out_btlevel = 0
do {
  p_reason.clear()
  confl.calcReason(this, p, p_reason) // invariant here: confl != NULL

  // Trace reason for p:
  for (int j = 0; j < p_reason.size(); j++) {
    lit q = p_reason[j]
    if (!seen[var(q)]) {
      seen[var(q)] = true
      if (level[var(q)] == decisionLevel()) {
        counter ++
      } else if (level[var(q)] > 0) {
        out_learnt.push(not q)
        out_btlevel = max(out_btlevel, level[var(q)])
      }
    }
  }

  // Select next literal to look at:
  do {
    p = trail.last()
    confl = reason[var(p)]
    undoOne()
  } while (!seen[var(p)])
  counter --
} while (counter > 0)
out_learnt[0] = not p
     */
  }

  override def toString: String = {
    val sb = new mutable.StringBuilder()
    var lastDecisionLevel = -1
    for (((vid, values, dl), aid) <- assignments.zipWithIndex) {
      if (dl != lastDecisionLevel) {
        sb.append("DL(").append(dl).append(") ")
        lastDecisionLevel = dl
      }
      sb.append(aid).append(":").append(vid).append("=").append(values).append(" ")
    }
    sb.append("\n")
    for ((aid, causes) <- implications) {
      sb.append(causes.toList).append("=>").append(aid).append(" ")
    }
    sb.toString()
  }
}
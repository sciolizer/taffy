package taffy

import collection.mutable.ArrayBuffer
import domains.{Literal, Disjunction}
import scala.collection.mutable
import collection.immutable.Stack

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 1/29/13
 * Time: 11:23 AM
 */
class ImplicationGraph[Constraint, Variables, Variable](numVariables: Int, allValues: Variables, ranger: Ranger[Variables, Variable]) {
  type VarId = Int
  type AssignmentId = Int
  type DecisionLevel = Int
  type MixedConstraint = Either[NoGood[Variables], Constraint]
  private var dl = 0
  private val assignments: ArrayBuffer[Assignment[Constraint, Variables]] = ArrayBuffer()
  private val implications: mutable.Map[AssignmentId /* implication */, Set[AssignmentId] /* impliers */] = mutable.Map() // entry does not exist for decision variables
  private val varIndex: mutable.Map[VarId, Stack[AssignmentId]] = mutable.Map().withDefaultValue(Stack.empty)

  for (i <- 0 until numVariables) {
    record(i, allValues, None)
  }

  def implies(vid: VarId, values: Variables, because: Set[AssignmentId], constraint: MixedConstraint): AssignmentId = {
    if (constraint == null) throw new IllegalArgumentException("constraint cannot be null")
    implications(assignments.size) = because + mostRecentAssignment(vid) // previous value of variable always plays a factor in determining its new value. todo: this is actually not true. e.g. a call to setVar involves no reading of previous values
    record(vid, values, Some(constraint))
  }

  def decide(vid: VarId, value: Variables) {
    dl += 1
    record(vid, value, None)
  }

  private def record(vid: VarId, values: Variables, constraint: Option[MixedConstraint]): Int = {
    val ret: AssignmentId = assignments.size
    assignments += Assignment(vid, values, dl, constraint)
    varIndex(vid) = varIndex(vid).push(ret)
    ret
  }

  def decisionLevel = dl

  def isEmpty = assignments.size <= numVariables

  def mostRecentAssignment(vid: VarId): AssignmentId = {
    varIndex(vid).top
  }

  def values(aid: AssignmentId): Variables = {
    assignments(aid).variables
  }

  def readVar(vid: VarId): Variables = {
    values(mostRecentAssignment(vid))
  }

  private def undoOne() {
    if (assignments.size <= numVariables) throw new RuntimeException("tried to undo past beginning")
    val i: Int = assignments.size - 1
    val vid = assignments.remove(i).varId
    implications.remove(i)
    if (assignments.isEmpty) {
      dl = 0
    } else {
      dl = assignments.last.decisionLevel
    }
    varIndex(vid) = varIndex(vid).pop2._2
  }

  // about the 3rd return value:
  // the first list within the list is the vars that are implied by the first unique implication point, along
  // with the constraints that implied them.
  // the second list within the list (if it exists), is the next layer of implications, and so on until
  // the final list within the list is a singleton containing the conflicting variable, and the constraint
  // which led to its downfall
  // previously I made the constraint be an Option, but that is wrong, since EVERYTHING on the conflict side
  // of the cut must be an implied variable.
  def fuip(): (NoGood[Variables], Set[VarId] /* rewound variables */, List[List[(VarId, MixedConstraint)]]) = {
    var rewound: Set[VarId] = Set.empty
    val originalDecisionLevel = decisionLevel

    // back track until we find most recent conflicting variable
    while (!ranger.isEmpty(assignments(assignments.size - 1).variables)) {
      rewound = rewound + assignments(assignments.size - 1).varId
      undoOne()
    }

    val last: Int = assignments.size - 1
    var causes: List[List[(VarId, MixedConstraint)]] = List()
    var frontier: Set[AssignmentId] = Set(last)
    var reasons: Set[AssignmentId] = Set.empty
    do {
      val newCauses: List[(VarId, MixedConstraint)] = frontier.toList.map(x => (assignments(x).varId, assignments(x).cause.get))
      val combined: List[List[(VarId, MixedConstraint)]] = newCauses +: causes
      causes = combined
      def impliers(of: AssignmentId): Set[AssignmentId] = implications.get(of) match {
        case None => Set.empty
        case Some(xs) => xs
      }
      frontier = frontier.flatMap(impliers)
      var remove: Set[AssignmentId] = Set()
      for (assignment <- frontier) {
        if (assignments(assignment).decisionLevel < originalDecisionLevel) {
          remove = remove + assignment
        }
      }
      // erhg.. this is not right
      // we want to track the causes of the frontier BEFORE they reach < originalDecisionLevel
      reasons = reasons ++ remove
      frontier = frontier -- remove
    } while (frontier.size > 1)
    if (frontier.size == 0) {
      throw new RuntimeException("unexpected state. empty frontier. reasons: " + reasons + ", causes: " + causes)
    }
    val uip = frontier.head
    val nogood = new NoGood[Variables]((reasons + uip).map(x => (assignments(x).varId, assignments(x).variables)).toMap)
    while (assignments(assignments.size - 1).decisionLevel == originalDecisionLevel) {
      rewound = rewound + assignments(assignments.size - 1).varId
      undoOne()
    }
    (nogood, rewound, causes)
  }
}
      /*
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
   */
  def fuipOld(): (NoGood[Variables], Set[VarId] /* rewound variables */, List[(VarId, Option[MixedConstraint])]) = {
    println("Before: " + toString())

    var rewound: Set[VarId] = Set.empty

    // back track until we find most recent conflicting variable
    while (!ranger.isEmpty(assignments(assignments.size - 1)._2)) {
      rewound = rewound + assignments(assignments.size - 1)._1
      undoOne()
    }

    // var confl = conflicting
    val seen: mutable.Set[AssignmentId] = mutable.Set.empty
    var counter = 0
    var aids: collection.Set[AssignmentId] = implications(assignments.size - 1) // todo: what if last assignment was not an empty collection?
    var nogoods: Map[VarId, Variables] = Map.empty
    var constraints: List[(VarId, Option[MixedConstraint])] = List.empty
    var out_btlevel = 0
    var lastVar: VarId = null.asInstanceOf[VarId]
    var lastReason: Variables = null.asInstanceOf[Variables]
    var lastConstraint: Option[MixedConstraint] = None
    val startingDecisionLevel = decisionLevel

    do {
//      println("aids: " + aids)
      for (aid <- aids) {
        if (!seen.contains(aid)) {
          seen += aid
//          println("seen: " + seen)
          val assignment: (VarId, Variables, DecisionLevel, Option[MixedConstraint]) = assignments(aid)
          val vidLevel: DecisionLevel = assignment._3
          val vid: ImplicationGraph.this.type#VarId = assignment._1
          if (vidLevel == startingDecisionLevel) { // todo: is this allowed to decrease over time?
            counter += 1
            println("at starting decision level: " + assignment._4 + " implies var " + vid + " is " + assignment._2)
            constraints = constraints :+ ((vid, assignment._4)) // todo: what is the performance of :+ and +: ? (also used below)
          } else if (vidLevel > 0) {
            println("beyond starting decision level: " + assignment._4 + " implies var " + vid + " is " + assignment._2)
            nogoods = nogoods + ((vid, assignment._2))
//            constraints = constraints :+ ((vid, assignment._4)) // todo: what is the performance of :+ and +: ? (also used below)
//            println("nogoods: " + nogoods)
            out_btlevel = math.max(out_btlevel, vidLevel)
          }
        }
      }
      var p: AssignmentId = null.asInstanceOf[AssignmentId]
      do {
        // todo: this loop can be made faster. See minisat C++ code. Only tricky part is probably rewound
        val lastAssignment: (VarId, Variables, DecisionLevel, Option[MixedConstraint]) = assignments.last
        p = assignments.size - 1
        lastVar = lastAssignment._1
        rewound = rewound + lastVar
        lastReason = lastAssignment._2
        lastConstraint = lastAssignment._4
        aids = implications.get(p) match { case None => null.asInstanceOf[collection.Set[AssignmentId]]; case Some(x) => x }
        undoOne()
      } while (!seen.contains(p))
//      println("inner rewound: " + rewound)
      counter -= 1
    } while (counter > 0)
    nogoods = nogoods + ((lastVar, lastReason))
    constraints = constraints :+ ((lastVar, lastConstraint))
    println("counter back to zero: " + lastConstraint + " implies var " + lastVar + " is " + lastReason)
    // this new constraint will be unit in the variable that is about to be tried next. I think.
    val nogood: NoGood[Variables] = new NoGood[Variables](nogoods)
    if (!nogood.isUnit[Constraint, Variable](new ReadWriteGraph(this, null.asInstanceOf[MixedConstraint], mutable.Set(), mutable.Set(), ranger), ranger)) {
      throw new RuntimeException("generated nogood is not unit: " + nogood)
    }
    while (out_btlevel < decisionLevel) {
      rewound = rewound + assignments.last._1
      undoOne()
    }
//    println("nogood: " + nogood)
//    println("outer rewound: " + rewound)
//    println("after: " + toString())
//    println("btlevel_out: " + out_btlevel)
    Tuple3(nogood, rewound, constraints)

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
    for (((vid, values, dl, _), aid) <- assignments.zipWithIndex) {
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
}                             */

case class Assignment[Constraint, Variables](
  varId: Int,
  variables: Variables,
  decisionLevel: Int,
  cause: Option[Either[NoGood[Variables], Constraint]])

object TestImplicationGraph {
  def main(args: Array[String]) {
    // Example from page 4 of http://www.cs.tau.ac.il/~msagiv/courses/ATP/iccad2001_final.pdf
    /*
    6 | ~11 | ~12
~11 | 13 | 16
12 | -16 | 2
~4 | 2 | -10
-8 | 10 | -1
10 | 3
10 | 5
17 | -1 | -3 | 5 | 18
-3 | -19 | 18

pick -6
deduce -17 (6 | -17)
pick -13
deduce 8 (13 | 8)
pick 4
deduce 19 (-4 | 19)
pick 11
deduce -12, 16, -2, -10, 1, 3, -5, 18, -18

     */
    val im = new ImplicationGraph[Disjunction, Set[Boolean], Boolean](20, Set(true, false), new SetRanger())
    im.decide(6, Set(false)) // 0
    im.implies(17, Set(false), Set(0), List(Literal(true, 6), Literal(false, -17))) // 1
  }
}
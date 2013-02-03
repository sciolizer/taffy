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

  // Finds the first unique implication point (FUIP).
  // about the 3rd return value:
  // the first list within the list is the vars that are implied by the first unique implication point, along
  // with the constraints that implied them.
  // the second list within the list (if it exists), is the next layer of implications, and so on until
  // the final list within the list is a singleton containing the conflicting variable, and the constraint
  // which led to its downfall
  // previously I made the constraint be an Option, but that is wrong, since EVERYTHING on the conflict side
  // of the cut must be an implied variable.
  def fuip(): (NoGood[Variables], Set[VarId] /* rewound variables */, List[(VarId, MixedConstraint)]) = {
    println("Before fuip: " + toString())
    var rewound: Set[VarId] = Set.empty
    val originalDecisionLevel = decisionLevel

    // backtrack until we find most recent conflicting variable
    while (!ranger.isEmpty(assignments(assignments.size - 1).variables)) {
      rewound = rewound + assignments(assignments.size - 1).varId
      undoOne()
    }

    var i: Int = assignments.size - 1
    val conflictingVariable = assignments(i).varId
    var conflictingAssignments: Set[AssignmentId] = Set.empty
    while (assignments(i).decisionLevel == originalDecisionLevel) {
      if (assignments(i).varId == conflictingVariable) {
        conflictingAssignments = conflictingAssignments + i
      }
      i -= 1
    }


    // The current decision variable + the minimum set of variables less than the current decision level that are
    // sufficient to lead to the current conflict.
    // The nogood will be the FUIP plus all reasons which are not ancestors of the uip.
    val reasons: mutable.Set[AssignmentId] = mutable.Set.empty

    // The implied variables at the current decision level that have at least one immediate parent
    // which is the decision variable or at a lower decision level.
    // The set of returned constraints will be from a subset of these: specifically, the ones which are not
    // ancestors of the FUIP.
    var firstImplications: Set[AssignmentId] = Set.empty

    def isLowerOrDecision(ad: AssignmentId): Boolean = {
      val a = assignments(ad)
      a.decisionLevel < originalDecisionLevel || a.cause.isEmpty /* the decision variable */
    }

    def parents(aid: AssignmentId): Set[AssignmentId] = {
      if (isLowerOrDecision(aid)) {
        reasons += aid
        Set()
      } else {
        val candidates = implications(aid)
        if (candidates.exists(a => isLowerOrDecision(a))) {
          firstImplications = firstImplications + aid
        }
        candidates
      }
    }
    def forbidden(x: AssignmentId): Set[(VarId, Variables)] =
      if (x >= numVariables) Set((assignments(x).varId, assignments(x).variables)) else Set.empty

    val pf = new PathFinder[AssignmentId](parents)
    val ps: Set[AssignmentId] = conflictingAssignments.flatMap(parents(_)).filter(x => assignments(x).decisionLevel == originalDecisionLevel)
    val firstUip = {
      val ancestors: Set[Set[AssignmentId]] = ps.map(x => pf.ancestors(x) + x)
      val everything: Set[AssignmentId] = conflictingAssignments.flatMap(pf.ancestors(_))
      // Despite the name, this variable will also contain the decision variable and variables at lower decision levels
      val uips = ancestors.fold(everything)((x,y) => x.intersect(y))
      uips.max
    }
    val exclude = pf.ancestors(firstUip)
    val nogood = new NoGood[Variables]((reasons -- exclude + firstUip).flatMap(forbidden).toMap)
    val causesSet: Set[(AssignmentId, VarId, MixedConstraint)] = (firstImplications -- exclude - firstUip).map(a => ((a, assignments(a).varId, assignments(a).cause.get)))
    val causes: List[(VarId, MixedConstraint)] = causesSet.toList.sortBy(_._1).map(x => (x._2, x._3))

    while (assignments(assignments.size - 1).decisionLevel == originalDecisionLevel) {
      rewound = rewound + assignments(assignments.size - 1).varId
      undoOne()
    }
    (nogood, rewound, causes)
  }

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
  //}                   */

  override def toString: String = {
    val sb = new mutable.StringBuilder()
    var lastDecisionLevel = -1
    for ((Assignment(vid, values, dl, _), aid) <- assignments.zipWithIndex) {
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

case class Assignment[Constraint, Variables](
  varId: Int,
  variables: Variables,
  decisionLevel: Int,
  cause: Option[Either[NoGood[Variables], Constraint]])

class TestImplicationGraph(im: ImplicationGraph[List[Literal], Set[Boolean], Boolean]) {
  def decide(literal: Int) { im.decide(math.abs(literal), Set(literal > 0)) }
  def implies(literals: Int*): Either[NoGood[Set[Boolean]], List[Literal]] = {
    val impliedVarId: Int = literals.last
    val impliedLiteral: Literal = Literal(impliedVarId > 0, math.abs(impliedVarId))
    val ret: Right[NoGood[Set[Boolean]], List[Literal]] = Right[NoGood[Set[Boolean]], List[Literal]](literals.init.map(x => Literal(x > 0, math.abs(x))).toList :+ impliedLiteral)
    im.implies(
      impliedLiteral.vid,
      Set(impliedLiteral.expected),
      literals.init.map(x => im.mostRecentAssignment(math.abs(x))).toSet,
      ret)
    ret
  }
}

object TestImplicationGraph {
  def main(args: Array[String]) {
    {
      // Example from page 4 of http://www.cs.tau.ac.il/~msagiv/courses/ATP/iccad2001_final.pdf
      val im = new ImplicationGraph[List[Literal], Set[Boolean], Boolean](20, Set(true, false), new SetRanger())
      val tig = new TestImplicationGraph(im)
      tig.decide(-6)
      tig.implies(6, -17)
      tig.decide(-13)
      tig.implies(13, 8)
      tig.decide(4)
      tig.decide(7) // not in graph... just need to fill in something for decision level 4.
      tig.implies(-4, 19)
      tig.decide(11)
      tig.implies(6, -11, -12)
      tig.implies(-11, 13, 16)
      tig.implies(12, -16, -2)
      tig.implies(-4, 2, -10)
      val implies1 = tig.implies(-8, 10, 1)
      val implies3 = tig.implies(10, 3)
      val impliesNot5 = tig.implies(10, -5)
      val implies18 = tig.implies(17, -1, -3, 5, 18)
      val impliesNot18 = Right[NoGood[Set[Boolean]], List[Literal]](List(Literal(false, 3), Literal(false, 19), Literal(false, 18)))
      // Can't use implies for this last one, since we need to make the value empty instead of a singleton boolean
      im.implies(
        18, Set(),
        Set(im.mostRecentAssignment(3), im.mostRecentAssignment(19)),
        impliesNot18)
      val (nogood, rewound, tolearn) = im.fuip()
      assert(Set(18, 5, 3, 1, 10, 2, 16, 12, 11).equals(rewound))
      assert(nogood.forbidden.equals(Map(17 -> Set(false), 8 -> Set(true), 10 -> Set(false), 19 -> Set(true))))
      val expected = List((1, implies1), (3, implies3), (5, impliesNot5), (18, implies18), (18, impliesNot18))
      assert(tolearn.equals(expected))
    }

    {
      // This test tests the case where the FUIP is immediately before the conflicting variable.
      /*
            /-> 3
      1 -> 2
            \-> -3
       */
      val im = new ImplicationGraph[List[Literal], Set[Boolean], Boolean](4, Set(true, false), new SetRanger())
      val tig = new TestImplicationGraph(im)
      tig.decide(1)
      tig.implies(-1, 2)
      val implies3 = tig.implies(-2, 3)
      val impliesNot3 = Right[NoGood[Set[Boolean]], List[Literal]](List(Literal(false, 2), Literal(true, 3)))
      // Can't use tig.implies for this last one, since we need to make the value empty instead of a singleton boolean
      im.implies(
        3, Set(),
        Set(im.mostRecentAssignment(2), im.mostRecentAssignment(3)),
        impliesNot3)
      val (nogood, rewound, tolearn) = im.fuip()
      assert(Set(1, 2, 3).equals(rewound))
      assert(nogood.forbidden.equals(Map(2 -> Set(true))))
      val expected = List((3, implies3))
      assert(tolearn.equals(expected))
    }

    {
      // Tests when the decision variable is the FUIP.
      /*
       /-> 2
      1
       \-> -2
       */

      val im = new ImplicationGraph[List[Literal], Set[Boolean], Boolean](3, Set(true, false), new SetRanger())
      val tig = new TestImplicationGraph(im)
      tig.decide(1)
      val implies2 = tig.implies(-1, 2)
      val impliesNot2 = Right[NoGood[Set[Boolean]], List[Literal]](List(Literal(false, 2), Literal(true, 1)))
      // Can't use tig.implies for this last one, since we need to make the value empty instead of a singleton boolean
      im.implies(
        2, Set(),
        Set(im.mostRecentAssignment(2), im.mostRecentAssignment(1)),
        impliesNot2)
      val (nogood, rewound, tolearn) = im.fuip()
      assert(Set(1, 2).equals(rewound))
      println("nogood: " + nogood.forbidden)
      assert(nogood.forbidden.equals(Map(1 -> Set(true))))
      val expected = List((2, implies2), (2, impliesNot2))
      println("tolearn: " + tolearn)
      assert(tolearn.equals(expected))
    }
  }
}

class PathFinder[A](parents: A => Set[A]) {
  val memoized: mutable.Map[A, Set[A]] = mutable.Map.empty
  def ancestors(of: A): Set[A] = {
    memoized.get(of) match {
      case None =>
        val ps = parents(of)
        ps ++ ps.flatMap(x => ancestors(x))
      case Some(x) => x
    }
  }
}

object TestPathFinder {
  def main(args: Array[String]) {
    /*
          /-> 3 ------\
    1 -> 2             -> 6 -> 7
          \-> 4 -> 5 -/
     */
    val graph: Map[Int, Set[Int]] = Map(1 -> Set(), 2 -> Set(1), 3 -> Set(2), 4 -> Set(2), 5 -> Set(4), 6 -> Set(3, 5), 7 -> Set(6))
    val pf = new PathFinder[Int](x => graph(x))
    assert(Set(1).equals(pf.ancestors(2)))
    assert(Set(2, 1).equals(pf.ancestors(3)))
    assert(Set(2, 1).equals(pf.ancestors(4)))
    assert(Set(4, 2, 1).equals(pf.ancestors(5)))
    assert(Set(5, 4, 3, 2, 1).equals(pf.ancestors(6)))
    assert(Set(6, 5, 4, 3, 2, 1).equals(pf.ancestors(7)))
  }
}
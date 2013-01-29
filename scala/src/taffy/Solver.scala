package taffy

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 1/28/13
 * Time: 9:23 AM
 */

import scala.collection.mutable
import scala.util.control.Breaks._
import scala.{collection, None, math}
import scala.Nothing

class Solver[Constraint, Variables, Variable]( domain: Domain[Constraint, Variables, Variable],
                                               problem: Problem[Constraint, Variables, Variable],
                                               ranger: Ranger[Variables, Variable]) {
  type VarId = Int
  type DecisionLevel = Int
  type MixedConstraint = Either[NoGood[Variables], Constraint]

  // private class Var(var values: Variables) {}

  // private val variables: mutable.ArrayBuffer[Variables] = mutable.ArrayBuffer()
  private val watchers: mutable.ArrayBuffer[Set[MixedConstraint]] = mutable.ArrayBuffer()

  private val unrevised: mutable.Set[MixedConstraint] = mutable.Set()

  private val unassigned: mutable.Set[VarId] = mutable.Set()

  // It is possible for a variable to appear multiple times in the trail, e.g. if the variable's
  // possible values was constrained but not reduced to a single value.
  // private val trail: mutable.Stack[(VarId, Variables /* original */, DecisionLevel /* original */)] = mutable.Stack()

  // private val reasons: mutable.Map[(VarId, Variables), (DecisionLevel, Option[(Constraint, Map[VarId, Variables])])] = mutable.Map()

  private val graph: ImplicationGraph[Variables, Variable] = new ImplicationGraph(problem.numVariables, problem.candidateValues, ranger)

  // private var decisionLevel: DecisionLevel = 0

  def solve() : Option[Read[Variables, Variable]] = {
    val initialDecisionLevel: DecisionLevel = -1
    val initialCause: Option[(Constraint, Map[VarId, Variables])] = None
    for (vid <- 0 until problem.numVariables) {
      watchers += Set.empty
      unassigned += vid
    }
    unrevised ++= problem.constraints.map(Right(_))

    while (!unrevised.isEmpty || !unassigned.isEmpty) {
      if (!unrevised.isEmpty) {
        val constraint: MixedConstraint = unrevised.head
        unrevised -= constraint
        val reads = mutable.Set[VarId]()
        val writes = mutable.Set[VarId]()
        val rw = new ReadWrite[Variables, Variable](graph, reads.asInstanceOf[mutable.Set[Int]], writes.asInstanceOf[mutable.Set[Int]], ranger)
        var bj = !revise(rw, constraint)
        for (vid <- writes) {
          unrevised ++= watchers(vid) - constraint // todo: don't update unrevised when bj is going to become true
          val values = graph.readVar(vid)
          if (ranger.isEmpty(values)) {
            bj = true
          } else if (ranger.isSingleton(values)) {
            unassigned -= vid
          }
        }
        if (bj) {
          if (graph.decisionLevel == 0) return None
          val (nogood, rewound) = graph.fuip(reads)
          if (graph.isEmpty) return None
          unassigned ++= rewound
          unrevised += Left(nogood)
        } else {
          for (varId <- reads) {
            watchers(varId) += constraint // todo: only watch on particular values
          }
        }
      } else if (!unassigned.isEmpty) {
        var vid = unassigned.head // todo: better variable ordering
        unassigned -= vid
        val values: Variables = graph.readVar(vid)
        val value = ranger.pick(values) // todo: better value picking
        // println("Assigning " + value + " to " + vid)
        unassigned -= vid
        val newValue: Variables = ranger.toSingleton(value)
        graph.decide(vid, newValue)
        unrevised ++= watchers(vid)
      }
    }
    Some(new Read(graph, ranger))
  }

  private def revise(rw: ReadWrite[Variables, Variable], constraint: MixedConstraint) : Boolean = {
    constraint match {
      case Left(nogood) => nogood.revise(rw, ranger)
      case Right(c) => domain.revise(rw, c)
    }
  }
  /*
  private def backjump() { // todo: currently this is only backtracking, not backjumping
    breakable {
      while (!trail.isEmpty) {
        println("backtrack")
        val (vid, original, decision) = trail.pop()
        decision match {
          case None =>
            variables(vid) = original
            unassigned += vid
          case Some(attempted) =>
            var untried = original
            for (value <- attempted) {
              untried = ranger.subtraction(untried, ranger.toSingleton(value))
            }
            if (ranger.isEmpty(untried)) {
              variables(vid) = original
              unassigned += vid
            } else {
              val value: Variable = ranger.pick(untried)
              variables(vid) = ranger.toSingleton(value)
              trail.push((vid, original, Some(attempted + value)))
              break()
            }
        }
      }
    }
  }
*/
}
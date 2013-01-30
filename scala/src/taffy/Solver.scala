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

  private val graph: ImplicationGraph[Constraint, Variables, Variable] = new ImplicationGraph(problem.numVariables, problem.candidateValues, ranger)

  private val emptyVals: Variables = ranger.subtraction(problem.candidateValues, problem.candidateValues)

  // private var decisionLevel: DecisionLevel = 0

  def solve() : Option[Read[Constraint, Variables, Variable]] = {
    val initialDecisionLevel: DecisionLevel = -1
    val initialCause: Option[(Constraint, Map[VarId, Variables])] = None
    for (vid <- 0 until problem.numVariables) {
      watchers += Set.empty
      unassigned += vid
    }
    unrevised ++= problem.constraints.map(Right(_))

    while (!unrevised.isEmpty || !unassigned.isEmpty) {
//      println("unrevised: " + unrevised)
      if (!unrevised.isEmpty) {
        val constraint: MixedConstraint = unrevised.head
        unrevised -= constraint
        val reads = mutable.Set[VarId]()
        val writes = mutable.Set[VarId]()
        val rw = new ReadWrite[Constraint, Variables, Variable](graph, constraint, reads, writes, ranger)
        val constraintUnsatisfiable = !revise(rw, constraint)
        var emptyVar = false
        for (vid <- writes) {
          unrevised ++= watchers(vid) - constraint // todo: don't update unrevised when bj is going to become true
          val values = graph.readVar(vid)
//          println("deduced " + vid + ": " + values)
          if (ranger.isEmpty(values)) {
            emptyVar = true
          } else if (ranger.isSingleton(values)) {
            unassigned -= vid
          }
        }
        if (constraintUnsatisfiable && !emptyVar) {
          // fuip expects there to be an empty variable, so we pick one arbitrarily
          val vars = coverage(constraint)
          if (vars.isEmpty) {
            throw new RuntimeException("Constraint covers no variables, and yet returns false: " + constraint)
          } else {
            val picked = vars.head
            rw.intersectVar(picked, emptyVals)
          }
        }
        if (emptyVar || constraintUnsatisfiable) {
          val origLevel: Int = graph.decisionLevel
          if (origLevel == 0) return None
          while (origLevel == graph.decisionLevel) { // don't think this while loop is actually necessary, but it might be for when a constraint causes multiple variables to be in conflict at once
            val (nogood, rewound, constraints) = graph.fuip()
            //          if (graph.isEmpty) return None
//            println("rewound: " + rewound)
            unassigned ++= rewound
            unrevised += Left(nogood)
            /*
            data.partition(_.isLeft) match {
  case (Nil,  ints) => Right(for(Right(i) <- ints.view) yield i)
  case (strings, _) => Left(for(Left(s) <- strings.view) yield s)
}
             */
            unrevised ++= domain.learn(constraints).map(x => Right(x._1)) // todo: incorporate _2 after isomorphisms have been implemented
          }
        } else {
          for (varId <- reads) {
            watchers(varId) += constraint // todo: only watch on particular values
          }
        }
      } else if (!unassigned.isEmpty) {
        var vid = unassigned.head // todo: better variable ordering
        unassigned -= vid
        val values: Variables = graph.readVar(vid)
        if (!ranger.isSingleton(values)) {
          // todo: better value picking; also, is it reasonable to pick a set of the values,
          // instead of a single value, so that no goods can be more useful? Of course, if any value is a valid
          // pick, then that would be a waste.
          val value = ranger.pick(values)
//          println("picking " + vid + ": " + value)
          val newValue: Variables = ranger.toSingleton(value)
          graph.decide(vid, newValue)
        }
        unrevised ++= watchers(vid) // todo: is this necessary if values IS a singleton?
      }
    }
    Some(new Read(graph, ranger))
  }

  private def revise(rw: ReadWrite[Constraint, Variables, Variable], constraint: MixedConstraint) : Boolean = {
    constraint match {
      case Left(nogood) => nogood.revise(rw, ranger)
      case Right(c) => domain.revise(rw, c)
    }
  }

  private def coverage(constraint: MixedConstraint): collection.Set[VarId] = {
    constraint match {
      case Left(nogood) => nogood.coverage()
      case Right(c) => domain.coverage(c)
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
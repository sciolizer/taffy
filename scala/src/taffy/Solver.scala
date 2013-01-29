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
  type MixedConstraint = Either[NoGood[Constraint, Variables, Variable], Constraint]

  // private class Var(var values: Variables) {}

  private val variables: mutable.ArrayBuffer[Variables] = mutable.ArrayBuffer()
  private val watchers: mutable.ArrayBuffer[Set[MixedConstraint]] = mutable.ArrayBuffer()

  private val unrevised: mutable.Set[MixedConstraint] = mutable.Set()

  private val unassigned: mutable.Set[VarId] = mutable.Set()

  // It is possible for a variable to appear multiple times in the trail, e.g. if the variable's
  // possible values was constrained but not reduced to a single value.
  private val trail: mutable.Stack[(VarId, Variables /* original */, DecisionLevel /* original */)] = mutable.Stack()

  private val reasons: mutable.Map[(VarId, Variables), (DecisionLevel, Option[(Constraint, Map[VarId, Variables])])] = mutable.Map()

  private var decisionLevel: DecisionLevel = 0

  def solve() : Option[Read[Variables, Variable]] = {
    val initialDecisionLevel: DecisionLevel = -1
    val initialCause: Option[(Constraint, Map[VarId, Variables])] = None
    val initialReason: Tuple2[DecisionLevel, Option[(Constraint, Map[VarId, Variables])]] = Tuple2(initialDecisionLevel, initialCause)
    val allValues: Variables = problem.candidateValues
    for (vid <- 0 until problem.numVariables) {
      variables += allValues
      watchers += Set.empty
      unassigned += vid
      // reasons((vid, allValues)) = initialReason
    }
    unrevised ++= problem.constraints.map(Right(_))

    while (!unrevised.isEmpty || !unassigned.isEmpty) {
      if (!unrevised.isEmpty) {
        val constraint: MixedConstraint = unrevised.head
        unrevised -= constraint
        val varsRead = mutable.Map[VarId, (Variables, Option[Set[Variable]])]()
        val undo = mutable.Map[VarId, Variables]()
        val rw = new ReadWrite[Constraint, Variables, Variable](variables, varsRead, undo, ranger)
        var bj = !revise(rw, constraint)
        for ((vid, original) <- undo) {
          trail.push((vid, original, decisionLevel))
          unrevised ++= watchers(vid) - constraint // todo: don't update unrevised when bj is going to become true
          if (ranger.isEmpty(variables(vid))) {
            bj = true
          } else if (ranger.isSingleton(variables(vid))) {
            unassigned -= vid
          }
        }
        val reason: collection.Map[VarId, Variables] = varsRead.mapValues(_._1)
        if (bj) {
          if (decisionLevel == 0) return None
          fuip(reason)
          if (trail.isEmpty) return None
        } else {
          for ((vid, _) <- undo) {
            // not sure why scala can't figure out this upward cast
            reasons((vid, variables(vid))) = (decisionLevel, Some((constraint, reason))).asInstanceOf[Tuple2[DecisionLevel, Option[(Constraint, Map[VarId, Variables])]]]
          }
          for ((varId, _) <- varsRead) {
            watchers(varId) += constraint // todo: only watch on particular values
          }
        }
      } else if (!unassigned.isEmpty) {
        decisionLevel += 1
        var vid = unassigned.head // todo: better variable ordering
        unassigned -= vid
        val values: Variables = variables(vid)
        val value = ranger.pick(values) // todo: better value picking
        // println("Assigning " + value + " to " + vid)
        unassigned -= vid
        val newValue: Variables = ranger.toSingleton(value)
        reasons((vid, newValue)) = (decisionLevel, None)
        variables(vid) = newValue
        trail.push((vid, /*ranger.subtraction(*/values/*, ranger.toSingleton(value))*/, decisionLevel))
        unrevised ++= watchers(vid)
      }
    }
    Some(new Read(variables, ranger))
  }

  private def revise(rw: ReadWrite[Constraint, Variables, Variable], constraint: MixedConstraint) : Boolean = {
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
  private def undoOne() {
    /* VarId, Variables /* original */, Option[Set[Variable]] */
    val (vid, original, _) = trail.pop()
    val current = variables(vid)
    variables(vid) = original
    unassigned += vid
    reasons.remove((vid, current))
    if (trail.isEmpty) {
      decisionLevel = 0
    } else {
      decisionLevel = trail.top._3
    }
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
  private def fuip(firstReason: collection.Map[VarId, Variables]) {
    /*
    Ok, here's my current thoughts:
    because we have a setVar function, we can track the reasons ourselves.
    If a variable becomes unit because of shrink or intersection, and NOT because
    of setVar, then we treat the variable as a decision variable.
     */

    // var confl = conflicting
    val seen: mutable.Set[(VarId, Variables)] = mutable.Set.empty // set((varId, Variables))
    var counter = 0
    var p: Any = null // (VarId, Variables)
    val nogoods: mutable.Map[Int, Variables] = mutable.Map()
    var out_btlevel = 0
    var lastReason: Any = null // but really : Variables

    do {
      val p_reason: collection.Map[VarId, Variables] = if (p == null) firstReason else {
        reasons.get(p.asInstanceOf[(VarId, Variables)]) match {
          case None => throw new RuntimeException("internal bug: can't find reason for " + p)
          case Some((_,None)) => throw new RuntimeException("internal bug: can't find reason for " + p)
          case Some((_,Some((_,reason)))) => reason
        }
      }
      for ((vid, values) <- p_reason) {
        if (!seen.contains((vid, values))) {          // seen contains pair
          seen += Tuple2(vid, values)
          val vidLevel: DecisionLevel = reasons.get((vid, values)) match {
            case None => throw new RuntimeException("internal bug: couldn't find decision level for " + vid)
            case Some((x,_)) => x
          }
          if (vidLevel == decisionLevel) {
            counter += 1
          } else if (vidLevel > 0) {
            nogoods(vid) = values
            out_btlevel = math.max(out_btlevel, vidLevel)
          }
        }
      }

      do {
        p = trail.top match {
          case (vid, values, _) => (vid, values)
        }
        lastReason = variables(p.asInstanceOf[(VarId, Variables)]._1)
        undoOne()
      } while (!seen.contains(p.asInstanceOf[(VarId, Variables)]))
      counter -= 1
    } while (counter > 0)
    nogoods(p.asInstanceOf[(VarId, Variables)]._1) = lastReason.asInstanceOf[Variables]
    // this new constraint should be unit in the variable that is about to be tried next
    val nogood: NoGood[Constraint, Variables, Variable] = new NoGood[Constraint, Variables, Variable](nogoods)
    if (!nogood.isUnit(new ReadWrite(variables, mutable.Map(), mutable.Map(), ranger), ranger)) {
      throw new RuntimeException("generated nogood is not unit: " + nogood)
    }
    unrevised += Left(nogood)

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
}
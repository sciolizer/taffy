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

  private val reasons: mutable.ArrayBuffer[Option[(DecisionLevel, Constraint, Map[VarId, Variables])]] = mutable.ArrayBuffer()

  private var decisionLevel: DecisionLevel = 0

  def solve() : Option[Read[Variables, Variable]] = {
    for (vid <- 0 until problem.numVariables) {
      variables += problem.candidateValues
      watchers += Set.empty
      unassigned += vid
      reasons += None
    }
    unrevised ++= problem.constraints.map(Right(_))

    while (!unrevised.isEmpty || !unassigned.isEmpty) {
      if (!unrevised.isEmpty) {
        val constraint: MixedConstraint = unrevised.head
        unrevised -= constraint
        val varsRead = mutable.Map[VarId, (Variables, Option[Set[Variable]])]()
        val undo = mutable.Map[VarId, Variables]()
        val setVars: mutable.Set[VarId] = mutable.Set.empty
        val rw = new ReadWrite[Constraint, Variables, Variable](variables, varsRead, undo, setVars, ranger)
        var bj = !revise(rw, constraint)
        for ((vid, original) <- undo) {
          trail.push((vid, original, decisionLevel))
          unrevised ++= watchers(vid) - constraint // todo: don't update unrevised when bj is going to become true
          if (ranger.isEmpty(variables(vid))) {
            bj = true
          }
        }
        val reason: collection.Map[VarId, Variables] = varsRead.mapValues(_._1)
        if (bj) {
          fuip(reason)
          if (trail.isEmpty) return None
        } else {
          for (vid <- setVars) {
            // If the set var was also read from, then we can't treat it as a deduction, because the reviser might
            // have just been computing a manual intersection.
            if (!varsRead.contains(vid)) {
              unassigned -= vid
              // not sure why scala can't figure out this upward cast
              reasons(vid) = Some((decisionLevel, constraint, reason)).asInstanceOf[Option[(DecisionLevel, Constraint, Map[VarId, Variables])]]
            }
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
        variables(vid) = ranger.toSingleton(value)
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
    val (vid, original, dl) = trail.pop()
    variables(vid) = original
    unassigned += vid
    reasons(vid) = None
    decisionLevel = dl
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
    val seen: mutable.Set[VarId] = mutable.Set.empty
    var counter = 0
    var p: VarId = -1
    val nogoods: mutable.Map[Int, Variables] = mutable.Map()
    var out_btlevel = 0
    var lastReason: Any = null // but really : Variables

    do {
      val p_reason = if (p == -1) firstReason else {
        reasons(p) match {
          case None => throw new RuntimeException("internal bug: can't find reason for " + p)
          case Some((_,_,reason)) => reason
        }
      }
      for ((vid, values) <- p_reason) {
        if (!seen.contains(vid)) {
          seen += vid
          val vidLevel: DecisionLevel = reasons(vid) match {
            case None => throw new RuntimeException("internal bug: couldn't find decision level for " + vid)
            case Some((dl, _, _)) => dl
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
        p = trail.top._1
        lastReason = variables(p)
        undoOne()
      } while (!seen.contains(p))
      counter -= 1
    } while (counter > 0)
    nogoods(p) = lastReason.asInstanceOf[Variables]
    // this new constraint should be unit in the variable that is about to be tried next
    val nogood: NoGood[Constraint, Variables, Variable] = new NoGood[Constraint, Variables, Variable](nogoods)
    if (!nogood.isUnit(new ReadWrite(variables, mutable.Map(), mutable.Map(), mutable.Set(), ranger), ranger)) {
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
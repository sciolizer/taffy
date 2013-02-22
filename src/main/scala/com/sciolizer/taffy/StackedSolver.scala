package com.sciolizer.taffy

import collection.mutable

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 2/22/13
 * Time: 11:15 AM
 */
// todo: support isomorphisms
class StackedSolver[-Constraint <: Revisable[Values, Value], Values, +Value](
    private[this] val inference: Inference[Constraint],
    private[this] val ranger: Ranger[Values, Value],
    private[this] val candidateValues: Values) {

  type VarId = Int

  private[this] var variables: Int = 0
  private[this] val constraints: mutable.Stack[Constraint] = mutable.Stack()
  private[this] val frames: mutable.Stack[StackFrame] = mutable.Stack()
  private[this] var recentSolution: RecentSolution = Unsolved()

  def insertVariable(): VarId = {
    val ret = variables
    variables += 1
    recentSolution = recentSolution.afterInsert
    ret
  }

  def insertConstraint(constraint: Constraint) {
    if (constraint.coverage.exists(_ >= variables)) {
      throw new IllegalArgumentException("Constraint covers not yet created variable.")
    }
    constraints.push(constraint)
    recentSolution = recentSolution.afterInsert
    // check that it only covers existing variables
  }

  def push() {
    frames.push(StackFrame(variables, constraints.size))
  }

  def pop() {
    val top = frames.pop()
    variables = top.frameVariables
    while (constraints.size > top.frameConstraints) {
      constraints.pop()
    }
  }

  // todo: make this substantially faster
  // todo: obtain learned constraints and add them to our own list of constraints
  def solution: Option[Map[VarId, Value]] = recentSolution match {
    case NoSolution() => None
    case Solution(ret) => Some(ret)
    case Unsolved() =>
      val problem: Problem[Constraint, Values, Value] = new Problem(variables, constraints.toSet, candidateValues)
      val sss = new SuperSimpleSolver[Constraint, Values, Value](inference, problem, ranger)
      val ret = sss.backtrackingSearch((0 until variables).map { _ -> candidateValues } toMap)
      ret match {
        case None => recentSolution = NoSolution()
        case Some(assignments) => recentSolution = Solution(assignments)
      }
      ret
  }

  case class StackFrame(frameVariables: Int, frameConstraints: Int) {
    def pop() {
      variables
    }
  }

  sealed trait RecentSolution {

    def afterInsert: RecentSolution

  }

  case class Unsolved() extends RecentSolution {

    def afterInsert: RecentSolution = this

  }

  case class NoSolution() extends RecentSolution {

    def afterInsert: RecentSolution = this

  }

  case class Solution(assignments: Map[VarId, Value]) extends RecentSolution {

    def afterInsert: RecentSolution = Unsolved()

  }

}

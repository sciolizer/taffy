package com.sciolizer.taffy.domains.boundedSum

import com.sciolizer.taffy.{Revisable, ReadWrite}
import collection.mutable

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 2/21/13
 * Time: 6:08 PM
 */
case class Equation(addends: List[Addend], relation: Relation, sum: Int, range: Range) extends Revisable[Set[Int], Int] {

  lazy val coverage: Set[VarId] = addends.map(_.variable).toSet

  def revise(rw: ReadWrite[Set[Int], Int]): Boolean = {
    val (positives, negatives) = addends.partition(_.coefficient > 0)
    var upper = positives.map(_.coefficient * range.max).sum
    var lower = negatives.map(_.coefficient * range.max).sum
    val settable = mutable.Map[VarId, Set[Int]]()
    def outOfBounds(l: Int, u: Int): Boolean = {
      def lteq(): Boolean = l > sum
      def gteq(): Boolean = u < sum
      relation match {
        case Eq() => lteq() || gteq()
        case LtEq() => lteq()
        case GtEq() => gteq()
      }
    }
    def adjustedRange(coefficient: Int, minval: Int, maxval: Int, origMinVal: Int, origMaxVal: Int): (Int, Int) = {
      val minAdjustment = math.abs(coefficient * (minval - origMinVal))
      val maxAdjustment = math.abs(coefficient * (maxval - origMaxVal))
      if (coefficient > 0) {
        ((lower + minAdjustment, upper - maxAdjustment))
      } else {
        ((lower + maxAdjustment, upper - minAdjustment))
      }
    }
    for (Addend(coefficient, vid) <- addends) {
      if (outOfBounds(lower, upper)) return false
      if (coefficient == 0) {
        throw new RuntimeException("invalid equation: zero coefficient")
      } else {
        val vals = rw.readVar(vid)
        if (vals.isEmpty) {
          throw new RuntimeException("invalid state: variable was already in a contradictory state")
        } else {
          val adjusted: (Int, Int) = adjustedRange(coefficient, vals.min, vals.max, range.min, range.max)
          lower = adjusted._1
          upper = adjusted._2
          //          (lower, upper) = adjustedRange(coefficient, vals.min, vals.max)
          if (vals.size > 1) settable += ((vid, vals))
        }
      }
    }
    if (outOfBounds(lower, upper)) {
      false
    } else {
      for (Addend(coefficient, vid) <- addends) {
        settable.get(vid) match {
          case None =>
          case Some(vals) =>
            for (value <- vals) { // todo: find a faster way to do this
            val (l, u) = adjustedRange(coefficient, value, value, vals.min, vals.max)
              if (outOfBounds(l, u)) rw.shrinkVar(vid, value)
            }
        }
      }
      true
    }
  }

  def substitute(substitution: Map[Int, Int]): Equation = {
    copy(addends = addends.map(_.substitute(substitution)))
  }

}

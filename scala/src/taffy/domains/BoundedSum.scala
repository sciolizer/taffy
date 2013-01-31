package taffy.domains

import scala.collection.mutable
import taffy.{ReadWrite, Domain}

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 1/31/13
 * Time: 10:16 AM
 */
class BoundedSum(minimum: Int, maximum: Int) extends Domain[Equation, Set[Int], Int] {
  if (minimum < 0) throw new IllegalArgumentException("Negative minimums is not currently supported: " + minimum)
  if (minimum > maximum) throw new IllegalArgumentException("maximum " + maximum + "must be greater than minimum " + minimum)

                                  /*
  override def learn(constraints: List[(VarId, Option[MixedConstraint])]): List[(Equation, List[MixedConstraint])] = {
    val vars = constraints.map(_._1).toSet
    val cs = (for ((_, Some(Right(eq))) <- constraints) yield { eq }).toSet.toArray
    println("to learn: " + cs.toList)
    var ret: mutable.Map[Equation, List[MixedConstraint]] = mutable.Map.empty
    def toMap(eq: Equation): Map[VarId, Int] = eq.addends.map(x => (x.variable, x.coefficient)).toMap
    for (i <- 0 until cs.size - 1) {
      val eq1: Equation = cs(i)
      val eq1map = toMap(eq1)
      for (j <- i + 1 until cs.size) {
        val eq2: Equation = cs(j)
        val eq2map = toMap(eq2)
        for (v <- vars) {
          if (eq1map.contains(v) && eq2map.contains(v)) {
            val eq1coefficient = eq1map(v)
            val eq2coefficient = eq2map(v)
            var learnedSum: mutable.Map[VarId, Int] = mutable.Map.empty.withDefaultValue(0)
            def include(eq: Map[VarId, Int], multiplier: Int) {
              for ((vid, coef) <- eq) {
//                learnedSum(vid) += coef * multiplier // black magic
                learnedSum(vid) = learnedSum(vid) + coef * multiplier
              }
            }
            include(eq1map, -eq2coefficient)
            include(eq2map, eq1coefficient)
            val addends = (for ((vid, coeff) <- learnedSum; if coeff != 0) yield { Addend(coeff, vid) }).toList
            ret(Equation(addends, eq1.sum * -eq2coefficient + eq2.sum * eq1coefficient)) = List(Right(eq1), Right(eq2))
          }
        }
      }
    }
    println("learned: " + ret)
    ret.toList
  }          */

  def revise(rw: ReadWrite[Equation, Set[Int], Int], e: Equation): Boolean = {
    val (positives, negatives) = e.addends.partition(_.coefficient > 0)
    var upper = positives.map(_.coefficient * maximum).sum
    var lower = negatives.map(_.coefficient * maximum).sum
    val settable = mutable.Map[VarId, Set[Int]]()
    var writing = 0 // 1 means maximize, -1 means minimize
    def outOfBounds(): Boolean = {
      def lteq(): Boolean = {
        if (lower > e.sum) return true
        if (lower == e.sum) writing = -1 // minimize sum on settable variables
        false
      }
      def gteq(): Boolean = {
        if (upper < e.sum) return true
        if (upper == e.sum) writing = 1 // maximize sum on settable variables
        false
      }
      e.relation match {
        case Eq() => lteq() || gteq()
        case LtEq() => lteq()
        case GtEq() => gteq()
      }
    }
    for (Addend(coefficient, vid) <- e.addends) {
      if (outOfBounds()) return false
      if (coefficient == 0) {
        throw new RuntimeException("invalid equation: zero coefficient")
      } else {
        val vals = rw.readVar(vid)
        if (vals.isEmpty) {
          throw new RuntimeException("invalid state: variable was already in a contradictory state")
        } else if (vals.size == 1) {
          val value = vals.head * coefficient
          val min = coefficient * (if (coefficient < 0) maximum else minimum)
          val max = coefficient * (if (coefficient > 0) maximum else minimum)
          lower += (value - min)
          upper -= (max - value)
        } else {
          settable += ((vid, vals))
        }
      }
    }
    if (outOfBounds()) {
      false
    } else if (writing == 0) {
      true
    } else {
      for (Addend(coefficient, vid) <- e.addends) {
        settable.get(vid) match {
          case None =>
          case Some(vals) =>
            if (writing == -1) {
              rw.setVar(vid, if (coefficient < 0) vals.max else vals.min)
            } else if (writing == 1) {
              rw.setVar(vid, if (coefficient > 0) vals.max else vals.min)
            }
        }
      }
      true
    }
  }

  def coverage(c: Equation): collection.Set[BoundedSum#VarId] = c.addends.map(_.variable).toSet
}

case class Addend(coefficient: Int, variable: Int)
case class Equation(addends: List[Addend], relation: Relation, sum: Int)
abstract class Relation
case class Eq() extends Relation
case class LtEq() extends Relation
case class GtEq() extends Relation
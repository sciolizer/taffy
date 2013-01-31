package taffy.domains

import scala.collection.mutable
import taffy.{SetRanger, ReadWriteMock, ReadWrite, Domain}

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

  def revise(rw: ReadWrite[Set[Int], Int], e: Equation): Boolean = {
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
          settable += ((vid, vals)) // todo: actually, lower and upper can still be modified in this case. Just need to look at vals.max and vals.min
        }
      }
    }
    if (outOfBounds()) {
      false
    } else if (writing == 0) {
      if (settable.size == 1) {
        rw.setVar(settable.keys.head, e.sum - lower)
      }
      true
    } else {
      for (Addend(coefficient, vid) <- e.addends) {
        settable.get(vid) match {
          case None =>
          case Some(vals) =>
            if (writing == -1) {
              rw.setVar(vid, if (coefficient < 0) maximum else minimum)
            } else if (writing == 1) {
              rw.setVar(vid, if (coefficient > 0) maximum else minimum)
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

object TestBoundedSum {
  def main(args: Array[String]) {
    {
      val rw = new ReadWriteMock[Set[Int], Int](Map(0 -> Set(0), 1 -> Set(0, 1, 2), 2 -> Set(1)), new SetRanger())
      val bs = new BoundedSum(0, 2)
      assert(bs.revise(rw, Equation(List(Addend(1, 0), Addend(1, 1), Addend(1, 2)), Eq(), 2)))
      val expected: Map[Int, Set[Int]] = Map[Int, Set[Int]](1 -> Set[Int](1))
      assert(rw.changes.equals(expected))
    }

    {
      val rw = new ReadWriteMock[Set[Int], Int](Map(0 -> Set(0), 1 -> Set(2), 2 -> Set(1), 3 -> Set(2), 4 -> Set(0)), new SetRanger())
      val bs = new BoundedSum(0, 2)
      assert(bs.revise(rw, Equation(List(Addend(1, 0), Addend(1, 3), Addend(1, 4)), Eq(), 2)))
      assert(rw.changes.isEmpty)
    }

    {
      val rw = new ReadWriteMock[Set[Int], Int](Map(0 -> Set(0), 3 -> Set(0, 1, 2), 4 -> Set(0)), new SetRanger())
      val bs = new BoundedSum(0, 2)
      assert(!bs.revise(rw, Equation(List(Addend(1, 0), Addend(1, 3), Addend(1, 4)), Eq(), 3)))
      assert(rw.changes.isEmpty)
    }

    {
      val rw = new ReadWriteMock[Set[Int], Int](Map(0 -> Set(0), 1 -> Set(0, 1, 2), 2 -> Set(0, 1, 2)), new SetRanger())
      val bs = new BoundedSum(0, 3)
      assert(bs.revise(rw, Equation(List(Addend(1, 0), Addend(1, 1), Addend(1, 2)), Eq(), 4)))
      assert(rw.changes.equals(Map(1 -> 2, 2 -> 2)))
    }

    // definitely should write more of these
  }
}


package com.sciolizer.taffy

import org.scalatest.FunSuite
import com.sciolizer.taffy.Isos.{Permutation, IsoKey, Iso}

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 2/14/13
 * Time: 5:45 PM
 */
class IsosSuite extends FunSuite {
  test("permutation creation") {
    val i = new Iso(new IsoKey(), List(4, 17, 9))
    assert(i.permutation(List(17, 4)) === Permutation(List(1, 0)))
  }

  test("permutation execution") {
    val p = Permutation(List(2, 0))
    assert(p.rearrange(List(20, 4, 9)) === List(9, 20))
  }

  test("rearranging self produces self") {
    val original = List(7, 12, 14)
    val i = new Iso(new IsoKey(), original)
    val rearranged = List(12, 7)
    val perm = i.permutation(rearranged)
    assert(perm.rearrange(original) === rearranged)
  }

  test("Transitive closure") {
    val i = new Isos()
    i.add(List(1, 2, 3), Set(List(4, 5, 6), List(7, 8, 9)))
    assert(i.get(List(6, 4)) === Set(List(3, 1), List(9, 7)))
    assert(i.get(List(4, 3)) === Set.empty)
  }

  sealed abstract class EqualityConstraint(val left: Int, val right: Int)
      extends Revisable[Set[Color], Color]
      with Comparable[EqualityConstraint] {

    lazy val coverage: Set[VarId] = Set(left, right)

    def revise(rw: ReadWrite[Set[Color], Color]): Boolean = {
      val leftVals = rw.readVar(left)
      if (leftVals.size == 1) {
        rw.setVar(right, toColor(leftVals.head))
        return true
      }
      val rightVals = rw.readVar(right)
      if (rightVals.size == 1) {
        rw.setVar(left, toColor(rightVals.head))
      }
      true
    }

    def compareTo(o: EqualityConstraint): Int = {
      if (left < o.left) return -1 else if (left > o.left) return 1
      if (right < o.right) return -1 else if (right > o.right) return 1
      if (left == right) 0 else if (this.isInstanceOf[Equal]) -1 else 1
    }

    def complement(vid: Int): Option[Int] = if (left == vid) Some(right) else if (right == vid) Some(left) else None

    def toColor(c: Color): Color
  }
  case class Equal(l: Int, r: Int) extends EqualityConstraint(l, r) {
    def toColor(c: Color): Color = c
  }
  case class Unequal(l: Int, r: Int) extends EqualityConstraint(l, r) {
    def toColor(c: Color): Color = c.opposite
  }
  abstract class Color { def opposite: Color }
  case class Black() extends Color { def opposite: Color = White() }
  case class White() extends Color { def opposite: Color = Black() }
  class TwoColoringInference extends Inference[EqualityConstraint] {

    /** Creates a copy of the given constraint with its variables swapped out for other variables.
      *
      * @param constraint constraint to make a copy of
      * @param substitution keys will be constraint.coverage. values are the desired replacement variables
      * @return A copy of the given constraint, but with different variables.
      */
    def substitute[C <: EqualityConstraint](
        constraint: C,
        substitution: Map[VarId, VarId]): EqualityConstraint =
      constraint match {
        case Equal(l, r) => Equal(substitution(l), substitution(r))
        case Unequal(l, r) => Unequal(substitution(l), substitution(r))
    }
                               /*
    override def superSimpleLearn(vars: Set[VarId], constraints: Set[MixedConstraint]): List[(EqualityConstraint, List[MixedConstraint])] = {
      val cs: Set[EqualityConstraint] = (for (Right(c) <- constraints) yield c).toSet
      var ret: List[(EqualityConstraint, List[MixedConstraint])] = List.empty
      for (one <- cs; two <- cs; if one.compareTo(two) < 0; vid <- vars) {
        (one.complement(vid), two.complement(vid)) match {
          case (Some(i), Some(j)) => ret = ret :+ (if (one.getClass == two.getClass) Equal(i, j) else Unequal(i, j), List(Right(one), Right(two)))
          case _ =>
        }
      }
      ret
    }          */
  }

  def twoColoringProblem(): SuperSimpleSolver[EqualityConstraint, Set[Color], Color] = {
    /*
      --- b ---       -- e --
     /         \     /       \
    a          -- d -         g
     \         /     \       /
      --- c ---       -- f --
     */
    val ab = Unequal(0, 1)
    val ac = Unequal(0, 2)
    val bd = Unequal(1, 3)
    val cd = Unequal(2, 3)
//    val de = Unequal(3, 4)
//    val df = Unequal(3, 5)
//    val eg = Unequal(4, 6)
//    val fg = Unequal(5, 6)
    val isos = new Isos()
    isos.add(List(0, 1, 2, 3), Set(List(3, 4, 5, 6)))
    val problem = new Problem[EqualityConstraint, Set[Color], Color](7, Set(ab, ac, bd, cd /*, de, df, eg, fg */), Set(Black(), White()), isos)
    new SuperSimpleSolver[EqualityConstraint, Set[Color], Color](new TwoColoringInference(), problem, new SetRanger[Color]())
  }

  test("Two color symmetry") {
    val sss = twoColoringProblem()
    assert(sss.backtrackingSearch(((0 until 7).map(_ -> sss.problem.candidateValues).toMap: Map[Int, Set[Color]]) ++ Map[Int, Set[Color]](0 -> Set(Black()), 3 -> Set(White()))) === None)
    println(sss.learned)
    println((for (Right(x) <- sss.learned) yield x).toSet)
    assert(sss.learned.contains(Right(Equal(1, 2))))
    assert(sss.learned.contains(Right(Equal(4, 5))))
  }

  test("Inferring initial constraints from symmetry") {
    val sss = twoColoringProblem()
    sss.learned.contains(Right(Unequal(5, 6)))
  }
}

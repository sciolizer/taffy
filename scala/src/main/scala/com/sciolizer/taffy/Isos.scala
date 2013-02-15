package com.sciolizer.taffy

import collection.mutable
import com.sciolizer.taffy.Isos.{Permutation, Iso, IsoKey}

/**
 * Iso laws:
 *   standard equivalence rules (reflexive, symmetric, transitive)
 *   Subsequences are isomorphic. (If [a,b,c] is isomorphic to [x,y,z], then [a,c] is isomorphic to [x,z].)
 *   Isomorphic vars have isomorphic constraints. If constraint A covers variables a and b, and [a,b,c] is
 *     isomorphic to [x,y,z], then the solver will deduce that there is an equivalent constraint on x and y.
 *     Constraints whose coverage is only partially within an iso are not assumed to be isomorphic.
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 2/14/13
 * Time: 5:07 PM
 */
object Isos {

  type VarId = Int
  class IsoKey
  class Iso[A](val key: IsoKey, original: List[A]) {
    def permutation(in: List[A]): Permutation = {
      var perm: List[Int] = List.empty
      for (vid <- in) {
        perm = perm :+ original.indexOf(vid)
      }
      Permutation(perm)
    }
  }
  case class Permutation(perm: List[Int]) {
    def rearrange[A](vars: List[A]): List[A] = {
      var ret: List[A] = List.empty
      for (i <- perm) {
        ret = ret :+ vars(i)
      }
      ret
    }
  }

}

trait Isomorphisms {
  type VarId = Int
  def get(one: List[VarId]): Set[List[VarId]]
}
object NullIsomorphisms extends Isomorphisms {
  def get(one: List[NullIsomorphisms.VarId]): Set[List[NullIsomorphisms.VarId]] = Set.empty
}
class Isos extends Isomorphisms {

  private val isos: mutable.Map[IsoKey, Set[List[VarId]]] = mutable.Map.empty
  private val lookup: mutable.Map[Set[VarId], Iso[VarId]] = mutable.Map.empty

  /**
   * Declares a set of isomorphisms. The transitive closure is computed implicitly.
   *
   * @param one template
   * @param others ismorphic variables
   */
  def add(one: List[VarId], others: Set[List[VarId]]) {
    val key = new IsoKey()
    val combined = others + one
    var vals: Set[List[VarId]] = Set.empty
    for (sequence <- combined) {
      val iso = new Iso(key, sequence)
      vals = vals + sequence
      val set = sequence.toSet
      if (lookup.contains(set)) {
        throw new NotImplementedError("combining of isos is not yet implemented")
      }
      lookup(set) = iso
    }
    isos(key) = vals
  }

  def get(one: List[VarId]): Set[List[VarId]] = {
    val subset = one.toSet
    var ret: Set[List[VarId]] = Set.empty
    for ((nums, iso) <- lookup) {
      if (subset.subsetOf(nums)) {
        val ordering: Permutation = iso.permutation(one)
        for (other <- isos(iso.key)) {
          val rearranged = ordering.rearrange(other)
          if (rearranged != one) ret = ret + rearranged
        }
      }
    }
    ret
  }
}

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
}

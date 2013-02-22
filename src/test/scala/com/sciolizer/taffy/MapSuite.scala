package com.sciolizer.taffy

import org.scalatest.FunSuite
import collection.mutable

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 2/14/13
 * Time: 10:08 AM
 */
class MapSuite extends FunSuite {
  test("Inserting into a set on non-existent key") {
    val map: mutable.Map[String, mutable.Set[Int]] = mutable.Map.empty.withDefault(_ => mutable.Set.empty)
    map("thekey") = map("thekey") + 3
//    map(2) = map(2) + 3
    assert(map.size === 1)
    val first = map.head
    assert(first._1 === "thekey")
    val set = first._2
    assert(set.size === 1)
    assert(set.head === 3)
  }
}

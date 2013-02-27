package com.sciolizer.taffy.domains.lists

import com.sciolizer.taffy.{Ranger, ReadWrite, Revisable}

case class ArithmeticSequence(
    difference: Int,
    list: DynamicList[Set[Int], Int],
    ranger: Ranger[Set[Int], Int])
  extends Revisable[Set[Int], Int] {

  def revise(rw: ReadWrite[Set[Int], Int]): Boolean = {
    val rwList = list.readWrite(rw)
    if (!rwList.isEmptyBools.contains(false)) return true // empty list satisfies any difference
    rwList.snoc match {
      case None =>
      case Some((head, tail)) =>
        val child: Option[Set[Int]] = reviseAt(head.map { _ + difference }, tail)
        child match {
          case None =>
          case Some(xs) =>
            rwList.intersectHead(xs map { _ - difference })
        }
        rwList.intersectHead(child map { _ - difference })
    }
    true // conflicts are discovered by emptying a variable of possible values
  }

  private def reviseAt(allowed: Set[Int], rwList: ReadsWritesList[Set[Int]]): Set[Int] = {
    if (!rwList.isEmptyBools.contains(true)) {
      // We only do the intersection if the list is necessarily non-empty
      rwList.intersectHead(allowed)
    }
    if (!rwList.isEmptyBools.contains(false)) return null // empty list satisfies any difference
    if (ranger.isEmpty(rwList.heads)) return // is this right? What is heads
    rwList.snoc match {
      case None =>
      case Some((head, tail)) =>
        val child: Option[Set[Int]] = reviseAt(head.map { _ + difference }, tail)
        child match {
          case None =>
          case Some(xs) =>
            rwList.intersectHead(xs map { _ - difference })
        }
        rwList.intersectHead(child map { _ - difference })
    }
  }

  def coverage: Set[VarId] = list.coverage

}

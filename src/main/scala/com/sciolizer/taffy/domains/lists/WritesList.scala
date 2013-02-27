package com.sciolizer.taffy.domains.lists

trait WritesList[-Values] {

  def intersectEmpty(isEmpty: Values)

  def intersectHead(values: Values)

}

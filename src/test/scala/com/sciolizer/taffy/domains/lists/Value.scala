package com.sciolizer.taffy.domains.lists

sealed trait Value
case class ValueInt(value: Int) extends Value
case class ValueList(isEmpty: Boolean) extends Value


package com.sciolizer.taffy.domains.lists

import com.sciolizer.taffy.{Variable, Ranger, Instantiator, ReadWrite}
import com.sciolizer.taffy.ReadWrite.{Is, Accepts, Rejects}

class DynamicLists[Constraint, Values, Value](
    boolean: Boolean => Value,
    trueFalse: Values,
    constraint: DynamicListConstraint[Values, Value] => Constraint,
    solver: Instantiator[Constraint, Value],
    ranger: Ranger[Values, Value]) { // todo: could probably get rid of ranger (just leave in constructor)

  val isEmpty: Values = ranger.toSingleton(boolean(true))
  val isNotEmpty: Values = ranger.toSingleton(boolean(false))
  val nothing: Values = ranger.intersection(isEmpty, isNotEmpty)

  def newList(): DList = {
    // todo: find a way to resolve this hack
    var ret: DList = null
    def sideEffects(value: Value) {
      if (ranger.equal(isNotEmpty, ranger.toSingleton(value))) {
        ret.expand()
      }
    }
    val sizeIsZero = solver.newVariableX(Set(boolean(false)), sideEffects)
    solver.newConstraint(constraint(IsTypeofList(sizeIsZero.varId)))
    ret = DList(sizeIsZero)
    ret
  }

  case class DList(size: Variable[Value]) extends DynamicList[Values, Value] {

    var contents: Option[(Variable[Value], DList)] = None

    def expand() {
      contents = Some((solver.newVariable(Set.empty), newList()))
    }

    def readWrite(rw: ReadWrite[Values, Value]): ReadsWritesList[Values] = new ReadsWritesList[Values] {

      def intersectEmpty(isEmpty: Values) {
        rw.intersectVar(size.varId, isEmpty)
      }

      def heads: Values = {
        contents match {
          case None =>
            nothing
          case Some((head, _)) =>
            rw.readVar(head.varId)
        }
      }

      def values: List[Values] = {
        rw.contains(size.varId, boolean(false)) match {
          case Rejects() =>
            return List.empty
        }
        contents match {
          case None =>
            List.empty
          case Some((head, tail)) =>
            rw.readVar(head.varId) +: tail.readWrite(rw).values
        }
      }

      def intersectHead(values: Values) {
        contents match {
          case None =>
          case Some((head, _)) =>
            rw.intersectVar(head.varId, values)
        }
      }

      def tails: Option[ReadsList[Values]] = {
        contents match {
          case None =>
            None
          case Some((_, tail: DList)) =>
            Some(tail.readWrite(rw))
        }
      }

      def isEmpty: Values = {
        rw.readVar(size.varId)
      }

      def bounded: Boolean = {
        rw.contains(size.varId, boolean(false)) match {
          case Rejects() => return true
        }
        contents match {
          case None =>
            false
          case Some((_, tail)) =>
            tail.readWrite(rw).bounded
        }
      }
    }
  }

  case class IsTypeofList(varId: Int) extends DynamicListConstraint[Values, Value] {

    def revise(rw: ReadWrite[Values, Value]): Boolean = {
      rw.intersectVar(varId, trueFalse)
      true
    }

    def coverage: Set[VarId] = Set(varId)

  }

}

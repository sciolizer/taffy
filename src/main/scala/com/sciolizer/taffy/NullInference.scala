package com.sciolizer.taffy

class NullInference[Constraint] extends Inference[Constraint] {

  def substitute[C <: Constraint](constraint: C, substitution: Map[VarId, VarId]): Constraint =
    throw new UnsupportedOperationException

}

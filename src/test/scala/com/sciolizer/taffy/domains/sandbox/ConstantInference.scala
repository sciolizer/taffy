package com.sciolizer.taffy.domains.sandbox

import com.sciolizer.taffy.Inference

object ConstantInference extends Inference[Constant] {

  def substitute[C <: Constant](constraint: C, substitution: Map[VarId, VarId]): Constant =
    constraint.substitute(substitution)

}

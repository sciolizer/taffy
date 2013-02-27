package com.sciolizer.taffy.domains.lists

import com.sciolizer.taffy.{ReadWrite, Revisable}

trait DynamicListConstraint[Values, Value] extends Revisable[Values, Value]

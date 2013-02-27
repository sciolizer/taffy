package com.sciolizer.taffy.domains.lists

trait ReadsWritesList[Values] extends ReadsList[Values] with WritesList[Values]
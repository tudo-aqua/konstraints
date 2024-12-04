/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2024 The Konstraints Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package tools.aqua.konstraints.theories

import tools.aqua.konstraints.parser.*
import tools.aqua.konstraints.smt.*

/**
 * Convert an integer [inner] to real
 *
 * (to_real Int Real)
 */
class ToReal(override val inner: Expression<IntSort>) :
    UnaryExpression<RealSort, IntSort>("to_real".symbol(), RealSort) {
  companion object {
    private val theoriesSet = setOf(Theories.REALS_INTS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override fun copy(children: List<Expression<*>>): Expression<RealSort> =
      ToRealDecl.buildExpression(children, emptyList())
}

/**
 * Convert a real [inner] to int
 *
 * (to_int Real Int)
 */
class ToInt(override val inner: Expression<RealSort>) :
    UnaryExpression<IntSort, RealSort>("to_int".symbol(), IntSort) {
  companion object {
    private val theoriesSet = setOf(Theories.REALS_INTS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      ToIntDecl.buildExpression(children, emptyList())
}

/** (is_int Real Bool) */
class IsInt(override val inner: Expression<RealSort>) :
    UnaryExpression<BoolSort, RealSort>("is_int".symbol(), BoolSort) {
  companion object {
    private val theoriesSet = setOf(Theories.REALS_INTS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      IsIntDecl.buildExpression(children, emptyList())
}

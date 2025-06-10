/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2025 The Konstraints Authors
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

package tools.aqua.konstraints.smt

import tools.aqua.konstraints.parser.*

/**
 * Convert an integer [inner] to real
 *
 * (to_real Int Real)
 */
class ToReal(override val inner: Expression<IntSort>) :
    UnaryExpression<RealSort, IntSort>("to_real".toSymbolWithQuotes(), RealSort) {
  override val theories = REALS_INTS_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<RealSort> =
      ToRealDecl.constructDynamic(children, emptyList())
}

/**
 * Convert a real [inner] to int
 *
 * (to_int Real Int)
 */
class ToInt(override val inner: Expression<RealSort>) :
    UnaryExpression<IntSort, RealSort>("to_int".toSymbolWithQuotes(), IntSort) {
  override val theories = REALS_INTS_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      ToIntDecl.constructDynamic(children, emptyList())
}

/** (is_int Real Bool) */
class IsInt(override val inner: Expression<RealSort>) :
    UnaryExpression<BoolSort, RealSort>("is_int".toSymbolWithQuotes(), BoolSort) {
  override val theories = REALS_INTS_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      IsIntDecl.constructDynamic(children, emptyList())
}

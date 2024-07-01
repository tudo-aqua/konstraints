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
import tools.aqua.konstraints.parser.SortDecl
import tools.aqua.konstraints.parser.Theory
import tools.aqua.konstraints.smt.*

/** Reals Ints theory context */
object RealsIntsTheory : Theory {
  override val functions =
      listOf(
              IntNegDecl,
              IntSubDecl,
              IntAddDecl,
              IntMulDecl,
              IntDivDecl,
              ModDecl,
              AbsDecl,
              IntLessEqDecl,
              IntLessDecl,
              IntGreaterEqDecl,
              IntGreaterDecl,
              DivisibleDecl,
              RealNegDecl,
              RealSubDecl,
              RealAddDecl,
              RealMulDecl,
              RealDivDecl,
              RealLessEqDecl,
              RealLessDecl,
              RealGreaterEqDecl,
              RealGreaterDecl,
              ToRealDecl,
              ToIntDecl,
              IsIntDecl)
          .associateBy { it.name.toString() }

  override val sorts: Map<String, SortDecl<*>> =
      mapOf(Pair("Int", IntSortDecl), Pair("Real", RealSortDecl))
}

/**
 * Convert an integer [inner] to real
 *
 * (to_real Int Real)
 */
class ToReal(override val inner: Expression<IntSort>) :
    UnaryExpression<RealSort, IntSort>("to_real".symbol(), RealSort) {
  override fun copy(children: List<Expression<*>>): Expression<RealSort> =
      ToRealDecl.buildExpression(children, emptySet())
}

object ToRealDecl :
    FunctionDecl1<IntSort, RealSort>(
        "to_real".symbol(), emptySet(), IntSort, emptySet(), emptySet(), RealSort) {
  override fun buildExpression(
      param: Expression<IntSort>,
      bindings: Bindings
  ): Expression<RealSort> = ToReal(param)
}

/**
 * Convert a real [inner] to int
 *
 * (to_int Real Int)
 */
class ToInt(override val inner: Expression<RealSort>) :
    UnaryExpression<IntSort, RealSort>("to_int".symbol(), IntSort) {
  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      ToIntDecl.buildExpression(children, emptySet())
}

object ToIntDecl :
    FunctionDecl1<RealSort, IntSort>(
        "to_real".symbol(), emptySet(), RealSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param: Expression<RealSort>,
      bindings: Bindings
  ): Expression<IntSort> = ToInt(param)
}

/** (is_int Real Bool) */
class IsInt(override val inner: Expression<RealSort>) :
    UnaryExpression<BoolSort, RealSort>("is_int".symbol(), BoolSort) {
  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      IsIntDecl.buildExpression(children, emptySet())
}

object IsIntDecl :
    FunctionDecl1<RealSort, BoolSort>(
        "to_real".symbol(), emptySet(), RealSort, emptySet(), emptySet(), BoolSort) {
  override fun buildExpression(
      param: Expression<RealSort>,
      bindings: Bindings
  ): Expression<BoolSort> = IsInt(param)
}

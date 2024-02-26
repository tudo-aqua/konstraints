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
import tools.aqua.konstraints.parser.TheoryContext
import tools.aqua.konstraints.smt.BoolSort
import tools.aqua.konstraints.smt.Expression

internal object RealsIntsContext : TheoryContext {
  override val functions: HashSet<FunctionDecl<*>> =
      hashSetOf(
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

  override val sorts: Map<String, SortDecl<*>> =
      mapOf(Pair("Int", IntSortDecl), Pair("Real", RealSortDecl))
}

class ToReal(val inner: Expression<IntSort>) : Expression<RealSort>() {
  override val symbol: String = "(to_real $inner)"
  override val sort: RealSort = RealSort

  override fun toString(): String = symbol
}

object ToRealDecl :
    FunctionDecl1<IntSort, RealSort>(
        "to_real", emptySet(), IntSort, emptySet(), emptySet(), RealSort) {
  override fun buildExpression(
      param: Expression<IntSort>,
      bindings: Bindings
  ): Expression<RealSort> = ToReal(param)
}

class ToInt(val inner: Expression<RealSort>) : Expression<IntSort>() {
  override val symbol: String = "(to_int $inner)"
  override val sort: IntSort = IntSort

  override fun toString(): String = symbol
}

object ToIntDecl :
    FunctionDecl1<RealSort, IntSort>(
        "to_real", emptySet(), RealSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param: Expression<RealSort>,
      bindings: Bindings
  ): Expression<IntSort> = ToInt(param)
}

class IsInt(val inner: Expression<RealSort>) : Expression<BoolSort>() {
  override val symbol: String = "(is_int $inner)"
  override val sort: BoolSort = BoolSort

  override fun toString(): String = symbol
}

object IsIntDecl :
    FunctionDecl1<RealSort, BoolSort>(
        "to_real", emptySet(), RealSort, emptySet(), emptySet(), BoolSort) {
  override fun buildExpression(
      param: Expression<RealSort>,
      bindings: Bindings
  ): Expression<BoolSort> = IsInt(param)
}

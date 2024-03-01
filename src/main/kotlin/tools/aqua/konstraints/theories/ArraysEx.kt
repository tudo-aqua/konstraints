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
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.smt.SortParameter

internal object ArrayExContext : TheoryContext {
  override val functions: HashSet<FunctionDecl<*>> = hashSetOf(ArraySelectDecl, ArrayStoreDecl)

  override val sorts: Map<String, SortDecl<*>> = mapOf(Pair("Array", ArraySortDecl))
}

class ArraySort(val x: Sort, val y: Sort) : Sort("Array".symbol(), emptyList(), listOf(x, y))

internal object ArraySortDecl :
    SortDecl<ArraySort>(
        "Array".symbol(), setOf(SortParameter("X"), SortParameter("Y")), emptySet()) {
  override fun getSort(bindings: Bindings): ArraySort =
      ArraySort(bindings[SortParameter("X")], bindings[SortParameter("Y")])
}

class ArraySelect(val array: Expression<ArraySort>, val index: Expression<*>) : Expression<Sort>() {
  override val symbol: Symbol = "select".symbol()
  override val sort: Sort = array.sort.y

  init {
    require(array.sort.x == index.sort)
  }
}

object ArraySelectDecl :
    FunctionDecl2<ArraySort, Sort, Sort>(
        "select".symbol(),
        setOf(SortParameter("X"), SortParameter("Y")),
        ArraySort(SortParameter("X"), SortParameter("Y")),
        SortParameter("X"),
        emptySet(),
        emptySet(),
        SortParameter("Y")) {
  override fun buildExpression(
      param1: Expression<ArraySort>,
      param2: Expression<Sort>,
      bindings: Bindings
  ): Expression<Sort> = ArraySelect(param1, param2)
}

class ArrayStore(
    val array: Expression<ArraySort>,
    val index: Expression<*>,
    val value: Expression<*>
) : Expression<ArraySort>() {
  override val symbol: Symbol = "store".symbol()
  override val sort: ArraySort = array.sort

  init {
    require(array.sort.x == index.sort)
    require(array.sort.y == value.sort)
  }
}

object ArrayStoreDecl :
    FunctionDecl3<ArraySort, Sort, Sort, ArraySort>(
        "store".symbol(),
        setOf(SortParameter("X"), SortParameter("Y")),
        ArraySort(SortParameter("X"), SortParameter("Y")),
        SortParameter("X"),
        SortParameter("Y"),
        emptySet(),
        emptySet(),
        ArraySort(SortParameter("X"), SortParameter("Y"))) {
  override fun buildExpression(
      param1: Expression<ArraySort>,
      param2: Expression<Sort>,
      param3: Expression<Sort>,
      bindings: Bindings
  ): Expression<ArraySort> = ArrayStore(param1, param2, param3)
}

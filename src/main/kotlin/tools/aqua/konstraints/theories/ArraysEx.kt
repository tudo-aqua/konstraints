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

/** Array extension theory object */
object ArrayExTheory : Theory {
  override val functions: Map<String, FunctionDecl<*>> =
      listOf(ArraySelectDecl, ArrayStoreDecl).associateBy { it.name.toString() }

  override val sorts: MutableMap<String, SortDecl<*>> = mutableMapOf(Pair("Array", ArraySortDecl))
}

/** Array sort */
class ArraySort<X : Sort, Y : Sort>(val x: X, val y: Y) :
    Sort("Array".symbol(), emptyList(), listOf(x, y)) {
  override fun toString(): String = "(Array $x $y)"
}

/** Sort declaration object for array sort */
internal object ArraySortDecl :
    SortDecl<ArraySort<Sort, Sort>>(
        "Array".symbol(), setOf(SortParameter("X"), SortParameter("Y")), emptySet()) {
  override fun getSort(bindings: Bindings): ArraySort<Sort, Sort> =
      ArraySort(bindings[SortParameter("X")], bindings[SortParameter("Y")])
}

/**
 * Array selection operation
 *
 * (par (X Y) (select (Array X Y) X Y)
 */
class ArraySelect<X : Sort, Y : Sort>(
    val array: Expression<ArraySort<X, Y>>,
    val index: Expression<X>
) : BinaryExpression<Y, ArraySort<X, Y>, X>("select".symbol(), array.sort.y) {
  init {
    require(array.sort.x == index.sort)
  }

  override val lhs: Expression<ArraySort<X, Y>> = array

  override val rhs: Expression<X> = index

  override fun copy(children: List<Expression<*>>): Expression<Y> =
      ArraySelectDecl.buildExpression(children, emptyList()) as Expression<Y>
}

/** Array selection declaration object */
object ArraySelectDecl :
    FunctionDecl2<ArraySort<Sort, Sort>, Sort, Sort>(
        "select".symbol(),
        setOf(SortParameter("X"), SortParameter("Y")),
        ArraySort(SortParameter("X"), SortParameter("Y")),
        SortParameter("X"),
        emptySet(),
        emptySet(),
        SortParameter("Y")) {
  override fun buildExpression(
      param1: Expression<ArraySort<Sort, Sort>>,
      param2: Expression<Sort>,
      bindings: Bindings
  ): Expression<Sort> = ArraySelect(param1, param2)
}

/**
 * Array store operation
 *
 * (par (X Y) (store (Array X Y) X Y (Array X Y)))
 */
class ArrayStore<X : Sort, Y : Sort>(
    val array: Expression<ArraySort<X, Y>>,
    val index: Expression<X>,
    val value: Expression<Y>
) : TernaryExpression<ArraySort<X, Y>, ArraySort<X, Y>, X, Y>("store".symbol(), array.sort) {
  init {
    require(array.sort.x == index.sort)
    require(array.sort.y == value.sort)
  }

  override val lhs: Expression<ArraySort<X, Y>> = array
  override val mid: Expression<X> = index
  override val rhs: Expression<Y> = value

  override val children: List<Expression<*>> = listOf(array, index, value)

  override fun copy(children: List<Expression<*>>): Expression<ArraySort<X, Y>> =
      ArrayStoreDecl.buildExpression(children, emptyList()) as Expression<ArraySort<X, Y>>
}

/** Array store declaration object */
object ArrayStoreDecl :
    FunctionDecl3<ArraySort<Sort, Sort>, Sort, Sort, ArraySort<Sort, Sort>>(
        "store".symbol(),
        setOf(SortParameter("X"), SortParameter("Y")),
        ArraySort(SortParameter("X"), SortParameter("Y")),
        SortParameter("X"),
        SortParameter("Y"),
        emptySet(),
        emptySet(),
        ArraySort(SortParameter("X"), SortParameter("Y"))) {
  override fun buildExpression(
      param1: Expression<ArraySort<Sort, Sort>>,
      param2: Expression<Sort>,
      param3: Expression<Sort>,
      bindings: Bindings
  ): Expression<ArraySort<Sort, Sort>> = ArrayStore(param1, param2, param3)
}

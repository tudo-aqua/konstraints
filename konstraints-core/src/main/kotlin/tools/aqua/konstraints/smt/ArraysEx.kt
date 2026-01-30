/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2026 The Konstraints Authors
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

/*
 * This file implements the SMT ArraysEx theory
 * https://smt-lib.org/theories-ArraysEx.shtml
 */

/**
 * Array selection operation.
 * - `(par (X Y) (select (Array X Y) X Y)`
 * - `(select [array] [index])`
 */
class ArraySelect<X : Sort, Y : Sort>(
    val array: Expression<ArraySort<X, Y>>,
    val index: Expression<X>,
) : BinaryExpression<Y, ArraySort<X, Y>, X>("select".toSymbol(), array.sort.y) {
  override val theories = ARRAYS_EX_MARKER_SET

  init {
    require(array.sort.x == index.sort)
  }

  override val lhs: Expression<ArraySort<X, Y>> = array

  override val rhs: Expression<X> = index

  @Suppress("UNCHECKED_CAST")
  override fun copy(children: List<Expression<*>>): Expression<Y> =
      ArraySelectDecl.constructDynamic(children, emptyList()) as Expression<Y>
}

/**
 * Array store operation.
 * - `(par (X Y) (store (Array X Y) X Y (Array X Y)))`
 * - `(store [array] [index] [value])`
 */
class ArrayStore<X : Sort, Y : Sort>(
    val array: Expression<ArraySort<X, Y>>,
    val index: Expression<X>,
    val value: Expression<Y>,
) :
    TernaryExpression<ArraySort<X, Y>, ArraySort<X, Y>, X, Y>(
        "store".toSymbol(),
        array.sort,
    ) {
  override val theories = ARRAYS_EX_MARKER_SET

  init {
    require(array.sort.x == index.sort)
    require(array.sort.y == value.sort)
  }

  override val lhs: Expression<ArraySort<X, Y>> = array
  override val mid: Expression<X> = index
  override val rhs: Expression<Y> = value

  override val children: List<Expression<*>> = listOf(array, index, value)

  @Suppress("UNCHECKED_CAST")
  override fun copy(children: List<Expression<*>>): Expression<ArraySort<X, Y>> =
      ArrayStoreDecl.constructDynamic(children, emptyList()) as Expression<ArraySort<X, Y>>
}

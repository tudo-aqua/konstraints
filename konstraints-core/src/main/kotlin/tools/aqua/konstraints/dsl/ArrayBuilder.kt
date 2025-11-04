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

package tools.aqua.konstraints.dsl

import tools.aqua.konstraints.dsl.IntStoreBuilder
import tools.aqua.konstraints.smt.*

/** Select value stored in [array] at location [index]. */
fun <X : Sort, Y : Sort> select(array: Expression<ArraySort<X, Y>>, index: Expression<X>) =
    ArraySelect(array, index)

/** Select value stored in [array] at location [index]. */
fun <X : Sort, Y : Sort> select(array: Expression<ArraySort<X, Y>>, index: () -> Expression<X>) =
    ArraySelect(array, index())

/** Select value stored in [array] at location [index]. */
fun <X : Sort, Y : Sort> select(array: () -> Expression<ArraySort<X, Y>>, index: Expression<X>) =
    ArraySelect(array(), index)

/** Select value stored in [array] at location [index]. */
fun <X : Sort, Y : Sort> select(
    array: () -> Expression<ArraySort<X, Y>>,
    index: () -> Expression<X>,
) = ArraySelect(array(), index())

/** Store [value] in [array] at location [index]. */
fun <X : Sort, Y : Sort> store(
    array: Expression<ArraySort<X, Y>>,
    index: Expression<X>,
    value: Expression<Y>,
) = ArrayStore(array, index, value)

/** Store [value] in [array] at location [index]. */
fun <X : Sort, Y : Sort> store(
    array: Expression<ArraySort<X, Y>>,
    index: Expression<X>,
    value: () -> Expression<Y>,
) = ArrayStore(array, index, value())

/** Store [value] in [array] at location [index]. */
fun <X : Sort, Y : Sort> store(
    array: Expression<ArraySort<X, Y>>,
    index: () -> Expression<X>,
    value: Expression<Y>,
) = ArrayStore(array, index(), value)

/** Store [value] in [array] at location [index]. */
fun <X : Sort, Y : Sort> store(
    array: Expression<ArraySort<X, Y>>,
    index: () -> Expression<X>,
    value: () -> Expression<Y>,
) = ArrayStore(array, index(), value())

/** Store [value] in [array] at location [index]. */
fun <X : Sort, Y : Sort> store(
    array: () -> Expression<ArraySort<X, Y>>,
    index: Expression<X>,
    value: Expression<Y>,
) = ArrayStore(array(), index, value)

/** Store [value] in [array] at location [index]. */
fun <X : Sort, Y : Sort> store(
    array: () -> Expression<ArraySort<X, Y>>,
    index: Expression<X>,
    value: () -> Expression<Y>,
) = ArrayStore(array(), index, value())

/** Store [value] in [array] at location [index]. */
fun <X : Sort, Y : Sort> store(
    array: () -> Expression<ArraySort<X, Y>>,
    index: () -> Expression<X>,
    value: Expression<Y>,
) = ArrayStore(array(), index(), value)

/** Store [value] in [array] at location [index]. */
fun <X : Sort, Y : Sort> store(
    array: () -> Expression<ArraySort<X, Y>>,
    index: () -> Expression<X>,
    value: () -> Expression<Y>,
) = ArrayStore(array(), index(), value())

/** Store [value] at location [index]. */
fun <X : Sort, Y : Sort> ArrayStore<X, Y>.store(index: Expression<X>, value: Expression<Y>) =
    store(this, index, value)

/** Store [value] at location [index]. */
fun <X : Sort, Y : Sort> ArrayStore<X, Y>.store(index: () -> Expression<X>, value: Expression<Y>) =
    store(this, index, value)

/** Store [value] at location [index]. */
fun <X : Sort, Y : Sort> ArrayStore<X, Y>.store(index: Expression<X>, value: () -> Expression<Y>) =
    store(this, index, value)

/** Store [value] at location [index]. */
fun <X : Sort, Y : Sort> ArrayStore<X, Y>.store(
    index: () -> Expression<X>,
    value: () -> Expression<Y>,
) = store(this, index, value)

infix fun<X : Sort, Y : Sort> Expression<Y>.at(index : Expression<X>) = this to index

infix fun<X: Sort, Y : Sort> Expression<ArraySort<X, Y>>.store(entry : Pair<Expression<Y>, Expression<X>>) = ArrayStore(this, entry.second, entry.first)

infix fun<X: Sort, Y : Sort> ArrayStore<X, Y>.then(entry: Pair<Expression<Y>, Expression<X>>) = ArrayStore(this, entry.second, entry.first)

infix fun<Y : Sort> Expression<Y>.at(index : Int) = this to index

infix fun<Y: Sort> Expression<ArraySort<IntSort, Y>>.store(entry : Pair<Expression<Y>, Int>) = ArrayStore(this, IntLiteral(entry.second), entry.first)

infix fun<Y: Sort> ArrayStore<IntSort, Y>.then(entry: Pair<Expression<Y>, Int>) = ArrayStore(this, IntLiteral(entry.second), entry.first)

infix fun<X : Sort> Int.at(index : Expression<X>) = this to index

infix fun<X: Sort> Expression<ArraySort<X, IntSort>>.store(entry : Pair<Int, Expression<X>>) = ArrayStore(this, entry.second, IntLiteral(entry.first))

infix fun<X: Sort> ArrayStore<X, IntSort>.then(entry: Pair<Int, Expression<X>>) = ArrayStore(this, entry.second, IntLiteral(entry.first))

fun main() {
  smt(QF_AX) {
    val expr = const(Bool)
    val index = const(SMTInt)
    val array = const(SMTArray(SMTInt, Bool))

    val expr1 = array store (expr at index) then (expr at index) then (expr at 1)
  }
}

// value storeAt index then (value at index) then... to array
// values storeAt indices to array

/*
 * store {
 *          value at index
 *          value at index
 *          ...
 * } to array
 */

/*
 * indexing operator?
 * - val array by ...
 * - array[i] = j (store array i j)
 * - array[i] (select array i)
 */

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
    index: () -> Expression<X>
) = ArraySelect(array(), index())

/** Store [value] in [array] at location [index]. */
fun <X : Sort, Y : Sort> store(
    array: Expression<ArraySort<X, Y>>,
    index: Expression<X>,
    value: Expression<Y>
) = ArrayStore(array, index, value)

/** Store [value] in [array] at location [index]. */
fun <X : Sort, Y : Sort> store(
    array: Expression<ArraySort<X, Y>>,
    index: Expression<X>,
    value: () -> Expression<Y>
) = ArrayStore(array, index, value())

/** Store [value] in [array] at location [index]. */
fun <X : Sort, Y : Sort> store(
    array: Expression<ArraySort<X, Y>>,
    index: () -> Expression<X>,
    value: Expression<Y>
) = ArrayStore(array, index(), value)

/** Store [value] in [array] at location [index]. */
fun <X : Sort, Y : Sort> store(
    array: Expression<ArraySort<X, Y>>,
    index: () -> Expression<X>,
    value: () -> Expression<Y>
) = ArrayStore(array, index(), value())

/** Store [value] in [array] at location [index]. */
fun <X : Sort, Y : Sort> store(
    array: () -> Expression<ArraySort<X, Y>>,
    index: Expression<X>,
    value: Expression<Y>
) = ArrayStore(array(), index, value)

/** Store [value] in [array] at location [index]. */
fun <X : Sort, Y : Sort> store(
    array: () -> Expression<ArraySort<X, Y>>,
    index: Expression<X>,
    value: () -> Expression<Y>
) = ArrayStore(array(), index, value())

/** Store [value] in [array] at location [index]. */
fun <X : Sort, Y : Sort> store(
    array: () -> Expression<ArraySort<X, Y>>,
    index: () -> Expression<X>,
    value: Expression<Y>
) = ArrayStore(array(), index(), value)

/** Store [value] in [array] at location [index]. */
fun <X : Sort, Y : Sort> store(
    array: () -> Expression<ArraySort<X, Y>>,
    index: () -> Expression<X>,
    value: () -> Expression<Y>
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
    value: () -> Expression<Y>
) = store(this, index, value)

data class StoreOperation<X : Sort, Y : Sort>(val value: Expression<Y>, val index: Expression<X>)

sealed class StoreBuilder<X : Sort, Y : Sort>(
    internal val operations: MutableList<StoreOperation<X, Y>> = mutableListOf()
) {
  infix fun Expression<Y>.at(index: Expression<X>) =
      this@StoreBuilder.apply { operations.add(StoreOperation(this@at, index)) }
}

class GenericStoreBuilder<X : Sort, Y : Sort> : StoreBuilder<X, Y>()

class IntStoreBuilder : StoreBuilder<IntSort, IntSort>() {
    infix fun Int.at(index: Int) =
        this@IntStoreBuilder.apply { operations.add(StoreOperation(IntLiteral(this@at), IntLiteral(index))) }
}

fun store(
    init: IntStoreBuilder.() -> IntStoreBuilder
) = IntStoreBuilder().init()


fun <X : Sort, Y : Sort> store(
    init: StoreBuilder<X, Y>.() -> StoreBuilder<X, Y>
) = GenericStoreBuilder<X, Y>().init()

fun <X : Sort, Y : Sort> storeAt(
    init: StoreBuilder<X, Y>.() -> StoreBuilder<X, Y>,
    array: Expression<ArraySort<X, Y>>
) = GenericStoreBuilder<X, Y>().init() into array


infix fun <X : Sort, Y : Sort> Expression<Y>.storeAt(index: Expression<X>): StoreBuilder<X, Y> =
    GenericStoreBuilder<X, Y>().apply { operations.add(StoreOperation<X, Y>(this@storeAt, index)) }

/** Store the values from [this] at the specified [indices] */
infix fun <X : Sort, Y : Sort> List<Expression<Y>>.storeAt(
    indices: List<Expression<X>>
): StoreBuilder<X, Y> =
    GenericStoreBuilder<X, Y>().apply {
      operations.addAll(
          (this@storeAt zip indices).map { (value, index) -> StoreOperation<X, Y>(value, index) })
    }

infix fun <X : Sort, Y : Sort> StoreBuilder<X, Y>.then(
    next: StoreOperation<X, Y>
): StoreBuilder<X, Y> = this.apply { operations.add(next) }

infix fun <X : Sort, Y : Sort> StoreBuilder<X, Y>.then(
    next: () -> StoreOperation<X, Y>
): StoreBuilder<X, Y> = this.apply { operations.add(next()) }

infix fun <X : Sort, Y : Sort> Expression<Y>.at(index: Expression<X>): StoreOperation<X, Y> =
    StoreOperation(this, index)

infix fun <X : Sort, Y : Sort> Expression<Y>.at(index: () -> Expression<X>): StoreOperation<X, Y> =
    StoreOperation(this, index())

infix fun <X : Sort, Y : Sort> (() -> Expression<Y>).at(index: Expression<X>): StoreOperation<X, Y> =
    StoreOperation(this(), index)

infix fun <X : Sort, Y : Sort> (() -> Expression<Y>).at(index: () -> Expression<X>): StoreOperation<X, Y> =
    StoreOperation(this(), index())

// Specify the target array
infix fun <X : Sort, Y : Sort> StoreBuilder<X, Y>.into(array: Expression<ArraySort<X, Y>>) =
    operations into array

infix fun<X : Sort, Y : Sort> List<StoreOperation<X, Y>>.into(array: Expression<ArraySort<X, Y>>) =
    this.foldRight(array) { operation, acc ->
        ArrayStore(acc, operation.index, operation.value)
    }

// TODO conversion of kotlin types to smt types to allow 0 storeAt 0 then ... for numerals and
// strings

/**
 * Creates a [StoreBuilder] for storing this [Expression] at the given [index].
 *
 * This infix function allows for Kotlin [Int] to be used as [index], [index] is automatically converted to [IntLiteral]
 */
infix fun <Y : Sort> Expression<Y>.storeAt(index: Int): StoreBuilder<IntSort, Y> =
    GenericStoreBuilder<IntSort, Y>().apply { operations.add(StoreOperation<IntSort, Y>(this@storeAt, IntLiteral(index))) }

/**
 * Store the values from [this] list at the specified [indices]
 *
 * This infix function allows for Kotlin [Int] to be used as index, [indices] are automatically converted to [IntLiteral]
 **/
infix fun <Y : Sort> List<Expression<Y>>.storeAt(
    indices: List<Int>
): StoreBuilder<IntSort, Y> =
    GenericStoreBuilder<IntSort, Y>().apply {
        operations.addAll(
            (this@storeAt zip indices).map { (value, index) -> StoreOperation<IntSort, Y>(value, IntLiteral(index)) })
    }

/**
 * Store [this] at [index], index is automatically converted to [IntLiteral]
 */
infix fun <Y : Sort> Expression<Y>.at(index: Int): StoreOperation<IntSort, Y> =
    StoreOperation(this, IntLiteral(index))

/**
 * Store [this] at [index], index is automatically converted to [IntLiteral]
 */
infix fun <Y : Sort> Expression<Y>.at(index: () -> Int): StoreOperation<IntSort, Y> =
    StoreOperation(this, IntLiteral(index()))

/**
 * Store [this] at [index], index is automatically converted to [IntLiteral]
 */
infix fun <Y : Sort> (() -> Expression<Y>).at(index: Int): StoreOperation<IntSort, Y> =
    StoreOperation(this(), IntLiteral(index))

/**
 * Store [this] at [index], index is automatically converted to [IntLiteral]
 */
infix fun <Y : Sort> (() -> Expression<Y>).at(index: () -> Int): StoreOperation<IntSort, Y> =
    StoreOperation(this(), IntLiteral(index()))

infix fun <X : Sort> Int.at(index: Expression<X>): StoreOperation<X, IntSort> =
    StoreOperation(IntLiteral(this), index)

infix fun <X : Sort> Int.at(index: () -> Expression<X>): StoreOperation<X, IntSort> =
    StoreOperation(IntLiteral(this), index())

infix fun <X : Sort> (() -> Int).at(index: Expression<X>): StoreOperation<X, IntSort> =
    StoreOperation(IntLiteral(this()), index)

infix fun <X : Sort> (() -> Int).at(index: () -> Expression<X>): StoreOperation<X, IntSort> =
    StoreOperation(IntLiteral(this()), index())

infix fun Int.at(index: Int): StoreOperation<IntSort, IntSort> =
    StoreOperation(IntLiteral(this), IntLiteral(index))

infix fun Int.at(index: () -> Int): StoreOperation<IntSort, IntSort> =
    StoreOperation(IntLiteral(this), IntLiteral(index()))

infix fun (() -> Int).at(index: Int): StoreOperation<IntSort, IntSort> =
    StoreOperation(IntLiteral(this()), IntLiteral(index))

infix fun (() -> Int).at(index: () -> Int): StoreOperation<IntSort, IntSort> =
    StoreOperation(IntLiteral(this()), IntLiteral(index()))

fun main() {
  smt(QF_AX) {
    val expr = const(Bool)
    val index = const(Bool)
    val array = const(SMTArray(Bool, Bool))

    val expr1 = expr storeAt index then (expr at index) then (expr at index) into array
    val expr2 = listOf(expr, expr) storeAt listOf(index, index) into array
      val expr3 = IntLiteral(0) storeAt 0 then (1 at 1) then (2 at 2) into const(SMTArray(SMTInt, SMTInt))
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

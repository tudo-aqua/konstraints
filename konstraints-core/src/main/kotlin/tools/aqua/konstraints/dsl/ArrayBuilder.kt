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

// Represents a single store operation: value and index
data class StoreOperation<X : Sort, Y : Sort>(val value: Expression<X>, val index: Expression<Y>)

// A builder to chain multiple store operations
class StoreBuilder<X : Sort, Y : Sort>(private val operations: MutableList<StoreOperation<X, Y>> = mutableListOf()) {

    // Adds a new operation
    infix fun Expression<X>.at(index: Expression<Y>): StoreOperation<X, Y> = StoreOperation(this, index)

    // Allows chaining: add another StoreOperation and returns this builder
    infix fun StoreOperation<X, Y>.then(next: StoreOperation<X, Y>): StoreBuilder<X, Y> {
        operations.add(this)
        operations.add(next)
        return this@StoreBuilder
    }

    // Overload to chain more than two: StoreBuilder and StoreOperation
    infix fun StoreBuilder<X, Y>.then(next: StoreOperation<X, Y>): StoreBuilder<X, Y> {
        operations.add(next)
        return this
    }

    // Specify the target array
    infix fun StoreBuilder<X, Y>.into(array: Expression<ArraySort<X, Y>>) {
        //TODO map StoreOperations to ArrayStore (best do it iteratively or using deep recursive functions)
    }
}

// Accepts the first StoreOperation and returns StoreBuilder for chaining
fun<X : Sort, Y : Sort> store(first: StoreOperation<X, Y>): StoreBuilder<X, Y> {
    val builder = StoreBuilder<X, Y>()
    builder.apply {
        // Add the first operation initially
        builder.then(first)
    }
    return builder
}

fun main() {
    smt(QF_AX) {
        val expr = True
        val index = False
        val array = const(SMTArray(Bool, Bool))

        store(expr at index) into array
    }
}


// select index from array
// store value at index then value at index then... to array
// store values at indices to array

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
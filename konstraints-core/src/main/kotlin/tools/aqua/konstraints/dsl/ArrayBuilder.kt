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

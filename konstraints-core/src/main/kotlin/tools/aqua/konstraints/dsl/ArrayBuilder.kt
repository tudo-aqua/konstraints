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
import java.util.UUID

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

@JvmName("atIntSortIntSort")
infix fun Expression<IntSort>.at(index : Expression<IntSort>) = this to index

@JvmName("storeIntSortIntSort")
infix fun Expression<ArraySort<IntSort, IntSort>>.store(entry : Pair<Expression<IntSort>, Expression<IntSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenIntSortIntSort")
infix fun ArrayStore<IntSort, IntSort>.then(entry: Pair<Expression<IntSort>, Expression<IntSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atIntSortInt")
infix fun Expression<IntSort>.at(index : Int) = this to IntLiteral(index)

@JvmName("storeIntSortInt")
infix fun Expression<ArraySort<IntSort, IntSort>>.store(entry : Pair<Expression<IntSort>, Int>) = ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("thenIntSortInt")
infix fun ArrayStore<IntSort, IntSort>.then(entry: Pair<Expression<IntSort>, Int>) = ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("atIntIntSort")
infix fun Int.at(index : Expression<IntSort>) = IntLiteral(this) to index

@JvmName("storeIntIntSort")
infix fun Expression<ArraySort<IntSort, IntSort>>.store(entry : Pair<Int, Expression<IntSort>>) = ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("thenIntIntSort")
infix fun ArrayStore<IntSort, IntSort>.then(entry: Pair<Int, Expression<IntSort>>) = ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("atIntInt")
infix fun Int.at(index : Int) = IntLiteral(this) to IntLiteral(index)

@JvmName("storeIntInt")
infix fun Expression<ArraySort<IntSort, IntSort>>.store(entry : Pair<Int, Int>) = ArrayStore(this, IntLiteral(entry.second), IntLiteral(entry.first))

@JvmName("thenIntInt")
infix fun ArrayStore<IntSort, IntSort>.then(entry: Pair<Int, Int>) = ArrayStore(this, IntLiteral(entry.second), IntLiteral(entry.first))

@JvmName("atBoolSortIntSort")
infix fun Expression<BoolSort>.at(index : Expression<IntSort>) = this to index

@JvmName("storeBoolSortIntSort")
infix fun Expression<ArraySort<IntSort, BoolSort>>.store(entry : Pair<Expression<BoolSort>, Expression<IntSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBoolSortIntSort")
infix fun ArrayStore<IntSort, BoolSort>.then(entry: Pair<Expression<BoolSort>, Expression<IntSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBoolSortInt")
infix fun Expression<BoolSort>.at(index : Int) = this to IntLiteral(index)

@JvmName("storeBoolSortInt")
infix fun Expression<ArraySort<IntSort, BoolSort>>.store(entry : Pair<Expression<BoolSort>, Int>) = ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("thenBoolSortInt")
infix fun ArrayStore<IntSort, BoolSort>.then(entry: Pair<Expression<BoolSort>, Int>) = ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("atBooleanIntSort")
infix fun Boolean.at(index : Expression<IntSort>) = this.toSMTBool() to index

@JvmName("storeBooleanIntSort")
infix fun Expression<ArraySort<IntSort, BoolSort>>.store(entry : Pair<Boolean, Expression<IntSort>>) = ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("thenBooleanIntSort")
infix fun ArrayStore<IntSort, BoolSort>.then(entry: Pair<Boolean, Expression<IntSort>>) = ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("atBooleanInt")
infix fun Boolean.at(index : Int) = this.toSMTBool() to IntLiteral(index)

@JvmName("storeBooleanInt")
infix fun Expression<ArraySort<IntSort, BoolSort>>.store(entry : Pair<Boolean, Int>) = ArrayStore(this, IntLiteral(entry.second), entry.first.toSMTBool())

@JvmName("thenBooleanInt")
infix fun ArrayStore<IntSort, BoolSort>.then(entry: Pair<Boolean, Int>) = ArrayStore(this, IntLiteral(entry.second), entry.first.toSMTBool())

@JvmName("atStringSortIntSort")
infix fun Expression<StringSort>.at(index : Expression<IntSort>) = this to index

@JvmName("storeStringSortIntSort")
infix fun Expression<ArraySort<IntSort, StringSort>>.store(entry : Pair<Expression<StringSort>, Expression<IntSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenStringSortIntSort")
infix fun ArrayStore<IntSort, StringSort>.then(entry: Pair<Expression<StringSort>, Expression<IntSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atStringSortInt")
infix fun Expression<StringSort>.at(index : Int) = this to IntLiteral(index)

@JvmName("storeStringSortInt")
infix fun Expression<ArraySort<IntSort, StringSort>>.store(entry : Pair<Expression<StringSort>, Int>) = ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("thenStringSortInt")
infix fun ArrayStore<IntSort, StringSort>.then(entry: Pair<Expression<StringSort>, Int>) = ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("atStringIntSort")
infix fun String.at(index : Expression<IntSort>) = StringLiteral(this) to index

@JvmName("storeStringIntSort")
infix fun Expression<ArraySort<IntSort, StringSort>>.store(entry : Pair<String, Expression<IntSort>>) = ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("thenStringIntSort")
infix fun ArrayStore<IntSort, StringSort>.then(entry: Pair<String, Expression<IntSort>>) = ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("atStringInt")
infix fun String.at(index : Int) = StringLiteral(this) to IntLiteral(index)

@JvmName("storeStringInt")
infix fun Expression<ArraySort<IntSort, StringSort>>.store(entry : Pair<String, Int>) = ArrayStore(this, IntLiteral(entry.second), StringLiteral(entry.first))

@JvmName("thenStringInt")
infix fun ArrayStore<IntSort, StringSort>.then(entry: Pair<String, Int>) = ArrayStore(this, IntLiteral(entry.second), StringLiteral(entry.first))

@JvmName("atRealSortIntSort")
infix fun Expression<RealSort>.at(index : Expression<IntSort>) = this to index

@JvmName("storeRealSortIntSort")
infix fun Expression<ArraySort<IntSort, RealSort>>.store(entry : Pair<Expression<RealSort>, Expression<IntSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRealSortIntSort")
infix fun ArrayStore<IntSort, RealSort>.then(entry: Pair<Expression<RealSort>, Expression<IntSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRealSortInt")
infix fun Expression<RealSort>.at(index : Int) = this to IntLiteral(index)

@JvmName("storeRealSortInt")
infix fun Expression<ArraySort<IntSort, RealSort>>.store(entry : Pair<Expression<RealSort>, Int>) = ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("thenRealSortInt")
infix fun ArrayStore<IntSort, RealSort>.then(entry: Pair<Expression<RealSort>, Int>) = ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("atRegLanSortIntSort")
infix fun Expression<RegLanSort>.at(index : Expression<IntSort>) = this to index

@JvmName("storeRegLanSortIntSort")
infix fun Expression<ArraySort<IntSort, RegLanSort>>.store(entry : Pair<Expression<RegLanSort>, Expression<IntSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRegLanSortIntSort")
infix fun ArrayStore<IntSort, RegLanSort>.then(entry: Pair<Expression<RegLanSort>, Expression<IntSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRegLanSortInt")
infix fun Expression<RegLanSort>.at(index : Int) = this to IntLiteral(index)

@JvmName("storeRegLanSortInt")
infix fun Expression<ArraySort<IntSort, RegLanSort>>.store(entry : Pair<Expression<RegLanSort>, Int>) = ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("thenRegLanSortInt")
infix fun ArrayStore<IntSort, RegLanSort>.then(entry: Pair<Expression<RegLanSort>, Int>) = ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("atFPSortIntSort")
infix fun Expression<FPSort>.at(index : Expression<IntSort>) = this to index

@JvmName("storeFPSortIntSort")
infix fun Expression<ArraySort<IntSort, FPSort>>.store(entry : Pair<Expression<FPSort>, Expression<IntSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenFPSortIntSort")
infix fun ArrayStore<IntSort, FPSort>.then(entry: Pair<Expression<FPSort>, Expression<IntSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atFPSortInt")
infix fun Expression<FPSort>.at(index : Int) = this to IntLiteral(index)

@JvmName("storeFPSortInt")
infix fun Expression<ArraySort<IntSort, FPSort>>.store(entry : Pair<Expression<FPSort>, Int>) = ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("thenFPSortInt")
infix fun ArrayStore<IntSort, FPSort>.then(entry: Pair<Expression<FPSort>, Int>) = ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("atRoundingModeSortIntSort")
infix fun Expression<RoundingModeSort>.at(index : Expression<IntSort>) = this to index

@JvmName("storeRoundingModeSortIntSort")
infix fun Expression<ArraySort<IntSort, RoundingModeSort>>.store(entry : Pair<Expression<RoundingModeSort>, Expression<IntSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRoundingModeSortIntSort")
infix fun ArrayStore<IntSort, RoundingModeSort>.then(entry: Pair<Expression<RoundingModeSort>, Expression<IntSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRoundingModeSortInt")
infix fun Expression<RoundingModeSort>.at(index : Int) = this to IntLiteral(index)

@JvmName("storeRoundingModeSortInt")
infix fun Expression<ArraySort<IntSort, RoundingModeSort>>.store(entry : Pair<Expression<RoundingModeSort>, Int>) = ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("thenRoundingModeSortInt")
infix fun ArrayStore<IntSort, RoundingModeSort>.then(entry: Pair<Expression<RoundingModeSort>, Int>) = ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("atBVSortIntSort")
infix fun Expression<BVSort>.at(index : Expression<IntSort>) = this to index

@JvmName("storeBVSortIntSort")
infix fun Expression<ArraySort<IntSort, BVSort>>.store(entry : Pair<Expression<BVSort>, Expression<IntSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBVSortIntSort")
infix fun ArrayStore<IntSort, BVSort>.then(entry: Pair<Expression<BVSort>, Expression<IntSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBVSortInt")
infix fun Expression<BVSort>.at(index : Int) = this to IntLiteral(index)

@JvmName("storeBVSortInt")
infix fun Expression<ArraySort<IntSort, BVSort>>.store(entry : Pair<Expression<BVSort>, Int>) = ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("thenBVSortInt")
infix fun ArrayStore<IntSort, BVSort>.then(entry: Pair<Expression<BVSort>, Int>) = ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("atIntSortBoolSort")
infix fun Expression<IntSort>.at(index : Expression<BoolSort>) = this to index

@JvmName("storeIntSortBoolSort")
infix fun Expression<ArraySort<BoolSort, IntSort>>.store(entry : Pair<Expression<IntSort>, Expression<BoolSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenIntSortBoolSort")
infix fun ArrayStore<BoolSort, IntSort>.then(entry: Pair<Expression<IntSort>, Expression<BoolSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atIntSortBoolean")
infix fun Expression<IntSort>.at(index : Boolean) = this to index.toSMTBool()

@JvmName("storeIntSortBoolean")
infix fun Expression<ArraySort<BoolSort, IntSort>>.store(entry : Pair<Expression<IntSort>, Boolean>) = ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("thenIntSortBoolean")
infix fun ArrayStore<BoolSort, IntSort>.then(entry: Pair<Expression<IntSort>, Boolean>) = ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("atIntBoolSort")
infix fun Int.at(index : Expression<BoolSort>) = IntLiteral(this) to index

@JvmName("storeIntBoolSort")
infix fun Expression<ArraySort<BoolSort, IntSort>>.store(entry : Pair<Int, Expression<BoolSort>>) = ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("thenIntBoolSort")
infix fun ArrayStore<BoolSort, IntSort>.then(entry: Pair<Int, Expression<BoolSort>>) = ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("atIntBoolean")
infix fun Int.at(index : Boolean) = IntLiteral(this) to index.toSMTBool()

@JvmName("storeIntBoolean")
infix fun Expression<ArraySort<BoolSort, IntSort>>.store(entry : Pair<Int, Boolean>) = ArrayStore(this, entry.second.toSMTBool(), IntLiteral(entry.first))

@JvmName("thenIntBoolean")
infix fun ArrayStore<BoolSort, IntSort>.then(entry: Pair<Int, Boolean>) = ArrayStore(this, entry.second.toSMTBool(), IntLiteral(entry.first))

@JvmName("atBoolSortBoolSort")
infix fun Expression<BoolSort>.at(index : Expression<BoolSort>) = this to index

@JvmName("storeBoolSortBoolSort")
infix fun Expression<ArraySort<BoolSort, BoolSort>>.store(entry : Pair<Expression<BoolSort>, Expression<BoolSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBoolSortBoolSort")
infix fun ArrayStore<BoolSort, BoolSort>.then(entry: Pair<Expression<BoolSort>, Expression<BoolSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBoolSortBoolean")
infix fun Expression<BoolSort>.at(index : Boolean) = this to index.toSMTBool()

@JvmName("storeBoolSortBoolean")
infix fun Expression<ArraySort<BoolSort, BoolSort>>.store(entry : Pair<Expression<BoolSort>, Boolean>) = ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("thenBoolSortBoolean")
infix fun ArrayStore<BoolSort, BoolSort>.then(entry: Pair<Expression<BoolSort>, Boolean>) = ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("atBooleanBoolSort")
infix fun Boolean.at(index : Expression<BoolSort>) = this.toSMTBool() to index

@JvmName("storeBooleanBoolSort")
infix fun Expression<ArraySort<BoolSort, BoolSort>>.store(entry : Pair<Boolean, Expression<BoolSort>>) = ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("thenBooleanBoolSort")
infix fun ArrayStore<BoolSort, BoolSort>.then(entry: Pair<Boolean, Expression<BoolSort>>) = ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("atBooleanBoolean")
infix fun Boolean.at(index : Boolean) = this.toSMTBool() to index.toSMTBool()

@JvmName("storeBooleanBoolean")
infix fun Expression<ArraySort<BoolSort, BoolSort>>.store(entry : Pair<Boolean, Boolean>) = ArrayStore(this, entry.second.toSMTBool(), entry.first.toSMTBool())

@JvmName("thenBooleanBoolean")
infix fun ArrayStore<BoolSort, BoolSort>.then(entry: Pair<Boolean, Boolean>) = ArrayStore(this, entry.second.toSMTBool(), entry.first.toSMTBool())

@JvmName("atStringSortBoolSort")
infix fun Expression<StringSort>.at(index : Expression<BoolSort>) = this to index

@JvmName("storeStringSortBoolSort")
infix fun Expression<ArraySort<BoolSort, StringSort>>.store(entry : Pair<Expression<StringSort>, Expression<BoolSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenStringSortBoolSort")
infix fun ArrayStore<BoolSort, StringSort>.then(entry: Pair<Expression<StringSort>, Expression<BoolSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atStringSortBoolean")
infix fun Expression<StringSort>.at(index : Boolean) = this to index.toSMTBool()

@JvmName("storeStringSortBoolean")
infix fun Expression<ArraySort<BoolSort, StringSort>>.store(entry : Pair<Expression<StringSort>, Boolean>) = ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("thenStringSortBoolean")
infix fun ArrayStore<BoolSort, StringSort>.then(entry: Pair<Expression<StringSort>, Boolean>) = ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("atStringBoolSort")
infix fun String.at(index : Expression<BoolSort>) = StringLiteral(this) to index

@JvmName("storeStringBoolSort")
infix fun Expression<ArraySort<BoolSort, StringSort>>.store(entry : Pair<String, Expression<BoolSort>>) = ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("thenStringBoolSort")
infix fun ArrayStore<BoolSort, StringSort>.then(entry: Pair<String, Expression<BoolSort>>) = ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("atStringBoolean")
infix fun String.at(index : Boolean) = StringLiteral(this) to index.toSMTBool()

@JvmName("storeStringBoolean")
infix fun Expression<ArraySort<BoolSort, StringSort>>.store(entry : Pair<String, Boolean>) = ArrayStore(this, entry.second.toSMTBool(), StringLiteral(entry.first))

@JvmName("thenStringBoolean")
infix fun ArrayStore<BoolSort, StringSort>.then(entry: Pair<String, Boolean>) = ArrayStore(this, entry.second.toSMTBool(), StringLiteral(entry.first))

@JvmName("atRealSortBoolSort")
infix fun Expression<RealSort>.at(index : Expression<BoolSort>) = this to index

@JvmName("storeRealSortBoolSort")
infix fun Expression<ArraySort<BoolSort, RealSort>>.store(entry : Pair<Expression<RealSort>, Expression<BoolSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRealSortBoolSort")
infix fun ArrayStore<BoolSort, RealSort>.then(entry: Pair<Expression<RealSort>, Expression<BoolSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRealSortBoolean")
infix fun Expression<RealSort>.at(index : Boolean) = this to index.toSMTBool()

@JvmName("storeRealSortBoolean")
infix fun Expression<ArraySort<BoolSort, RealSort>>.store(entry : Pair<Expression<RealSort>, Boolean>) = ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("thenRealSortBoolean")
infix fun ArrayStore<BoolSort, RealSort>.then(entry: Pair<Expression<RealSort>, Boolean>) = ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("atRegLanSortBoolSort")
infix fun Expression<RegLanSort>.at(index : Expression<BoolSort>) = this to index

@JvmName("storeRegLanSortBoolSort")
infix fun Expression<ArraySort<BoolSort, RegLanSort>>.store(entry : Pair<Expression<RegLanSort>, Expression<BoolSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRegLanSortBoolSort")
infix fun ArrayStore<BoolSort, RegLanSort>.then(entry: Pair<Expression<RegLanSort>, Expression<BoolSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRegLanSortBoolean")
infix fun Expression<RegLanSort>.at(index : Boolean) = this to index.toSMTBool()

@JvmName("storeRegLanSortBoolean")
infix fun Expression<ArraySort<BoolSort, RegLanSort>>.store(entry : Pair<Expression<RegLanSort>, Boolean>) = ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("thenRegLanSortBoolean")
infix fun ArrayStore<BoolSort, RegLanSort>.then(entry: Pair<Expression<RegLanSort>, Boolean>) = ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("atFPSortBoolSort")
infix fun Expression<FPSort>.at(index : Expression<BoolSort>) = this to index

@JvmName("storeFPSortBoolSort")
infix fun Expression<ArraySort<BoolSort, FPSort>>.store(entry : Pair<Expression<FPSort>, Expression<BoolSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenFPSortBoolSort")
infix fun ArrayStore<BoolSort, FPSort>.then(entry: Pair<Expression<FPSort>, Expression<BoolSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atFPSortBoolean")
infix fun Expression<FPSort>.at(index : Boolean) = this to index.toSMTBool()

@JvmName("storeFPSortBoolean")
infix fun Expression<ArraySort<BoolSort, FPSort>>.store(entry : Pair<Expression<FPSort>, Boolean>) = ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("thenFPSortBoolean")
infix fun ArrayStore<BoolSort, FPSort>.then(entry: Pair<Expression<FPSort>, Boolean>) = ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("atRoundingModeSortBoolSort")
infix fun Expression<RoundingModeSort>.at(index : Expression<BoolSort>) = this to index

@JvmName("storeRoundingModeSortBoolSort")
infix fun Expression<ArraySort<BoolSort, RoundingModeSort>>.store(entry : Pair<Expression<RoundingModeSort>, Expression<BoolSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRoundingModeSortBoolSort")
infix fun ArrayStore<BoolSort, RoundingModeSort>.then(entry: Pair<Expression<RoundingModeSort>, Expression<BoolSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRoundingModeSortBoolean")
infix fun Expression<RoundingModeSort>.at(index : Boolean) = this to index.toSMTBool()

@JvmName("storeRoundingModeSortBoolean")
infix fun Expression<ArraySort<BoolSort, RoundingModeSort>>.store(entry : Pair<Expression<RoundingModeSort>, Boolean>) = ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("thenRoundingModeSortBoolean")
infix fun ArrayStore<BoolSort, RoundingModeSort>.then(entry: Pair<Expression<RoundingModeSort>, Boolean>) = ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("atBVSortBoolSort")
infix fun Expression<BVSort>.at(index : Expression<BoolSort>) = this to index

@JvmName("storeBVSortBoolSort")
infix fun Expression<ArraySort<BoolSort, BVSort>>.store(entry : Pair<Expression<BVSort>, Expression<BoolSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBVSortBoolSort")
infix fun ArrayStore<BoolSort, BVSort>.then(entry: Pair<Expression<BVSort>, Expression<BoolSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBVSortBoolean")
infix fun Expression<BVSort>.at(index : Boolean) = this to index.toSMTBool()

@JvmName("storeBVSortBoolean")
infix fun Expression<ArraySort<BoolSort, BVSort>>.store(entry : Pair<Expression<BVSort>, Boolean>) = ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("thenBVSortBoolean")
infix fun ArrayStore<BoolSort, BVSort>.then(entry: Pair<Expression<BVSort>, Boolean>) = ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("atIntSortStringSort")
infix fun Expression<IntSort>.at(index : Expression<StringSort>) = this to index

@JvmName("storeIntSortStringSort")
infix fun Expression<ArraySort<StringSort, IntSort>>.store(entry : Pair<Expression<IntSort>, Expression<StringSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenIntSortStringSort")
infix fun ArrayStore<StringSort, IntSort>.then(entry: Pair<Expression<IntSort>, Expression<StringSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atIntSortString")
infix fun Expression<IntSort>.at(index : String) = this to StringLiteral(index)

@JvmName("storeIntSortString")
infix fun Expression<ArraySort<StringSort, IntSort>>.store(entry : Pair<Expression<IntSort>, String>) = ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("thenIntSortString")
infix fun ArrayStore<StringSort, IntSort>.then(entry: Pair<Expression<IntSort>, String>) = ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("atIntStringSort")
infix fun Int.at(index : Expression<StringSort>) = IntLiteral(this) to index

@JvmName("storeIntStringSort")
infix fun Expression<ArraySort<StringSort, IntSort>>.store(entry : Pair<Int, Expression<StringSort>>) = ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("thenIntStringSort")
infix fun ArrayStore<StringSort, IntSort>.then(entry: Pair<Int, Expression<StringSort>>) = ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("atIntString")
infix fun Int.at(index : String) = IntLiteral(this) to StringLiteral(index)

@JvmName("storeIntString")
infix fun Expression<ArraySort<StringSort, IntSort>>.store(entry : Pair<Int, String>) = ArrayStore(this, StringLiteral(entry.second), IntLiteral(entry.first))

@JvmName("thenIntString")
infix fun ArrayStore<StringSort, IntSort>.then(entry: Pair<Int, String>) = ArrayStore(this, StringLiteral(entry.second), IntLiteral(entry.first))

@JvmName("atBoolSortStringSort")
infix fun Expression<BoolSort>.at(index : Expression<StringSort>) = this to index

@JvmName("storeBoolSortStringSort")
infix fun Expression<ArraySort<StringSort, BoolSort>>.store(entry : Pair<Expression<BoolSort>, Expression<StringSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBoolSortStringSort")
infix fun ArrayStore<StringSort, BoolSort>.then(entry: Pair<Expression<BoolSort>, Expression<StringSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBoolSortString")
infix fun Expression<BoolSort>.at(index : String) = this to StringLiteral(index)

@JvmName("storeBoolSortString")
infix fun Expression<ArraySort<StringSort, BoolSort>>.store(entry : Pair<Expression<BoolSort>, String>) = ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("thenBoolSortString")
infix fun ArrayStore<StringSort, BoolSort>.then(entry: Pair<Expression<BoolSort>, String>) = ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("atBooleanStringSort")
infix fun Boolean.at(index : Expression<StringSort>) = this.toSMTBool() to index

@JvmName("storeBooleanStringSort")
infix fun Expression<ArraySort<StringSort, BoolSort>>.store(entry : Pair<Boolean, Expression<StringSort>>) = ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("thenBooleanStringSort")
infix fun ArrayStore<StringSort, BoolSort>.then(entry: Pair<Boolean, Expression<StringSort>>) = ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("atBooleanString")
infix fun Boolean.at(index : String) = this.toSMTBool() to StringLiteral(index)

@JvmName("storeBooleanString")
infix fun Expression<ArraySort<StringSort, BoolSort>>.store(entry : Pair<Boolean, String>) = ArrayStore(this, StringLiteral(entry.second), entry.first.toSMTBool())

@JvmName("thenBooleanString")
infix fun ArrayStore<StringSort, BoolSort>.then(entry: Pair<Boolean, String>) = ArrayStore(this, StringLiteral(entry.second), entry.first.toSMTBool())

@JvmName("atStringSortStringSort")
infix fun Expression<StringSort>.at(index : Expression<StringSort>) = this to index

@JvmName("storeStringSortStringSort")
infix fun Expression<ArraySort<StringSort, StringSort>>.store(entry : Pair<Expression<StringSort>, Expression<StringSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenStringSortStringSort")
infix fun ArrayStore<StringSort, StringSort>.then(entry: Pair<Expression<StringSort>, Expression<StringSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atStringSortString")
infix fun Expression<StringSort>.at(index : String) = this to StringLiteral(index)

@JvmName("storeStringSortString")
infix fun Expression<ArraySort<StringSort, StringSort>>.store(entry : Pair<Expression<StringSort>, String>) = ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("thenStringSortString")
infix fun ArrayStore<StringSort, StringSort>.then(entry: Pair<Expression<StringSort>, String>) = ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("atStringStringSort")
infix fun String.at(index : Expression<StringSort>) = StringLiteral(this) to index

@JvmName("storeStringStringSort")
infix fun Expression<ArraySort<StringSort, StringSort>>.store(entry : Pair<String, Expression<StringSort>>) = ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("thenStringStringSort")
infix fun ArrayStore<StringSort, StringSort>.then(entry: Pair<String, Expression<StringSort>>) = ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("atStringString")
infix fun String.at(index : String) = StringLiteral(this) to StringLiteral(index)

@JvmName("storeStringString")
infix fun Expression<ArraySort<StringSort, StringSort>>.store(entry : Pair<String, String>) = ArrayStore(this, StringLiteral(entry.second), StringLiteral(entry.first))

@JvmName("thenStringString")
infix fun ArrayStore<StringSort, StringSort>.then(entry: Pair<String, String>) = ArrayStore(this, StringLiteral(entry.second), StringLiteral(entry.first))

@JvmName("atRealSortStringSort")
infix fun Expression<RealSort>.at(index : Expression<StringSort>) = this to index

@JvmName("storeRealSortStringSort")
infix fun Expression<ArraySort<StringSort, RealSort>>.store(entry : Pair<Expression<RealSort>, Expression<StringSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRealSortStringSort")
infix fun ArrayStore<StringSort, RealSort>.then(entry: Pair<Expression<RealSort>, Expression<StringSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRealSortString")
infix fun Expression<RealSort>.at(index : String) = this to StringLiteral(index)

@JvmName("storeRealSortString")
infix fun Expression<ArraySort<StringSort, RealSort>>.store(entry : Pair<Expression<RealSort>, String>) = ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("thenRealSortString")
infix fun ArrayStore<StringSort, RealSort>.then(entry: Pair<Expression<RealSort>, String>) = ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("atRegLanSortStringSort")
infix fun Expression<RegLanSort>.at(index : Expression<StringSort>) = this to index

@JvmName("storeRegLanSortStringSort")
infix fun Expression<ArraySort<StringSort, RegLanSort>>.store(entry : Pair<Expression<RegLanSort>, Expression<StringSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRegLanSortStringSort")
infix fun ArrayStore<StringSort, RegLanSort>.then(entry: Pair<Expression<RegLanSort>, Expression<StringSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRegLanSortString")
infix fun Expression<RegLanSort>.at(index : String) = this to StringLiteral(index)

@JvmName("storeRegLanSortString")
infix fun Expression<ArraySort<StringSort, RegLanSort>>.store(entry : Pair<Expression<RegLanSort>, String>) = ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("thenRegLanSortString")
infix fun ArrayStore<StringSort, RegLanSort>.then(entry: Pair<Expression<RegLanSort>, String>) = ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("atFPSortStringSort")
infix fun Expression<FPSort>.at(index : Expression<StringSort>) = this to index

@JvmName("storeFPSortStringSort")
infix fun Expression<ArraySort<StringSort, FPSort>>.store(entry : Pair<Expression<FPSort>, Expression<StringSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenFPSortStringSort")
infix fun ArrayStore<StringSort, FPSort>.then(entry: Pair<Expression<FPSort>, Expression<StringSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atFPSortString")
infix fun Expression<FPSort>.at(index : String) = this to StringLiteral(index)

@JvmName("storeFPSortString")
infix fun Expression<ArraySort<StringSort, FPSort>>.store(entry : Pair<Expression<FPSort>, String>) = ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("thenFPSortString")
infix fun ArrayStore<StringSort, FPSort>.then(entry: Pair<Expression<FPSort>, String>) = ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("atRoundingModeSortStringSort")
infix fun Expression<RoundingModeSort>.at(index : Expression<StringSort>) = this to index

@JvmName("storeRoundingModeSortStringSort")
infix fun Expression<ArraySort<StringSort, RoundingModeSort>>.store(entry : Pair<Expression<RoundingModeSort>, Expression<StringSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRoundingModeSortStringSort")
infix fun ArrayStore<StringSort, RoundingModeSort>.then(entry: Pair<Expression<RoundingModeSort>, Expression<StringSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRoundingModeSortString")
infix fun Expression<RoundingModeSort>.at(index : String) = this to StringLiteral(index)

@JvmName("storeRoundingModeSortString")
infix fun Expression<ArraySort<StringSort, RoundingModeSort>>.store(entry : Pair<Expression<RoundingModeSort>, String>) = ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("thenRoundingModeSortString")
infix fun ArrayStore<StringSort, RoundingModeSort>.then(entry: Pair<Expression<RoundingModeSort>, String>) = ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("atBVSortStringSort")
infix fun Expression<BVSort>.at(index : Expression<StringSort>) = this to index

@JvmName("storeBVSortStringSort")
infix fun Expression<ArraySort<StringSort, BVSort>>.store(entry : Pair<Expression<BVSort>, Expression<StringSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBVSortStringSort")
infix fun ArrayStore<StringSort, BVSort>.then(entry: Pair<Expression<BVSort>, Expression<StringSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBVSortString")
infix fun Expression<BVSort>.at(index : String) = this to StringLiteral(index)

@JvmName("storeBVSortString")
infix fun Expression<ArraySort<StringSort, BVSort>>.store(entry : Pair<Expression<BVSort>, String>) = ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("thenBVSortString")
infix fun ArrayStore<StringSort, BVSort>.then(entry: Pair<Expression<BVSort>, String>) = ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("atIntSortRealSort")
infix fun Expression<IntSort>.at(index : Expression<RealSort>) = this to index

@JvmName("storeIntSortRealSort")
infix fun Expression<ArraySort<RealSort, IntSort>>.store(entry : Pair<Expression<IntSort>, Expression<RealSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenIntSortRealSort")
infix fun ArrayStore<RealSort, IntSort>.then(entry: Pair<Expression<IntSort>, Expression<RealSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atIntRealSort")
infix fun Int.at(index : Expression<RealSort>) = IntLiteral(this) to index

@JvmName("storeIntRealSort")
infix fun Expression<ArraySort<RealSort, IntSort>>.store(entry : Pair<Int, Expression<RealSort>>) = ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("thenIntRealSort")
infix fun ArrayStore<RealSort, IntSort>.then(entry: Pair<Int, Expression<RealSort>>) = ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("atBoolSortRealSort")
infix fun Expression<BoolSort>.at(index : Expression<RealSort>) = this to index

@JvmName("storeBoolSortRealSort")
infix fun Expression<ArraySort<RealSort, BoolSort>>.store(entry : Pair<Expression<BoolSort>, Expression<RealSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBoolSortRealSort")
infix fun ArrayStore<RealSort, BoolSort>.then(entry: Pair<Expression<BoolSort>, Expression<RealSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBooleanRealSort")
infix fun Boolean.at(index : Expression<RealSort>) = this.toSMTBool() to index

@JvmName("storeBooleanRealSort")
infix fun Expression<ArraySort<RealSort, BoolSort>>.store(entry : Pair<Boolean, Expression<RealSort>>) = ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("thenBooleanRealSort")
infix fun ArrayStore<RealSort, BoolSort>.then(entry: Pair<Boolean, Expression<RealSort>>) = ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("atStringSortRealSort")
infix fun Expression<StringSort>.at(index : Expression<RealSort>) = this to index

@JvmName("storeStringSortRealSort")
infix fun Expression<ArraySort<RealSort, StringSort>>.store(entry : Pair<Expression<StringSort>, Expression<RealSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenStringSortRealSort")
infix fun ArrayStore<RealSort, StringSort>.then(entry: Pair<Expression<StringSort>, Expression<RealSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atStringRealSort")
infix fun String.at(index : Expression<RealSort>) = StringLiteral(this) to index

@JvmName("storeStringRealSort")
infix fun Expression<ArraySort<RealSort, StringSort>>.store(entry : Pair<String, Expression<RealSort>>) = ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("thenStringRealSort")
infix fun ArrayStore<RealSort, StringSort>.then(entry: Pair<String, Expression<RealSort>>) = ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("atRealSortRealSort")
infix fun Expression<RealSort>.at(index : Expression<RealSort>) = this to index

@JvmName("storeRealSortRealSort")
infix fun Expression<ArraySort<RealSort, RealSort>>.store(entry : Pair<Expression<RealSort>, Expression<RealSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRealSortRealSort")
infix fun ArrayStore<RealSort, RealSort>.then(entry: Pair<Expression<RealSort>, Expression<RealSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRegLanSortRealSort")
infix fun Expression<RegLanSort>.at(index : Expression<RealSort>) = this to index

@JvmName("storeRegLanSortRealSort")
infix fun Expression<ArraySort<RealSort, RegLanSort>>.store(entry : Pair<Expression<RegLanSort>, Expression<RealSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRegLanSortRealSort")
infix fun ArrayStore<RealSort, RegLanSort>.then(entry: Pair<Expression<RegLanSort>, Expression<RealSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atFPSortRealSort")
infix fun Expression<FPSort>.at(index : Expression<RealSort>) = this to index

@JvmName("storeFPSortRealSort")
infix fun Expression<ArraySort<RealSort, FPSort>>.store(entry : Pair<Expression<FPSort>, Expression<RealSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenFPSortRealSort")
infix fun ArrayStore<RealSort, FPSort>.then(entry: Pair<Expression<FPSort>, Expression<RealSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRoundingModeSortRealSort")
infix fun Expression<RoundingModeSort>.at(index : Expression<RealSort>) = this to index

@JvmName("storeRoundingModeSortRealSort")
infix fun Expression<ArraySort<RealSort, RoundingModeSort>>.store(entry : Pair<Expression<RoundingModeSort>, Expression<RealSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRoundingModeSortRealSort")
infix fun ArrayStore<RealSort, RoundingModeSort>.then(entry: Pair<Expression<RoundingModeSort>, Expression<RealSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBVSortRealSort")
infix fun Expression<BVSort>.at(index : Expression<RealSort>) = this to index

@JvmName("storeBVSortRealSort")
infix fun Expression<ArraySort<RealSort, BVSort>>.store(entry : Pair<Expression<BVSort>, Expression<RealSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBVSortRealSort")
infix fun ArrayStore<RealSort, BVSort>.then(entry: Pair<Expression<BVSort>, Expression<RealSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atIntSortRegLanSort")
infix fun Expression<IntSort>.at(index : Expression<RegLanSort>) = this to index

@JvmName("storeIntSortRegLanSort")
infix fun Expression<ArraySort<RegLanSort, IntSort>>.store(entry : Pair<Expression<IntSort>, Expression<RegLanSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenIntSortRegLanSort")
infix fun ArrayStore<RegLanSort, IntSort>.then(entry: Pair<Expression<IntSort>, Expression<RegLanSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atIntRegLanSort")
infix fun Int.at(index : Expression<RegLanSort>) = IntLiteral(this) to index

@JvmName("storeIntRegLanSort")
infix fun Expression<ArraySort<RegLanSort, IntSort>>.store(entry : Pair<Int, Expression<RegLanSort>>) = ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("thenIntRegLanSort")
infix fun ArrayStore<RegLanSort, IntSort>.then(entry: Pair<Int, Expression<RegLanSort>>) = ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("atBoolSortRegLanSort")
infix fun Expression<BoolSort>.at(index : Expression<RegLanSort>) = this to index

@JvmName("storeBoolSortRegLanSort")
infix fun Expression<ArraySort<RegLanSort, BoolSort>>.store(entry : Pair<Expression<BoolSort>, Expression<RegLanSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBoolSortRegLanSort")
infix fun ArrayStore<RegLanSort, BoolSort>.then(entry: Pair<Expression<BoolSort>, Expression<RegLanSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBooleanRegLanSort")
infix fun Boolean.at(index : Expression<RegLanSort>) = this.toSMTBool() to index

@JvmName("storeBooleanRegLanSort")
infix fun Expression<ArraySort<RegLanSort, BoolSort>>.store(entry : Pair<Boolean, Expression<RegLanSort>>) = ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("thenBooleanRegLanSort")
infix fun ArrayStore<RegLanSort, BoolSort>.then(entry: Pair<Boolean, Expression<RegLanSort>>) = ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("atStringSortRegLanSort")
infix fun Expression<StringSort>.at(index : Expression<RegLanSort>) = this to index

@JvmName("storeStringSortRegLanSort")
infix fun Expression<ArraySort<RegLanSort, StringSort>>.store(entry : Pair<Expression<StringSort>, Expression<RegLanSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenStringSortRegLanSort")
infix fun ArrayStore<RegLanSort, StringSort>.then(entry: Pair<Expression<StringSort>, Expression<RegLanSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atStringRegLanSort")
infix fun String.at(index : Expression<RegLanSort>) = StringLiteral(this) to index

@JvmName("storeStringRegLanSort")
infix fun Expression<ArraySort<RegLanSort, StringSort>>.store(entry : Pair<String, Expression<RegLanSort>>) = ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("thenStringRegLanSort")
infix fun ArrayStore<RegLanSort, StringSort>.then(entry: Pair<String, Expression<RegLanSort>>) = ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("atRealSortRegLanSort")
infix fun Expression<RealSort>.at(index : Expression<RegLanSort>) = this to index

@JvmName("storeRealSortRegLanSort")
infix fun Expression<ArraySort<RegLanSort, RealSort>>.store(entry : Pair<Expression<RealSort>, Expression<RegLanSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRealSortRegLanSort")
infix fun ArrayStore<RegLanSort, RealSort>.then(entry: Pair<Expression<RealSort>, Expression<RegLanSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRegLanSortRegLanSort")
infix fun Expression<RegLanSort>.at(index : Expression<RegLanSort>) = this to index

@JvmName("storeRegLanSortRegLanSort")
infix fun Expression<ArraySort<RegLanSort, RegLanSort>>.store(entry : Pair<Expression<RegLanSort>, Expression<RegLanSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRegLanSortRegLanSort")
infix fun ArrayStore<RegLanSort, RegLanSort>.then(entry: Pair<Expression<RegLanSort>, Expression<RegLanSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atFPSortRegLanSort")
infix fun Expression<FPSort>.at(index : Expression<RegLanSort>) = this to index

@JvmName("storeFPSortRegLanSort")
infix fun Expression<ArraySort<RegLanSort, FPSort>>.store(entry : Pair<Expression<FPSort>, Expression<RegLanSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenFPSortRegLanSort")
infix fun ArrayStore<RegLanSort, FPSort>.then(entry: Pair<Expression<FPSort>, Expression<RegLanSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRoundingModeSortRegLanSort")
infix fun Expression<RoundingModeSort>.at(index : Expression<RegLanSort>) = this to index

@JvmName("storeRoundingModeSortRegLanSort")
infix fun Expression<ArraySort<RegLanSort, RoundingModeSort>>.store(entry : Pair<Expression<RoundingModeSort>, Expression<RegLanSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRoundingModeSortRegLanSort")
infix fun ArrayStore<RegLanSort, RoundingModeSort>.then(entry: Pair<Expression<RoundingModeSort>, Expression<RegLanSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBVSortRegLanSort")
infix fun Expression<BVSort>.at(index : Expression<RegLanSort>) = this to index

@JvmName("storeBVSortRegLanSort")
infix fun Expression<ArraySort<RegLanSort, BVSort>>.store(entry : Pair<Expression<BVSort>, Expression<RegLanSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBVSortRegLanSort")
infix fun ArrayStore<RegLanSort, BVSort>.then(entry: Pair<Expression<BVSort>, Expression<RegLanSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atIntSortFPSort")
infix fun Expression<IntSort>.at(index : Expression<FPSort>) = this to index

@JvmName("storeIntSortFPSort")
infix fun Expression<ArraySort<FPSort, IntSort>>.store(entry : Pair<Expression<IntSort>, Expression<FPSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenIntSortFPSort")
infix fun ArrayStore<FPSort, IntSort>.then(entry: Pair<Expression<IntSort>, Expression<FPSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atIntFPSort")
infix fun Int.at(index : Expression<FPSort>) = IntLiteral(this) to index

@JvmName("storeIntFPSort")
infix fun Expression<ArraySort<FPSort, IntSort>>.store(entry : Pair<Int, Expression<FPSort>>) = ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("thenIntFPSort")
infix fun ArrayStore<FPSort, IntSort>.then(entry: Pair<Int, Expression<FPSort>>) = ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("atBoolSortFPSort")
infix fun Expression<BoolSort>.at(index : Expression<FPSort>) = this to index

@JvmName("storeBoolSortFPSort")
infix fun Expression<ArraySort<FPSort, BoolSort>>.store(entry : Pair<Expression<BoolSort>, Expression<FPSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBoolSortFPSort")
infix fun ArrayStore<FPSort, BoolSort>.then(entry: Pair<Expression<BoolSort>, Expression<FPSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBooleanFPSort")
infix fun Boolean.at(index : Expression<FPSort>) = this.toSMTBool() to index

@JvmName("storeBooleanFPSort")
infix fun Expression<ArraySort<FPSort, BoolSort>>.store(entry : Pair<Boolean, Expression<FPSort>>) = ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("thenBooleanFPSort")
infix fun ArrayStore<FPSort, BoolSort>.then(entry: Pair<Boolean, Expression<FPSort>>) = ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("atStringSortFPSort")
infix fun Expression<StringSort>.at(index : Expression<FPSort>) = this to index

@JvmName("storeStringSortFPSort")
infix fun Expression<ArraySort<FPSort, StringSort>>.store(entry : Pair<Expression<StringSort>, Expression<FPSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenStringSortFPSort")
infix fun ArrayStore<FPSort, StringSort>.then(entry: Pair<Expression<StringSort>, Expression<FPSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atStringFPSort")
infix fun String.at(index : Expression<FPSort>) = StringLiteral(this) to index

@JvmName("storeStringFPSort")
infix fun Expression<ArraySort<FPSort, StringSort>>.store(entry : Pair<String, Expression<FPSort>>) = ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("thenStringFPSort")
infix fun ArrayStore<FPSort, StringSort>.then(entry: Pair<String, Expression<FPSort>>) = ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("atRealSortFPSort")
infix fun Expression<RealSort>.at(index : Expression<FPSort>) = this to index

@JvmName("storeRealSortFPSort")
infix fun Expression<ArraySort<FPSort, RealSort>>.store(entry : Pair<Expression<RealSort>, Expression<FPSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRealSortFPSort")
infix fun ArrayStore<FPSort, RealSort>.then(entry: Pair<Expression<RealSort>, Expression<FPSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRegLanSortFPSort")
infix fun Expression<RegLanSort>.at(index : Expression<FPSort>) = this to index

@JvmName("storeRegLanSortFPSort")
infix fun Expression<ArraySort<FPSort, RegLanSort>>.store(entry : Pair<Expression<RegLanSort>, Expression<FPSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRegLanSortFPSort")
infix fun ArrayStore<FPSort, RegLanSort>.then(entry: Pair<Expression<RegLanSort>, Expression<FPSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atFPSortFPSort")
infix fun Expression<FPSort>.at(index : Expression<FPSort>) = this to index

@JvmName("storeFPSortFPSort")
infix fun Expression<ArraySort<FPSort, FPSort>>.store(entry : Pair<Expression<FPSort>, Expression<FPSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenFPSortFPSort")
infix fun ArrayStore<FPSort, FPSort>.then(entry: Pair<Expression<FPSort>, Expression<FPSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRoundingModeSortFPSort")
infix fun Expression<RoundingModeSort>.at(index : Expression<FPSort>) = this to index

@JvmName("storeRoundingModeSortFPSort")
infix fun Expression<ArraySort<FPSort, RoundingModeSort>>.store(entry : Pair<Expression<RoundingModeSort>, Expression<FPSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRoundingModeSortFPSort")
infix fun ArrayStore<FPSort, RoundingModeSort>.then(entry: Pair<Expression<RoundingModeSort>, Expression<FPSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBVSortFPSort")
infix fun Expression<BVSort>.at(index : Expression<FPSort>) = this to index

@JvmName("storeBVSortFPSort")
infix fun Expression<ArraySort<FPSort, BVSort>>.store(entry : Pair<Expression<BVSort>, Expression<FPSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBVSortFPSort")
infix fun ArrayStore<FPSort, BVSort>.then(entry: Pair<Expression<BVSort>, Expression<FPSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atIntSortRoundingModeSort")
infix fun Expression<IntSort>.at(index : Expression<RoundingModeSort>) = this to index

@JvmName("storeIntSortRoundingModeSort")
infix fun Expression<ArraySort<RoundingModeSort, IntSort>>.store(entry : Pair<Expression<IntSort>, Expression<RoundingModeSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenIntSortRoundingModeSort")
infix fun ArrayStore<RoundingModeSort, IntSort>.then(entry: Pair<Expression<IntSort>, Expression<RoundingModeSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atIntRoundingModeSort")
infix fun Int.at(index : Expression<RoundingModeSort>) = IntLiteral(this) to index

@JvmName("storeIntRoundingModeSort")
infix fun Expression<ArraySort<RoundingModeSort, IntSort>>.store(entry : Pair<Int, Expression<RoundingModeSort>>) = ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("thenIntRoundingModeSort")
infix fun ArrayStore<RoundingModeSort, IntSort>.then(entry: Pair<Int, Expression<RoundingModeSort>>) = ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("atBoolSortRoundingModeSort")
infix fun Expression<BoolSort>.at(index : Expression<RoundingModeSort>) = this to index

@JvmName("storeBoolSortRoundingModeSort")
infix fun Expression<ArraySort<RoundingModeSort, BoolSort>>.store(entry : Pair<Expression<BoolSort>, Expression<RoundingModeSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBoolSortRoundingModeSort")
infix fun ArrayStore<RoundingModeSort, BoolSort>.then(entry: Pair<Expression<BoolSort>, Expression<RoundingModeSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBooleanRoundingModeSort")
infix fun Boolean.at(index : Expression<RoundingModeSort>) = this.toSMTBool() to index

@JvmName("storeBooleanRoundingModeSort")
infix fun Expression<ArraySort<RoundingModeSort, BoolSort>>.store(entry : Pair<Boolean, Expression<RoundingModeSort>>) = ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("thenBooleanRoundingModeSort")
infix fun ArrayStore<RoundingModeSort, BoolSort>.then(entry: Pair<Boolean, Expression<RoundingModeSort>>) = ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("atStringSortRoundingModeSort")
infix fun Expression<StringSort>.at(index : Expression<RoundingModeSort>) = this to index

@JvmName("storeStringSortRoundingModeSort")
infix fun Expression<ArraySort<RoundingModeSort, StringSort>>.store(entry : Pair<Expression<StringSort>, Expression<RoundingModeSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenStringSortRoundingModeSort")
infix fun ArrayStore<RoundingModeSort, StringSort>.then(entry: Pair<Expression<StringSort>, Expression<RoundingModeSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atStringRoundingModeSort")
infix fun String.at(index : Expression<RoundingModeSort>) = StringLiteral(this) to index

@JvmName("storeStringRoundingModeSort")
infix fun Expression<ArraySort<RoundingModeSort, StringSort>>.store(entry : Pair<String, Expression<RoundingModeSort>>) = ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("thenStringRoundingModeSort")
infix fun ArrayStore<RoundingModeSort, StringSort>.then(entry: Pair<String, Expression<RoundingModeSort>>) = ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("atRealSortRoundingModeSort")
infix fun Expression<RealSort>.at(index : Expression<RoundingModeSort>) = this to index

@JvmName("storeRealSortRoundingModeSort")
infix fun Expression<ArraySort<RoundingModeSort, RealSort>>.store(entry : Pair<Expression<RealSort>, Expression<RoundingModeSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRealSortRoundingModeSort")
infix fun ArrayStore<RoundingModeSort, RealSort>.then(entry: Pair<Expression<RealSort>, Expression<RoundingModeSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRegLanSortRoundingModeSort")
infix fun Expression<RegLanSort>.at(index : Expression<RoundingModeSort>) = this to index

@JvmName("storeRegLanSortRoundingModeSort")
infix fun Expression<ArraySort<RoundingModeSort, RegLanSort>>.store(entry : Pair<Expression<RegLanSort>, Expression<RoundingModeSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRegLanSortRoundingModeSort")
infix fun ArrayStore<RoundingModeSort, RegLanSort>.then(entry: Pair<Expression<RegLanSort>, Expression<RoundingModeSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atFPSortRoundingModeSort")
infix fun Expression<FPSort>.at(index : Expression<RoundingModeSort>) = this to index

@JvmName("storeFPSortRoundingModeSort")
infix fun Expression<ArraySort<RoundingModeSort, FPSort>>.store(entry : Pair<Expression<FPSort>, Expression<RoundingModeSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenFPSortRoundingModeSort")
infix fun ArrayStore<RoundingModeSort, FPSort>.then(entry: Pair<Expression<FPSort>, Expression<RoundingModeSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRoundingModeSortRoundingModeSort")
infix fun Expression<RoundingModeSort>.at(index : Expression<RoundingModeSort>) = this to index

@JvmName("storeRoundingModeSortRoundingModeSort")
infix fun Expression<ArraySort<RoundingModeSort, RoundingModeSort>>.store(entry : Pair<Expression<RoundingModeSort>, Expression<RoundingModeSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRoundingModeSortRoundingModeSort")
infix fun ArrayStore<RoundingModeSort, RoundingModeSort>.then(entry: Pair<Expression<RoundingModeSort>, Expression<RoundingModeSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBVSortRoundingModeSort")
infix fun Expression<BVSort>.at(index : Expression<RoundingModeSort>) = this to index

@JvmName("storeBVSortRoundingModeSort")
infix fun Expression<ArraySort<RoundingModeSort, BVSort>>.store(entry : Pair<Expression<BVSort>, Expression<RoundingModeSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBVSortRoundingModeSort")
infix fun ArrayStore<RoundingModeSort, BVSort>.then(entry: Pair<Expression<BVSort>, Expression<RoundingModeSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atIntSortBVSort")
infix fun Expression<IntSort>.at(index : Expression<BVSort>) = this to index

@JvmName("storeIntSortBVSort")
infix fun Expression<ArraySort<BVSort, IntSort>>.store(entry : Pair<Expression<IntSort>, Expression<BVSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenIntSortBVSort")
infix fun ArrayStore<BVSort, IntSort>.then(entry: Pair<Expression<IntSort>, Expression<BVSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atIntBVSort")
infix fun Int.at(index : Expression<BVSort>) = IntLiteral(this) to index

@JvmName("storeIntBVSort")
infix fun Expression<ArraySort<BVSort, IntSort>>.store(entry : Pair<Int, Expression<BVSort>>) = ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("thenIntBVSort")
infix fun ArrayStore<BVSort, IntSort>.then(entry: Pair<Int, Expression<BVSort>>) = ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("atBoolSortBVSort")
infix fun Expression<BoolSort>.at(index : Expression<BVSort>) = this to index

@JvmName("storeBoolSortBVSort")
infix fun Expression<ArraySort<BVSort, BoolSort>>.store(entry : Pair<Expression<BoolSort>, Expression<BVSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBoolSortBVSort")
infix fun ArrayStore<BVSort, BoolSort>.then(entry: Pair<Expression<BoolSort>, Expression<BVSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBooleanBVSort")
infix fun Boolean.at(index : Expression<BVSort>) = this.toSMTBool() to index

@JvmName("storeBooleanBVSort")
infix fun Expression<ArraySort<BVSort, BoolSort>>.store(entry : Pair<Boolean, Expression<BVSort>>) = ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("thenBooleanBVSort")
infix fun ArrayStore<BVSort, BoolSort>.then(entry: Pair<Boolean, Expression<BVSort>>) = ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("atStringSortBVSort")
infix fun Expression<StringSort>.at(index : Expression<BVSort>) = this to index

@JvmName("storeStringSortBVSort")
infix fun Expression<ArraySort<BVSort, StringSort>>.store(entry : Pair<Expression<StringSort>, Expression<BVSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenStringSortBVSort")
infix fun ArrayStore<BVSort, StringSort>.then(entry: Pair<Expression<StringSort>, Expression<BVSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atStringBVSort")
infix fun String.at(index : Expression<BVSort>) = StringLiteral(this) to index

@JvmName("storeStringBVSort")
infix fun Expression<ArraySort<BVSort, StringSort>>.store(entry : Pair<String, Expression<BVSort>>) = ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("thenStringBVSort")
infix fun ArrayStore<BVSort, StringSort>.then(entry: Pair<String, Expression<BVSort>>) = ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("atRealSortBVSort")
infix fun Expression<RealSort>.at(index : Expression<BVSort>) = this to index

@JvmName("storeRealSortBVSort")
infix fun Expression<ArraySort<BVSort, RealSort>>.store(entry : Pair<Expression<RealSort>, Expression<BVSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRealSortBVSort")
infix fun ArrayStore<BVSort, RealSort>.then(entry: Pair<Expression<RealSort>, Expression<BVSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRegLanSortBVSort")
infix fun Expression<RegLanSort>.at(index : Expression<BVSort>) = this to index

@JvmName("storeRegLanSortBVSort")
infix fun Expression<ArraySort<BVSort, RegLanSort>>.store(entry : Pair<Expression<RegLanSort>, Expression<BVSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRegLanSortBVSort")
infix fun ArrayStore<BVSort, RegLanSort>.then(entry: Pair<Expression<RegLanSort>, Expression<BVSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atFPSortBVSort")
infix fun Expression<FPSort>.at(index : Expression<BVSort>) = this to index

@JvmName("storeFPSortBVSort")
infix fun Expression<ArraySort<BVSort, FPSort>>.store(entry : Pair<Expression<FPSort>, Expression<BVSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenFPSortBVSort")
infix fun ArrayStore<BVSort, FPSort>.then(entry: Pair<Expression<FPSort>, Expression<BVSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRoundingModeSortBVSort")
infix fun Expression<RoundingModeSort>.at(index : Expression<BVSort>) = this to index

@JvmName("storeRoundingModeSortBVSort")
infix fun Expression<ArraySort<BVSort, RoundingModeSort>>.store(entry : Pair<Expression<RoundingModeSort>, Expression<BVSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRoundingModeSortBVSort")
infix fun ArrayStore<BVSort, RoundingModeSort>.then(entry: Pair<Expression<RoundingModeSort>, Expression<BVSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBVSortBVSort")
infix fun Expression<BVSort>.at(index : Expression<BVSort>) = this to index

@JvmName("storeBVSortBVSort")
infix fun Expression<ArraySort<BVSort, BVSort>>.store(entry : Pair<Expression<BVSort>, Expression<BVSort>>) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBVSortBVSort")
infix fun ArrayStore<BVSort, BVSort>.then(entry: Pair<Expression<BVSort>, Expression<BVSort>>) = ArrayStore(this, entry.second, entry.first)

/* this requires define-fun-rec which is not supported yet
 * (define-fun-rec arr () (Array Int Int) (store (store arr 0 0) 1 1))
fun <K : Sort, V : Sort> Iterable<Pair<K, V>>.toSMTArray(program: MutableSMTProgram, indexType : K, valueType : V) {
    program.defineFun(
        FunctionDef(
            "|array!$indexType!$valueType!${UUID.randomUUID()}|".toSymbolWithQuotes(),
            emptyList(),
            SMTArray(indexType, valueType),
            ))
}
*/

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

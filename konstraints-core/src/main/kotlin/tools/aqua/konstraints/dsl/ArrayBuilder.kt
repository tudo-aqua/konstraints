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

import java.math.BigDecimal
import java.math.BigInteger
import kotlin.experimental.ExperimentalTypeInference
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

@JvmName("selectInfixBase")
infix fun <X : Sort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: Expression<X>) =
    ArraySelect(this, index)

@JvmName("selectIntSortByte")
/** Select value stored at [index] in [this]. */
infix fun <X : IntSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: Byte) =
    ArraySelect(this, IntLiteral(index))

@JvmName("selectIntSortByteLambdaIndex")
/** Select value stored at [index] in [this]. */
infix fun <X : IntSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: (() -> Byte)) =
    ArraySelect(this, IntLiteral(index()))

@JvmName("selectIntSortByteLambdaArray")
/** Select value stored at [index] in [this]. */
infix fun <X : IntSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: Byte) =
    ArraySelect(this(), IntLiteral(index))

@JvmName("selectIntSortByteLambda")
/** Select value stored at [index] in [this]. */
infix fun <X : IntSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: (() -> Byte)) =
    ArraySelect(this(), IntLiteral(index()))

@JvmName("selectIntSortShort")
/** Select value stored at [index] in [this]. */
infix fun <X : IntSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: Short) =
    ArraySelect(this, IntLiteral(index))

@JvmName("selectIntSortShortLambdaIndex")
/** Select value stored at [index] in [this]. */
infix fun <X : IntSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: (() -> Short)) =
    ArraySelect(this, IntLiteral(index()))

@JvmName("selectIntSortShortLambdaArray")
/** Select value stored at [index] in [this]. */
infix fun <X : IntSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: Short) =
    ArraySelect(this(), IntLiteral(index))

@JvmName("selectIntSortShortLambda")
/** Select value stored at [index] in [this]. */
infix fun <X : IntSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: (() -> Short)) =
    ArraySelect(this(), IntLiteral(index()))

@JvmName("selectIntSortInt")
/** Select value stored at [index] in [this]. */
infix fun <X : IntSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: Int) =
    ArraySelect(this, IntLiteral(index))

@JvmName("selectIntSortIntLambdaIndex")
/** Select value stored at [index] in [this]. */
infix fun <X : IntSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: (() -> Int)) =
    ArraySelect(this, IntLiteral(index()))

@JvmName("selectIntSortIntLambdaArray")
/** Select value stored at [index] in [this]. */
infix fun <X : IntSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: Int) =
    ArraySelect(this(), IntLiteral(index))

@JvmName("selectIntSortIntLambda")
/** Select value stored at [index] in [this]. */
infix fun <X : IntSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: (() -> Int)) =
    ArraySelect(this(), IntLiteral(index()))

@JvmName("selectIntSortLong")
/** Select value stored at [index] in [this]. */
infix fun <X : IntSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: Long) =
    ArraySelect(this, IntLiteral(index))

@JvmName("selectIntSortLongLambdaIndex")
/** Select value stored at [index] in [this]. */
infix fun <X : IntSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: (() -> Long)) =
    ArraySelect(this, IntLiteral(index()))

@JvmName("selectIntSortLongLambdaArray")
/** Select value stored at [index] in [this]. */
infix fun <X : IntSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: Long) =
    ArraySelect(this(), IntLiteral(index))

@JvmName("selectIntSortLongLambda")
/** Select value stored at [index] in [this]. */
infix fun <X : IntSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: (() -> Long)) =
    ArraySelect(this(), IntLiteral(index()))

@JvmName("selectIntSortBigInteger")
/** Select value stored at [index] in [this]. */
infix fun <X : IntSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: BigInteger) =
    ArraySelect(this, IntLiteral(index))

@JvmName("selectIntSortBigIntegerLambdaIndex")
/** Select value stored at [index] in [this]. */
infix fun <X : IntSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: (() -> BigInteger)) =
    ArraySelect(this, IntLiteral(index()))

@JvmName("selectIntSortBigIntegerLambdaArray")
/** Select value stored at [index] in [this]. */
infix fun <X : IntSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: BigInteger) =
    ArraySelect(this(), IntLiteral(index))

@JvmName("selectIntSortBigIntegerLambda")
/** Select value stored at [index] in [this]. */
infix fun <X : IntSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(
    index: (() -> BigInteger)
) = ArraySelect(this(), IntLiteral(index()))

@JvmName("selectBoolSortBoolean")
/** Select value stored at [index] in [this]. */
infix fun <X : BoolSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: Boolean) =
    ArraySelect(this, index.toSMTBool())

@JvmName("selectBoolSortBooleanLambdaIndex")
/** Select value stored at [index] in [this]. */
infix fun <X : BoolSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: (() -> Boolean)) =
    ArraySelect(this, index().toSMTBool())

@JvmName("selectBoolSortBooleanLambdaArray")
/** Select value stored at [index] in [this]. */
infix fun <X : BoolSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: Boolean) =
    ArraySelect(this(), index.toSMTBool())

@JvmName("selectBoolSortBooleanLambda")
/** Select value stored at [index] in [this]. */
infix fun <X : BoolSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(
    index: (() -> Boolean)
) = ArraySelect(this(), index().toSMTBool())

@JvmName("selectStringSortString")
/** Select value stored at [index] in [this]. */
infix fun <X : StringSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: String) =
    ArraySelect(this, StringLiteral(index))

@JvmName("selectStringSortStringLambdaIndex")
/** Select value stored at [index] in [this]. */
infix fun <X : StringSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: (() -> String)) =
    ArraySelect(this, StringLiteral(index()))

@JvmName("selectStringSortStringLambdaArray")
/** Select value stored at [index] in [this]. */
infix fun <X : StringSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: String) =
    ArraySelect(this(), StringLiteral(index))

@JvmName("selectStringSortStringLambda")
/** Select value stored at [index] in [this]. */
infix fun <X : StringSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(
    index: (() -> String)
) = ArraySelect(this(), StringLiteral(index()))

@JvmName("selectRealSortByte")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: Byte) =
    ArraySelect(this, RealLiteral(index))

@JvmName("selectRealSortByteLambdaIndex")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: (() -> Byte)) =
    ArraySelect(this, RealLiteral(index()))

@JvmName("selectRealSortByteLambdaArray")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: Byte) =
    ArraySelect(this(), RealLiteral(index))

@JvmName("selectRealSortByteLambda")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: (() -> Byte)) =
    ArraySelect(this(), RealLiteral(index()))

@JvmName("selectRealSortShort")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: Short) =
    ArraySelect(this, RealLiteral(index))

@JvmName("selectRealSortShortLambdaIndex")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: (() -> Short)) =
    ArraySelect(this, RealLiteral(index()))

@JvmName("selectRealSortShortLambdaArray")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: Short) =
    ArraySelect(this(), RealLiteral(index))

@JvmName("selectRealSortShortLambda")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(
    index: (() -> Short)
) = ArraySelect(this(), RealLiteral(index()))

@JvmName("selectRealSortInt")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: Int) =
    ArraySelect(this, RealLiteral(index))

@JvmName("selectRealSortIntLambdaIndex")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: (() -> Int)) =
    ArraySelect(this, RealLiteral(index()))

@JvmName("selectRealSortIntLambdaArray")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: Int) =
    ArraySelect(this(), RealLiteral(index))

@JvmName("selectRealSortIntLambda")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: (() -> Int)) =
    ArraySelect(this(), RealLiteral(index()))

@JvmName("selectRealSortLong")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: Long) =
    ArraySelect(this, RealLiteral(index))

@JvmName("selectRealSortLongLambdaIndex")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: (() -> Long)) =
    ArraySelect(this, RealLiteral(index()))

@JvmName("selectRealSortLongLambdaArray")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: Long) =
    ArraySelect(this(), RealLiteral(index))

@JvmName("selectRealSortLongLambda")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: (() -> Long)) =
    ArraySelect(this(), RealLiteral(index()))

@JvmName("selectRealSortBigInteger")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: BigInteger) =
    ArraySelect(this, RealLiteral(index))

@JvmName("selectRealSortBigIntegerLambdaIndex")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: (() -> BigInteger)) =
    ArraySelect(this, RealLiteral(index()))

@JvmName("selectRealSortBigIntegerLambdaArray")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: BigInteger) =
    ArraySelect(this(), RealLiteral(index))

@JvmName("selectRealSortBigIntegerLambda")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(
    index: (() -> BigInteger)
) = ArraySelect(this(), RealLiteral(index()))

@JvmName("selectRealSortFloat")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: Float) =
    ArraySelect(this, RealLiteral(index))

@JvmName("selectRealSortFloatLambdaIndex")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: (() -> Float)) =
    ArraySelect(this, RealLiteral(index()))

@JvmName("selectRealSortFloatLambdaArray")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: Float) =
    ArraySelect(this(), RealLiteral(index))

@JvmName("selectRealSortFloatLambda")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(
    index: (() -> Float)
) = ArraySelect(this(), RealLiteral(index()))

@JvmName("selectRealSortDouble")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: Double) =
    ArraySelect(this, RealLiteral(index))

@JvmName("selectRealSortDoubleLambdaIndex")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: (() -> Double)) =
    ArraySelect(this, RealLiteral(index()))

@JvmName("selectRealSortDoubleLambdaArray")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: Double) =
    ArraySelect(this(), RealLiteral(index))

@JvmName("selectRealSortDoubleLambda")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(
    index: (() -> Double)
) = ArraySelect(this(), RealLiteral(index()))

@JvmName("selectRealSortBigDecimal")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: BigDecimal) =
    ArraySelect(this, RealLiteral(index))

@JvmName("selectRealSortBigDecimalLambdaIndex")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: (() -> BigDecimal)) =
    ArraySelect(this, RealLiteral(index()))

@JvmName("selectRealSortBigDecimalLambdaArray")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: BigDecimal) =
    ArraySelect(this(), RealLiteral(index))

@JvmName("selectRealSortBigDecimalLambda")
/** Select value stored at [index] in [this]. */
infix fun <X : RealSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(
    index: (() -> BigDecimal)
) = ArraySelect(this(), RealLiteral(index()))

@JvmName("selectFPSortFloat")
/** Select value stored at [index] in [this]. */
infix fun <X : FPSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: Float) =
    ArraySelect(this, FPLiteral(index))

@JvmName("selectFPSortFloatLambdaIndex")
/** Select value stored at [index] in [this]. */
infix fun <X : FPSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: (() -> Float)) =
    ArraySelect(this, FPLiteral(index()))

@JvmName("selectFPSortFloatLambdaArray")
/** Select value stored at [index] in [this]. */
infix fun <X : FPSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: Float) =
    ArraySelect(this(), FPLiteral(index))

@JvmName("selectFPSortFloatLambda")
/** Select value stored at [index] in [this]. */
infix fun <X : FPSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: (() -> Float)) =
    ArraySelect(this(), FPLiteral(index()))

@JvmName("selectFPSortDouble")
/** Select value stored at [index] in [this]. */
infix fun <X : FPSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: Double) =
    ArraySelect(this, FPLiteral(index))

@JvmName("selectFPSortDoubleLambdaIndex")
/** Select value stored at [index] in [this]. */
infix fun <X : FPSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: (() -> Double)) =
    ArraySelect(this, FPLiteral(index()))

@JvmName("selectFPSortDoubleLambdaArray")
/** Select value stored at [index] in [this]. */
infix fun <X : FPSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: Double) =
    ArraySelect(this(), FPLiteral(index))

@JvmName("selectFPSortDoubleLambda")
/** Select value stored at [index] in [this]. */
infix fun <X : FPSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: (() -> Double)) =
    ArraySelect(this(), FPLiteral(index()))

@JvmName("selectBitVecSortByte")
/** Select value stored at [index] in [this]. */
infix fun <X : BitVecSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: Byte) =
    ArraySelect(this, BVLiteral(index))

@JvmName("selectBitVecSortByteLambdaIndex")
/** Select value stored at [index] in [this]. */
infix fun <X : BitVecSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: (() -> Byte)) =
    ArraySelect(this, BVLiteral(index()))

@JvmName("selectBitVecSortByteLambdaArray")
/** Select value stored at [index] in [this]. */
infix fun <X : BitVecSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: Byte) =
    ArraySelect(this(), BVLiteral(index))

@JvmName("selectBitVecSortByteLambda")
/** Select value stored at [index] in [this]. */
infix fun <X : BitVecSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(
    index: (() -> Byte)
) = ArraySelect(this(), BVLiteral(index()))

@JvmName("selectBitVecSortShort")
/** Select value stored at [index] in [this]. */
infix fun <X : BitVecSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: Short) =
    ArraySelect(this, BVLiteral(index))

@JvmName("selectBitVecSortShortLambdaIndex")
/** Select value stored at [index] in [this]. */
infix fun <X : BitVecSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: (() -> Short)) =
    ArraySelect(this, BVLiteral(index()))

@JvmName("selectBitVecSortShortLambdaArray")
/** Select value stored at [index] in [this]. */
infix fun <X : BitVecSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: Short) =
    ArraySelect(this(), BVLiteral(index))

@JvmName("selectBitVecSortShortLambda")
/** Select value stored at [index] in [this]. */
infix fun <X : BitVecSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(
    index: (() -> Short)
) = ArraySelect(this(), BVLiteral(index()))

@JvmName("selectBitVecSortInt")
/** Select value stored at [index] in [this]. */
infix fun <X : BitVecSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: Int) =
    ArraySelect(this, BVLiteral(index))

@JvmName("selectBitVecSortIntLambdaIndex")
/** Select value stored at [index] in [this]. */
infix fun <X : BitVecSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: (() -> Int)) =
    ArraySelect(this, BVLiteral(index()))

@JvmName("selectBitVecSortIntLambdaArray")
/** Select value stored at [index] in [this]. */
infix fun <X : BitVecSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: Int) =
    ArraySelect(this(), BVLiteral(index))

@JvmName("selectBitVecSortIntLambda")
/** Select value stored at [index] in [this]. */
infix fun <X : BitVecSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(
    index: (() -> Int)
) = ArraySelect(this(), BVLiteral(index()))

@JvmName("selectBitVecSortLong")
/** Select value stored at [index] in [this]. */
infix fun <X : BitVecSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: Long) =
    ArraySelect(this, BVLiteral(index))

@JvmName("selectBitVecSortLongLambdaIndex")
/** Select value stored at [index] in [this]. */
infix fun <X : BitVecSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: (() -> Long)) =
    ArraySelect(this, BVLiteral(index()))

@JvmName("selectBitVecSortLongLambdaArray")
/** Select value stored at [index] in [this]. */
infix fun <X : BitVecSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: Long) =
    ArraySelect(this(), BVLiteral(index))

@JvmName("selectBitVecSortLongLambda")
/** Select value stored at [index] in [this]. */
infix fun <X : BitVecSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(
    index: (() -> Long)
) = ArraySelect(this(), BVLiteral(index()))

@JvmName("selectBitVecSortBigInteger")
/** Select value stored at [index] in [this]. */
infix fun <X : BitVecSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: BigInteger) =
    ArraySelect(this, BVLiteral(index))

@JvmName("selectBitVecSortBigIntegerLambdaIndex")
/** Select value stored at [index] in [this]. */
infix fun <X : BitVecSort, Y : Sort> Expression<ArraySort<X, Y>>.select(index: (() -> BigInteger)) =
    ArraySelect(this, BVLiteral(index()))

@JvmName("selectBitVecSortBigIntegerLambdaArray")
/** Select value stored at [index] in [this]. */
infix fun <X : BitVecSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(index: BigInteger) =
    ArraySelect(this(), BVLiteral(index))

@JvmName("selectBitVecSortBigIntegerLambda")
/** Select value stored at [index] in [this]. */
infix fun <X : BitVecSort, Y : Sort> (() -> Expression<ArraySort<X, Y>>).select(
    index: (() -> BigInteger)
) = ArraySelect(this(), BVLiteral(index()))

@JvmName("atIntSortIntSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<IntSort>.at(index: Expression<IntSort>) = this to index

@JvmName("storeIntSortIntSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, IntSort>>.store(
    entry: Pair<Expression<IntSort>, Expression<IntSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenIntSortIntSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, IntSort>.then(entry: Pair<Expression<IntSort>, Expression<IntSort>>) =
    ArrayStore(this, entry.second, entry.first)

@JvmName("atIntSortIntSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<IntSort>).at(index: Expression<IntSort>) = this() to index

@JvmName("storeIntSortIntSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, IntSort>>).store(
    entry: Pair<Expression<IntSort>, Expression<IntSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenIntSortIntSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, IntSort>).then(
    entry: Pair<Expression<IntSort>, Expression<IntSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atIntSortIntSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<IntSort>.at(index: (() -> Expression<IntSort>)) = this to index()

@JvmName("storeIntSortIntSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, IntSort>>.store(
    entry: (() -> Pair<Expression<IntSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenIntSortIntSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, IntSort>.then(
    entry: (() -> Pair<Expression<IntSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atIntSortIntSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<IntSort>).at(index: (() -> Expression<IntSort>)) = this() to index()

@JvmName("storeIntSortIntSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, IntSort>>).store(
    entry: (() -> Pair<Expression<IntSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenIntSortIntSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, IntSort>).then(
    entry: (() -> Pair<Expression<IntSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atIntSortInt")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<IntSort>.at(index: Int) = this to IntLiteral(index)

@JvmName("storeIntSortInt")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, IntSort>>.store(entry: Pair<Expression<IntSort>, Int>) =
    ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("thenIntSortInt")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, IntSort>.then(entry: Pair<Expression<IntSort>, Int>) =
    ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("atIntSortIntLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Expression<IntSort>).at(index: Int) = this() to IntLiteral(index)

@JvmName("storeIntSortIntLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, IntSort>>).store(
    entry: Pair<Expression<IntSort>, Int>
) = ArrayStore(this(), IntLiteral(entry.second), entry.first)

@JvmName("thenIntSortIntLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, IntSort>).then(entry: Pair<Expression<IntSort>, Int>) =
    ArrayStore(this(), IntLiteral(entry.second), entry.first)

@JvmName("atIntSortIntLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<IntSort>.at(index: (() -> Int)) = this to IntLiteral(index())

@JvmName("storeIntSortIntLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, IntSort>>.store(
    entry: (() -> Pair<Expression<IntSort>, Int>)
) = entry().let { (first, second) -> ArrayStore(this, IntLiteral(second), first) }

@JvmName("thenIntSortIntLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, IntSort>.then(entry: (() -> Pair<Expression<IntSort>, Int>)) =
    entry().let { (first, second) -> ArrayStore(this, IntLiteral(second), first) }

@JvmName("atIntSortIntLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<IntSort>).at(index: (() -> Int)) = this() to IntLiteral(index())

@JvmName("storeIntSortIntLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, IntSort>>).store(
    entry: (() -> Pair<Expression<IntSort>, Int>)
) = entry().let { (first, second) -> ArrayStore(this(), IntLiteral(second), first) }

@JvmName("thenIntSortIntLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, IntSort>).then(entry: (() -> Pair<Expression<IntSort>, Int>)) =
    entry().let { (first, second) -> ArrayStore(this(), IntLiteral(second), first) }

@JvmName("atIntIntSort")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Int.at(index: Expression<IntSort>) = IntLiteral(this) to index

@JvmName("storeIntIntSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, IntSort>>.store(entry: Pair<Int, Expression<IntSort>>) =
    ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("thenIntIntSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, IntSort>.then(entry: Pair<Int, Expression<IntSort>>) =
    ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("atIntIntSortLambdaValue")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Int).at(index: Expression<IntSort>) = IntLiteral(this()) to index

@JvmName("storeIntIntSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, IntSort>>).store(
    entry: Pair<Int, Expression<IntSort>>
) = ArrayStore(this(), entry.second, IntLiteral(entry.first))

@JvmName("thenIntIntSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, IntSort>).then(entry: Pair<Int, Expression<IntSort>>) =
    ArrayStore(this(), entry.second, IntLiteral(entry.first))

@JvmName("atIntIntSortLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Int.at(index: (() -> Expression<IntSort>)) = IntLiteral(this) to index()

@JvmName("storeIntIntSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, IntSort>>.store(
    entry: (() -> Pair<Int, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, IntLiteral(first)) }

@JvmName("thenIntIntSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, IntSort>.then(entry: (() -> Pair<Int, Expression<IntSort>>)) =
    entry().let { (first, second) -> ArrayStore(this, second, IntLiteral(first)) }

@JvmName("atIntIntSortLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Int).at(index: (() -> Expression<IntSort>)) = IntLiteral(this()) to index()

@JvmName("storeIntIntSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, IntSort>>).store(
    entry: (() -> Pair<Int, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, IntLiteral(first)) }

@JvmName("thenIntIntSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, IntSort>).then(entry: (() -> Pair<Int, Expression<IntSort>>)) =
    entry().let { (first, second) -> ArrayStore(this(), second, IntLiteral(first)) }

@JvmName("atIntInt")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Int.at(index: Int) = IntLiteral(this) to IntLiteral(index)

@JvmName("storeIntInt")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, IntSort>>.store(entry: Pair<Int, Int>) =
    ArrayStore(this, IntLiteral(entry.second), IntLiteral(entry.first))

@JvmName("thenIntInt")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, IntSort>.then(entry: Pair<Int, Int>) =
    ArrayStore(this, IntLiteral(entry.second), IntLiteral(entry.first))

@JvmName("atIntIntLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Int).at(index: Int) = IntLiteral(this()) to IntLiteral(index)

@JvmName("storeIntIntLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, IntSort>>).store(entry: Pair<Int, Int>) =
    ArrayStore(this(), IntLiteral(entry.second), IntLiteral(entry.first))

@JvmName("thenIntIntLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, IntSort>).then(entry: Pair<Int, Int>) =
    ArrayStore(this(), IntLiteral(entry.second), IntLiteral(entry.first))

@JvmName("atIntIntLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Int.at(index: (() -> Int)) = IntLiteral(this) to IntLiteral(index())

@JvmName("storeIntIntLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, IntSort>>.store(entry: (() -> Pair<Int, Int>)) =
    entry().let { (first, second) -> ArrayStore(this, IntLiteral(second), IntLiteral(first)) }

@JvmName("thenIntIntLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, IntSort>.then(entry: (() -> Pair<Int, Int>)) =
    entry().let { (first, second) -> ArrayStore(this, IntLiteral(second), IntLiteral(first)) }

@JvmName("atIntIntLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Int).at(index: (() -> Int)) = IntLiteral(this()) to IntLiteral(index())

@JvmName("storeIntIntLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, IntSort>>).store(entry: (() -> Pair<Int, Int>)) =
    entry().let { (first, second) -> ArrayStore(this(), IntLiteral(second), IntLiteral(first)) }

@JvmName("thenIntIntLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, IntSort>).then(entry: (() -> Pair<Int, Int>)) =
    entry().let { (first, second) -> ArrayStore(this(), IntLiteral(second), IntLiteral(first)) }

@JvmName("atBoolSortIntSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BoolSort>.at(index: Expression<IntSort>) = this to index

@JvmName("storeBoolSortIntSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, BoolSort>>.store(
    entry: Pair<Expression<BoolSort>, Expression<IntSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBoolSortIntSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, BoolSort>.then(
    entry: Pair<Expression<BoolSort>, Expression<IntSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBoolSortIntSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BoolSort>).at(index: Expression<IntSort>) = this() to index

@JvmName("storeBoolSortIntSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, BoolSort>>).store(
    entry: Pair<Expression<BoolSort>, Expression<IntSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenBoolSortIntSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, BoolSort>).then(
    entry: Pair<Expression<BoolSort>, Expression<IntSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atBoolSortIntSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BoolSort>.at(index: (() -> Expression<IntSort>)) = this to index()

@JvmName("storeBoolSortIntSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, BoolSort>>.store(
    entry: (() -> Pair<Expression<BoolSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenBoolSortIntSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, BoolSort>.then(
    entry: (() -> Pair<Expression<BoolSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atBoolSortIntSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BoolSort>).at(index: (() -> Expression<IntSort>)) = this() to index()

@JvmName("storeBoolSortIntSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, BoolSort>>).store(
    entry: (() -> Pair<Expression<BoolSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenBoolSortIntSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, BoolSort>).then(
    entry: (() -> Pair<Expression<BoolSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atBoolSortInt")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<BoolSort>.at(index: Int) = this to IntLiteral(index)

@JvmName("storeBoolSortInt")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, BoolSort>>.store(entry: Pair<Expression<BoolSort>, Int>) =
    ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("thenBoolSortInt")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, BoolSort>.then(entry: Pair<Expression<BoolSort>, Int>) =
    ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("atBoolSortIntLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Expression<BoolSort>).at(index: Int) = this() to IntLiteral(index)

@JvmName("storeBoolSortIntLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, BoolSort>>).store(
    entry: Pair<Expression<BoolSort>, Int>
) = ArrayStore(this(), IntLiteral(entry.second), entry.first)

@JvmName("thenBoolSortIntLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, BoolSort>).then(entry: Pair<Expression<BoolSort>, Int>) =
    ArrayStore(this(), IntLiteral(entry.second), entry.first)

@JvmName("atBoolSortIntLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<BoolSort>.at(index: (() -> Int)) = this to IntLiteral(index())

@JvmName("storeBoolSortIntLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, BoolSort>>.store(
    entry: (() -> Pair<Expression<BoolSort>, Int>)
) = entry().let { (first, second) -> ArrayStore(this, IntLiteral(second), first) }

@JvmName("thenBoolSortIntLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, BoolSort>.then(entry: (() -> Pair<Expression<BoolSort>, Int>)) =
    entry().let { (first, second) -> ArrayStore(this, IntLiteral(second), first) }

@JvmName("atBoolSortIntLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BoolSort>).at(index: (() -> Int)) = this() to IntLiteral(index())

@JvmName("storeBoolSortIntLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, BoolSort>>).store(
    entry: (() -> Pair<Expression<BoolSort>, Int>)
) = entry().let { (first, second) -> ArrayStore(this(), IntLiteral(second), first) }

@JvmName("thenBoolSortIntLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, BoolSort>).then(
    entry: (() -> Pair<Expression<BoolSort>, Int>)
) = entry().let { (first, second) -> ArrayStore(this(), IntLiteral(second), first) }

@JvmName("atBooleanIntSort")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Boolean.at(index: Expression<IntSort>) = this.toSMTBool() to index

@JvmName("storeBooleanIntSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, BoolSort>>.store(
    entry: Pair<Boolean, Expression<IntSort>>
) = ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("thenBooleanIntSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, BoolSort>.then(entry: Pair<Boolean, Expression<IntSort>>) =
    ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("atBooleanIntSortLambdaValue")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Boolean).at(index: Expression<IntSort>) = this().toSMTBool() to index

@JvmName("storeBooleanIntSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, BoolSort>>).store(
    entry: Pair<Boolean, Expression<IntSort>>
) = ArrayStore(this(), entry.second, entry.first.toSMTBool())

@JvmName("thenBooleanIntSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, BoolSort>).then(entry: Pair<Boolean, Expression<IntSort>>) =
    ArrayStore(this(), entry.second, entry.first.toSMTBool())

@JvmName("atBooleanIntSortLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Boolean.at(index: (() -> Expression<IntSort>)) = this.toSMTBool() to index()

@JvmName("storeBooleanIntSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, BoolSort>>.store(
    entry: (() -> Pair<Boolean, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first.toSMTBool()) }

@JvmName("thenBooleanIntSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, BoolSort>.then(entry: (() -> Pair<Boolean, Expression<IntSort>>)) =
    entry().let { (first, second) -> ArrayStore(this, second, first.toSMTBool()) }

@JvmName("atBooleanIntSortLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Boolean).at(index: (() -> Expression<IntSort>)) = this().toSMTBool() to index()

@JvmName("storeBooleanIntSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, BoolSort>>).store(
    entry: (() -> Pair<Boolean, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first.toSMTBool()) }

@JvmName("thenBooleanIntSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, BoolSort>).then(
    entry: (() -> Pair<Boolean, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first.toSMTBool()) }

@JvmName("atBooleanInt")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Boolean.at(index: Int) = this.toSMTBool() to IntLiteral(index)

@JvmName("storeBooleanInt")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, BoolSort>>.store(entry: Pair<Boolean, Int>) =
    ArrayStore(this, IntLiteral(entry.second), entry.first.toSMTBool())

@JvmName("thenBooleanInt")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, BoolSort>.then(entry: Pair<Boolean, Int>) =
    ArrayStore(this, IntLiteral(entry.second), entry.first.toSMTBool())

@JvmName("atBooleanIntLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Boolean).at(index: Int) = this().toSMTBool() to IntLiteral(index)

@JvmName("storeBooleanIntLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, BoolSort>>).store(entry: Pair<Boolean, Int>) =
    ArrayStore(this(), IntLiteral(entry.second), entry.first.toSMTBool())

@JvmName("thenBooleanIntLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, BoolSort>).then(entry: Pair<Boolean, Int>) =
    ArrayStore(this(), IntLiteral(entry.second), entry.first.toSMTBool())

@JvmName("atBooleanIntLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Boolean.at(index: (() -> Int)) = this.toSMTBool() to IntLiteral(index())

@JvmName("storeBooleanIntLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, BoolSort>>.store(entry: (() -> Pair<Boolean, Int>)) =
    entry().let { (first, second) -> ArrayStore(this, IntLiteral(second), first.toSMTBool()) }

@JvmName("thenBooleanIntLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, BoolSort>.then(entry: (() -> Pair<Boolean, Int>)) =
    entry().let { (first, second) -> ArrayStore(this, IntLiteral(second), first.toSMTBool()) }

@JvmName("atBooleanIntLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Boolean).at(index: (() -> Int)) = this().toSMTBool() to IntLiteral(index())

@JvmName("storeBooleanIntLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, BoolSort>>).store(
    entry: (() -> Pair<Boolean, Int>)
) = entry().let { (first, second) -> ArrayStore(this(), IntLiteral(second), first.toSMTBool()) }

@JvmName("thenBooleanIntLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, BoolSort>).then(entry: (() -> Pair<Boolean, Int>)) =
    entry().let { (first, second) -> ArrayStore(this(), IntLiteral(second), first.toSMTBool()) }

@JvmName("atStringSortIntSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<StringSort>.at(index: Expression<IntSort>) = this to index

@JvmName("storeStringSortIntSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, StringSort>>.store(
    entry: Pair<Expression<StringSort>, Expression<IntSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenStringSortIntSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, StringSort>.then(
    entry: Pair<Expression<StringSort>, Expression<IntSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atStringSortIntSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<StringSort>).at(index: Expression<IntSort>) = this() to index

@JvmName("storeStringSortIntSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, StringSort>>).store(
    entry: Pair<Expression<StringSort>, Expression<IntSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenStringSortIntSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, StringSort>).then(
    entry: Pair<Expression<StringSort>, Expression<IntSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atStringSortIntSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<StringSort>.at(index: (() -> Expression<IntSort>)) = this to index()

@JvmName("storeStringSortIntSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, StringSort>>.store(
    entry: (() -> Pair<Expression<StringSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenStringSortIntSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, StringSort>.then(
    entry: (() -> Pair<Expression<StringSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atStringSortIntSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<StringSort>).at(index: (() -> Expression<IntSort>)) = this() to index()

@JvmName("storeStringSortIntSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, StringSort>>).store(
    entry: (() -> Pair<Expression<StringSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenStringSortIntSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, StringSort>).then(
    entry: (() -> Pair<Expression<StringSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atStringSortInt")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<StringSort>.at(index: Int) = this to IntLiteral(index)

@JvmName("storeStringSortInt")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, StringSort>>.store(
    entry: Pair<Expression<StringSort>, Int>
) = ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("thenStringSortInt")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, StringSort>.then(entry: Pair<Expression<StringSort>, Int>) =
    ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("atStringSortIntLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Expression<StringSort>).at(index: Int) = this() to IntLiteral(index)

@JvmName("storeStringSortIntLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, StringSort>>).store(
    entry: Pair<Expression<StringSort>, Int>
) = ArrayStore(this(), IntLiteral(entry.second), entry.first)

@JvmName("thenStringSortIntLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, StringSort>).then(entry: Pair<Expression<StringSort>, Int>) =
    ArrayStore(this(), IntLiteral(entry.second), entry.first)

@JvmName("atStringSortIntLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<StringSort>.at(index: (() -> Int)) = this to IntLiteral(index())

@JvmName("storeStringSortIntLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, StringSort>>.store(
    entry: (() -> Pair<Expression<StringSort>, Int>)
) = entry().let { (first, second) -> ArrayStore(this, IntLiteral(second), first) }

@JvmName("thenStringSortIntLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, StringSort>.then(entry: (() -> Pair<Expression<StringSort>, Int>)) =
    entry().let { (first, second) -> ArrayStore(this, IntLiteral(second), first) }

@JvmName("atStringSortIntLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<StringSort>).at(index: (() -> Int)) = this() to IntLiteral(index())

@JvmName("storeStringSortIntLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, StringSort>>).store(
    entry: (() -> Pair<Expression<StringSort>, Int>)
) = entry().let { (first, second) -> ArrayStore(this(), IntLiteral(second), first) }

@JvmName("thenStringSortIntLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, StringSort>).then(
    entry: (() -> Pair<Expression<StringSort>, Int>)
) = entry().let { (first, second) -> ArrayStore(this(), IntLiteral(second), first) }

@JvmName("atStringIntSort")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun String.at(index: Expression<IntSort>) = StringLiteral(this) to index

@JvmName("storeStringIntSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, StringSort>>.store(
    entry: Pair<String, Expression<IntSort>>
) = ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("thenStringIntSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, StringSort>.then(entry: Pair<String, Expression<IntSort>>) =
    ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("atStringIntSortLambdaValue")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> String).at(index: Expression<IntSort>) = StringLiteral(this()) to index

@JvmName("storeStringIntSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, StringSort>>).store(
    entry: Pair<String, Expression<IntSort>>
) = ArrayStore(this(), entry.second, StringLiteral(entry.first))

@JvmName("thenStringIntSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, StringSort>).then(entry: Pair<String, Expression<IntSort>>) =
    ArrayStore(this(), entry.second, StringLiteral(entry.first))

@JvmName("atStringIntSortLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun String.at(index: (() -> Expression<IntSort>)) = StringLiteral(this) to index()

@JvmName("storeStringIntSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, StringSort>>.store(
    entry: (() -> Pair<String, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, StringLiteral(first)) }

@JvmName("thenStringIntSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, StringSort>.then(entry: (() -> Pair<String, Expression<IntSort>>)) =
    entry().let { (first, second) -> ArrayStore(this, second, StringLiteral(first)) }

@JvmName("atStringIntSortLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> String).at(index: (() -> Expression<IntSort>)) = StringLiteral(this()) to index()

@JvmName("storeStringIntSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, StringSort>>).store(
    entry: (() -> Pair<String, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, StringLiteral(first)) }

@JvmName("thenStringIntSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, StringSort>).then(
    entry: (() -> Pair<String, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, StringLiteral(first)) }

@JvmName("atStringInt")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun String.at(index: Int) = StringLiteral(this) to IntLiteral(index)

@JvmName("storeStringInt")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, StringSort>>.store(entry: Pair<String, Int>) =
    ArrayStore(this, IntLiteral(entry.second), StringLiteral(entry.first))

@JvmName("thenStringInt")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, StringSort>.then(entry: Pair<String, Int>) =
    ArrayStore(this, IntLiteral(entry.second), StringLiteral(entry.first))

@JvmName("atStringIntLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> String).at(index: Int) = StringLiteral(this()) to IntLiteral(index)

@JvmName("storeStringIntLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, StringSort>>).store(entry: Pair<String, Int>) =
    ArrayStore(this(), IntLiteral(entry.second), StringLiteral(entry.first))

@JvmName("thenStringIntLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, StringSort>).then(entry: Pair<String, Int>) =
    ArrayStore(this(), IntLiteral(entry.second), StringLiteral(entry.first))

@JvmName("atStringIntLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun String.at(index: (() -> Int)) = StringLiteral(this) to IntLiteral(index())

@JvmName("storeStringIntLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, StringSort>>.store(entry: (() -> Pair<String, Int>)) =
    entry().let { (first, second) -> ArrayStore(this, IntLiteral(second), StringLiteral(first)) }

@JvmName("thenStringIntLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, StringSort>.then(entry: (() -> Pair<String, Int>)) =
    entry().let { (first, second) -> ArrayStore(this, IntLiteral(second), StringLiteral(first)) }

@JvmName("atStringIntLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> String).at(index: (() -> Int)) = StringLiteral(this()) to IntLiteral(index())

@JvmName("storeStringIntLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, StringSort>>).store(
    entry: (() -> Pair<String, Int>)
) = entry().let { (first, second) -> ArrayStore(this(), IntLiteral(second), StringLiteral(first)) }

@JvmName("thenStringIntLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, StringSort>).then(entry: (() -> Pair<String, Int>)) =
    entry().let { (first, second) -> ArrayStore(this(), IntLiteral(second), StringLiteral(first)) }

@JvmName("atRealSortIntSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RealSort>.at(index: Expression<IntSort>) = this to index

@JvmName("storeRealSortIntSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, RealSort>>.store(
    entry: Pair<Expression<RealSort>, Expression<IntSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRealSortIntSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, RealSort>.then(
    entry: Pair<Expression<RealSort>, Expression<IntSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRealSortIntSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RealSort>).at(index: Expression<IntSort>) = this() to index

@JvmName("storeRealSortIntSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, RealSort>>).store(
    entry: Pair<Expression<RealSort>, Expression<IntSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenRealSortIntSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, RealSort>).then(
    entry: Pair<Expression<RealSort>, Expression<IntSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atRealSortIntSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RealSort>.at(index: (() -> Expression<IntSort>)) = this to index()

@JvmName("storeRealSortIntSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, RealSort>>.store(
    entry: (() -> Pair<Expression<RealSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenRealSortIntSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, RealSort>.then(
    entry: (() -> Pair<Expression<RealSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atRealSortIntSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RealSort>).at(index: (() -> Expression<IntSort>)) = this() to index()

@JvmName("storeRealSortIntSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, RealSort>>).store(
    entry: (() -> Pair<Expression<RealSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenRealSortIntSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, RealSort>).then(
    entry: (() -> Pair<Expression<RealSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atRealSortInt")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<RealSort>.at(index: Int) = this to IntLiteral(index)

@JvmName("storeRealSortInt")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, RealSort>>.store(entry: Pair<Expression<RealSort>, Int>) =
    ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("thenRealSortInt")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, RealSort>.then(entry: Pair<Expression<RealSort>, Int>) =
    ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("atRealSortIntLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Expression<RealSort>).at(index: Int) = this() to IntLiteral(index)

@JvmName("storeRealSortIntLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, RealSort>>).store(
    entry: Pair<Expression<RealSort>, Int>
) = ArrayStore(this(), IntLiteral(entry.second), entry.first)

@JvmName("thenRealSortIntLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, RealSort>).then(entry: Pair<Expression<RealSort>, Int>) =
    ArrayStore(this(), IntLiteral(entry.second), entry.first)

@JvmName("atRealSortIntLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<RealSort>.at(index: (() -> Int)) = this to IntLiteral(index())

@JvmName("storeRealSortIntLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, RealSort>>.store(
    entry: (() -> Pair<Expression<RealSort>, Int>)
) = entry().let { (first, second) -> ArrayStore(this, IntLiteral(second), first) }

@JvmName("thenRealSortIntLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, RealSort>.then(entry: (() -> Pair<Expression<RealSort>, Int>)) =
    entry().let { (first, second) -> ArrayStore(this, IntLiteral(second), first) }

@JvmName("atRealSortIntLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RealSort>).at(index: (() -> Int)) = this() to IntLiteral(index())

@JvmName("storeRealSortIntLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, RealSort>>).store(
    entry: (() -> Pair<Expression<RealSort>, Int>)
) = entry().let { (first, second) -> ArrayStore(this(), IntLiteral(second), first) }

@JvmName("thenRealSortIntLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, RealSort>).then(
    entry: (() -> Pair<Expression<RealSort>, Int>)
) = entry().let { (first, second) -> ArrayStore(this(), IntLiteral(second), first) }

@JvmName("atRegLanSortIntSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RegLanSort>.at(index: Expression<IntSort>) = this to index

@JvmName("storeRegLanSortIntSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, RegLanSort>>.store(
    entry: Pair<Expression<RegLanSort>, Expression<IntSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRegLanSortIntSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, RegLanSort>.then(
    entry: Pair<Expression<RegLanSort>, Expression<IntSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRegLanSortIntSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RegLanSort>).at(index: Expression<IntSort>) = this() to index

@JvmName("storeRegLanSortIntSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, RegLanSort>>).store(
    entry: Pair<Expression<RegLanSort>, Expression<IntSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenRegLanSortIntSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, RegLanSort>).then(
    entry: Pair<Expression<RegLanSort>, Expression<IntSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atRegLanSortIntSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RegLanSort>.at(index: (() -> Expression<IntSort>)) = this to index()

@JvmName("storeRegLanSortIntSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, RegLanSort>>.store(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenRegLanSortIntSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, RegLanSort>.then(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atRegLanSortIntSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RegLanSort>).at(index: (() -> Expression<IntSort>)) = this() to index()

@JvmName("storeRegLanSortIntSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, RegLanSort>>).store(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenRegLanSortIntSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, RegLanSort>).then(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atRegLanSortInt")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<RegLanSort>.at(index: Int) = this to IntLiteral(index)

@JvmName("storeRegLanSortInt")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, RegLanSort>>.store(
    entry: Pair<Expression<RegLanSort>, Int>
) = ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("thenRegLanSortInt")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, RegLanSort>.then(entry: Pair<Expression<RegLanSort>, Int>) =
    ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("atRegLanSortIntLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Expression<RegLanSort>).at(index: Int) = this() to IntLiteral(index)

@JvmName("storeRegLanSortIntLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, RegLanSort>>).store(
    entry: Pair<Expression<RegLanSort>, Int>
) = ArrayStore(this(), IntLiteral(entry.second), entry.first)

@JvmName("thenRegLanSortIntLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, RegLanSort>).then(entry: Pair<Expression<RegLanSort>, Int>) =
    ArrayStore(this(), IntLiteral(entry.second), entry.first)

@JvmName("atRegLanSortIntLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<RegLanSort>.at(index: (() -> Int)) = this to IntLiteral(index())

@JvmName("storeRegLanSortIntLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, RegLanSort>>.store(
    entry: (() -> Pair<Expression<RegLanSort>, Int>)
) = entry().let { (first, second) -> ArrayStore(this, IntLiteral(second), first) }

@JvmName("thenRegLanSortIntLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, RegLanSort>.then(entry: (() -> Pair<Expression<RegLanSort>, Int>)) =
    entry().let { (first, second) -> ArrayStore(this, IntLiteral(second), first) }

@JvmName("atRegLanSortIntLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RegLanSort>).at(index: (() -> Int)) = this() to IntLiteral(index())

@JvmName("storeRegLanSortIntLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, RegLanSort>>).store(
    entry: (() -> Pair<Expression<RegLanSort>, Int>)
) = entry().let { (first, second) -> ArrayStore(this(), IntLiteral(second), first) }

@JvmName("thenRegLanSortIntLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, RegLanSort>).then(
    entry: (() -> Pair<Expression<RegLanSort>, Int>)
) = entry().let { (first, second) -> ArrayStore(this(), IntLiteral(second), first) }

@JvmName("atFPSortIntSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<FPSort>.at(index: Expression<IntSort>) = this to index

@JvmName("storeFPSortIntSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, FPSort>>.store(
    entry: Pair<Expression<FPSort>, Expression<IntSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenFPSortIntSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, FPSort>.then(entry: Pair<Expression<FPSort>, Expression<IntSort>>) =
    ArrayStore(this, entry.second, entry.first)

@JvmName("atFPSortIntSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<FPSort>).at(index: Expression<IntSort>) = this() to index

@JvmName("storeFPSortIntSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, FPSort>>).store(
    entry: Pair<Expression<FPSort>, Expression<IntSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenFPSortIntSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, FPSort>).then(
    entry: Pair<Expression<FPSort>, Expression<IntSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atFPSortIntSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<FPSort>.at(index: (() -> Expression<IntSort>)) = this to index()

@JvmName("storeFPSortIntSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, FPSort>>.store(
    entry: (() -> Pair<Expression<FPSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenFPSortIntSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, FPSort>.then(
    entry: (() -> Pair<Expression<FPSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atFPSortIntSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<FPSort>).at(index: (() -> Expression<IntSort>)) = this() to index()

@JvmName("storeFPSortIntSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, FPSort>>).store(
    entry: (() -> Pair<Expression<FPSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenFPSortIntSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, FPSort>).then(
    entry: (() -> Pair<Expression<FPSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atFPSortInt")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<FPSort>.at(index: Int) = this to IntLiteral(index)

@JvmName("storeFPSortInt")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, FPSort>>.store(entry: Pair<Expression<FPSort>, Int>) =
    ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("thenFPSortInt")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, FPSort>.then(entry: Pair<Expression<FPSort>, Int>) =
    ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("atFPSortIntLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Expression<FPSort>).at(index: Int) = this() to IntLiteral(index)

@JvmName("storeFPSortIntLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, FPSort>>).store(
    entry: Pair<Expression<FPSort>, Int>
) = ArrayStore(this(), IntLiteral(entry.second), entry.first)

@JvmName("thenFPSortIntLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, FPSort>).then(entry: Pair<Expression<FPSort>, Int>) =
    ArrayStore(this(), IntLiteral(entry.second), entry.first)

@JvmName("atFPSortIntLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<FPSort>.at(index: (() -> Int)) = this to IntLiteral(index())

@JvmName("storeFPSortIntLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, FPSort>>.store(
    entry: (() -> Pair<Expression<FPSort>, Int>)
) = entry().let { (first, second) -> ArrayStore(this, IntLiteral(second), first) }

@JvmName("thenFPSortIntLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, FPSort>.then(entry: (() -> Pair<Expression<FPSort>, Int>)) =
    entry().let { (first, second) -> ArrayStore(this, IntLiteral(second), first) }

@JvmName("atFPSortIntLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<FPSort>).at(index: (() -> Int)) = this() to IntLiteral(index())

@JvmName("storeFPSortIntLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, FPSort>>).store(
    entry: (() -> Pair<Expression<FPSort>, Int>)
) = entry().let { (first, second) -> ArrayStore(this(), IntLiteral(second), first) }

@JvmName("thenFPSortIntLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, FPSort>).then(entry: (() -> Pair<Expression<FPSort>, Int>)) =
    entry().let { (first, second) -> ArrayStore(this(), IntLiteral(second), first) }

@JvmName("atRoundingModeSortIntSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RoundingModeSort>.at(index: Expression<IntSort>) = this to index

@JvmName("storeRoundingModeSortIntSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, RoundingModeSort>>.store(
    entry: Pair<Expression<RoundingModeSort>, Expression<IntSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRoundingModeSortIntSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, RoundingModeSort>.then(
    entry: Pair<Expression<RoundingModeSort>, Expression<IntSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRoundingModeSortIntSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RoundingModeSort>).at(index: Expression<IntSort>) = this() to index

@JvmName("storeRoundingModeSortIntSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, RoundingModeSort>>).store(
    entry: Pair<Expression<RoundingModeSort>, Expression<IntSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenRoundingModeSortIntSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, RoundingModeSort>).then(
    entry: Pair<Expression<RoundingModeSort>, Expression<IntSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atRoundingModeSortIntSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RoundingModeSort>.at(index: (() -> Expression<IntSort>)) = this to index()

@JvmName("storeRoundingModeSortIntSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, RoundingModeSort>>.store(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenRoundingModeSortIntSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, RoundingModeSort>.then(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atRoundingModeSortIntSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RoundingModeSort>).at(index: (() -> Expression<IntSort>)) =
    this() to index()

@JvmName("storeRoundingModeSortIntSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, RoundingModeSort>>).store(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenRoundingModeSortIntSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, RoundingModeSort>).then(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atRoundingModeSortInt")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<RoundingModeSort>.at(index: Int) = this to IntLiteral(index)

@JvmName("storeRoundingModeSortInt")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, RoundingModeSort>>.store(
    entry: Pair<Expression<RoundingModeSort>, Int>
) = ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("thenRoundingModeSortInt")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, RoundingModeSort>.then(
    entry: Pair<Expression<RoundingModeSort>, Int>
) = ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("atRoundingModeSortIntLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Expression<RoundingModeSort>).at(index: Int) = this() to IntLiteral(index)

@JvmName("storeRoundingModeSortIntLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, RoundingModeSort>>).store(
    entry: Pair<Expression<RoundingModeSort>, Int>
) = ArrayStore(this(), IntLiteral(entry.second), entry.first)

@JvmName("thenRoundingModeSortIntLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, RoundingModeSort>).then(
    entry: Pair<Expression<RoundingModeSort>, Int>
) = ArrayStore(this(), IntLiteral(entry.second), entry.first)

@JvmName("atRoundingModeSortIntLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<RoundingModeSort>.at(index: (() -> Int)) = this to IntLiteral(index())

@JvmName("storeRoundingModeSortIntLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, RoundingModeSort>>.store(
    entry: (() -> Pair<Expression<RoundingModeSort>, Int>)
) = entry().let { (first, second) -> ArrayStore(this, IntLiteral(second), first) }

@JvmName("thenRoundingModeSortIntLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, RoundingModeSort>.then(
    entry: (() -> Pair<Expression<RoundingModeSort>, Int>)
) = entry().let { (first, second) -> ArrayStore(this, IntLiteral(second), first) }

@JvmName("atRoundingModeSortIntLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RoundingModeSort>).at(index: (() -> Int)) =
    this() to IntLiteral(index())

@JvmName("storeRoundingModeSortIntLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, RoundingModeSort>>).store(
    entry: (() -> Pair<Expression<RoundingModeSort>, Int>)
) = entry().let { (first, second) -> ArrayStore(this(), IntLiteral(second), first) }

@JvmName("thenRoundingModeSortIntLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, RoundingModeSort>).then(
    entry: (() -> Pair<Expression<RoundingModeSort>, Int>)
) = entry().let { (first, second) -> ArrayStore(this(), IntLiteral(second), first) }

@JvmName("atBitVecSortIntSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BitVecSort>.at(index: Expression<IntSort>) = this to index

@JvmName("storeBitVecSortIntSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, BitVecSort>>.store(
    entry: Pair<Expression<BitVecSort>, Expression<IntSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBitVecSortIntSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, BitVecSort>.then(
    entry: Pair<Expression<BitVecSort>, Expression<IntSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBitVecSortIntSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BitVecSort>).at(index: Expression<IntSort>) = this() to index

@JvmName("storeBitVecSortIntSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, BitVecSort>>).store(
    entry: Pair<Expression<BitVecSort>, Expression<IntSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenBitVecSortIntSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, BitVecSort>).then(
    entry: Pair<Expression<BitVecSort>, Expression<IntSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atBitVecSortIntSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BitVecSort>.at(index: (() -> Expression<IntSort>)) = this to index()

@JvmName("storeBitVecSortIntSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, BitVecSort>>.store(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenBitVecSortIntSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, BitVecSort>.then(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atBitVecSortIntSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BitVecSort>).at(index: (() -> Expression<IntSort>)) = this() to index()

@JvmName("storeBitVecSortIntSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, BitVecSort>>).store(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenBitVecSortIntSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, BitVecSort>).then(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<IntSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atBitVecSortInt")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<BitVecSort>.at(index: Int) = this to IntLiteral(index)

@JvmName("storeBitVecSortInt")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, BitVecSort>>.store(
    entry: Pair<Expression<BitVecSort>, Int>
) = ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("thenBitVecSortInt")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, BitVecSort>.then(entry: Pair<Expression<BitVecSort>, Int>) =
    ArrayStore(this, IntLiteral(entry.second), entry.first)

@JvmName("atBitVecSortIntLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Expression<BitVecSort>).at(index: Int) = this() to IntLiteral(index)

@JvmName("storeBitVecSortIntLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, BitVecSort>>).store(
    entry: Pair<Expression<BitVecSort>, Int>
) = ArrayStore(this(), IntLiteral(entry.second), entry.first)

@JvmName("thenBitVecSortIntLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, BitVecSort>).then(entry: Pair<Expression<BitVecSort>, Int>) =
    ArrayStore(this(), IntLiteral(entry.second), entry.first)

@JvmName("atBitVecSortIntLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<BitVecSort>.at(index: (() -> Int)) = this to IntLiteral(index())

@JvmName("storeBitVecSortIntLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<IntSort, BitVecSort>>.store(
    entry: (() -> Pair<Expression<BitVecSort>, Int>)
) = entry().let { (first, second) -> ArrayStore(this, IntLiteral(second), first) }

@JvmName("thenBitVecSortIntLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<IntSort, BitVecSort>.then(entry: (() -> Pair<Expression<BitVecSort>, Int>)) =
    entry().let { (first, second) -> ArrayStore(this, IntLiteral(second), first) }

@JvmName("atBitVecSortIntLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BitVecSort>).at(index: (() -> Int)) = this() to IntLiteral(index())

@JvmName("storeBitVecSortIntLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<IntSort, BitVecSort>>).store(
    entry: (() -> Pair<Expression<BitVecSort>, Int>)
) = entry().let { (first, second) -> ArrayStore(this(), IntLiteral(second), first) }

@JvmName("thenBitVecSortIntLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<IntSort, BitVecSort>).then(
    entry: (() -> Pair<Expression<BitVecSort>, Int>)
) = entry().let { (first, second) -> ArrayStore(this(), IntLiteral(second), first) }

@JvmName("atIntSortBoolSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<IntSort>.at(index: Expression<BoolSort>) = this to index

@JvmName("storeIntSortBoolSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, IntSort>>.store(
    entry: Pair<Expression<IntSort>, Expression<BoolSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenIntSortBoolSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, IntSort>.then(
    entry: Pair<Expression<IntSort>, Expression<BoolSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atIntSortBoolSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<IntSort>).at(index: Expression<BoolSort>) = this() to index

@JvmName("storeIntSortBoolSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, IntSort>>).store(
    entry: Pair<Expression<IntSort>, Expression<BoolSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenIntSortBoolSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, IntSort>).then(
    entry: Pair<Expression<IntSort>, Expression<BoolSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atIntSortBoolSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<IntSort>.at(index: (() -> Expression<BoolSort>)) = this to index()

@JvmName("storeIntSortBoolSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, IntSort>>.store(
    entry: (() -> Pair<Expression<IntSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenIntSortBoolSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, IntSort>.then(
    entry: (() -> Pair<Expression<IntSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atIntSortBoolSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<IntSort>).at(index: (() -> Expression<BoolSort>)) = this() to index()

@JvmName("storeIntSortBoolSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, IntSort>>).store(
    entry: (() -> Pair<Expression<IntSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenIntSortBoolSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, IntSort>).then(
    entry: (() -> Pair<Expression<IntSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atIntSortBoolean")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<IntSort>.at(index: Boolean) = this to index.toSMTBool()

@JvmName("storeIntSortBoolean")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, IntSort>>.store(
    entry: Pair<Expression<IntSort>, Boolean>
) = ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("thenIntSortBoolean")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, IntSort>.then(entry: Pair<Expression<IntSort>, Boolean>) =
    ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("atIntSortBooleanLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Expression<IntSort>).at(index: Boolean) = this() to index.toSMTBool()

@JvmName("storeIntSortBooleanLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, IntSort>>).store(
    entry: Pair<Expression<IntSort>, Boolean>
) = ArrayStore(this(), entry.second.toSMTBool(), entry.first)

@JvmName("thenIntSortBooleanLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, IntSort>).then(entry: Pair<Expression<IntSort>, Boolean>) =
    ArrayStore(this(), entry.second.toSMTBool(), entry.first)

@JvmName("atIntSortBooleanLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<IntSort>.at(index: (() -> Boolean)) = this to index().toSMTBool()

@JvmName("storeIntSortBooleanLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, IntSort>>.store(
    entry: (() -> Pair<Expression<IntSort>, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this, second.toSMTBool(), first) }

@JvmName("thenIntSortBooleanLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, IntSort>.then(entry: (() -> Pair<Expression<IntSort>, Boolean>)) =
    entry().let { (first, second) -> ArrayStore(this, second.toSMTBool(), first) }

@JvmName("atIntSortBooleanLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<IntSort>).at(index: (() -> Boolean)) = this() to index().toSMTBool()

@JvmName("storeIntSortBooleanLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, IntSort>>).store(
    entry: (() -> Pair<Expression<IntSort>, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this(), second.toSMTBool(), first) }

@JvmName("thenIntSortBooleanLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, IntSort>).then(
    entry: (() -> Pair<Expression<IntSort>, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this(), second.toSMTBool(), first) }

@JvmName("atIntBoolSort")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Int.at(index: Expression<BoolSort>) = IntLiteral(this) to index

@JvmName("storeIntBoolSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, IntSort>>.store(entry: Pair<Int, Expression<BoolSort>>) =
    ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("thenIntBoolSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, IntSort>.then(entry: Pair<Int, Expression<BoolSort>>) =
    ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("atIntBoolSortLambdaValue")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Int).at(index: Expression<BoolSort>) = IntLiteral(this()) to index

@JvmName("storeIntBoolSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, IntSort>>).store(
    entry: Pair<Int, Expression<BoolSort>>
) = ArrayStore(this(), entry.second, IntLiteral(entry.first))

@JvmName("thenIntBoolSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, IntSort>).then(entry: Pair<Int, Expression<BoolSort>>) =
    ArrayStore(this(), entry.second, IntLiteral(entry.first))

@JvmName("atIntBoolSortLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Int.at(index: (() -> Expression<BoolSort>)) = IntLiteral(this) to index()

@JvmName("storeIntBoolSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, IntSort>>.store(
    entry: (() -> Pair<Int, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, IntLiteral(first)) }

@JvmName("thenIntBoolSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, IntSort>.then(entry: (() -> Pair<Int, Expression<BoolSort>>)) =
    entry().let { (first, second) -> ArrayStore(this, second, IntLiteral(first)) }

@JvmName("atIntBoolSortLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Int).at(index: (() -> Expression<BoolSort>)) = IntLiteral(this()) to index()

@JvmName("storeIntBoolSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, IntSort>>).store(
    entry: (() -> Pair<Int, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, IntLiteral(first)) }

@JvmName("thenIntBoolSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, IntSort>).then(
    entry: (() -> Pair<Int, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, IntLiteral(first)) }

@JvmName("atIntBoolean")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Int.at(index: Boolean) = IntLiteral(this) to index.toSMTBool()

@JvmName("storeIntBoolean")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, IntSort>>.store(entry: Pair<Int, Boolean>) =
    ArrayStore(this, entry.second.toSMTBool(), IntLiteral(entry.first))

@JvmName("thenIntBoolean")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, IntSort>.then(entry: Pair<Int, Boolean>) =
    ArrayStore(this, entry.second.toSMTBool(), IntLiteral(entry.first))

@JvmName("atIntBooleanLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Int).at(index: Boolean) = IntLiteral(this()) to index.toSMTBool()

@JvmName("storeIntBooleanLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, IntSort>>).store(entry: Pair<Int, Boolean>) =
    ArrayStore(this(), entry.second.toSMTBool(), IntLiteral(entry.first))

@JvmName("thenIntBooleanLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, IntSort>).then(entry: Pair<Int, Boolean>) =
    ArrayStore(this(), entry.second.toSMTBool(), IntLiteral(entry.first))

@JvmName("atIntBooleanLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Int.at(index: (() -> Boolean)) = IntLiteral(this) to index().toSMTBool()

@JvmName("storeIntBooleanLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, IntSort>>.store(entry: (() -> Pair<Int, Boolean>)) =
    entry().let { (first, second) -> ArrayStore(this, second.toSMTBool(), IntLiteral(first)) }

@JvmName("thenIntBooleanLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, IntSort>.then(entry: (() -> Pair<Int, Boolean>)) =
    entry().let { (first, second) -> ArrayStore(this, second.toSMTBool(), IntLiteral(first)) }

@JvmName("atIntBooleanLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Int).at(index: (() -> Boolean)) = IntLiteral(this()) to index().toSMTBool()

@JvmName("storeIntBooleanLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, IntSort>>).store(
    entry: (() -> Pair<Int, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this(), second.toSMTBool(), IntLiteral(first)) }

@JvmName("thenIntBooleanLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, IntSort>).then(entry: (() -> Pair<Int, Boolean>)) =
    entry().let { (first, second) -> ArrayStore(this(), second.toSMTBool(), IntLiteral(first)) }

@JvmName("atBoolSortBoolSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BoolSort>.at(index: Expression<BoolSort>) = this to index

@JvmName("storeBoolSortBoolSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, BoolSort>>.store(
    entry: Pair<Expression<BoolSort>, Expression<BoolSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBoolSortBoolSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, BoolSort>.then(
    entry: Pair<Expression<BoolSort>, Expression<BoolSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBoolSortBoolSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BoolSort>).at(index: Expression<BoolSort>) = this() to index

@JvmName("storeBoolSortBoolSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, BoolSort>>).store(
    entry: Pair<Expression<BoolSort>, Expression<BoolSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenBoolSortBoolSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, BoolSort>).then(
    entry: Pair<Expression<BoolSort>, Expression<BoolSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atBoolSortBoolSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BoolSort>.at(index: (() -> Expression<BoolSort>)) = this to index()

@JvmName("storeBoolSortBoolSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, BoolSort>>.store(
    entry: (() -> Pair<Expression<BoolSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenBoolSortBoolSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, BoolSort>.then(
    entry: (() -> Pair<Expression<BoolSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atBoolSortBoolSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BoolSort>).at(index: (() -> Expression<BoolSort>)) = this() to index()

@JvmName("storeBoolSortBoolSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, BoolSort>>).store(
    entry: (() -> Pair<Expression<BoolSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenBoolSortBoolSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, BoolSort>).then(
    entry: (() -> Pair<Expression<BoolSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atBoolSortBoolean")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<BoolSort>.at(index: Boolean) = this to index.toSMTBool()

@JvmName("storeBoolSortBoolean")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, BoolSort>>.store(
    entry: Pair<Expression<BoolSort>, Boolean>
) = ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("thenBoolSortBoolean")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, BoolSort>.then(entry: Pair<Expression<BoolSort>, Boolean>) =
    ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("atBoolSortBooleanLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Expression<BoolSort>).at(index: Boolean) = this() to index.toSMTBool()

@JvmName("storeBoolSortBooleanLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, BoolSort>>).store(
    entry: Pair<Expression<BoolSort>, Boolean>
) = ArrayStore(this(), entry.second.toSMTBool(), entry.first)

@JvmName("thenBoolSortBooleanLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, BoolSort>).then(entry: Pair<Expression<BoolSort>, Boolean>) =
    ArrayStore(this(), entry.second.toSMTBool(), entry.first)

@JvmName("atBoolSortBooleanLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<BoolSort>.at(index: (() -> Boolean)) = this to index().toSMTBool()

@JvmName("storeBoolSortBooleanLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, BoolSort>>.store(
    entry: (() -> Pair<Expression<BoolSort>, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this, second.toSMTBool(), first) }

@JvmName("thenBoolSortBooleanLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, BoolSort>.then(entry: (() -> Pair<Expression<BoolSort>, Boolean>)) =
    entry().let { (first, second) -> ArrayStore(this, second.toSMTBool(), first) }

@JvmName("atBoolSortBooleanLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BoolSort>).at(index: (() -> Boolean)) = this() to index().toSMTBool()

@JvmName("storeBoolSortBooleanLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, BoolSort>>).store(
    entry: (() -> Pair<Expression<BoolSort>, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this(), second.toSMTBool(), first) }

@JvmName("thenBoolSortBooleanLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, BoolSort>).then(
    entry: (() -> Pair<Expression<BoolSort>, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this(), second.toSMTBool(), first) }

@JvmName("atBooleanBoolSort")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Boolean.at(index: Expression<BoolSort>) = this.toSMTBool() to index

@JvmName("storeBooleanBoolSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, BoolSort>>.store(
    entry: Pair<Boolean, Expression<BoolSort>>
) = ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("thenBooleanBoolSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, BoolSort>.then(entry: Pair<Boolean, Expression<BoolSort>>) =
    ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("atBooleanBoolSortLambdaValue")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Boolean).at(index: Expression<BoolSort>) = this().toSMTBool() to index

@JvmName("storeBooleanBoolSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, BoolSort>>).store(
    entry: Pair<Boolean, Expression<BoolSort>>
) = ArrayStore(this(), entry.second, entry.first.toSMTBool())

@JvmName("thenBooleanBoolSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, BoolSort>).then(entry: Pair<Boolean, Expression<BoolSort>>) =
    ArrayStore(this(), entry.second, entry.first.toSMTBool())

@JvmName("atBooleanBoolSortLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Boolean.at(index: (() -> Expression<BoolSort>)) = this.toSMTBool() to index()

@JvmName("storeBooleanBoolSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, BoolSort>>.store(
    entry: (() -> Pair<Boolean, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first.toSMTBool()) }

@JvmName("thenBooleanBoolSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, BoolSort>.then(entry: (() -> Pair<Boolean, Expression<BoolSort>>)) =
    entry().let { (first, second) -> ArrayStore(this, second, first.toSMTBool()) }

@JvmName("atBooleanBoolSortLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Boolean).at(index: (() -> Expression<BoolSort>)) = this().toSMTBool() to index()

@JvmName("storeBooleanBoolSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, BoolSort>>).store(
    entry: (() -> Pair<Boolean, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first.toSMTBool()) }

@JvmName("thenBooleanBoolSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, BoolSort>).then(
    entry: (() -> Pair<Boolean, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first.toSMTBool()) }

@JvmName("atBooleanBoolean")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Boolean.at(index: Boolean) = this.toSMTBool() to index.toSMTBool()

@JvmName("storeBooleanBoolean")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, BoolSort>>.store(entry: Pair<Boolean, Boolean>) =
    ArrayStore(this, entry.second.toSMTBool(), entry.first.toSMTBool())

@JvmName("thenBooleanBoolean")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, BoolSort>.then(entry: Pair<Boolean, Boolean>) =
    ArrayStore(this, entry.second.toSMTBool(), entry.first.toSMTBool())

@JvmName("atBooleanBooleanLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Boolean).at(index: Boolean) = this().toSMTBool() to index.toSMTBool()

@JvmName("storeBooleanBooleanLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, BoolSort>>).store(entry: Pair<Boolean, Boolean>) =
    ArrayStore(this(), entry.second.toSMTBool(), entry.first.toSMTBool())

@JvmName("thenBooleanBooleanLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, BoolSort>).then(entry: Pair<Boolean, Boolean>) =
    ArrayStore(this(), entry.second.toSMTBool(), entry.first.toSMTBool())

@JvmName("atBooleanBooleanLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Boolean.at(index: (() -> Boolean)) = this.toSMTBool() to index().toSMTBool()

@JvmName("storeBooleanBooleanLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, BoolSort>>.store(entry: (() -> Pair<Boolean, Boolean>)) =
    entry().let { (first, second) -> ArrayStore(this, second.toSMTBool(), first.toSMTBool()) }

@JvmName("thenBooleanBooleanLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, BoolSort>.then(entry: (() -> Pair<Boolean, Boolean>)) =
    entry().let { (first, second) -> ArrayStore(this, second.toSMTBool(), first.toSMTBool()) }

@JvmName("atBooleanBooleanLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Boolean).at(index: (() -> Boolean)) = this().toSMTBool() to index().toSMTBool()

@JvmName("storeBooleanBooleanLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, BoolSort>>).store(
    entry: (() -> Pair<Boolean, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this(), second.toSMTBool(), first.toSMTBool()) }

@JvmName("thenBooleanBooleanLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, BoolSort>).then(entry: (() -> Pair<Boolean, Boolean>)) =
    entry().let { (first, second) -> ArrayStore(this(), second.toSMTBool(), first.toSMTBool()) }

@JvmName("atStringSortBoolSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<StringSort>.at(index: Expression<BoolSort>) = this to index

@JvmName("storeStringSortBoolSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, StringSort>>.store(
    entry: Pair<Expression<StringSort>, Expression<BoolSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenStringSortBoolSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, StringSort>.then(
    entry: Pair<Expression<StringSort>, Expression<BoolSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atStringSortBoolSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<StringSort>).at(index: Expression<BoolSort>) = this() to index

@JvmName("storeStringSortBoolSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, StringSort>>).store(
    entry: Pair<Expression<StringSort>, Expression<BoolSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenStringSortBoolSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, StringSort>).then(
    entry: Pair<Expression<StringSort>, Expression<BoolSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atStringSortBoolSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<StringSort>.at(index: (() -> Expression<BoolSort>)) = this to index()

@JvmName("storeStringSortBoolSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, StringSort>>.store(
    entry: (() -> Pair<Expression<StringSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenStringSortBoolSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, StringSort>.then(
    entry: (() -> Pair<Expression<StringSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atStringSortBoolSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<StringSort>).at(index: (() -> Expression<BoolSort>)) = this() to index()

@JvmName("storeStringSortBoolSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, StringSort>>).store(
    entry: (() -> Pair<Expression<StringSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenStringSortBoolSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, StringSort>).then(
    entry: (() -> Pair<Expression<StringSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atStringSortBoolean")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<StringSort>.at(index: Boolean) = this to index.toSMTBool()

@JvmName("storeStringSortBoolean")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, StringSort>>.store(
    entry: Pair<Expression<StringSort>, Boolean>
) = ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("thenStringSortBoolean")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, StringSort>.then(entry: Pair<Expression<StringSort>, Boolean>) =
    ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("atStringSortBooleanLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Expression<StringSort>).at(index: Boolean) = this() to index.toSMTBool()

@JvmName("storeStringSortBooleanLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, StringSort>>).store(
    entry: Pair<Expression<StringSort>, Boolean>
) = ArrayStore(this(), entry.second.toSMTBool(), entry.first)

@JvmName("thenStringSortBooleanLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, StringSort>).then(
    entry: Pair<Expression<StringSort>, Boolean>
) = ArrayStore(this(), entry.second.toSMTBool(), entry.first)

@JvmName("atStringSortBooleanLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<StringSort>.at(index: (() -> Boolean)) = this to index().toSMTBool()

@JvmName("storeStringSortBooleanLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, StringSort>>.store(
    entry: (() -> Pair<Expression<StringSort>, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this, second.toSMTBool(), first) }

@JvmName("thenStringSortBooleanLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, StringSort>.then(
    entry: (() -> Pair<Expression<StringSort>, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this, second.toSMTBool(), first) }

@JvmName("atStringSortBooleanLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<StringSort>).at(index: (() -> Boolean)) = this() to index().toSMTBool()

@JvmName("storeStringSortBooleanLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, StringSort>>).store(
    entry: (() -> Pair<Expression<StringSort>, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this(), second.toSMTBool(), first) }

@JvmName("thenStringSortBooleanLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, StringSort>).then(
    entry: (() -> Pair<Expression<StringSort>, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this(), second.toSMTBool(), first) }

@JvmName("atStringBoolSort")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun String.at(index: Expression<BoolSort>) = StringLiteral(this) to index

@JvmName("storeStringBoolSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, StringSort>>.store(
    entry: Pair<String, Expression<BoolSort>>
) = ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("thenStringBoolSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, StringSort>.then(entry: Pair<String, Expression<BoolSort>>) =
    ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("atStringBoolSortLambdaValue")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> String).at(index: Expression<BoolSort>) = StringLiteral(this()) to index

@JvmName("storeStringBoolSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, StringSort>>).store(
    entry: Pair<String, Expression<BoolSort>>
) = ArrayStore(this(), entry.second, StringLiteral(entry.first))

@JvmName("thenStringBoolSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, StringSort>).then(entry: Pair<String, Expression<BoolSort>>) =
    ArrayStore(this(), entry.second, StringLiteral(entry.first))

@JvmName("atStringBoolSortLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun String.at(index: (() -> Expression<BoolSort>)) = StringLiteral(this) to index()

@JvmName("storeStringBoolSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, StringSort>>.store(
    entry: (() -> Pair<String, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, StringLiteral(first)) }

@JvmName("thenStringBoolSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, StringSort>.then(entry: (() -> Pair<String, Expression<BoolSort>>)) =
    entry().let { (first, second) -> ArrayStore(this, second, StringLiteral(first)) }

@JvmName("atStringBoolSortLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> String).at(index: (() -> Expression<BoolSort>)) = StringLiteral(this()) to index()

@JvmName("storeStringBoolSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, StringSort>>).store(
    entry: (() -> Pair<String, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, StringLiteral(first)) }

@JvmName("thenStringBoolSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, StringSort>).then(
    entry: (() -> Pair<String, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, StringLiteral(first)) }

@JvmName("atStringBoolean")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun String.at(index: Boolean) = StringLiteral(this) to index.toSMTBool()

@JvmName("storeStringBoolean")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, StringSort>>.store(entry: Pair<String, Boolean>) =
    ArrayStore(this, entry.second.toSMTBool(), StringLiteral(entry.first))

@JvmName("thenStringBoolean")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, StringSort>.then(entry: Pair<String, Boolean>) =
    ArrayStore(this, entry.second.toSMTBool(), StringLiteral(entry.first))

@JvmName("atStringBooleanLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> String).at(index: Boolean) = StringLiteral(this()) to index.toSMTBool()

@JvmName("storeStringBooleanLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, StringSort>>).store(entry: Pair<String, Boolean>) =
    ArrayStore(this(), entry.second.toSMTBool(), StringLiteral(entry.first))

@JvmName("thenStringBooleanLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, StringSort>).then(entry: Pair<String, Boolean>) =
    ArrayStore(this(), entry.second.toSMTBool(), StringLiteral(entry.first))

@JvmName("atStringBooleanLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun String.at(index: (() -> Boolean)) = StringLiteral(this) to index().toSMTBool()

@JvmName("storeStringBooleanLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, StringSort>>.store(entry: (() -> Pair<String, Boolean>)) =
    entry().let { (first, second) -> ArrayStore(this, second.toSMTBool(), StringLiteral(first)) }

@JvmName("thenStringBooleanLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, StringSort>.then(entry: (() -> Pair<String, Boolean>)) =
    entry().let { (first, second) -> ArrayStore(this, second.toSMTBool(), StringLiteral(first)) }

@JvmName("atStringBooleanLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> String).at(index: (() -> Boolean)) = StringLiteral(this()) to index().toSMTBool()

@JvmName("storeStringBooleanLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, StringSort>>).store(
    entry: (() -> Pair<String, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this(), second.toSMTBool(), StringLiteral(first)) }

@JvmName("thenStringBooleanLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, StringSort>).then(entry: (() -> Pair<String, Boolean>)) =
    entry().let { (first, second) -> ArrayStore(this(), second.toSMTBool(), StringLiteral(first)) }

@JvmName("atRealSortBoolSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RealSort>.at(index: Expression<BoolSort>) = this to index

@JvmName("storeRealSortBoolSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, RealSort>>.store(
    entry: Pair<Expression<RealSort>, Expression<BoolSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRealSortBoolSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, RealSort>.then(
    entry: Pair<Expression<RealSort>, Expression<BoolSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRealSortBoolSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RealSort>).at(index: Expression<BoolSort>) = this() to index

@JvmName("storeRealSortBoolSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, RealSort>>).store(
    entry: Pair<Expression<RealSort>, Expression<BoolSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenRealSortBoolSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, RealSort>).then(
    entry: Pair<Expression<RealSort>, Expression<BoolSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atRealSortBoolSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RealSort>.at(index: (() -> Expression<BoolSort>)) = this to index()

@JvmName("storeRealSortBoolSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, RealSort>>.store(
    entry: (() -> Pair<Expression<RealSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenRealSortBoolSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, RealSort>.then(
    entry: (() -> Pair<Expression<RealSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atRealSortBoolSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RealSort>).at(index: (() -> Expression<BoolSort>)) = this() to index()

@JvmName("storeRealSortBoolSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, RealSort>>).store(
    entry: (() -> Pair<Expression<RealSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenRealSortBoolSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, RealSort>).then(
    entry: (() -> Pair<Expression<RealSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atRealSortBoolean")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<RealSort>.at(index: Boolean) = this to index.toSMTBool()

@JvmName("storeRealSortBoolean")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, RealSort>>.store(
    entry: Pair<Expression<RealSort>, Boolean>
) = ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("thenRealSortBoolean")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, RealSort>.then(entry: Pair<Expression<RealSort>, Boolean>) =
    ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("atRealSortBooleanLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Expression<RealSort>).at(index: Boolean) = this() to index.toSMTBool()

@JvmName("storeRealSortBooleanLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, RealSort>>).store(
    entry: Pair<Expression<RealSort>, Boolean>
) = ArrayStore(this(), entry.second.toSMTBool(), entry.first)

@JvmName("thenRealSortBooleanLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, RealSort>).then(entry: Pair<Expression<RealSort>, Boolean>) =
    ArrayStore(this(), entry.second.toSMTBool(), entry.first)

@JvmName("atRealSortBooleanLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<RealSort>.at(index: (() -> Boolean)) = this to index().toSMTBool()

@JvmName("storeRealSortBooleanLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, RealSort>>.store(
    entry: (() -> Pair<Expression<RealSort>, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this, second.toSMTBool(), first) }

@JvmName("thenRealSortBooleanLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, RealSort>.then(entry: (() -> Pair<Expression<RealSort>, Boolean>)) =
    entry().let { (first, second) -> ArrayStore(this, second.toSMTBool(), first) }

@JvmName("atRealSortBooleanLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RealSort>).at(index: (() -> Boolean)) = this() to index().toSMTBool()

@JvmName("storeRealSortBooleanLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, RealSort>>).store(
    entry: (() -> Pair<Expression<RealSort>, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this(), second.toSMTBool(), first) }

@JvmName("thenRealSortBooleanLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, RealSort>).then(
    entry: (() -> Pair<Expression<RealSort>, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this(), second.toSMTBool(), first) }

@JvmName("atRegLanSortBoolSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RegLanSort>.at(index: Expression<BoolSort>) = this to index

@JvmName("storeRegLanSortBoolSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, RegLanSort>>.store(
    entry: Pair<Expression<RegLanSort>, Expression<BoolSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRegLanSortBoolSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, RegLanSort>.then(
    entry: Pair<Expression<RegLanSort>, Expression<BoolSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRegLanSortBoolSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RegLanSort>).at(index: Expression<BoolSort>) = this() to index

@JvmName("storeRegLanSortBoolSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, RegLanSort>>).store(
    entry: Pair<Expression<RegLanSort>, Expression<BoolSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenRegLanSortBoolSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, RegLanSort>).then(
    entry: Pair<Expression<RegLanSort>, Expression<BoolSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atRegLanSortBoolSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RegLanSort>.at(index: (() -> Expression<BoolSort>)) = this to index()

@JvmName("storeRegLanSortBoolSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, RegLanSort>>.store(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenRegLanSortBoolSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, RegLanSort>.then(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atRegLanSortBoolSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RegLanSort>).at(index: (() -> Expression<BoolSort>)) = this() to index()

@JvmName("storeRegLanSortBoolSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, RegLanSort>>).store(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenRegLanSortBoolSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, RegLanSort>).then(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atRegLanSortBoolean")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<RegLanSort>.at(index: Boolean) = this to index.toSMTBool()

@JvmName("storeRegLanSortBoolean")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, RegLanSort>>.store(
    entry: Pair<Expression<RegLanSort>, Boolean>
) = ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("thenRegLanSortBoolean")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, RegLanSort>.then(entry: Pair<Expression<RegLanSort>, Boolean>) =
    ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("atRegLanSortBooleanLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Expression<RegLanSort>).at(index: Boolean) = this() to index.toSMTBool()

@JvmName("storeRegLanSortBooleanLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, RegLanSort>>).store(
    entry: Pair<Expression<RegLanSort>, Boolean>
) = ArrayStore(this(), entry.second.toSMTBool(), entry.first)

@JvmName("thenRegLanSortBooleanLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, RegLanSort>).then(
    entry: Pair<Expression<RegLanSort>, Boolean>
) = ArrayStore(this(), entry.second.toSMTBool(), entry.first)

@JvmName("atRegLanSortBooleanLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<RegLanSort>.at(index: (() -> Boolean)) = this to index().toSMTBool()

@JvmName("storeRegLanSortBooleanLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, RegLanSort>>.store(
    entry: (() -> Pair<Expression<RegLanSort>, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this, second.toSMTBool(), first) }

@JvmName("thenRegLanSortBooleanLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, RegLanSort>.then(
    entry: (() -> Pair<Expression<RegLanSort>, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this, second.toSMTBool(), first) }

@JvmName("atRegLanSortBooleanLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RegLanSort>).at(index: (() -> Boolean)) = this() to index().toSMTBool()

@JvmName("storeRegLanSortBooleanLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, RegLanSort>>).store(
    entry: (() -> Pair<Expression<RegLanSort>, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this(), second.toSMTBool(), first) }

@JvmName("thenRegLanSortBooleanLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, RegLanSort>).then(
    entry: (() -> Pair<Expression<RegLanSort>, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this(), second.toSMTBool(), first) }

@JvmName("atFPSortBoolSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<FPSort>.at(index: Expression<BoolSort>) = this to index

@JvmName("storeFPSortBoolSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, FPSort>>.store(
    entry: Pair<Expression<FPSort>, Expression<BoolSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenFPSortBoolSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, FPSort>.then(entry: Pair<Expression<FPSort>, Expression<BoolSort>>) =
    ArrayStore(this, entry.second, entry.first)

@JvmName("atFPSortBoolSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<FPSort>).at(index: Expression<BoolSort>) = this() to index

@JvmName("storeFPSortBoolSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, FPSort>>).store(
    entry: Pair<Expression<FPSort>, Expression<BoolSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenFPSortBoolSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, FPSort>).then(
    entry: Pair<Expression<FPSort>, Expression<BoolSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atFPSortBoolSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<FPSort>.at(index: (() -> Expression<BoolSort>)) = this to index()

@JvmName("storeFPSortBoolSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, FPSort>>.store(
    entry: (() -> Pair<Expression<FPSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenFPSortBoolSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, FPSort>.then(
    entry: (() -> Pair<Expression<FPSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atFPSortBoolSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<FPSort>).at(index: (() -> Expression<BoolSort>)) = this() to index()

@JvmName("storeFPSortBoolSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, FPSort>>).store(
    entry: (() -> Pair<Expression<FPSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenFPSortBoolSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, FPSort>).then(
    entry: (() -> Pair<Expression<FPSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atFPSortBoolean")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<FPSort>.at(index: Boolean) = this to index.toSMTBool()

@JvmName("storeFPSortBoolean")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, FPSort>>.store(entry: Pair<Expression<FPSort>, Boolean>) =
    ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("thenFPSortBoolean")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, FPSort>.then(entry: Pair<Expression<FPSort>, Boolean>) =
    ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("atFPSortBooleanLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Expression<FPSort>).at(index: Boolean) = this() to index.toSMTBool()

@JvmName("storeFPSortBooleanLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, FPSort>>).store(
    entry: Pair<Expression<FPSort>, Boolean>
) = ArrayStore(this(), entry.second.toSMTBool(), entry.first)

@JvmName("thenFPSortBooleanLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, FPSort>).then(entry: Pair<Expression<FPSort>, Boolean>) =
    ArrayStore(this(), entry.second.toSMTBool(), entry.first)

@JvmName("atFPSortBooleanLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<FPSort>.at(index: (() -> Boolean)) = this to index().toSMTBool()

@JvmName("storeFPSortBooleanLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, FPSort>>.store(
    entry: (() -> Pair<Expression<FPSort>, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this, second.toSMTBool(), first) }

@JvmName("thenFPSortBooleanLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, FPSort>.then(entry: (() -> Pair<Expression<FPSort>, Boolean>)) =
    entry().let { (first, second) -> ArrayStore(this, second.toSMTBool(), first) }

@JvmName("atFPSortBooleanLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<FPSort>).at(index: (() -> Boolean)) = this() to index().toSMTBool()

@JvmName("storeFPSortBooleanLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, FPSort>>).store(
    entry: (() -> Pair<Expression<FPSort>, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this(), second.toSMTBool(), first) }

@JvmName("thenFPSortBooleanLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, FPSort>).then(
    entry: (() -> Pair<Expression<FPSort>, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this(), second.toSMTBool(), first) }

@JvmName("atRoundingModeSortBoolSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RoundingModeSort>.at(index: Expression<BoolSort>) = this to index

@JvmName("storeRoundingModeSortBoolSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, RoundingModeSort>>.store(
    entry: Pair<Expression<RoundingModeSort>, Expression<BoolSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRoundingModeSortBoolSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, RoundingModeSort>.then(
    entry: Pair<Expression<RoundingModeSort>, Expression<BoolSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRoundingModeSortBoolSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RoundingModeSort>).at(index: Expression<BoolSort>) = this() to index

@JvmName("storeRoundingModeSortBoolSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, RoundingModeSort>>).store(
    entry: Pair<Expression<RoundingModeSort>, Expression<BoolSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenRoundingModeSortBoolSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, RoundingModeSort>).then(
    entry: Pair<Expression<RoundingModeSort>, Expression<BoolSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atRoundingModeSortBoolSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RoundingModeSort>.at(index: (() -> Expression<BoolSort>)) = this to index()

@JvmName("storeRoundingModeSortBoolSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, RoundingModeSort>>.store(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenRoundingModeSortBoolSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, RoundingModeSort>.then(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atRoundingModeSortBoolSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RoundingModeSort>).at(index: (() -> Expression<BoolSort>)) =
    this() to index()

@JvmName("storeRoundingModeSortBoolSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, RoundingModeSort>>).store(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenRoundingModeSortBoolSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, RoundingModeSort>).then(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atRoundingModeSortBoolean")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<RoundingModeSort>.at(index: Boolean) = this to index.toSMTBool()

@JvmName("storeRoundingModeSortBoolean")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, RoundingModeSort>>.store(
    entry: Pair<Expression<RoundingModeSort>, Boolean>
) = ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("thenRoundingModeSortBoolean")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, RoundingModeSort>.then(
    entry: Pair<Expression<RoundingModeSort>, Boolean>
) = ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("atRoundingModeSortBooleanLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Expression<RoundingModeSort>).at(index: Boolean) = this() to index.toSMTBool()

@JvmName("storeRoundingModeSortBooleanLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, RoundingModeSort>>).store(
    entry: Pair<Expression<RoundingModeSort>, Boolean>
) = ArrayStore(this(), entry.second.toSMTBool(), entry.first)

@JvmName("thenRoundingModeSortBooleanLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, RoundingModeSort>).then(
    entry: Pair<Expression<RoundingModeSort>, Boolean>
) = ArrayStore(this(), entry.second.toSMTBool(), entry.first)

@JvmName("atRoundingModeSortBooleanLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<RoundingModeSort>.at(index: (() -> Boolean)) = this to index().toSMTBool()

@JvmName("storeRoundingModeSortBooleanLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, RoundingModeSort>>.store(
    entry: (() -> Pair<Expression<RoundingModeSort>, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this, second.toSMTBool(), first) }

@JvmName("thenRoundingModeSortBooleanLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, RoundingModeSort>.then(
    entry: (() -> Pair<Expression<RoundingModeSort>, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this, second.toSMTBool(), first) }

@JvmName("atRoundingModeSortBooleanLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RoundingModeSort>).at(index: (() -> Boolean)) =
    this() to index().toSMTBool()

@JvmName("storeRoundingModeSortBooleanLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, RoundingModeSort>>).store(
    entry: (() -> Pair<Expression<RoundingModeSort>, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this(), second.toSMTBool(), first) }

@JvmName("thenRoundingModeSortBooleanLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, RoundingModeSort>).then(
    entry: (() -> Pair<Expression<RoundingModeSort>, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this(), second.toSMTBool(), first) }

@JvmName("atBitVecSortBoolSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BitVecSort>.at(index: Expression<BoolSort>) = this to index

@JvmName("storeBitVecSortBoolSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, BitVecSort>>.store(
    entry: Pair<Expression<BitVecSort>, Expression<BoolSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBitVecSortBoolSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, BitVecSort>.then(
    entry: Pair<Expression<BitVecSort>, Expression<BoolSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBitVecSortBoolSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BitVecSort>).at(index: Expression<BoolSort>) = this() to index

@JvmName("storeBitVecSortBoolSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, BitVecSort>>).store(
    entry: Pair<Expression<BitVecSort>, Expression<BoolSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenBitVecSortBoolSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, BitVecSort>).then(
    entry: Pair<Expression<BitVecSort>, Expression<BoolSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atBitVecSortBoolSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BitVecSort>.at(index: (() -> Expression<BoolSort>)) = this to index()

@JvmName("storeBitVecSortBoolSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, BitVecSort>>.store(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenBitVecSortBoolSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, BitVecSort>.then(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atBitVecSortBoolSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BitVecSort>).at(index: (() -> Expression<BoolSort>)) = this() to index()

@JvmName("storeBitVecSortBoolSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, BitVecSort>>).store(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenBitVecSortBoolSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, BitVecSort>).then(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<BoolSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atBitVecSortBoolean")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<BitVecSort>.at(index: Boolean) = this to index.toSMTBool()

@JvmName("storeBitVecSortBoolean")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, BitVecSort>>.store(
    entry: Pair<Expression<BitVecSort>, Boolean>
) = ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("thenBitVecSortBoolean")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, BitVecSort>.then(entry: Pair<Expression<BitVecSort>, Boolean>) =
    ArrayStore(this, entry.second.toSMTBool(), entry.first)

@JvmName("atBitVecSortBooleanLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Expression<BitVecSort>).at(index: Boolean) = this() to index.toSMTBool()

@JvmName("storeBitVecSortBooleanLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, BitVecSort>>).store(
    entry: Pair<Expression<BitVecSort>, Boolean>
) = ArrayStore(this(), entry.second.toSMTBool(), entry.first)

@JvmName("thenBitVecSortBooleanLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, BitVecSort>).then(
    entry: Pair<Expression<BitVecSort>, Boolean>
) = ArrayStore(this(), entry.second.toSMTBool(), entry.first)

@JvmName("atBitVecSortBooleanLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<BitVecSort>.at(index: (() -> Boolean)) = this to index().toSMTBool()

@JvmName("storeBitVecSortBooleanLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BoolSort, BitVecSort>>.store(
    entry: (() -> Pair<Expression<BitVecSort>, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this, second.toSMTBool(), first) }

@JvmName("thenBitVecSortBooleanLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BoolSort, BitVecSort>.then(
    entry: (() -> Pair<Expression<BitVecSort>, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this, second.toSMTBool(), first) }

@JvmName("atBitVecSortBooleanLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BitVecSort>).at(index: (() -> Boolean)) = this() to index().toSMTBool()

@JvmName("storeBitVecSortBooleanLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BoolSort, BitVecSort>>).store(
    entry: (() -> Pair<Expression<BitVecSort>, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this(), second.toSMTBool(), first) }

@JvmName("thenBitVecSortBooleanLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BoolSort, BitVecSort>).then(
    entry: (() -> Pair<Expression<BitVecSort>, Boolean>)
) = entry().let { (first, second) -> ArrayStore(this(), second.toSMTBool(), first) }

@JvmName("atIntSortStringSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<IntSort>.at(index: Expression<StringSort>) = this to index

@JvmName("storeIntSortStringSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, IntSort>>.store(
    entry: Pair<Expression<IntSort>, Expression<StringSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenIntSortStringSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, IntSort>.then(
    entry: Pair<Expression<IntSort>, Expression<StringSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atIntSortStringSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<IntSort>).at(index: Expression<StringSort>) = this() to index

@JvmName("storeIntSortStringSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, IntSort>>).store(
    entry: Pair<Expression<IntSort>, Expression<StringSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenIntSortStringSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, IntSort>).then(
    entry: Pair<Expression<IntSort>, Expression<StringSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atIntSortStringSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<IntSort>.at(index: (() -> Expression<StringSort>)) = this to index()

@JvmName("storeIntSortStringSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, IntSort>>.store(
    entry: (() -> Pair<Expression<IntSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenIntSortStringSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, IntSort>.then(
    entry: (() -> Pair<Expression<IntSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atIntSortStringSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<IntSort>).at(index: (() -> Expression<StringSort>)) = this() to index()

@JvmName("storeIntSortStringSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, IntSort>>).store(
    entry: (() -> Pair<Expression<IntSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenIntSortStringSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, IntSort>).then(
    entry: (() -> Pair<Expression<IntSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atIntSortString")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<IntSort>.at(index: String) = this to StringLiteral(index)

@JvmName("storeIntSortString")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, IntSort>>.store(
    entry: Pair<Expression<IntSort>, String>
) = ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("thenIntSortString")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, IntSort>.then(entry: Pair<Expression<IntSort>, String>) =
    ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("atIntSortStringLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Expression<IntSort>).at(index: String) = this() to StringLiteral(index)

@JvmName("storeIntSortStringLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, IntSort>>).store(
    entry: Pair<Expression<IntSort>, String>
) = ArrayStore(this(), StringLiteral(entry.second), entry.first)

@JvmName("thenIntSortStringLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, IntSort>).then(entry: Pair<Expression<IntSort>, String>) =
    ArrayStore(this(), StringLiteral(entry.second), entry.first)

@JvmName("atIntSortStringLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<IntSort>.at(index: (() -> String)) = this to StringLiteral(index())

@JvmName("storeIntSortStringLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, IntSort>>.store(
    entry: (() -> Pair<Expression<IntSort>, String>)
) = entry().let { (first, second) -> ArrayStore(this, StringLiteral(second), first) }

@JvmName("thenIntSortStringLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, IntSort>.then(entry: (() -> Pair<Expression<IntSort>, String>)) =
    entry().let { (first, second) -> ArrayStore(this, StringLiteral(second), first) }

@JvmName("atIntSortStringLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<IntSort>).at(index: (() -> String)) = this() to StringLiteral(index())

@JvmName("storeIntSortStringLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, IntSort>>).store(
    entry: (() -> Pair<Expression<IntSort>, String>)
) = entry().let { (first, second) -> ArrayStore(this(), StringLiteral(second), first) }

@JvmName("thenIntSortStringLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, IntSort>).then(
    entry: (() -> Pair<Expression<IntSort>, String>)
) = entry().let { (first, second) -> ArrayStore(this(), StringLiteral(second), first) }

@JvmName("atIntStringSort")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Int.at(index: Expression<StringSort>) = IntLiteral(this) to index

@JvmName("storeIntStringSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, IntSort>>.store(
    entry: Pair<Int, Expression<StringSort>>
) = ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("thenIntStringSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, IntSort>.then(entry: Pair<Int, Expression<StringSort>>) =
    ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("atIntStringSortLambdaValue")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Int).at(index: Expression<StringSort>) = IntLiteral(this()) to index

@JvmName("storeIntStringSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, IntSort>>).store(
    entry: Pair<Int, Expression<StringSort>>
) = ArrayStore(this(), entry.second, IntLiteral(entry.first))

@JvmName("thenIntStringSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, IntSort>).then(entry: Pair<Int, Expression<StringSort>>) =
    ArrayStore(this(), entry.second, IntLiteral(entry.first))

@JvmName("atIntStringSortLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Int.at(index: (() -> Expression<StringSort>)) = IntLiteral(this) to index()

@JvmName("storeIntStringSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, IntSort>>.store(
    entry: (() -> Pair<Int, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, IntLiteral(first)) }

@JvmName("thenIntStringSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, IntSort>.then(entry: (() -> Pair<Int, Expression<StringSort>>)) =
    entry().let { (first, second) -> ArrayStore(this, second, IntLiteral(first)) }

@JvmName("atIntStringSortLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Int).at(index: (() -> Expression<StringSort>)) = IntLiteral(this()) to index()

@JvmName("storeIntStringSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, IntSort>>).store(
    entry: (() -> Pair<Int, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, IntLiteral(first)) }

@JvmName("thenIntStringSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, IntSort>).then(
    entry: (() -> Pair<Int, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, IntLiteral(first)) }

@JvmName("atIntString")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Int.at(index: String) = IntLiteral(this) to StringLiteral(index)

@JvmName("storeIntString")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, IntSort>>.store(entry: Pair<Int, String>) =
    ArrayStore(this, StringLiteral(entry.second), IntLiteral(entry.first))

@JvmName("thenIntString")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, IntSort>.then(entry: Pair<Int, String>) =
    ArrayStore(this, StringLiteral(entry.second), IntLiteral(entry.first))

@JvmName("atIntStringLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Int).at(index: String) = IntLiteral(this()) to StringLiteral(index)

@JvmName("storeIntStringLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, IntSort>>).store(entry: Pair<Int, String>) =
    ArrayStore(this(), StringLiteral(entry.second), IntLiteral(entry.first))

@JvmName("thenIntStringLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, IntSort>).then(entry: Pair<Int, String>) =
    ArrayStore(this(), StringLiteral(entry.second), IntLiteral(entry.first))

@JvmName("atIntStringLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Int.at(index: (() -> String)) = IntLiteral(this) to StringLiteral(index())

@JvmName("storeIntStringLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, IntSort>>.store(entry: (() -> Pair<Int, String>)) =
    entry().let { (first, second) -> ArrayStore(this, StringLiteral(second), IntLiteral(first)) }

@JvmName("thenIntStringLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, IntSort>.then(entry: (() -> Pair<Int, String>)) =
    entry().let { (first, second) -> ArrayStore(this, StringLiteral(second), IntLiteral(first)) }

@JvmName("atIntStringLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Int).at(index: (() -> String)) = IntLiteral(this()) to StringLiteral(index())

@JvmName("storeIntStringLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, IntSort>>).store(
    entry: (() -> Pair<Int, String>)
) = entry().let { (first, second) -> ArrayStore(this(), StringLiteral(second), IntLiteral(first)) }

@JvmName("thenIntStringLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, IntSort>).then(entry: (() -> Pair<Int, String>)) =
    entry().let { (first, second) -> ArrayStore(this(), StringLiteral(second), IntLiteral(first)) }

@JvmName("atBoolSortStringSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BoolSort>.at(index: Expression<StringSort>) = this to index

@JvmName("storeBoolSortStringSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, BoolSort>>.store(
    entry: Pair<Expression<BoolSort>, Expression<StringSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBoolSortStringSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, BoolSort>.then(
    entry: Pair<Expression<BoolSort>, Expression<StringSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBoolSortStringSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BoolSort>).at(index: Expression<StringSort>) = this() to index

@JvmName("storeBoolSortStringSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, BoolSort>>).store(
    entry: Pair<Expression<BoolSort>, Expression<StringSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenBoolSortStringSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, BoolSort>).then(
    entry: Pair<Expression<BoolSort>, Expression<StringSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atBoolSortStringSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BoolSort>.at(index: (() -> Expression<StringSort>)) = this to index()

@JvmName("storeBoolSortStringSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, BoolSort>>.store(
    entry: (() -> Pair<Expression<BoolSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenBoolSortStringSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, BoolSort>.then(
    entry: (() -> Pair<Expression<BoolSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atBoolSortStringSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BoolSort>).at(index: (() -> Expression<StringSort>)) = this() to index()

@JvmName("storeBoolSortStringSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, BoolSort>>).store(
    entry: (() -> Pair<Expression<BoolSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenBoolSortStringSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, BoolSort>).then(
    entry: (() -> Pair<Expression<BoolSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atBoolSortString")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<BoolSort>.at(index: String) = this to StringLiteral(index)

@JvmName("storeBoolSortString")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, BoolSort>>.store(
    entry: Pair<Expression<BoolSort>, String>
) = ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("thenBoolSortString")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, BoolSort>.then(entry: Pair<Expression<BoolSort>, String>) =
    ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("atBoolSortStringLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Expression<BoolSort>).at(index: String) = this() to StringLiteral(index)

@JvmName("storeBoolSortStringLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, BoolSort>>).store(
    entry: Pair<Expression<BoolSort>, String>
) = ArrayStore(this(), StringLiteral(entry.second), entry.first)

@JvmName("thenBoolSortStringLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, BoolSort>).then(entry: Pair<Expression<BoolSort>, String>) =
    ArrayStore(this(), StringLiteral(entry.second), entry.first)

@JvmName("atBoolSortStringLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<BoolSort>.at(index: (() -> String)) = this to StringLiteral(index())

@JvmName("storeBoolSortStringLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, BoolSort>>.store(
    entry: (() -> Pair<Expression<BoolSort>, String>)
) = entry().let { (first, second) -> ArrayStore(this, StringLiteral(second), first) }

@JvmName("thenBoolSortStringLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, BoolSort>.then(entry: (() -> Pair<Expression<BoolSort>, String>)) =
    entry().let { (first, second) -> ArrayStore(this, StringLiteral(second), first) }

@JvmName("atBoolSortStringLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BoolSort>).at(index: (() -> String)) = this() to StringLiteral(index())

@JvmName("storeBoolSortStringLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, BoolSort>>).store(
    entry: (() -> Pair<Expression<BoolSort>, String>)
) = entry().let { (first, second) -> ArrayStore(this(), StringLiteral(second), first) }

@JvmName("thenBoolSortStringLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, BoolSort>).then(
    entry: (() -> Pair<Expression<BoolSort>, String>)
) = entry().let { (first, second) -> ArrayStore(this(), StringLiteral(second), first) }

@JvmName("atBooleanStringSort")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Boolean.at(index: Expression<StringSort>) = this.toSMTBool() to index

@JvmName("storeBooleanStringSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, BoolSort>>.store(
    entry: Pair<Boolean, Expression<StringSort>>
) = ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("thenBooleanStringSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, BoolSort>.then(entry: Pair<Boolean, Expression<StringSort>>) =
    ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("atBooleanStringSortLambdaValue")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Boolean).at(index: Expression<StringSort>) = this().toSMTBool() to index

@JvmName("storeBooleanStringSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, BoolSort>>).store(
    entry: Pair<Boolean, Expression<StringSort>>
) = ArrayStore(this(), entry.second, entry.first.toSMTBool())

@JvmName("thenBooleanStringSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, BoolSort>).then(
    entry: Pair<Boolean, Expression<StringSort>>
) = ArrayStore(this(), entry.second, entry.first.toSMTBool())

@JvmName("atBooleanStringSortLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Boolean.at(index: (() -> Expression<StringSort>)) = this.toSMTBool() to index()

@JvmName("storeBooleanStringSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, BoolSort>>.store(
    entry: (() -> Pair<Boolean, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first.toSMTBool()) }

@JvmName("thenBooleanStringSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, BoolSort>.then(
    entry: (() -> Pair<Boolean, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first.toSMTBool()) }

@JvmName("atBooleanStringSortLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Boolean).at(index: (() -> Expression<StringSort>)) = this().toSMTBool() to index()

@JvmName("storeBooleanStringSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, BoolSort>>).store(
    entry: (() -> Pair<Boolean, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first.toSMTBool()) }

@JvmName("thenBooleanStringSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, BoolSort>).then(
    entry: (() -> Pair<Boolean, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first.toSMTBool()) }

@JvmName("atBooleanString")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Boolean.at(index: String) = this.toSMTBool() to StringLiteral(index)

@JvmName("storeBooleanString")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, BoolSort>>.store(entry: Pair<Boolean, String>) =
    ArrayStore(this, StringLiteral(entry.second), entry.first.toSMTBool())

@JvmName("thenBooleanString")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, BoolSort>.then(entry: Pair<Boolean, String>) =
    ArrayStore(this, StringLiteral(entry.second), entry.first.toSMTBool())

@JvmName("atBooleanStringLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Boolean).at(index: String) = this().toSMTBool() to StringLiteral(index)

@JvmName("storeBooleanStringLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, BoolSort>>).store(entry: Pair<Boolean, String>) =
    ArrayStore(this(), StringLiteral(entry.second), entry.first.toSMTBool())

@JvmName("thenBooleanStringLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, BoolSort>).then(entry: Pair<Boolean, String>) =
    ArrayStore(this(), StringLiteral(entry.second), entry.first.toSMTBool())

@JvmName("atBooleanStringLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Boolean.at(index: (() -> String)) = this.toSMTBool() to StringLiteral(index())

@JvmName("storeBooleanStringLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, BoolSort>>.store(entry: (() -> Pair<Boolean, String>)) =
    entry().let { (first, second) -> ArrayStore(this, StringLiteral(second), first.toSMTBool()) }

@JvmName("thenBooleanStringLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, BoolSort>.then(entry: (() -> Pair<Boolean, String>)) =
    entry().let { (first, second) -> ArrayStore(this, StringLiteral(second), first.toSMTBool()) }

@JvmName("atBooleanStringLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Boolean).at(index: (() -> String)) = this().toSMTBool() to StringLiteral(index())

@JvmName("storeBooleanStringLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, BoolSort>>).store(
    entry: (() -> Pair<Boolean, String>)
) = entry().let { (first, second) -> ArrayStore(this(), StringLiteral(second), first.toSMTBool()) }

@JvmName("thenBooleanStringLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, BoolSort>).then(entry: (() -> Pair<Boolean, String>)) =
    entry().let { (first, second) -> ArrayStore(this(), StringLiteral(second), first.toSMTBool()) }

@JvmName("atStringSortStringSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<StringSort>.at(index: Expression<StringSort>) = this to index

@JvmName("storeStringSortStringSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, StringSort>>.store(
    entry: Pair<Expression<StringSort>, Expression<StringSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenStringSortStringSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, StringSort>.then(
    entry: Pair<Expression<StringSort>, Expression<StringSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atStringSortStringSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<StringSort>).at(index: Expression<StringSort>) = this() to index

@JvmName("storeStringSortStringSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, StringSort>>).store(
    entry: Pair<Expression<StringSort>, Expression<StringSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenStringSortStringSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, StringSort>).then(
    entry: Pair<Expression<StringSort>, Expression<StringSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atStringSortStringSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<StringSort>.at(index: (() -> Expression<StringSort>)) = this to index()

@JvmName("storeStringSortStringSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, StringSort>>.store(
    entry: (() -> Pair<Expression<StringSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenStringSortStringSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, StringSort>.then(
    entry: (() -> Pair<Expression<StringSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atStringSortStringSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<StringSort>).at(index: (() -> Expression<StringSort>)) =
    this() to index()

@JvmName("storeStringSortStringSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, StringSort>>).store(
    entry: (() -> Pair<Expression<StringSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenStringSortStringSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, StringSort>).then(
    entry: (() -> Pair<Expression<StringSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atStringSortString")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<StringSort>.at(index: String) = this to StringLiteral(index)

@JvmName("storeStringSortString")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, StringSort>>.store(
    entry: Pair<Expression<StringSort>, String>
) = ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("thenStringSortString")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, StringSort>.then(entry: Pair<Expression<StringSort>, String>) =
    ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("atStringSortStringLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Expression<StringSort>).at(index: String) = this() to StringLiteral(index)

@JvmName("storeStringSortStringLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, StringSort>>).store(
    entry: Pair<Expression<StringSort>, String>
) = ArrayStore(this(), StringLiteral(entry.second), entry.first)

@JvmName("thenStringSortStringLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, StringSort>).then(
    entry: Pair<Expression<StringSort>, String>
) = ArrayStore(this(), StringLiteral(entry.second), entry.first)

@JvmName("atStringSortStringLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<StringSort>.at(index: (() -> String)) = this to StringLiteral(index())

@JvmName("storeStringSortStringLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, StringSort>>.store(
    entry: (() -> Pair<Expression<StringSort>, String>)
) = entry().let { (first, second) -> ArrayStore(this, StringLiteral(second), first) }

@JvmName("thenStringSortStringLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, StringSort>.then(
    entry: (() -> Pair<Expression<StringSort>, String>)
) = entry().let { (first, second) -> ArrayStore(this, StringLiteral(second), first) }

@JvmName("atStringSortStringLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<StringSort>).at(index: (() -> String)) =
    this() to StringLiteral(index())

@JvmName("storeStringSortStringLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, StringSort>>).store(
    entry: (() -> Pair<Expression<StringSort>, String>)
) = entry().let { (first, second) -> ArrayStore(this(), StringLiteral(second), first) }

@JvmName("thenStringSortStringLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, StringSort>).then(
    entry: (() -> Pair<Expression<StringSort>, String>)
) = entry().let { (first, second) -> ArrayStore(this(), StringLiteral(second), first) }

@JvmName("atStringStringSort")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun String.at(index: Expression<StringSort>) = StringLiteral(this) to index

@JvmName("storeStringStringSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, StringSort>>.store(
    entry: Pair<String, Expression<StringSort>>
) = ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("thenStringStringSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, StringSort>.then(entry: Pair<String, Expression<StringSort>>) =
    ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("atStringStringSortLambdaValue")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> String).at(index: Expression<StringSort>) = StringLiteral(this()) to index

@JvmName("storeStringStringSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, StringSort>>).store(
    entry: Pair<String, Expression<StringSort>>
) = ArrayStore(this(), entry.second, StringLiteral(entry.first))

@JvmName("thenStringStringSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, StringSort>).then(
    entry: Pair<String, Expression<StringSort>>
) = ArrayStore(this(), entry.second, StringLiteral(entry.first))

@JvmName("atStringStringSortLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun String.at(index: (() -> Expression<StringSort>)) = StringLiteral(this) to index()

@JvmName("storeStringStringSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, StringSort>>.store(
    entry: (() -> Pair<String, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, StringLiteral(first)) }

@JvmName("thenStringStringSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, StringSort>.then(
    entry: (() -> Pair<String, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, StringLiteral(first)) }

@JvmName("atStringStringSortLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> String).at(index: (() -> Expression<StringSort>)) =
    StringLiteral(this()) to index()

@JvmName("storeStringStringSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, StringSort>>).store(
    entry: (() -> Pair<String, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, StringLiteral(first)) }

@JvmName("thenStringStringSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, StringSort>).then(
    entry: (() -> Pair<String, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, StringLiteral(first)) }

@JvmName("atStringString")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun String.at(index: String) = StringLiteral(this) to StringLiteral(index)

@JvmName("storeStringString")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, StringSort>>.store(entry: Pair<String, String>) =
    ArrayStore(this, StringLiteral(entry.second), StringLiteral(entry.first))

@JvmName("thenStringString")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, StringSort>.then(entry: Pair<String, String>) =
    ArrayStore(this, StringLiteral(entry.second), StringLiteral(entry.first))

@JvmName("atStringStringLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> String).at(index: String) = StringLiteral(this()) to StringLiteral(index)

@JvmName("storeStringStringLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, StringSort>>).store(entry: Pair<String, String>) =
    ArrayStore(this(), StringLiteral(entry.second), StringLiteral(entry.first))

@JvmName("thenStringStringLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, StringSort>).then(entry: Pair<String, String>) =
    ArrayStore(this(), StringLiteral(entry.second), StringLiteral(entry.first))

@JvmName("atStringStringLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun String.at(index: (() -> String)) = StringLiteral(this) to StringLiteral(index())

@JvmName("storeStringStringLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, StringSort>>.store(entry: (() -> Pair<String, String>)) =
    entry().let { (first, second) -> ArrayStore(this, StringLiteral(second), StringLiteral(first)) }

@JvmName("thenStringStringLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, StringSort>.then(entry: (() -> Pair<String, String>)) =
    entry().let { (first, second) -> ArrayStore(this, StringLiteral(second), StringLiteral(first)) }

@JvmName("atStringStringLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> String).at(index: (() -> String)) = StringLiteral(this()) to StringLiteral(index())

@JvmName("storeStringStringLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, StringSort>>).store(
    entry: (() -> Pair<String, String>)
) =
    entry().let { (first, second) ->
      ArrayStore(this(), StringLiteral(second), StringLiteral(first))
    }

@JvmName("thenStringStringLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, StringSort>).then(entry: (() -> Pair<String, String>)) =
    entry().let { (first, second) ->
      ArrayStore(this(), StringLiteral(second), StringLiteral(first))
    }

@JvmName("atRealSortStringSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RealSort>.at(index: Expression<StringSort>) = this to index

@JvmName("storeRealSortStringSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, RealSort>>.store(
    entry: Pair<Expression<RealSort>, Expression<StringSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRealSortStringSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, RealSort>.then(
    entry: Pair<Expression<RealSort>, Expression<StringSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRealSortStringSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RealSort>).at(index: Expression<StringSort>) = this() to index

@JvmName("storeRealSortStringSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, RealSort>>).store(
    entry: Pair<Expression<RealSort>, Expression<StringSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenRealSortStringSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, RealSort>).then(
    entry: Pair<Expression<RealSort>, Expression<StringSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atRealSortStringSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RealSort>.at(index: (() -> Expression<StringSort>)) = this to index()

@JvmName("storeRealSortStringSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, RealSort>>.store(
    entry: (() -> Pair<Expression<RealSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenRealSortStringSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, RealSort>.then(
    entry: (() -> Pair<Expression<RealSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atRealSortStringSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RealSort>).at(index: (() -> Expression<StringSort>)) = this() to index()

@JvmName("storeRealSortStringSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, RealSort>>).store(
    entry: (() -> Pair<Expression<RealSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenRealSortStringSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, RealSort>).then(
    entry: (() -> Pair<Expression<RealSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atRealSortString")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<RealSort>.at(index: String) = this to StringLiteral(index)

@JvmName("storeRealSortString")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, RealSort>>.store(
    entry: Pair<Expression<RealSort>, String>
) = ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("thenRealSortString")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, RealSort>.then(entry: Pair<Expression<RealSort>, String>) =
    ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("atRealSortStringLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Expression<RealSort>).at(index: String) = this() to StringLiteral(index)

@JvmName("storeRealSortStringLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, RealSort>>).store(
    entry: Pair<Expression<RealSort>, String>
) = ArrayStore(this(), StringLiteral(entry.second), entry.first)

@JvmName("thenRealSortStringLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, RealSort>).then(entry: Pair<Expression<RealSort>, String>) =
    ArrayStore(this(), StringLiteral(entry.second), entry.first)

@JvmName("atRealSortStringLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<RealSort>.at(index: (() -> String)) = this to StringLiteral(index())

@JvmName("storeRealSortStringLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, RealSort>>.store(
    entry: (() -> Pair<Expression<RealSort>, String>)
) = entry().let { (first, second) -> ArrayStore(this, StringLiteral(second), first) }

@JvmName("thenRealSortStringLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, RealSort>.then(entry: (() -> Pair<Expression<RealSort>, String>)) =
    entry().let { (first, second) -> ArrayStore(this, StringLiteral(second), first) }

@JvmName("atRealSortStringLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RealSort>).at(index: (() -> String)) = this() to StringLiteral(index())

@JvmName("storeRealSortStringLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, RealSort>>).store(
    entry: (() -> Pair<Expression<RealSort>, String>)
) = entry().let { (first, second) -> ArrayStore(this(), StringLiteral(second), first) }

@JvmName("thenRealSortStringLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, RealSort>).then(
    entry: (() -> Pair<Expression<RealSort>, String>)
) = entry().let { (first, second) -> ArrayStore(this(), StringLiteral(second), first) }

@JvmName("atRegLanSortStringSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RegLanSort>.at(index: Expression<StringSort>) = this to index

@JvmName("storeRegLanSortStringSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, RegLanSort>>.store(
    entry: Pair<Expression<RegLanSort>, Expression<StringSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRegLanSortStringSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, RegLanSort>.then(
    entry: Pair<Expression<RegLanSort>, Expression<StringSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRegLanSortStringSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RegLanSort>).at(index: Expression<StringSort>) = this() to index

@JvmName("storeRegLanSortStringSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, RegLanSort>>).store(
    entry: Pair<Expression<RegLanSort>, Expression<StringSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenRegLanSortStringSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, RegLanSort>).then(
    entry: Pair<Expression<RegLanSort>, Expression<StringSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atRegLanSortStringSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RegLanSort>.at(index: (() -> Expression<StringSort>)) = this to index()

@JvmName("storeRegLanSortStringSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, RegLanSort>>.store(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenRegLanSortStringSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, RegLanSort>.then(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atRegLanSortStringSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RegLanSort>).at(index: (() -> Expression<StringSort>)) =
    this() to index()

@JvmName("storeRegLanSortStringSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, RegLanSort>>).store(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenRegLanSortStringSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, RegLanSort>).then(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atRegLanSortString")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<RegLanSort>.at(index: String) = this to StringLiteral(index)

@JvmName("storeRegLanSortString")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, RegLanSort>>.store(
    entry: Pair<Expression<RegLanSort>, String>
) = ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("thenRegLanSortString")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, RegLanSort>.then(entry: Pair<Expression<RegLanSort>, String>) =
    ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("atRegLanSortStringLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Expression<RegLanSort>).at(index: String) = this() to StringLiteral(index)

@JvmName("storeRegLanSortStringLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, RegLanSort>>).store(
    entry: Pair<Expression<RegLanSort>, String>
) = ArrayStore(this(), StringLiteral(entry.second), entry.first)

@JvmName("thenRegLanSortStringLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, RegLanSort>).then(
    entry: Pair<Expression<RegLanSort>, String>
) = ArrayStore(this(), StringLiteral(entry.second), entry.first)

@JvmName("atRegLanSortStringLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<RegLanSort>.at(index: (() -> String)) = this to StringLiteral(index())

@JvmName("storeRegLanSortStringLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, RegLanSort>>.store(
    entry: (() -> Pair<Expression<RegLanSort>, String>)
) = entry().let { (first, second) -> ArrayStore(this, StringLiteral(second), first) }

@JvmName("thenRegLanSortStringLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, RegLanSort>.then(
    entry: (() -> Pair<Expression<RegLanSort>, String>)
) = entry().let { (first, second) -> ArrayStore(this, StringLiteral(second), first) }

@JvmName("atRegLanSortStringLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RegLanSort>).at(index: (() -> String)) =
    this() to StringLiteral(index())

@JvmName("storeRegLanSortStringLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, RegLanSort>>).store(
    entry: (() -> Pair<Expression<RegLanSort>, String>)
) = entry().let { (first, second) -> ArrayStore(this(), StringLiteral(second), first) }

@JvmName("thenRegLanSortStringLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, RegLanSort>).then(
    entry: (() -> Pair<Expression<RegLanSort>, String>)
) = entry().let { (first, second) -> ArrayStore(this(), StringLiteral(second), first) }

@JvmName("atFPSortStringSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<FPSort>.at(index: Expression<StringSort>) = this to index

@JvmName("storeFPSortStringSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, FPSort>>.store(
    entry: Pair<Expression<FPSort>, Expression<StringSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenFPSortStringSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, FPSort>.then(
    entry: Pair<Expression<FPSort>, Expression<StringSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atFPSortStringSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<FPSort>).at(index: Expression<StringSort>) = this() to index

@JvmName("storeFPSortStringSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, FPSort>>).store(
    entry: Pair<Expression<FPSort>, Expression<StringSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenFPSortStringSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, FPSort>).then(
    entry: Pair<Expression<FPSort>, Expression<StringSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atFPSortStringSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<FPSort>.at(index: (() -> Expression<StringSort>)) = this to index()

@JvmName("storeFPSortStringSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, FPSort>>.store(
    entry: (() -> Pair<Expression<FPSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenFPSortStringSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, FPSort>.then(
    entry: (() -> Pair<Expression<FPSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atFPSortStringSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<FPSort>).at(index: (() -> Expression<StringSort>)) = this() to index()

@JvmName("storeFPSortStringSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, FPSort>>).store(
    entry: (() -> Pair<Expression<FPSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenFPSortStringSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, FPSort>).then(
    entry: (() -> Pair<Expression<FPSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atFPSortString")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<FPSort>.at(index: String) = this to StringLiteral(index)

@JvmName("storeFPSortString")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, FPSort>>.store(entry: Pair<Expression<FPSort>, String>) =
    ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("thenFPSortString")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, FPSort>.then(entry: Pair<Expression<FPSort>, String>) =
    ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("atFPSortStringLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Expression<FPSort>).at(index: String) = this() to StringLiteral(index)

@JvmName("storeFPSortStringLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, FPSort>>).store(
    entry: Pair<Expression<FPSort>, String>
) = ArrayStore(this(), StringLiteral(entry.second), entry.first)

@JvmName("thenFPSortStringLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, FPSort>).then(entry: Pair<Expression<FPSort>, String>) =
    ArrayStore(this(), StringLiteral(entry.second), entry.first)

@JvmName("atFPSortStringLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<FPSort>.at(index: (() -> String)) = this to StringLiteral(index())

@JvmName("storeFPSortStringLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, FPSort>>.store(
    entry: (() -> Pair<Expression<FPSort>, String>)
) = entry().let { (first, second) -> ArrayStore(this, StringLiteral(second), first) }

@JvmName("thenFPSortStringLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, FPSort>.then(entry: (() -> Pair<Expression<FPSort>, String>)) =
    entry().let { (first, second) -> ArrayStore(this, StringLiteral(second), first) }

@JvmName("atFPSortStringLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<FPSort>).at(index: (() -> String)) = this() to StringLiteral(index())

@JvmName("storeFPSortStringLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, FPSort>>).store(
    entry: (() -> Pair<Expression<FPSort>, String>)
) = entry().let { (first, second) -> ArrayStore(this(), StringLiteral(second), first) }

@JvmName("thenFPSortStringLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, FPSort>).then(
    entry: (() -> Pair<Expression<FPSort>, String>)
) = entry().let { (first, second) -> ArrayStore(this(), StringLiteral(second), first) }

@JvmName("atRoundingModeSortStringSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RoundingModeSort>.at(index: Expression<StringSort>) = this to index

@JvmName("storeRoundingModeSortStringSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, RoundingModeSort>>.store(
    entry: Pair<Expression<RoundingModeSort>, Expression<StringSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRoundingModeSortStringSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, RoundingModeSort>.then(
    entry: Pair<Expression<RoundingModeSort>, Expression<StringSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRoundingModeSortStringSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RoundingModeSort>).at(index: Expression<StringSort>) = this() to index

@JvmName("storeRoundingModeSortStringSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, RoundingModeSort>>).store(
    entry: Pair<Expression<RoundingModeSort>, Expression<StringSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenRoundingModeSortStringSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, RoundingModeSort>).then(
    entry: Pair<Expression<RoundingModeSort>, Expression<StringSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atRoundingModeSortStringSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RoundingModeSort>.at(index: (() -> Expression<StringSort>)) = this to index()

@JvmName("storeRoundingModeSortStringSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, RoundingModeSort>>.store(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenRoundingModeSortStringSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, RoundingModeSort>.then(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atRoundingModeSortStringSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RoundingModeSort>).at(index: (() -> Expression<StringSort>)) =
    this() to index()

@JvmName("storeRoundingModeSortStringSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, RoundingModeSort>>).store(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenRoundingModeSortStringSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, RoundingModeSort>).then(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atRoundingModeSortString")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<RoundingModeSort>.at(index: String) = this to StringLiteral(index)

@JvmName("storeRoundingModeSortString")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, RoundingModeSort>>.store(
    entry: Pair<Expression<RoundingModeSort>, String>
) = ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("thenRoundingModeSortString")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, RoundingModeSort>.then(
    entry: Pair<Expression<RoundingModeSort>, String>
) = ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("atRoundingModeSortStringLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Expression<RoundingModeSort>).at(index: String) = this() to StringLiteral(index)

@JvmName("storeRoundingModeSortStringLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, RoundingModeSort>>).store(
    entry: Pair<Expression<RoundingModeSort>, String>
) = ArrayStore(this(), StringLiteral(entry.second), entry.first)

@JvmName("thenRoundingModeSortStringLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, RoundingModeSort>).then(
    entry: Pair<Expression<RoundingModeSort>, String>
) = ArrayStore(this(), StringLiteral(entry.second), entry.first)

@JvmName("atRoundingModeSortStringLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<RoundingModeSort>.at(index: (() -> String)) = this to StringLiteral(index())

@JvmName("storeRoundingModeSortStringLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, RoundingModeSort>>.store(
    entry: (() -> Pair<Expression<RoundingModeSort>, String>)
) = entry().let { (first, second) -> ArrayStore(this, StringLiteral(second), first) }

@JvmName("thenRoundingModeSortStringLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, RoundingModeSort>.then(
    entry: (() -> Pair<Expression<RoundingModeSort>, String>)
) = entry().let { (first, second) -> ArrayStore(this, StringLiteral(second), first) }

@JvmName("atRoundingModeSortStringLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RoundingModeSort>).at(index: (() -> String)) =
    this() to StringLiteral(index())

@JvmName("storeRoundingModeSortStringLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, RoundingModeSort>>).store(
    entry: (() -> Pair<Expression<RoundingModeSort>, String>)
) = entry().let { (first, second) -> ArrayStore(this(), StringLiteral(second), first) }

@JvmName("thenRoundingModeSortStringLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, RoundingModeSort>).then(
    entry: (() -> Pair<Expression<RoundingModeSort>, String>)
) = entry().let { (first, second) -> ArrayStore(this(), StringLiteral(second), first) }

@JvmName("atBitVecSortStringSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BitVecSort>.at(index: Expression<StringSort>) = this to index

@JvmName("storeBitVecSortStringSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, BitVecSort>>.store(
    entry: Pair<Expression<BitVecSort>, Expression<StringSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBitVecSortStringSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, BitVecSort>.then(
    entry: Pair<Expression<BitVecSort>, Expression<StringSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBitVecSortStringSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BitVecSort>).at(index: Expression<StringSort>) = this() to index

@JvmName("storeBitVecSortStringSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, BitVecSort>>).store(
    entry: Pair<Expression<BitVecSort>, Expression<StringSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenBitVecSortStringSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, BitVecSort>).then(
    entry: Pair<Expression<BitVecSort>, Expression<StringSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atBitVecSortStringSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BitVecSort>.at(index: (() -> Expression<StringSort>)) = this to index()

@JvmName("storeBitVecSortStringSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, BitVecSort>>.store(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenBitVecSortStringSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, BitVecSort>.then(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atBitVecSortStringSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BitVecSort>).at(index: (() -> Expression<StringSort>)) =
    this() to index()

@JvmName("storeBitVecSortStringSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, BitVecSort>>).store(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenBitVecSortStringSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, BitVecSort>).then(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<StringSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atBitVecSortString")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<BitVecSort>.at(index: String) = this to StringLiteral(index)

@JvmName("storeBitVecSortString")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, BitVecSort>>.store(
    entry: Pair<Expression<BitVecSort>, String>
) = ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("thenBitVecSortString")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, BitVecSort>.then(entry: Pair<Expression<BitVecSort>, String>) =
    ArrayStore(this, StringLiteral(entry.second), entry.first)

@JvmName("atBitVecSortStringLambdaArray")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Expression<BitVecSort>).at(index: String) = this() to StringLiteral(index)

@JvmName("storeBitVecSortStringLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, BitVecSort>>).store(
    entry: Pair<Expression<BitVecSort>, String>
) = ArrayStore(this(), StringLiteral(entry.second), entry.first)

@JvmName("thenBitVecSortStringLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, BitVecSort>).then(
    entry: Pair<Expression<BitVecSort>, String>
) = ArrayStore(this(), StringLiteral(entry.second), entry.first)

@JvmName("atBitVecSortStringLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Expression<BitVecSort>.at(index: (() -> String)) = this to StringLiteral(index())

@JvmName("storeBitVecSortStringLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<StringSort, BitVecSort>>.store(
    entry: (() -> Pair<Expression<BitVecSort>, String>)
) = entry().let { (first, second) -> ArrayStore(this, StringLiteral(second), first) }

@JvmName("thenBitVecSortStringLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<StringSort, BitVecSort>.then(
    entry: (() -> Pair<Expression<BitVecSort>, String>)
) = entry().let { (first, second) -> ArrayStore(this, StringLiteral(second), first) }

@JvmName("atBitVecSortStringLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BitVecSort>).at(index: (() -> String)) =
    this() to StringLiteral(index())

@JvmName("storeBitVecSortStringLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<StringSort, BitVecSort>>).store(
    entry: (() -> Pair<Expression<BitVecSort>, String>)
) = entry().let { (first, second) -> ArrayStore(this(), StringLiteral(second), first) }

@JvmName("thenBitVecSortStringLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<StringSort, BitVecSort>).then(
    entry: (() -> Pair<Expression<BitVecSort>, String>)
) = entry().let { (first, second) -> ArrayStore(this(), StringLiteral(second), first) }

@JvmName("atIntSortRealSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<IntSort>.at(index: Expression<RealSort>) = this to index

@JvmName("storeIntSortRealSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RealSort, IntSort>>.store(
    entry: Pair<Expression<IntSort>, Expression<RealSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenIntSortRealSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RealSort, IntSort>.then(
    entry: Pair<Expression<IntSort>, Expression<RealSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atIntSortRealSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<IntSort>).at(index: Expression<RealSort>) = this() to index

@JvmName("storeIntSortRealSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RealSort, IntSort>>).store(
    entry: Pair<Expression<IntSort>, Expression<RealSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenIntSortRealSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RealSort, IntSort>).then(
    entry: Pair<Expression<IntSort>, Expression<RealSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atIntSortRealSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<IntSort>.at(index: (() -> Expression<RealSort>)) = this to index()

@JvmName("storeIntSortRealSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RealSort, IntSort>>.store(
    entry: (() -> Pair<Expression<IntSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenIntSortRealSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RealSort, IntSort>.then(
    entry: (() -> Pair<Expression<IntSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atIntSortRealSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<IntSort>).at(index: (() -> Expression<RealSort>)) = this() to index()

@JvmName("storeIntSortRealSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RealSort, IntSort>>).store(
    entry: (() -> Pair<Expression<IntSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenIntSortRealSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RealSort, IntSort>).then(
    entry: (() -> Pair<Expression<IntSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atIntRealSort")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Int.at(index: Expression<RealSort>) = IntLiteral(this) to index

@JvmName("storeIntRealSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RealSort, IntSort>>.store(entry: Pair<Int, Expression<RealSort>>) =
    ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("thenIntRealSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RealSort, IntSort>.then(entry: Pair<Int, Expression<RealSort>>) =
    ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("atIntRealSortLambdaValue")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Int).at(index: Expression<RealSort>) = IntLiteral(this()) to index

@JvmName("storeIntRealSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RealSort, IntSort>>).store(
    entry: Pair<Int, Expression<RealSort>>
) = ArrayStore(this(), entry.second, IntLiteral(entry.first))

@JvmName("thenIntRealSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RealSort, IntSort>).then(entry: Pair<Int, Expression<RealSort>>) =
    ArrayStore(this(), entry.second, IntLiteral(entry.first))

@JvmName("atIntRealSortLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Int.at(index: (() -> Expression<RealSort>)) = IntLiteral(this) to index()

@JvmName("storeIntRealSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RealSort, IntSort>>.store(
    entry: (() -> Pair<Int, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, IntLiteral(first)) }

@JvmName("thenIntRealSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RealSort, IntSort>.then(entry: (() -> Pair<Int, Expression<RealSort>>)) =
    entry().let { (first, second) -> ArrayStore(this, second, IntLiteral(first)) }

@JvmName("atIntRealSortLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Int).at(index: (() -> Expression<RealSort>)) = IntLiteral(this()) to index()

@JvmName("storeIntRealSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RealSort, IntSort>>).store(
    entry: (() -> Pair<Int, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, IntLiteral(first)) }

@JvmName("thenIntRealSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RealSort, IntSort>).then(
    entry: (() -> Pair<Int, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, IntLiteral(first)) }

@JvmName("atBoolSortRealSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BoolSort>.at(index: Expression<RealSort>) = this to index

@JvmName("storeBoolSortRealSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RealSort, BoolSort>>.store(
    entry: Pair<Expression<BoolSort>, Expression<RealSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBoolSortRealSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RealSort, BoolSort>.then(
    entry: Pair<Expression<BoolSort>, Expression<RealSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBoolSortRealSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BoolSort>).at(index: Expression<RealSort>) = this() to index

@JvmName("storeBoolSortRealSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RealSort, BoolSort>>).store(
    entry: Pair<Expression<BoolSort>, Expression<RealSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenBoolSortRealSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RealSort, BoolSort>).then(
    entry: Pair<Expression<BoolSort>, Expression<RealSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atBoolSortRealSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BoolSort>.at(index: (() -> Expression<RealSort>)) = this to index()

@JvmName("storeBoolSortRealSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RealSort, BoolSort>>.store(
    entry: (() -> Pair<Expression<BoolSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenBoolSortRealSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RealSort, BoolSort>.then(
    entry: (() -> Pair<Expression<BoolSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atBoolSortRealSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BoolSort>).at(index: (() -> Expression<RealSort>)) = this() to index()

@JvmName("storeBoolSortRealSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RealSort, BoolSort>>).store(
    entry: (() -> Pair<Expression<BoolSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenBoolSortRealSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RealSort, BoolSort>).then(
    entry: (() -> Pair<Expression<BoolSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atBooleanRealSort")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Boolean.at(index: Expression<RealSort>) = this.toSMTBool() to index

@JvmName("storeBooleanRealSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RealSort, BoolSort>>.store(
    entry: Pair<Boolean, Expression<RealSort>>
) = ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("thenBooleanRealSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RealSort, BoolSort>.then(entry: Pair<Boolean, Expression<RealSort>>) =
    ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("atBooleanRealSortLambdaValue")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Boolean).at(index: Expression<RealSort>) = this().toSMTBool() to index

@JvmName("storeBooleanRealSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RealSort, BoolSort>>).store(
    entry: Pair<Boolean, Expression<RealSort>>
) = ArrayStore(this(), entry.second, entry.first.toSMTBool())

@JvmName("thenBooleanRealSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RealSort, BoolSort>).then(entry: Pair<Boolean, Expression<RealSort>>) =
    ArrayStore(this(), entry.second, entry.first.toSMTBool())

@JvmName("atBooleanRealSortLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Boolean.at(index: (() -> Expression<RealSort>)) = this.toSMTBool() to index()

@JvmName("storeBooleanRealSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RealSort, BoolSort>>.store(
    entry: (() -> Pair<Boolean, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first.toSMTBool()) }

@JvmName("thenBooleanRealSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RealSort, BoolSort>.then(entry: (() -> Pair<Boolean, Expression<RealSort>>)) =
    entry().let { (first, second) -> ArrayStore(this, second, first.toSMTBool()) }

@JvmName("atBooleanRealSortLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Boolean).at(index: (() -> Expression<RealSort>)) = this().toSMTBool() to index()

@JvmName("storeBooleanRealSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RealSort, BoolSort>>).store(
    entry: (() -> Pair<Boolean, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first.toSMTBool()) }

@JvmName("thenBooleanRealSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RealSort, BoolSort>).then(
    entry: (() -> Pair<Boolean, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first.toSMTBool()) }

@JvmName("atStringSortRealSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<StringSort>.at(index: Expression<RealSort>) = this to index

@JvmName("storeStringSortRealSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RealSort, StringSort>>.store(
    entry: Pair<Expression<StringSort>, Expression<RealSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenStringSortRealSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RealSort, StringSort>.then(
    entry: Pair<Expression<StringSort>, Expression<RealSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atStringSortRealSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<StringSort>).at(index: Expression<RealSort>) = this() to index

@JvmName("storeStringSortRealSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RealSort, StringSort>>).store(
    entry: Pair<Expression<StringSort>, Expression<RealSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenStringSortRealSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RealSort, StringSort>).then(
    entry: Pair<Expression<StringSort>, Expression<RealSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atStringSortRealSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<StringSort>.at(index: (() -> Expression<RealSort>)) = this to index()

@JvmName("storeStringSortRealSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RealSort, StringSort>>.store(
    entry: (() -> Pair<Expression<StringSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenStringSortRealSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RealSort, StringSort>.then(
    entry: (() -> Pair<Expression<StringSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atStringSortRealSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<StringSort>).at(index: (() -> Expression<RealSort>)) = this() to index()

@JvmName("storeStringSortRealSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RealSort, StringSort>>).store(
    entry: (() -> Pair<Expression<StringSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenStringSortRealSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RealSort, StringSort>).then(
    entry: (() -> Pair<Expression<StringSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atStringRealSort")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun String.at(index: Expression<RealSort>) = StringLiteral(this) to index

@JvmName("storeStringRealSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RealSort, StringSort>>.store(
    entry: Pair<String, Expression<RealSort>>
) = ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("thenStringRealSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RealSort, StringSort>.then(entry: Pair<String, Expression<RealSort>>) =
    ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("atStringRealSortLambdaValue")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> String).at(index: Expression<RealSort>) = StringLiteral(this()) to index

@JvmName("storeStringRealSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RealSort, StringSort>>).store(
    entry: Pair<String, Expression<RealSort>>
) = ArrayStore(this(), entry.second, StringLiteral(entry.first))

@JvmName("thenStringRealSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RealSort, StringSort>).then(entry: Pair<String, Expression<RealSort>>) =
    ArrayStore(this(), entry.second, StringLiteral(entry.first))

@JvmName("atStringRealSortLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun String.at(index: (() -> Expression<RealSort>)) = StringLiteral(this) to index()

@JvmName("storeStringRealSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RealSort, StringSort>>.store(
    entry: (() -> Pair<String, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, StringLiteral(first)) }

@JvmName("thenStringRealSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RealSort, StringSort>.then(entry: (() -> Pair<String, Expression<RealSort>>)) =
    entry().let { (first, second) -> ArrayStore(this, second, StringLiteral(first)) }

@JvmName("atStringRealSortLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> String).at(index: (() -> Expression<RealSort>)) = StringLiteral(this()) to index()

@JvmName("storeStringRealSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RealSort, StringSort>>).store(
    entry: (() -> Pair<String, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, StringLiteral(first)) }

@JvmName("thenStringRealSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RealSort, StringSort>).then(
    entry: (() -> Pair<String, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, StringLiteral(first)) }

@JvmName("atRealSortRealSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RealSort>.at(index: Expression<RealSort>) = this to index

@JvmName("storeRealSortRealSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RealSort, RealSort>>.store(
    entry: Pair<Expression<RealSort>, Expression<RealSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRealSortRealSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RealSort, RealSort>.then(
    entry: Pair<Expression<RealSort>, Expression<RealSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRealSortRealSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RealSort>).at(index: Expression<RealSort>) = this() to index

@JvmName("storeRealSortRealSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RealSort, RealSort>>).store(
    entry: Pair<Expression<RealSort>, Expression<RealSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenRealSortRealSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RealSort, RealSort>).then(
    entry: Pair<Expression<RealSort>, Expression<RealSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atRealSortRealSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RealSort>.at(index: (() -> Expression<RealSort>)) = this to index()

@JvmName("storeRealSortRealSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RealSort, RealSort>>.store(
    entry: (() -> Pair<Expression<RealSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenRealSortRealSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RealSort, RealSort>.then(
    entry: (() -> Pair<Expression<RealSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atRealSortRealSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RealSort>).at(index: (() -> Expression<RealSort>)) = this() to index()

@JvmName("storeRealSortRealSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RealSort, RealSort>>).store(
    entry: (() -> Pair<Expression<RealSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenRealSortRealSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RealSort, RealSort>).then(
    entry: (() -> Pair<Expression<RealSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atRegLanSortRealSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RegLanSort>.at(index: Expression<RealSort>) = this to index

@JvmName("storeRegLanSortRealSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RealSort, RegLanSort>>.store(
    entry: Pair<Expression<RegLanSort>, Expression<RealSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRegLanSortRealSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RealSort, RegLanSort>.then(
    entry: Pair<Expression<RegLanSort>, Expression<RealSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRegLanSortRealSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RegLanSort>).at(index: Expression<RealSort>) = this() to index

@JvmName("storeRegLanSortRealSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RealSort, RegLanSort>>).store(
    entry: Pair<Expression<RegLanSort>, Expression<RealSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenRegLanSortRealSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RealSort, RegLanSort>).then(
    entry: Pair<Expression<RegLanSort>, Expression<RealSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atRegLanSortRealSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RegLanSort>.at(index: (() -> Expression<RealSort>)) = this to index()

@JvmName("storeRegLanSortRealSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RealSort, RegLanSort>>.store(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenRegLanSortRealSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RealSort, RegLanSort>.then(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atRegLanSortRealSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RegLanSort>).at(index: (() -> Expression<RealSort>)) = this() to index()

@JvmName("storeRegLanSortRealSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RealSort, RegLanSort>>).store(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenRegLanSortRealSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RealSort, RegLanSort>).then(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atFPSortRealSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<FPSort>.at(index: Expression<RealSort>) = this to index

@JvmName("storeFPSortRealSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RealSort, FPSort>>.store(
    entry: Pair<Expression<FPSort>, Expression<RealSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenFPSortRealSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RealSort, FPSort>.then(entry: Pair<Expression<FPSort>, Expression<RealSort>>) =
    ArrayStore(this, entry.second, entry.first)

@JvmName("atFPSortRealSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<FPSort>).at(index: Expression<RealSort>) = this() to index

@JvmName("storeFPSortRealSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RealSort, FPSort>>).store(
    entry: Pair<Expression<FPSort>, Expression<RealSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenFPSortRealSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RealSort, FPSort>).then(
    entry: Pair<Expression<FPSort>, Expression<RealSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atFPSortRealSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<FPSort>.at(index: (() -> Expression<RealSort>)) = this to index()

@JvmName("storeFPSortRealSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RealSort, FPSort>>.store(
    entry: (() -> Pair<Expression<FPSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenFPSortRealSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RealSort, FPSort>.then(
    entry: (() -> Pair<Expression<FPSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atFPSortRealSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<FPSort>).at(index: (() -> Expression<RealSort>)) = this() to index()

@JvmName("storeFPSortRealSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RealSort, FPSort>>).store(
    entry: (() -> Pair<Expression<FPSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenFPSortRealSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RealSort, FPSort>).then(
    entry: (() -> Pair<Expression<FPSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atRoundingModeSortRealSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RoundingModeSort>.at(index: Expression<RealSort>) = this to index

@JvmName("storeRoundingModeSortRealSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RealSort, RoundingModeSort>>.store(
    entry: Pair<Expression<RoundingModeSort>, Expression<RealSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRoundingModeSortRealSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RealSort, RoundingModeSort>.then(
    entry: Pair<Expression<RoundingModeSort>, Expression<RealSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRoundingModeSortRealSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RoundingModeSort>).at(index: Expression<RealSort>) = this() to index

@JvmName("storeRoundingModeSortRealSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RealSort, RoundingModeSort>>).store(
    entry: Pair<Expression<RoundingModeSort>, Expression<RealSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenRoundingModeSortRealSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RealSort, RoundingModeSort>).then(
    entry: Pair<Expression<RoundingModeSort>, Expression<RealSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atRoundingModeSortRealSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RoundingModeSort>.at(index: (() -> Expression<RealSort>)) = this to index()

@JvmName("storeRoundingModeSortRealSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RealSort, RoundingModeSort>>.store(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenRoundingModeSortRealSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RealSort, RoundingModeSort>.then(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atRoundingModeSortRealSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RoundingModeSort>).at(index: (() -> Expression<RealSort>)) =
    this() to index()

@JvmName("storeRoundingModeSortRealSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RealSort, RoundingModeSort>>).store(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenRoundingModeSortRealSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RealSort, RoundingModeSort>).then(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atBitVecSortRealSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BitVecSort>.at(index: Expression<RealSort>) = this to index

@JvmName("storeBitVecSortRealSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RealSort, BitVecSort>>.store(
    entry: Pair<Expression<BitVecSort>, Expression<RealSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBitVecSortRealSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RealSort, BitVecSort>.then(
    entry: Pair<Expression<BitVecSort>, Expression<RealSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBitVecSortRealSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BitVecSort>).at(index: Expression<RealSort>) = this() to index

@JvmName("storeBitVecSortRealSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RealSort, BitVecSort>>).store(
    entry: Pair<Expression<BitVecSort>, Expression<RealSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenBitVecSortRealSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RealSort, BitVecSort>).then(
    entry: Pair<Expression<BitVecSort>, Expression<RealSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atBitVecSortRealSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BitVecSort>.at(index: (() -> Expression<RealSort>)) = this to index()

@JvmName("storeBitVecSortRealSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RealSort, BitVecSort>>.store(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenBitVecSortRealSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RealSort, BitVecSort>.then(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atBitVecSortRealSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BitVecSort>).at(index: (() -> Expression<RealSort>)) = this() to index()

@JvmName("storeBitVecSortRealSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RealSort, BitVecSort>>).store(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenBitVecSortRealSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RealSort, BitVecSort>).then(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<RealSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atIntSortRegLanSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<IntSort>.at(index: Expression<RegLanSort>) = this to index

@JvmName("storeIntSortRegLanSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RegLanSort, IntSort>>.store(
    entry: Pair<Expression<IntSort>, Expression<RegLanSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenIntSortRegLanSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RegLanSort, IntSort>.then(
    entry: Pair<Expression<IntSort>, Expression<RegLanSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atIntSortRegLanSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<IntSort>).at(index: Expression<RegLanSort>) = this() to index

@JvmName("storeIntSortRegLanSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RegLanSort, IntSort>>).store(
    entry: Pair<Expression<IntSort>, Expression<RegLanSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenIntSortRegLanSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RegLanSort, IntSort>).then(
    entry: Pair<Expression<IntSort>, Expression<RegLanSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atIntSortRegLanSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<IntSort>.at(index: (() -> Expression<RegLanSort>)) = this to index()

@JvmName("storeIntSortRegLanSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RegLanSort, IntSort>>.store(
    entry: (() -> Pair<Expression<IntSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenIntSortRegLanSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RegLanSort, IntSort>.then(
    entry: (() -> Pair<Expression<IntSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atIntSortRegLanSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<IntSort>).at(index: (() -> Expression<RegLanSort>)) = this() to index()

@JvmName("storeIntSortRegLanSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RegLanSort, IntSort>>).store(
    entry: (() -> Pair<Expression<IntSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenIntSortRegLanSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RegLanSort, IntSort>).then(
    entry: (() -> Pair<Expression<IntSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atIntRegLanSort")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Int.at(index: Expression<RegLanSort>) = IntLiteral(this) to index

@JvmName("storeIntRegLanSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RegLanSort, IntSort>>.store(
    entry: Pair<Int, Expression<RegLanSort>>
) = ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("thenIntRegLanSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RegLanSort, IntSort>.then(entry: Pair<Int, Expression<RegLanSort>>) =
    ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("atIntRegLanSortLambdaValue")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Int).at(index: Expression<RegLanSort>) = IntLiteral(this()) to index

@JvmName("storeIntRegLanSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RegLanSort, IntSort>>).store(
    entry: Pair<Int, Expression<RegLanSort>>
) = ArrayStore(this(), entry.second, IntLiteral(entry.first))

@JvmName("thenIntRegLanSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RegLanSort, IntSort>).then(entry: Pair<Int, Expression<RegLanSort>>) =
    ArrayStore(this(), entry.second, IntLiteral(entry.first))

@JvmName("atIntRegLanSortLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Int.at(index: (() -> Expression<RegLanSort>)) = IntLiteral(this) to index()

@JvmName("storeIntRegLanSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RegLanSort, IntSort>>.store(
    entry: (() -> Pair<Int, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, IntLiteral(first)) }

@JvmName("thenIntRegLanSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RegLanSort, IntSort>.then(entry: (() -> Pair<Int, Expression<RegLanSort>>)) =
    entry().let { (first, second) -> ArrayStore(this, second, IntLiteral(first)) }

@JvmName("atIntRegLanSortLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Int).at(index: (() -> Expression<RegLanSort>)) = IntLiteral(this()) to index()

@JvmName("storeIntRegLanSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RegLanSort, IntSort>>).store(
    entry: (() -> Pair<Int, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, IntLiteral(first)) }

@JvmName("thenIntRegLanSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RegLanSort, IntSort>).then(
    entry: (() -> Pair<Int, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, IntLiteral(first)) }

@JvmName("atBoolSortRegLanSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BoolSort>.at(index: Expression<RegLanSort>) = this to index

@JvmName("storeBoolSortRegLanSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RegLanSort, BoolSort>>.store(
    entry: Pair<Expression<BoolSort>, Expression<RegLanSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBoolSortRegLanSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RegLanSort, BoolSort>.then(
    entry: Pair<Expression<BoolSort>, Expression<RegLanSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBoolSortRegLanSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BoolSort>).at(index: Expression<RegLanSort>) = this() to index

@JvmName("storeBoolSortRegLanSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RegLanSort, BoolSort>>).store(
    entry: Pair<Expression<BoolSort>, Expression<RegLanSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenBoolSortRegLanSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RegLanSort, BoolSort>).then(
    entry: Pair<Expression<BoolSort>, Expression<RegLanSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atBoolSortRegLanSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BoolSort>.at(index: (() -> Expression<RegLanSort>)) = this to index()

@JvmName("storeBoolSortRegLanSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RegLanSort, BoolSort>>.store(
    entry: (() -> Pair<Expression<BoolSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenBoolSortRegLanSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RegLanSort, BoolSort>.then(
    entry: (() -> Pair<Expression<BoolSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atBoolSortRegLanSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BoolSort>).at(index: (() -> Expression<RegLanSort>)) = this() to index()

@JvmName("storeBoolSortRegLanSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RegLanSort, BoolSort>>).store(
    entry: (() -> Pair<Expression<BoolSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenBoolSortRegLanSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RegLanSort, BoolSort>).then(
    entry: (() -> Pair<Expression<BoolSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atBooleanRegLanSort")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Boolean.at(index: Expression<RegLanSort>) = this.toSMTBool() to index

@JvmName("storeBooleanRegLanSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RegLanSort, BoolSort>>.store(
    entry: Pair<Boolean, Expression<RegLanSort>>
) = ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("thenBooleanRegLanSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RegLanSort, BoolSort>.then(entry: Pair<Boolean, Expression<RegLanSort>>) =
    ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("atBooleanRegLanSortLambdaValue")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Boolean).at(index: Expression<RegLanSort>) = this().toSMTBool() to index

@JvmName("storeBooleanRegLanSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RegLanSort, BoolSort>>).store(
    entry: Pair<Boolean, Expression<RegLanSort>>
) = ArrayStore(this(), entry.second, entry.first.toSMTBool())

@JvmName("thenBooleanRegLanSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RegLanSort, BoolSort>).then(
    entry: Pair<Boolean, Expression<RegLanSort>>
) = ArrayStore(this(), entry.second, entry.first.toSMTBool())

@JvmName("atBooleanRegLanSortLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Boolean.at(index: (() -> Expression<RegLanSort>)) = this.toSMTBool() to index()

@JvmName("storeBooleanRegLanSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RegLanSort, BoolSort>>.store(
    entry: (() -> Pair<Boolean, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first.toSMTBool()) }

@JvmName("thenBooleanRegLanSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RegLanSort, BoolSort>.then(
    entry: (() -> Pair<Boolean, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first.toSMTBool()) }

@JvmName("atBooleanRegLanSortLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Boolean).at(index: (() -> Expression<RegLanSort>)) = this().toSMTBool() to index()

@JvmName("storeBooleanRegLanSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RegLanSort, BoolSort>>).store(
    entry: (() -> Pair<Boolean, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first.toSMTBool()) }

@JvmName("thenBooleanRegLanSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RegLanSort, BoolSort>).then(
    entry: (() -> Pair<Boolean, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first.toSMTBool()) }

@JvmName("atStringSortRegLanSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<StringSort>.at(index: Expression<RegLanSort>) = this to index

@JvmName("storeStringSortRegLanSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RegLanSort, StringSort>>.store(
    entry: Pair<Expression<StringSort>, Expression<RegLanSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenStringSortRegLanSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RegLanSort, StringSort>.then(
    entry: Pair<Expression<StringSort>, Expression<RegLanSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atStringSortRegLanSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<StringSort>).at(index: Expression<RegLanSort>) = this() to index

@JvmName("storeStringSortRegLanSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RegLanSort, StringSort>>).store(
    entry: Pair<Expression<StringSort>, Expression<RegLanSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenStringSortRegLanSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RegLanSort, StringSort>).then(
    entry: Pair<Expression<StringSort>, Expression<RegLanSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atStringSortRegLanSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<StringSort>.at(index: (() -> Expression<RegLanSort>)) = this to index()

@JvmName("storeStringSortRegLanSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RegLanSort, StringSort>>.store(
    entry: (() -> Pair<Expression<StringSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenStringSortRegLanSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RegLanSort, StringSort>.then(
    entry: (() -> Pair<Expression<StringSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atStringSortRegLanSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<StringSort>).at(index: (() -> Expression<RegLanSort>)) =
    this() to index()

@JvmName("storeStringSortRegLanSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RegLanSort, StringSort>>).store(
    entry: (() -> Pair<Expression<StringSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenStringSortRegLanSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RegLanSort, StringSort>).then(
    entry: (() -> Pair<Expression<StringSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atStringRegLanSort")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun String.at(index: Expression<RegLanSort>) = StringLiteral(this) to index

@JvmName("storeStringRegLanSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RegLanSort, StringSort>>.store(
    entry: Pair<String, Expression<RegLanSort>>
) = ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("thenStringRegLanSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RegLanSort, StringSort>.then(entry: Pair<String, Expression<RegLanSort>>) =
    ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("atStringRegLanSortLambdaValue")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> String).at(index: Expression<RegLanSort>) = StringLiteral(this()) to index

@JvmName("storeStringRegLanSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RegLanSort, StringSort>>).store(
    entry: Pair<String, Expression<RegLanSort>>
) = ArrayStore(this(), entry.second, StringLiteral(entry.first))

@JvmName("thenStringRegLanSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RegLanSort, StringSort>).then(
    entry: Pair<String, Expression<RegLanSort>>
) = ArrayStore(this(), entry.second, StringLiteral(entry.first))

@JvmName("atStringRegLanSortLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun String.at(index: (() -> Expression<RegLanSort>)) = StringLiteral(this) to index()

@JvmName("storeStringRegLanSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RegLanSort, StringSort>>.store(
    entry: (() -> Pair<String, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, StringLiteral(first)) }

@JvmName("thenStringRegLanSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RegLanSort, StringSort>.then(
    entry: (() -> Pair<String, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, StringLiteral(first)) }

@JvmName("atStringRegLanSortLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> String).at(index: (() -> Expression<RegLanSort>)) =
    StringLiteral(this()) to index()

@JvmName("storeStringRegLanSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RegLanSort, StringSort>>).store(
    entry: (() -> Pair<String, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, StringLiteral(first)) }

@JvmName("thenStringRegLanSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RegLanSort, StringSort>).then(
    entry: (() -> Pair<String, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, StringLiteral(first)) }

@JvmName("atRealSortRegLanSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RealSort>.at(index: Expression<RegLanSort>) = this to index

@JvmName("storeRealSortRegLanSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RegLanSort, RealSort>>.store(
    entry: Pair<Expression<RealSort>, Expression<RegLanSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRealSortRegLanSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RegLanSort, RealSort>.then(
    entry: Pair<Expression<RealSort>, Expression<RegLanSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRealSortRegLanSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RealSort>).at(index: Expression<RegLanSort>) = this() to index

@JvmName("storeRealSortRegLanSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RegLanSort, RealSort>>).store(
    entry: Pair<Expression<RealSort>, Expression<RegLanSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenRealSortRegLanSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RegLanSort, RealSort>).then(
    entry: Pair<Expression<RealSort>, Expression<RegLanSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atRealSortRegLanSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RealSort>.at(index: (() -> Expression<RegLanSort>)) = this to index()

@JvmName("storeRealSortRegLanSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RegLanSort, RealSort>>.store(
    entry: (() -> Pair<Expression<RealSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenRealSortRegLanSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RegLanSort, RealSort>.then(
    entry: (() -> Pair<Expression<RealSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atRealSortRegLanSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RealSort>).at(index: (() -> Expression<RegLanSort>)) = this() to index()

@JvmName("storeRealSortRegLanSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RegLanSort, RealSort>>).store(
    entry: (() -> Pair<Expression<RealSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenRealSortRegLanSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RegLanSort, RealSort>).then(
    entry: (() -> Pair<Expression<RealSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atRegLanSortRegLanSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RegLanSort>.at(index: Expression<RegLanSort>) = this to index

@JvmName("storeRegLanSortRegLanSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RegLanSort, RegLanSort>>.store(
    entry: Pair<Expression<RegLanSort>, Expression<RegLanSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRegLanSortRegLanSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RegLanSort, RegLanSort>.then(
    entry: Pair<Expression<RegLanSort>, Expression<RegLanSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRegLanSortRegLanSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RegLanSort>).at(index: Expression<RegLanSort>) = this() to index

@JvmName("storeRegLanSortRegLanSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RegLanSort, RegLanSort>>).store(
    entry: Pair<Expression<RegLanSort>, Expression<RegLanSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenRegLanSortRegLanSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RegLanSort, RegLanSort>).then(
    entry: Pair<Expression<RegLanSort>, Expression<RegLanSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atRegLanSortRegLanSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RegLanSort>.at(index: (() -> Expression<RegLanSort>)) = this to index()

@JvmName("storeRegLanSortRegLanSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RegLanSort, RegLanSort>>.store(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenRegLanSortRegLanSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RegLanSort, RegLanSort>.then(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atRegLanSortRegLanSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RegLanSort>).at(index: (() -> Expression<RegLanSort>)) =
    this() to index()

@JvmName("storeRegLanSortRegLanSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RegLanSort, RegLanSort>>).store(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenRegLanSortRegLanSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RegLanSort, RegLanSort>).then(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atFPSortRegLanSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<FPSort>.at(index: Expression<RegLanSort>) = this to index

@JvmName("storeFPSortRegLanSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RegLanSort, FPSort>>.store(
    entry: Pair<Expression<FPSort>, Expression<RegLanSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenFPSortRegLanSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RegLanSort, FPSort>.then(
    entry: Pair<Expression<FPSort>, Expression<RegLanSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atFPSortRegLanSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<FPSort>).at(index: Expression<RegLanSort>) = this() to index

@JvmName("storeFPSortRegLanSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RegLanSort, FPSort>>).store(
    entry: Pair<Expression<FPSort>, Expression<RegLanSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenFPSortRegLanSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RegLanSort, FPSort>).then(
    entry: Pair<Expression<FPSort>, Expression<RegLanSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atFPSortRegLanSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<FPSort>.at(index: (() -> Expression<RegLanSort>)) = this to index()

@JvmName("storeFPSortRegLanSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RegLanSort, FPSort>>.store(
    entry: (() -> Pair<Expression<FPSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenFPSortRegLanSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RegLanSort, FPSort>.then(
    entry: (() -> Pair<Expression<FPSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atFPSortRegLanSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<FPSort>).at(index: (() -> Expression<RegLanSort>)) = this() to index()

@JvmName("storeFPSortRegLanSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RegLanSort, FPSort>>).store(
    entry: (() -> Pair<Expression<FPSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenFPSortRegLanSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RegLanSort, FPSort>).then(
    entry: (() -> Pair<Expression<FPSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atRoundingModeSortRegLanSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RoundingModeSort>.at(index: Expression<RegLanSort>) = this to index

@JvmName("storeRoundingModeSortRegLanSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RegLanSort, RoundingModeSort>>.store(
    entry: Pair<Expression<RoundingModeSort>, Expression<RegLanSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRoundingModeSortRegLanSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RegLanSort, RoundingModeSort>.then(
    entry: Pair<Expression<RoundingModeSort>, Expression<RegLanSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRoundingModeSortRegLanSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RoundingModeSort>).at(index: Expression<RegLanSort>) = this() to index

@JvmName("storeRoundingModeSortRegLanSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RegLanSort, RoundingModeSort>>).store(
    entry: Pair<Expression<RoundingModeSort>, Expression<RegLanSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenRoundingModeSortRegLanSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RegLanSort, RoundingModeSort>).then(
    entry: Pair<Expression<RoundingModeSort>, Expression<RegLanSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atRoundingModeSortRegLanSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RoundingModeSort>.at(index: (() -> Expression<RegLanSort>)) = this to index()

@JvmName("storeRoundingModeSortRegLanSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RegLanSort, RoundingModeSort>>.store(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenRoundingModeSortRegLanSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RegLanSort, RoundingModeSort>.then(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atRoundingModeSortRegLanSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RoundingModeSort>).at(index: (() -> Expression<RegLanSort>)) =
    this() to index()

@JvmName("storeRoundingModeSortRegLanSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RegLanSort, RoundingModeSort>>).store(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenRoundingModeSortRegLanSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RegLanSort, RoundingModeSort>).then(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atBitVecSortRegLanSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BitVecSort>.at(index: Expression<RegLanSort>) = this to index

@JvmName("storeBitVecSortRegLanSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RegLanSort, BitVecSort>>.store(
    entry: Pair<Expression<BitVecSort>, Expression<RegLanSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBitVecSortRegLanSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RegLanSort, BitVecSort>.then(
    entry: Pair<Expression<BitVecSort>, Expression<RegLanSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBitVecSortRegLanSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BitVecSort>).at(index: Expression<RegLanSort>) = this() to index

@JvmName("storeBitVecSortRegLanSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RegLanSort, BitVecSort>>).store(
    entry: Pair<Expression<BitVecSort>, Expression<RegLanSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenBitVecSortRegLanSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RegLanSort, BitVecSort>).then(
    entry: Pair<Expression<BitVecSort>, Expression<RegLanSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atBitVecSortRegLanSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BitVecSort>.at(index: (() -> Expression<RegLanSort>)) = this to index()

@JvmName("storeBitVecSortRegLanSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RegLanSort, BitVecSort>>.store(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenBitVecSortRegLanSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RegLanSort, BitVecSort>.then(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atBitVecSortRegLanSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BitVecSort>).at(index: (() -> Expression<RegLanSort>)) =
    this() to index()

@JvmName("storeBitVecSortRegLanSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RegLanSort, BitVecSort>>).store(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenBitVecSortRegLanSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RegLanSort, BitVecSort>).then(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<RegLanSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atIntSortFPSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<IntSort>.at(index: Expression<FPSort>) = this to index

@JvmName("storeIntSortFPSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<FPSort, IntSort>>.store(
    entry: Pair<Expression<IntSort>, Expression<FPSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenIntSortFPSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<FPSort, IntSort>.then(entry: Pair<Expression<IntSort>, Expression<FPSort>>) =
    ArrayStore(this, entry.second, entry.first)

@JvmName("atIntSortFPSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<IntSort>).at(index: Expression<FPSort>) = this() to index

@JvmName("storeIntSortFPSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<FPSort, IntSort>>).store(
    entry: Pair<Expression<IntSort>, Expression<FPSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenIntSortFPSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<FPSort, IntSort>).then(
    entry: Pair<Expression<IntSort>, Expression<FPSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atIntSortFPSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<IntSort>.at(index: (() -> Expression<FPSort>)) = this to index()

@JvmName("storeIntSortFPSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<FPSort, IntSort>>.store(
    entry: (() -> Pair<Expression<IntSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenIntSortFPSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<FPSort, IntSort>.then(
    entry: (() -> Pair<Expression<IntSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atIntSortFPSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<IntSort>).at(index: (() -> Expression<FPSort>)) = this() to index()

@JvmName("storeIntSortFPSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<FPSort, IntSort>>).store(
    entry: (() -> Pair<Expression<IntSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenIntSortFPSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<FPSort, IntSort>).then(
    entry: (() -> Pair<Expression<IntSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atIntFPSort")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Int.at(index: Expression<FPSort>) = IntLiteral(this) to index

@JvmName("storeIntFPSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<FPSort, IntSort>>.store(entry: Pair<Int, Expression<FPSort>>) =
    ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("thenIntFPSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<FPSort, IntSort>.then(entry: Pair<Int, Expression<FPSort>>) =
    ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("atIntFPSortLambdaValue")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Int).at(index: Expression<FPSort>) = IntLiteral(this()) to index

@JvmName("storeIntFPSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<FPSort, IntSort>>).store(
    entry: Pair<Int, Expression<FPSort>>
) = ArrayStore(this(), entry.second, IntLiteral(entry.first))

@JvmName("thenIntFPSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<FPSort, IntSort>).then(entry: Pair<Int, Expression<FPSort>>) =
    ArrayStore(this(), entry.second, IntLiteral(entry.first))

@JvmName("atIntFPSortLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Int.at(index: (() -> Expression<FPSort>)) = IntLiteral(this) to index()

@JvmName("storeIntFPSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<FPSort, IntSort>>.store(
    entry: (() -> Pair<Int, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, IntLiteral(first)) }

@JvmName("thenIntFPSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<FPSort, IntSort>.then(entry: (() -> Pair<Int, Expression<FPSort>>)) =
    entry().let { (first, second) -> ArrayStore(this, second, IntLiteral(first)) }

@JvmName("atIntFPSortLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Int).at(index: (() -> Expression<FPSort>)) = IntLiteral(this()) to index()

@JvmName("storeIntFPSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<FPSort, IntSort>>).store(
    entry: (() -> Pair<Int, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, IntLiteral(first)) }

@JvmName("thenIntFPSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<FPSort, IntSort>).then(entry: (() -> Pair<Int, Expression<FPSort>>)) =
    entry().let { (first, second) -> ArrayStore(this(), second, IntLiteral(first)) }

@JvmName("atBoolSortFPSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BoolSort>.at(index: Expression<FPSort>) = this to index

@JvmName("storeBoolSortFPSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<FPSort, BoolSort>>.store(
    entry: Pair<Expression<BoolSort>, Expression<FPSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBoolSortFPSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<FPSort, BoolSort>.then(entry: Pair<Expression<BoolSort>, Expression<FPSort>>) =
    ArrayStore(this, entry.second, entry.first)

@JvmName("atBoolSortFPSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BoolSort>).at(index: Expression<FPSort>) = this() to index

@JvmName("storeBoolSortFPSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<FPSort, BoolSort>>).store(
    entry: Pair<Expression<BoolSort>, Expression<FPSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenBoolSortFPSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<FPSort, BoolSort>).then(
    entry: Pair<Expression<BoolSort>, Expression<FPSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atBoolSortFPSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BoolSort>.at(index: (() -> Expression<FPSort>)) = this to index()

@JvmName("storeBoolSortFPSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<FPSort, BoolSort>>.store(
    entry: (() -> Pair<Expression<BoolSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenBoolSortFPSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<FPSort, BoolSort>.then(
    entry: (() -> Pair<Expression<BoolSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atBoolSortFPSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BoolSort>).at(index: (() -> Expression<FPSort>)) = this() to index()

@JvmName("storeBoolSortFPSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<FPSort, BoolSort>>).store(
    entry: (() -> Pair<Expression<BoolSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenBoolSortFPSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<FPSort, BoolSort>).then(
    entry: (() -> Pair<Expression<BoolSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atBooleanFPSort")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Boolean.at(index: Expression<FPSort>) = this.toSMTBool() to index

@JvmName("storeBooleanFPSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<FPSort, BoolSort>>.store(entry: Pair<Boolean, Expression<FPSort>>) =
    ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("thenBooleanFPSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<FPSort, BoolSort>.then(entry: Pair<Boolean, Expression<FPSort>>) =
    ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("atBooleanFPSortLambdaValue")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Boolean).at(index: Expression<FPSort>) = this().toSMTBool() to index

@JvmName("storeBooleanFPSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<FPSort, BoolSort>>).store(
    entry: Pair<Boolean, Expression<FPSort>>
) = ArrayStore(this(), entry.second, entry.first.toSMTBool())

@JvmName("thenBooleanFPSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<FPSort, BoolSort>).then(entry: Pair<Boolean, Expression<FPSort>>) =
    ArrayStore(this(), entry.second, entry.first.toSMTBool())

@JvmName("atBooleanFPSortLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Boolean.at(index: (() -> Expression<FPSort>)) = this.toSMTBool() to index()

@JvmName("storeBooleanFPSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<FPSort, BoolSort>>.store(
    entry: (() -> Pair<Boolean, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first.toSMTBool()) }

@JvmName("thenBooleanFPSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<FPSort, BoolSort>.then(entry: (() -> Pair<Boolean, Expression<FPSort>>)) =
    entry().let { (first, second) -> ArrayStore(this, second, first.toSMTBool()) }

@JvmName("atBooleanFPSortLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Boolean).at(index: (() -> Expression<FPSort>)) = this().toSMTBool() to index()

@JvmName("storeBooleanFPSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<FPSort, BoolSort>>).store(
    entry: (() -> Pair<Boolean, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first.toSMTBool()) }

@JvmName("thenBooleanFPSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<FPSort, BoolSort>).then(
    entry: (() -> Pair<Boolean, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first.toSMTBool()) }

@JvmName("atStringSortFPSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<StringSort>.at(index: Expression<FPSort>) = this to index

@JvmName("storeStringSortFPSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<FPSort, StringSort>>.store(
    entry: Pair<Expression<StringSort>, Expression<FPSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenStringSortFPSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<FPSort, StringSort>.then(
    entry: Pair<Expression<StringSort>, Expression<FPSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atStringSortFPSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<StringSort>).at(index: Expression<FPSort>) = this() to index

@JvmName("storeStringSortFPSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<FPSort, StringSort>>).store(
    entry: Pair<Expression<StringSort>, Expression<FPSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenStringSortFPSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<FPSort, StringSort>).then(
    entry: Pair<Expression<StringSort>, Expression<FPSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atStringSortFPSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<StringSort>.at(index: (() -> Expression<FPSort>)) = this to index()

@JvmName("storeStringSortFPSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<FPSort, StringSort>>.store(
    entry: (() -> Pair<Expression<StringSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenStringSortFPSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<FPSort, StringSort>.then(
    entry: (() -> Pair<Expression<StringSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atStringSortFPSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<StringSort>).at(index: (() -> Expression<FPSort>)) = this() to index()

@JvmName("storeStringSortFPSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<FPSort, StringSort>>).store(
    entry: (() -> Pair<Expression<StringSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenStringSortFPSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<FPSort, StringSort>).then(
    entry: (() -> Pair<Expression<StringSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atStringFPSort")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun String.at(index: Expression<FPSort>) = StringLiteral(this) to index

@JvmName("storeStringFPSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<FPSort, StringSort>>.store(entry: Pair<String, Expression<FPSort>>) =
    ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("thenStringFPSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<FPSort, StringSort>.then(entry: Pair<String, Expression<FPSort>>) =
    ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("atStringFPSortLambdaValue")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> String).at(index: Expression<FPSort>) = StringLiteral(this()) to index

@JvmName("storeStringFPSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<FPSort, StringSort>>).store(
    entry: Pair<String, Expression<FPSort>>
) = ArrayStore(this(), entry.second, StringLiteral(entry.first))

@JvmName("thenStringFPSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<FPSort, StringSort>).then(entry: Pair<String, Expression<FPSort>>) =
    ArrayStore(this(), entry.second, StringLiteral(entry.first))

@JvmName("atStringFPSortLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun String.at(index: (() -> Expression<FPSort>)) = StringLiteral(this) to index()

@JvmName("storeStringFPSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<FPSort, StringSort>>.store(
    entry: (() -> Pair<String, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, StringLiteral(first)) }

@JvmName("thenStringFPSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<FPSort, StringSort>.then(entry: (() -> Pair<String, Expression<FPSort>>)) =
    entry().let { (first, second) -> ArrayStore(this, second, StringLiteral(first)) }

@JvmName("atStringFPSortLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> String).at(index: (() -> Expression<FPSort>)) = StringLiteral(this()) to index()

@JvmName("storeStringFPSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<FPSort, StringSort>>).store(
    entry: (() -> Pair<String, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, StringLiteral(first)) }

@JvmName("thenStringFPSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<FPSort, StringSort>).then(
    entry: (() -> Pair<String, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, StringLiteral(first)) }

@JvmName("atRealSortFPSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RealSort>.at(index: Expression<FPSort>) = this to index

@JvmName("storeRealSortFPSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<FPSort, RealSort>>.store(
    entry: Pair<Expression<RealSort>, Expression<FPSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRealSortFPSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<FPSort, RealSort>.then(entry: Pair<Expression<RealSort>, Expression<FPSort>>) =
    ArrayStore(this, entry.second, entry.first)

@JvmName("atRealSortFPSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RealSort>).at(index: Expression<FPSort>) = this() to index

@JvmName("storeRealSortFPSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<FPSort, RealSort>>).store(
    entry: Pair<Expression<RealSort>, Expression<FPSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenRealSortFPSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<FPSort, RealSort>).then(
    entry: Pair<Expression<RealSort>, Expression<FPSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atRealSortFPSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RealSort>.at(index: (() -> Expression<FPSort>)) = this to index()

@JvmName("storeRealSortFPSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<FPSort, RealSort>>.store(
    entry: (() -> Pair<Expression<RealSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenRealSortFPSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<FPSort, RealSort>.then(
    entry: (() -> Pair<Expression<RealSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atRealSortFPSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RealSort>).at(index: (() -> Expression<FPSort>)) = this() to index()

@JvmName("storeRealSortFPSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<FPSort, RealSort>>).store(
    entry: (() -> Pair<Expression<RealSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenRealSortFPSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<FPSort, RealSort>).then(
    entry: (() -> Pair<Expression<RealSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atRegLanSortFPSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RegLanSort>.at(index: Expression<FPSort>) = this to index

@JvmName("storeRegLanSortFPSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<FPSort, RegLanSort>>.store(
    entry: Pair<Expression<RegLanSort>, Expression<FPSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRegLanSortFPSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<FPSort, RegLanSort>.then(
    entry: Pair<Expression<RegLanSort>, Expression<FPSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRegLanSortFPSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RegLanSort>).at(index: Expression<FPSort>) = this() to index

@JvmName("storeRegLanSortFPSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<FPSort, RegLanSort>>).store(
    entry: Pair<Expression<RegLanSort>, Expression<FPSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenRegLanSortFPSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<FPSort, RegLanSort>).then(
    entry: Pair<Expression<RegLanSort>, Expression<FPSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atRegLanSortFPSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RegLanSort>.at(index: (() -> Expression<FPSort>)) = this to index()

@JvmName("storeRegLanSortFPSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<FPSort, RegLanSort>>.store(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenRegLanSortFPSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<FPSort, RegLanSort>.then(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atRegLanSortFPSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RegLanSort>).at(index: (() -> Expression<FPSort>)) = this() to index()

@JvmName("storeRegLanSortFPSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<FPSort, RegLanSort>>).store(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenRegLanSortFPSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<FPSort, RegLanSort>).then(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atFPSortFPSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<FPSort>.at(index: Expression<FPSort>) = this to index

@JvmName("storeFPSortFPSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<FPSort, FPSort>>.store(
    entry: Pair<Expression<FPSort>, Expression<FPSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenFPSortFPSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<FPSort, FPSort>.then(entry: Pair<Expression<FPSort>, Expression<FPSort>>) =
    ArrayStore(this, entry.second, entry.first)

@JvmName("atFPSortFPSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<FPSort>).at(index: Expression<FPSort>) = this() to index

@JvmName("storeFPSortFPSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<FPSort, FPSort>>).store(
    entry: Pair<Expression<FPSort>, Expression<FPSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenFPSortFPSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<FPSort, FPSort>).then(
    entry: Pair<Expression<FPSort>, Expression<FPSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atFPSortFPSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<FPSort>.at(index: (() -> Expression<FPSort>)) = this to index()

@JvmName("storeFPSortFPSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<FPSort, FPSort>>.store(
    entry: (() -> Pair<Expression<FPSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenFPSortFPSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<FPSort, FPSort>.then(
    entry: (() -> Pair<Expression<FPSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atFPSortFPSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<FPSort>).at(index: (() -> Expression<FPSort>)) = this() to index()

@JvmName("storeFPSortFPSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<FPSort, FPSort>>).store(
    entry: (() -> Pair<Expression<FPSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenFPSortFPSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<FPSort, FPSort>).then(
    entry: (() -> Pair<Expression<FPSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atRoundingModeSortFPSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RoundingModeSort>.at(index: Expression<FPSort>) = this to index

@JvmName("storeRoundingModeSortFPSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<FPSort, RoundingModeSort>>.store(
    entry: Pair<Expression<RoundingModeSort>, Expression<FPSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRoundingModeSortFPSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<FPSort, RoundingModeSort>.then(
    entry: Pair<Expression<RoundingModeSort>, Expression<FPSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRoundingModeSortFPSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RoundingModeSort>).at(index: Expression<FPSort>) = this() to index

@JvmName("storeRoundingModeSortFPSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<FPSort, RoundingModeSort>>).store(
    entry: Pair<Expression<RoundingModeSort>, Expression<FPSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenRoundingModeSortFPSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<FPSort, RoundingModeSort>).then(
    entry: Pair<Expression<RoundingModeSort>, Expression<FPSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atRoundingModeSortFPSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RoundingModeSort>.at(index: (() -> Expression<FPSort>)) = this to index()

@JvmName("storeRoundingModeSortFPSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<FPSort, RoundingModeSort>>.store(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenRoundingModeSortFPSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<FPSort, RoundingModeSort>.then(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atRoundingModeSortFPSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RoundingModeSort>).at(index: (() -> Expression<FPSort>)) =
    this() to index()

@JvmName("storeRoundingModeSortFPSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<FPSort, RoundingModeSort>>).store(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenRoundingModeSortFPSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<FPSort, RoundingModeSort>).then(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atBitVecSortFPSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BitVecSort>.at(index: Expression<FPSort>) = this to index

@JvmName("storeBitVecSortFPSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<FPSort, BitVecSort>>.store(
    entry: Pair<Expression<BitVecSort>, Expression<FPSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBitVecSortFPSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<FPSort, BitVecSort>.then(
    entry: Pair<Expression<BitVecSort>, Expression<FPSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBitVecSortFPSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BitVecSort>).at(index: Expression<FPSort>) = this() to index

@JvmName("storeBitVecSortFPSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<FPSort, BitVecSort>>).store(
    entry: Pair<Expression<BitVecSort>, Expression<FPSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenBitVecSortFPSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<FPSort, BitVecSort>).then(
    entry: Pair<Expression<BitVecSort>, Expression<FPSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atBitVecSortFPSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BitVecSort>.at(index: (() -> Expression<FPSort>)) = this to index()

@JvmName("storeBitVecSortFPSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<FPSort, BitVecSort>>.store(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenBitVecSortFPSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<FPSort, BitVecSort>.then(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atBitVecSortFPSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BitVecSort>).at(index: (() -> Expression<FPSort>)) = this() to index()

@JvmName("storeBitVecSortFPSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<FPSort, BitVecSort>>).store(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenBitVecSortFPSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<FPSort, BitVecSort>).then(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<FPSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atIntSortRoundingModeSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<IntSort>.at(index: Expression<RoundingModeSort>) = this to index

@JvmName("storeIntSortRoundingModeSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RoundingModeSort, IntSort>>.store(
    entry: Pair<Expression<IntSort>, Expression<RoundingModeSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenIntSortRoundingModeSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RoundingModeSort, IntSort>.then(
    entry: Pair<Expression<IntSort>, Expression<RoundingModeSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atIntSortRoundingModeSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<IntSort>).at(index: Expression<RoundingModeSort>) = this() to index

@JvmName("storeIntSortRoundingModeSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RoundingModeSort, IntSort>>).store(
    entry: Pair<Expression<IntSort>, Expression<RoundingModeSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenIntSortRoundingModeSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RoundingModeSort, IntSort>).then(
    entry: Pair<Expression<IntSort>, Expression<RoundingModeSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atIntSortRoundingModeSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<IntSort>.at(index: (() -> Expression<RoundingModeSort>)) = this to index()

@JvmName("storeIntSortRoundingModeSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RoundingModeSort, IntSort>>.store(
    entry: (() -> Pair<Expression<IntSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenIntSortRoundingModeSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RoundingModeSort, IntSort>.then(
    entry: (() -> Pair<Expression<IntSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atIntSortRoundingModeSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<IntSort>).at(index: (() -> Expression<RoundingModeSort>)) =
    this() to index()

@JvmName("storeIntSortRoundingModeSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RoundingModeSort, IntSort>>).store(
    entry: (() -> Pair<Expression<IntSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenIntSortRoundingModeSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RoundingModeSort, IntSort>).then(
    entry: (() -> Pair<Expression<IntSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atIntRoundingModeSort")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Int.at(index: Expression<RoundingModeSort>) = IntLiteral(this) to index

@JvmName("storeIntRoundingModeSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RoundingModeSort, IntSort>>.store(
    entry: Pair<Int, Expression<RoundingModeSort>>
) = ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("thenIntRoundingModeSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RoundingModeSort, IntSort>.then(
    entry: Pair<Int, Expression<RoundingModeSort>>
) = ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("atIntRoundingModeSortLambdaValue")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Int).at(index: Expression<RoundingModeSort>) = IntLiteral(this()) to index

@JvmName("storeIntRoundingModeSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RoundingModeSort, IntSort>>).store(
    entry: Pair<Int, Expression<RoundingModeSort>>
) = ArrayStore(this(), entry.second, IntLiteral(entry.first))

@JvmName("thenIntRoundingModeSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RoundingModeSort, IntSort>).then(
    entry: Pair<Int, Expression<RoundingModeSort>>
) = ArrayStore(this(), entry.second, IntLiteral(entry.first))

@JvmName("atIntRoundingModeSortLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Int.at(index: (() -> Expression<RoundingModeSort>)) = IntLiteral(this) to index()

@JvmName("storeIntRoundingModeSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RoundingModeSort, IntSort>>.store(
    entry: (() -> Pair<Int, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, IntLiteral(first)) }

@JvmName("thenIntRoundingModeSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RoundingModeSort, IntSort>.then(
    entry: (() -> Pair<Int, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, IntLiteral(first)) }

@JvmName("atIntRoundingModeSortLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Int).at(index: (() -> Expression<RoundingModeSort>)) =
    IntLiteral(this()) to index()

@JvmName("storeIntRoundingModeSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RoundingModeSort, IntSort>>).store(
    entry: (() -> Pair<Int, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, IntLiteral(first)) }

@JvmName("thenIntRoundingModeSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RoundingModeSort, IntSort>).then(
    entry: (() -> Pair<Int, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, IntLiteral(first)) }

@JvmName("atBoolSortRoundingModeSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BoolSort>.at(index: Expression<RoundingModeSort>) = this to index

@JvmName("storeBoolSortRoundingModeSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RoundingModeSort, BoolSort>>.store(
    entry: Pair<Expression<BoolSort>, Expression<RoundingModeSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBoolSortRoundingModeSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RoundingModeSort, BoolSort>.then(
    entry: Pair<Expression<BoolSort>, Expression<RoundingModeSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBoolSortRoundingModeSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BoolSort>).at(index: Expression<RoundingModeSort>) = this() to index

@JvmName("storeBoolSortRoundingModeSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RoundingModeSort, BoolSort>>).store(
    entry: Pair<Expression<BoolSort>, Expression<RoundingModeSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenBoolSortRoundingModeSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RoundingModeSort, BoolSort>).then(
    entry: Pair<Expression<BoolSort>, Expression<RoundingModeSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atBoolSortRoundingModeSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BoolSort>.at(index: (() -> Expression<RoundingModeSort>)) = this to index()

@JvmName("storeBoolSortRoundingModeSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RoundingModeSort, BoolSort>>.store(
    entry: (() -> Pair<Expression<BoolSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenBoolSortRoundingModeSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RoundingModeSort, BoolSort>.then(
    entry: (() -> Pair<Expression<BoolSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atBoolSortRoundingModeSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BoolSort>).at(index: (() -> Expression<RoundingModeSort>)) =
    this() to index()

@JvmName("storeBoolSortRoundingModeSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RoundingModeSort, BoolSort>>).store(
    entry: (() -> Pair<Expression<BoolSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenBoolSortRoundingModeSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RoundingModeSort, BoolSort>).then(
    entry: (() -> Pair<Expression<BoolSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atBooleanRoundingModeSort")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Boolean.at(index: Expression<RoundingModeSort>) = this.toSMTBool() to index

@JvmName("storeBooleanRoundingModeSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RoundingModeSort, BoolSort>>.store(
    entry: Pair<Boolean, Expression<RoundingModeSort>>
) = ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("thenBooleanRoundingModeSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RoundingModeSort, BoolSort>.then(
    entry: Pair<Boolean, Expression<RoundingModeSort>>
) = ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("atBooleanRoundingModeSortLambdaValue")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Boolean).at(index: Expression<RoundingModeSort>) = this().toSMTBool() to index

@JvmName("storeBooleanRoundingModeSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RoundingModeSort, BoolSort>>).store(
    entry: Pair<Boolean, Expression<RoundingModeSort>>
) = ArrayStore(this(), entry.second, entry.first.toSMTBool())

@JvmName("thenBooleanRoundingModeSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RoundingModeSort, BoolSort>).then(
    entry: Pair<Boolean, Expression<RoundingModeSort>>
) = ArrayStore(this(), entry.second, entry.first.toSMTBool())

@JvmName("atBooleanRoundingModeSortLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Boolean.at(index: (() -> Expression<RoundingModeSort>)) = this.toSMTBool() to index()

@JvmName("storeBooleanRoundingModeSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RoundingModeSort, BoolSort>>.store(
    entry: (() -> Pair<Boolean, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first.toSMTBool()) }

@JvmName("thenBooleanRoundingModeSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RoundingModeSort, BoolSort>.then(
    entry: (() -> Pair<Boolean, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first.toSMTBool()) }

@JvmName("atBooleanRoundingModeSortLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Boolean).at(index: (() -> Expression<RoundingModeSort>)) =
    this().toSMTBool() to index()

@JvmName("storeBooleanRoundingModeSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RoundingModeSort, BoolSort>>).store(
    entry: (() -> Pair<Boolean, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first.toSMTBool()) }

@JvmName("thenBooleanRoundingModeSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RoundingModeSort, BoolSort>).then(
    entry: (() -> Pair<Boolean, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first.toSMTBool()) }

@JvmName("atStringSortRoundingModeSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<StringSort>.at(index: Expression<RoundingModeSort>) = this to index

@JvmName("storeStringSortRoundingModeSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RoundingModeSort, StringSort>>.store(
    entry: Pair<Expression<StringSort>, Expression<RoundingModeSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenStringSortRoundingModeSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RoundingModeSort, StringSort>.then(
    entry: Pair<Expression<StringSort>, Expression<RoundingModeSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atStringSortRoundingModeSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<StringSort>).at(index: Expression<RoundingModeSort>) = this() to index

@JvmName("storeStringSortRoundingModeSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RoundingModeSort, StringSort>>).store(
    entry: Pair<Expression<StringSort>, Expression<RoundingModeSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenStringSortRoundingModeSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RoundingModeSort, StringSort>).then(
    entry: Pair<Expression<StringSort>, Expression<RoundingModeSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atStringSortRoundingModeSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<StringSort>.at(index: (() -> Expression<RoundingModeSort>)) = this to index()

@JvmName("storeStringSortRoundingModeSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RoundingModeSort, StringSort>>.store(
    entry: (() -> Pair<Expression<StringSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenStringSortRoundingModeSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RoundingModeSort, StringSort>.then(
    entry: (() -> Pair<Expression<StringSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atStringSortRoundingModeSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<StringSort>).at(index: (() -> Expression<RoundingModeSort>)) =
    this() to index()

@JvmName("storeStringSortRoundingModeSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RoundingModeSort, StringSort>>).store(
    entry: (() -> Pair<Expression<StringSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenStringSortRoundingModeSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RoundingModeSort, StringSort>).then(
    entry: (() -> Pair<Expression<StringSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atStringRoundingModeSort")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun String.at(index: Expression<RoundingModeSort>) = StringLiteral(this) to index

@JvmName("storeStringRoundingModeSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RoundingModeSort, StringSort>>.store(
    entry: Pair<String, Expression<RoundingModeSort>>
) = ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("thenStringRoundingModeSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RoundingModeSort, StringSort>.then(
    entry: Pair<String, Expression<RoundingModeSort>>
) = ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("atStringRoundingModeSortLambdaValue")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> String).at(index: Expression<RoundingModeSort>) = StringLiteral(this()) to index

@JvmName("storeStringRoundingModeSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RoundingModeSort, StringSort>>).store(
    entry: Pair<String, Expression<RoundingModeSort>>
) = ArrayStore(this(), entry.second, StringLiteral(entry.first))

@JvmName("thenStringRoundingModeSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RoundingModeSort, StringSort>).then(
    entry: Pair<String, Expression<RoundingModeSort>>
) = ArrayStore(this(), entry.second, StringLiteral(entry.first))

@JvmName("atStringRoundingModeSortLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun String.at(index: (() -> Expression<RoundingModeSort>)) = StringLiteral(this) to index()

@JvmName("storeStringRoundingModeSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RoundingModeSort, StringSort>>.store(
    entry: (() -> Pair<String, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, StringLiteral(first)) }

@JvmName("thenStringRoundingModeSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RoundingModeSort, StringSort>.then(
    entry: (() -> Pair<String, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, StringLiteral(first)) }

@JvmName("atStringRoundingModeSortLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> String).at(index: (() -> Expression<RoundingModeSort>)) =
    StringLiteral(this()) to index()

@JvmName("storeStringRoundingModeSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RoundingModeSort, StringSort>>).store(
    entry: (() -> Pair<String, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, StringLiteral(first)) }

@JvmName("thenStringRoundingModeSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RoundingModeSort, StringSort>).then(
    entry: (() -> Pair<String, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, StringLiteral(first)) }

@JvmName("atRealSortRoundingModeSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RealSort>.at(index: Expression<RoundingModeSort>) = this to index

@JvmName("storeRealSortRoundingModeSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RoundingModeSort, RealSort>>.store(
    entry: Pair<Expression<RealSort>, Expression<RoundingModeSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRealSortRoundingModeSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RoundingModeSort, RealSort>.then(
    entry: Pair<Expression<RealSort>, Expression<RoundingModeSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRealSortRoundingModeSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RealSort>).at(index: Expression<RoundingModeSort>) = this() to index

@JvmName("storeRealSortRoundingModeSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RoundingModeSort, RealSort>>).store(
    entry: Pair<Expression<RealSort>, Expression<RoundingModeSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenRealSortRoundingModeSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RoundingModeSort, RealSort>).then(
    entry: Pair<Expression<RealSort>, Expression<RoundingModeSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atRealSortRoundingModeSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RealSort>.at(index: (() -> Expression<RoundingModeSort>)) = this to index()

@JvmName("storeRealSortRoundingModeSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RoundingModeSort, RealSort>>.store(
    entry: (() -> Pair<Expression<RealSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenRealSortRoundingModeSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RoundingModeSort, RealSort>.then(
    entry: (() -> Pair<Expression<RealSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atRealSortRoundingModeSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RealSort>).at(index: (() -> Expression<RoundingModeSort>)) =
    this() to index()

@JvmName("storeRealSortRoundingModeSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RoundingModeSort, RealSort>>).store(
    entry: (() -> Pair<Expression<RealSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenRealSortRoundingModeSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RoundingModeSort, RealSort>).then(
    entry: (() -> Pair<Expression<RealSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atRegLanSortRoundingModeSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RegLanSort>.at(index: Expression<RoundingModeSort>) = this to index

@JvmName("storeRegLanSortRoundingModeSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RoundingModeSort, RegLanSort>>.store(
    entry: Pair<Expression<RegLanSort>, Expression<RoundingModeSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRegLanSortRoundingModeSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RoundingModeSort, RegLanSort>.then(
    entry: Pair<Expression<RegLanSort>, Expression<RoundingModeSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRegLanSortRoundingModeSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RegLanSort>).at(index: Expression<RoundingModeSort>) = this() to index

@JvmName("storeRegLanSortRoundingModeSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RoundingModeSort, RegLanSort>>).store(
    entry: Pair<Expression<RegLanSort>, Expression<RoundingModeSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenRegLanSortRoundingModeSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RoundingModeSort, RegLanSort>).then(
    entry: Pair<Expression<RegLanSort>, Expression<RoundingModeSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atRegLanSortRoundingModeSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RegLanSort>.at(index: (() -> Expression<RoundingModeSort>)) = this to index()

@JvmName("storeRegLanSortRoundingModeSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RoundingModeSort, RegLanSort>>.store(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenRegLanSortRoundingModeSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RoundingModeSort, RegLanSort>.then(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atRegLanSortRoundingModeSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RegLanSort>).at(index: (() -> Expression<RoundingModeSort>)) =
    this() to index()

@JvmName("storeRegLanSortRoundingModeSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RoundingModeSort, RegLanSort>>).store(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenRegLanSortRoundingModeSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RoundingModeSort, RegLanSort>).then(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atFPSortRoundingModeSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<FPSort>.at(index: Expression<RoundingModeSort>) = this to index

@JvmName("storeFPSortRoundingModeSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RoundingModeSort, FPSort>>.store(
    entry: Pair<Expression<FPSort>, Expression<RoundingModeSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenFPSortRoundingModeSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RoundingModeSort, FPSort>.then(
    entry: Pair<Expression<FPSort>, Expression<RoundingModeSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atFPSortRoundingModeSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<FPSort>).at(index: Expression<RoundingModeSort>) = this() to index

@JvmName("storeFPSortRoundingModeSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RoundingModeSort, FPSort>>).store(
    entry: Pair<Expression<FPSort>, Expression<RoundingModeSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenFPSortRoundingModeSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RoundingModeSort, FPSort>).then(
    entry: Pair<Expression<FPSort>, Expression<RoundingModeSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atFPSortRoundingModeSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<FPSort>.at(index: (() -> Expression<RoundingModeSort>)) = this to index()

@JvmName("storeFPSortRoundingModeSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RoundingModeSort, FPSort>>.store(
    entry: (() -> Pair<Expression<FPSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenFPSortRoundingModeSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RoundingModeSort, FPSort>.then(
    entry: (() -> Pair<Expression<FPSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atFPSortRoundingModeSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<FPSort>).at(index: (() -> Expression<RoundingModeSort>)) =
    this() to index()

@JvmName("storeFPSortRoundingModeSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RoundingModeSort, FPSort>>).store(
    entry: (() -> Pair<Expression<FPSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenFPSortRoundingModeSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RoundingModeSort, FPSort>).then(
    entry: (() -> Pair<Expression<FPSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atRoundingModeSortRoundingModeSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RoundingModeSort>.at(index: Expression<RoundingModeSort>) = this to index

@JvmName("storeRoundingModeSortRoundingModeSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RoundingModeSort, RoundingModeSort>>.store(
    entry: Pair<Expression<RoundingModeSort>, Expression<RoundingModeSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRoundingModeSortRoundingModeSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RoundingModeSort, RoundingModeSort>.then(
    entry: Pair<Expression<RoundingModeSort>, Expression<RoundingModeSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRoundingModeSortRoundingModeSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RoundingModeSort>).at(index: Expression<RoundingModeSort>) =
    this() to index

@JvmName("storeRoundingModeSortRoundingModeSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RoundingModeSort, RoundingModeSort>>).store(
    entry: Pair<Expression<RoundingModeSort>, Expression<RoundingModeSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenRoundingModeSortRoundingModeSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RoundingModeSort, RoundingModeSort>).then(
    entry: Pair<Expression<RoundingModeSort>, Expression<RoundingModeSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atRoundingModeSortRoundingModeSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RoundingModeSort>.at(index: (() -> Expression<RoundingModeSort>)) =
    this to index()

@JvmName("storeRoundingModeSortRoundingModeSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RoundingModeSort, RoundingModeSort>>.store(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenRoundingModeSortRoundingModeSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RoundingModeSort, RoundingModeSort>.then(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atRoundingModeSortRoundingModeSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RoundingModeSort>).at(index: (() -> Expression<RoundingModeSort>)) =
    this() to index()

@JvmName("storeRoundingModeSortRoundingModeSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RoundingModeSort, RoundingModeSort>>).store(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenRoundingModeSortRoundingModeSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RoundingModeSort, RoundingModeSort>).then(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atBitVecSortRoundingModeSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BitVecSort>.at(index: Expression<RoundingModeSort>) = this to index

@JvmName("storeBitVecSortRoundingModeSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RoundingModeSort, BitVecSort>>.store(
    entry: Pair<Expression<BitVecSort>, Expression<RoundingModeSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBitVecSortRoundingModeSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RoundingModeSort, BitVecSort>.then(
    entry: Pair<Expression<BitVecSort>, Expression<RoundingModeSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBitVecSortRoundingModeSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BitVecSort>).at(index: Expression<RoundingModeSort>) = this() to index

@JvmName("storeBitVecSortRoundingModeSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RoundingModeSort, BitVecSort>>).store(
    entry: Pair<Expression<BitVecSort>, Expression<RoundingModeSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenBitVecSortRoundingModeSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RoundingModeSort, BitVecSort>).then(
    entry: Pair<Expression<BitVecSort>, Expression<RoundingModeSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atBitVecSortRoundingModeSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BitVecSort>.at(index: (() -> Expression<RoundingModeSort>)) = this to index()

@JvmName("storeBitVecSortRoundingModeSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<RoundingModeSort, BitVecSort>>.store(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenBitVecSortRoundingModeSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<RoundingModeSort, BitVecSort>.then(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atBitVecSortRoundingModeSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BitVecSort>).at(index: (() -> Expression<RoundingModeSort>)) =
    this() to index()

@JvmName("storeBitVecSortRoundingModeSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<RoundingModeSort, BitVecSort>>).store(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenBitVecSortRoundingModeSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<RoundingModeSort, BitVecSort>).then(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<RoundingModeSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atIntSortBitVecSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<IntSort>.at(index: Expression<BitVecSort>) = this to index

@JvmName("storeIntSortBitVecSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BitVecSort, IntSort>>.store(
    entry: Pair<Expression<IntSort>, Expression<BitVecSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenIntSortBitVecSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BitVecSort, IntSort>.then(
    entry: Pair<Expression<IntSort>, Expression<BitVecSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atIntSortBitVecSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<IntSort>).at(index: Expression<BitVecSort>) = this() to index

@JvmName("storeIntSortBitVecSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BitVecSort, IntSort>>).store(
    entry: Pair<Expression<IntSort>, Expression<BitVecSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenIntSortBitVecSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BitVecSort, IntSort>).then(
    entry: Pair<Expression<IntSort>, Expression<BitVecSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atIntSortBitVecSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<IntSort>.at(index: (() -> Expression<BitVecSort>)) = this to index()

@JvmName("storeIntSortBitVecSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BitVecSort, IntSort>>.store(
    entry: (() -> Pair<Expression<IntSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenIntSortBitVecSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BitVecSort, IntSort>.then(
    entry: (() -> Pair<Expression<IntSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atIntSortBitVecSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<IntSort>).at(index: (() -> Expression<BitVecSort>)) = this() to index()

@JvmName("storeIntSortBitVecSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BitVecSort, IntSort>>).store(
    entry: (() -> Pair<Expression<IntSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenIntSortBitVecSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BitVecSort, IntSort>).then(
    entry: (() -> Pair<Expression<IntSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atIntBitVecSort")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Int.at(index: Expression<BitVecSort>) = IntLiteral(this) to index

@JvmName("storeIntBitVecSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BitVecSort, IntSort>>.store(
    entry: Pair<Int, Expression<BitVecSort>>
) = ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("thenIntBitVecSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BitVecSort, IntSort>.then(entry: Pair<Int, Expression<BitVecSort>>) =
    ArrayStore(this, entry.second, IntLiteral(entry.first))

@JvmName("atIntBitVecSortLambdaValue")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Int).at(index: Expression<BitVecSort>) = IntLiteral(this()) to index

@JvmName("storeIntBitVecSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BitVecSort, IntSort>>).store(
    entry: Pair<Int, Expression<BitVecSort>>
) = ArrayStore(this(), entry.second, IntLiteral(entry.first))

@JvmName("thenIntBitVecSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BitVecSort, IntSort>).then(entry: Pair<Int, Expression<BitVecSort>>) =
    ArrayStore(this(), entry.second, IntLiteral(entry.first))

@JvmName("atIntBitVecSortLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Int.at(index: (() -> Expression<BitVecSort>)) = IntLiteral(this) to index()

@JvmName("storeIntBitVecSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BitVecSort, IntSort>>.store(
    entry: (() -> Pair<Int, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, IntLiteral(first)) }

@JvmName("thenIntBitVecSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BitVecSort, IntSort>.then(entry: (() -> Pair<Int, Expression<BitVecSort>>)) =
    entry().let { (first, second) -> ArrayStore(this, second, IntLiteral(first)) }

@JvmName("atIntBitVecSortLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Int).at(index: (() -> Expression<BitVecSort>)) = IntLiteral(this()) to index()

@JvmName("storeIntBitVecSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BitVecSort, IntSort>>).store(
    entry: (() -> Pair<Int, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, IntLiteral(first)) }

@JvmName("thenIntBitVecSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BitVecSort, IntSort>).then(
    entry: (() -> Pair<Int, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, IntLiteral(first)) }

@JvmName("atBoolSortBitVecSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BoolSort>.at(index: Expression<BitVecSort>) = this to index

@JvmName("storeBoolSortBitVecSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BitVecSort, BoolSort>>.store(
    entry: Pair<Expression<BoolSort>, Expression<BitVecSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBoolSortBitVecSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BitVecSort, BoolSort>.then(
    entry: Pair<Expression<BoolSort>, Expression<BitVecSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBoolSortBitVecSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BoolSort>).at(index: Expression<BitVecSort>) = this() to index

@JvmName("storeBoolSortBitVecSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BitVecSort, BoolSort>>).store(
    entry: Pair<Expression<BoolSort>, Expression<BitVecSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenBoolSortBitVecSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BitVecSort, BoolSort>).then(
    entry: Pair<Expression<BoolSort>, Expression<BitVecSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atBoolSortBitVecSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BoolSort>.at(index: (() -> Expression<BitVecSort>)) = this to index()

@JvmName("storeBoolSortBitVecSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BitVecSort, BoolSort>>.store(
    entry: (() -> Pair<Expression<BoolSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenBoolSortBitVecSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BitVecSort, BoolSort>.then(
    entry: (() -> Pair<Expression<BoolSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atBoolSortBitVecSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BoolSort>).at(index: (() -> Expression<BitVecSort>)) = this() to index()

@JvmName("storeBoolSortBitVecSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BitVecSort, BoolSort>>).store(
    entry: (() -> Pair<Expression<BoolSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenBoolSortBitVecSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BitVecSort, BoolSort>).then(
    entry: (() -> Pair<Expression<BoolSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atBooleanBitVecSort")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Boolean.at(index: Expression<BitVecSort>) = this.toSMTBool() to index

@JvmName("storeBooleanBitVecSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BitVecSort, BoolSort>>.store(
    entry: Pair<Boolean, Expression<BitVecSort>>
) = ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("thenBooleanBitVecSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BitVecSort, BoolSort>.then(entry: Pair<Boolean, Expression<BitVecSort>>) =
    ArrayStore(this, entry.second, entry.first.toSMTBool())

@JvmName("atBooleanBitVecSortLambdaValue")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Boolean).at(index: Expression<BitVecSort>) = this().toSMTBool() to index

@JvmName("storeBooleanBitVecSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BitVecSort, BoolSort>>).store(
    entry: Pair<Boolean, Expression<BitVecSort>>
) = ArrayStore(this(), entry.second, entry.first.toSMTBool())

@JvmName("thenBooleanBitVecSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BitVecSort, BoolSort>).then(
    entry: Pair<Boolean, Expression<BitVecSort>>
) = ArrayStore(this(), entry.second, entry.first.toSMTBool())

@JvmName("atBooleanBitVecSortLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun Boolean.at(index: (() -> Expression<BitVecSort>)) = this.toSMTBool() to index()

@JvmName("storeBooleanBitVecSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BitVecSort, BoolSort>>.store(
    entry: (() -> Pair<Boolean, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first.toSMTBool()) }

@JvmName("thenBooleanBitVecSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BitVecSort, BoolSort>.then(
    entry: (() -> Pair<Boolean, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first.toSMTBool()) }

@JvmName("atBooleanBitVecSortLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> Boolean).at(index: (() -> Expression<BitVecSort>)) = this().toSMTBool() to index()

@JvmName("storeBooleanBitVecSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BitVecSort, BoolSort>>).store(
    entry: (() -> Pair<Boolean, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first.toSMTBool()) }

@JvmName("thenBooleanBitVecSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BitVecSort, BoolSort>).then(
    entry: (() -> Pair<Boolean, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first.toSMTBool()) }

@JvmName("atStringSortBitVecSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<StringSort>.at(index: Expression<BitVecSort>) = this to index

@JvmName("storeStringSortBitVecSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BitVecSort, StringSort>>.store(
    entry: Pair<Expression<StringSort>, Expression<BitVecSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenStringSortBitVecSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BitVecSort, StringSort>.then(
    entry: Pair<Expression<StringSort>, Expression<BitVecSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atStringSortBitVecSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<StringSort>).at(index: Expression<BitVecSort>) = this() to index

@JvmName("storeStringSortBitVecSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BitVecSort, StringSort>>).store(
    entry: Pair<Expression<StringSort>, Expression<BitVecSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenStringSortBitVecSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BitVecSort, StringSort>).then(
    entry: Pair<Expression<StringSort>, Expression<BitVecSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atStringSortBitVecSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<StringSort>.at(index: (() -> Expression<BitVecSort>)) = this to index()

@JvmName("storeStringSortBitVecSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BitVecSort, StringSort>>.store(
    entry: (() -> Pair<Expression<StringSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenStringSortBitVecSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BitVecSort, StringSort>.then(
    entry: (() -> Pair<Expression<StringSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atStringSortBitVecSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<StringSort>).at(index: (() -> Expression<BitVecSort>)) =
    this() to index()

@JvmName("storeStringSortBitVecSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BitVecSort, StringSort>>).store(
    entry: (() -> Pair<Expression<StringSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenStringSortBitVecSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BitVecSort, StringSort>).then(
    entry: (() -> Pair<Expression<StringSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atStringBitVecSort")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun String.at(index: Expression<BitVecSort>) = StringLiteral(this) to index

@JvmName("storeStringBitVecSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BitVecSort, StringSort>>.store(
    entry: Pair<String, Expression<BitVecSort>>
) = ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("thenStringBitVecSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BitVecSort, StringSort>.then(entry: Pair<String, Expression<BitVecSort>>) =
    ArrayStore(this, entry.second, StringLiteral(entry.first))

@JvmName("atStringBitVecSortLambdaValue")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> String).at(index: Expression<BitVecSort>) = StringLiteral(this()) to index

@JvmName("storeStringBitVecSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BitVecSort, StringSort>>).store(
    entry: Pair<String, Expression<BitVecSort>>
) = ArrayStore(this(), entry.second, StringLiteral(entry.first))

@JvmName("thenStringBitVecSortLambdaValue")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BitVecSort, StringSort>).then(
    entry: Pair<String, Expression<BitVecSort>>
) = ArrayStore(this(), entry.second, StringLiteral(entry.first))

@JvmName("atStringBitVecSortLambdaIndex")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun String.at(index: (() -> Expression<BitVecSort>)) = StringLiteral(this) to index()

@JvmName("storeStringBitVecSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BitVecSort, StringSort>>.store(
    entry: (() -> Pair<String, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, StringLiteral(first)) }

@JvmName("thenStringBitVecSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BitVecSort, StringSort>.then(
    entry: (() -> Pair<String, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, StringLiteral(first)) }

@JvmName("atStringBitVecSortLambda")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
/** Create a pair to store [this] at [index] in a smt array. */
infix fun (() -> String).at(index: (() -> Expression<BitVecSort>)) =
    StringLiteral(this()) to index()

@JvmName("storeStringBitVecSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BitVecSort, StringSort>>).store(
    entry: (() -> Pair<String, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, StringLiteral(first)) }

@JvmName("thenStringBitVecSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BitVecSort, StringSort>).then(
    entry: (() -> Pair<String, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, StringLiteral(first)) }

@JvmName("atRealSortBitVecSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RealSort>.at(index: Expression<BitVecSort>) = this to index

@JvmName("storeRealSortBitVecSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BitVecSort, RealSort>>.store(
    entry: Pair<Expression<RealSort>, Expression<BitVecSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRealSortBitVecSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BitVecSort, RealSort>.then(
    entry: Pair<Expression<RealSort>, Expression<BitVecSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRealSortBitVecSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RealSort>).at(index: Expression<BitVecSort>) = this() to index

@JvmName("storeRealSortBitVecSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BitVecSort, RealSort>>).store(
    entry: Pair<Expression<RealSort>, Expression<BitVecSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenRealSortBitVecSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BitVecSort, RealSort>).then(
    entry: Pair<Expression<RealSort>, Expression<BitVecSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atRealSortBitVecSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RealSort>.at(index: (() -> Expression<BitVecSort>)) = this to index()

@JvmName("storeRealSortBitVecSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BitVecSort, RealSort>>.store(
    entry: (() -> Pair<Expression<RealSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenRealSortBitVecSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BitVecSort, RealSort>.then(
    entry: (() -> Pair<Expression<RealSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atRealSortBitVecSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RealSort>).at(index: (() -> Expression<BitVecSort>)) = this() to index()

@JvmName("storeRealSortBitVecSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BitVecSort, RealSort>>).store(
    entry: (() -> Pair<Expression<RealSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenRealSortBitVecSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BitVecSort, RealSort>).then(
    entry: (() -> Pair<Expression<RealSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atRegLanSortBitVecSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RegLanSort>.at(index: Expression<BitVecSort>) = this to index

@JvmName("storeRegLanSortBitVecSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BitVecSort, RegLanSort>>.store(
    entry: Pair<Expression<RegLanSort>, Expression<BitVecSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRegLanSortBitVecSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BitVecSort, RegLanSort>.then(
    entry: Pair<Expression<RegLanSort>, Expression<BitVecSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRegLanSortBitVecSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RegLanSort>).at(index: Expression<BitVecSort>) = this() to index

@JvmName("storeRegLanSortBitVecSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BitVecSort, RegLanSort>>).store(
    entry: Pair<Expression<RegLanSort>, Expression<BitVecSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenRegLanSortBitVecSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BitVecSort, RegLanSort>).then(
    entry: Pair<Expression<RegLanSort>, Expression<BitVecSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atRegLanSortBitVecSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RegLanSort>.at(index: (() -> Expression<BitVecSort>)) = this to index()

@JvmName("storeRegLanSortBitVecSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BitVecSort, RegLanSort>>.store(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenRegLanSortBitVecSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BitVecSort, RegLanSort>.then(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atRegLanSortBitVecSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RegLanSort>).at(index: (() -> Expression<BitVecSort>)) =
    this() to index()

@JvmName("storeRegLanSortBitVecSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BitVecSort, RegLanSort>>).store(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenRegLanSortBitVecSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BitVecSort, RegLanSort>).then(
    entry: (() -> Pair<Expression<RegLanSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atFPSortBitVecSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<FPSort>.at(index: Expression<BitVecSort>) = this to index

@JvmName("storeFPSortBitVecSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BitVecSort, FPSort>>.store(
    entry: Pair<Expression<FPSort>, Expression<BitVecSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenFPSortBitVecSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BitVecSort, FPSort>.then(
    entry: Pair<Expression<FPSort>, Expression<BitVecSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atFPSortBitVecSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<FPSort>).at(index: Expression<BitVecSort>) = this() to index

@JvmName("storeFPSortBitVecSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BitVecSort, FPSort>>).store(
    entry: Pair<Expression<FPSort>, Expression<BitVecSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenFPSortBitVecSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BitVecSort, FPSort>).then(
    entry: Pair<Expression<FPSort>, Expression<BitVecSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atFPSortBitVecSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<FPSort>.at(index: (() -> Expression<BitVecSort>)) = this to index()

@JvmName("storeFPSortBitVecSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BitVecSort, FPSort>>.store(
    entry: (() -> Pair<Expression<FPSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenFPSortBitVecSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BitVecSort, FPSort>.then(
    entry: (() -> Pair<Expression<FPSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atFPSortBitVecSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<FPSort>).at(index: (() -> Expression<BitVecSort>)) = this() to index()

@JvmName("storeFPSortBitVecSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BitVecSort, FPSort>>).store(
    entry: (() -> Pair<Expression<FPSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenFPSortBitVecSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BitVecSort, FPSort>).then(
    entry: (() -> Pair<Expression<FPSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atRoundingModeSortBitVecSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RoundingModeSort>.at(index: Expression<BitVecSort>) = this to index

@JvmName("storeRoundingModeSortBitVecSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BitVecSort, RoundingModeSort>>.store(
    entry: Pair<Expression<RoundingModeSort>, Expression<BitVecSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenRoundingModeSortBitVecSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BitVecSort, RoundingModeSort>.then(
    entry: Pair<Expression<RoundingModeSort>, Expression<BitVecSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atRoundingModeSortBitVecSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RoundingModeSort>).at(index: Expression<BitVecSort>) = this() to index

@JvmName("storeRoundingModeSortBitVecSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BitVecSort, RoundingModeSort>>).store(
    entry: Pair<Expression<RoundingModeSort>, Expression<BitVecSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenRoundingModeSortBitVecSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BitVecSort, RoundingModeSort>).then(
    entry: Pair<Expression<RoundingModeSort>, Expression<BitVecSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atRoundingModeSortBitVecSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<RoundingModeSort>.at(index: (() -> Expression<BitVecSort>)) = this to index()

@JvmName("storeRoundingModeSortBitVecSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BitVecSort, RoundingModeSort>>.store(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenRoundingModeSortBitVecSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BitVecSort, RoundingModeSort>.then(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atRoundingModeSortBitVecSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<RoundingModeSort>).at(index: (() -> Expression<BitVecSort>)) =
    this() to index()

@JvmName("storeRoundingModeSortBitVecSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BitVecSort, RoundingModeSort>>).store(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenRoundingModeSortBitVecSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BitVecSort, RoundingModeSort>).then(
    entry: (() -> Pair<Expression<RoundingModeSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("atBitVecSortBitVecSort")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BitVecSort>.at(index: Expression<BitVecSort>) = this to index

@JvmName("storeBitVecSortBitVecSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BitVecSort, BitVecSort>>.store(
    entry: Pair<Expression<BitVecSort>, Expression<BitVecSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("thenBitVecSortBitVecSort")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BitVecSort, BitVecSort>.then(
    entry: Pair<Expression<BitVecSort>, Expression<BitVecSort>>
) = ArrayStore(this, entry.second, entry.first)

@JvmName("atBitVecSortBitVecSortLambdaValue")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BitVecSort>).at(index: Expression<BitVecSort>) = this() to index

@JvmName("storeBitVecSortBitVecSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BitVecSort, BitVecSort>>).store(
    entry: Pair<Expression<BitVecSort>, Expression<BitVecSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("thenBitVecSortBitVecSortLambdaArray")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BitVecSort, BitVecSort>).then(
    entry: Pair<Expression<BitVecSort>, Expression<BitVecSort>>
) = ArrayStore(this(), entry.second, entry.first)

@JvmName("atBitVecSortBitVecSortLambdaIndex")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun Expression<BitVecSort>.at(index: (() -> Expression<BitVecSort>)) = this to index()

@JvmName("storeBitVecSortBitVecSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun Expression<ArraySort<BitVecSort, BitVecSort>>.store(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("thenBitVecSortBitVecSortLambdaEntry")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun ArrayStore<BitVecSort, BitVecSort>.then(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this, second, first) }

@JvmName("atBitVecSortBitVecSortLambda")
/** Create a pair to store [this] at [index] in a smt array. */
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
infix fun (() -> Expression<BitVecSort>).at(index: (() -> Expression<BitVecSort>)) =
    this() to index()

@JvmName("storeBitVecSortBitVecSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> Expression<ArraySort<BitVecSort, BitVecSort>>).store(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@JvmName("thenBitVecSortBitVecSortLambda")
/** Store [entry.first][Pair.first] at [entry.second][Pair.second] in [this]. */
infix fun (() -> ArrayStore<BitVecSort, BitVecSort>).then(
    entry: (() -> Pair<Expression<BitVecSort>, Expression<BitVecSort>>)
) = entry().let { (first, second) -> ArrayStore(this(), second, first) }

@Deprecated(
    "The array access operator does not behave like a user would expect, thus this is deprecated and will not be implemented",
    level = DeprecationLevel.ERROR,
)
operator fun <X : Sort, Y : Sort> Expression<ArraySort<X, Y>>.get(index: Expression<X>) =
    ArraySelect(this, index)

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

import java.math.BigDecimal
import java.math.BigInteger
import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.theories.*

/** Negation operator for RealSort Expressions. */
operator fun Expression<RealSort>.unaryMinus() = RealNeg(this)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 */
infix operator fun Expression<RealSort>.minus(subtrahend: Expression<RealSort>) =
    if (this is RealSub) {
      RealSub(this.children + subtrahend)
    } else {
      RealSub(this, subtrahend)
    }

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 */
infix operator fun Expression<RealSort>.minus(subtrahend: () -> Expression<RealSort>) =
    this minus subtrahend()

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 */
infix operator fun (() -> Expression<RealSort>).minus(subtrahend: Expression<RealSort>) =
    this() minus subtrahend

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 */
infix operator fun (() -> Expression<RealSort>).minus(subtrahend: () -> Expression<RealSort>) =
    this() minus subtrahend()

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [Byte] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.minus(subtrahend: Byte) = this minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [Byte] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).minus(subtrahend: Byte) =
    this() minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [Byte] to [IntLiteral].
 */
infix operator fun Byte.minus(subtrahend: Expression<RealSort>) = RealLiteral(this) minus subtrahend

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [Byte] to [IntLiteral].
 */
infix operator fun Byte.minus(subtrahend: () -> Expression<RealSort>) =
    RealLiteral(this) minus subtrahend()

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [Short] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.minus(subtrahend: Short) =
    this minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [Short] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).minus(subtrahend: Short) =
    this() minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [Short] to [IntLiteral].
 */
infix operator fun Short.minus(subtrahend: Expression<RealSort>) =
    RealLiteral(this) minus subtrahend

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [Short] to [IntLiteral].
 */
infix operator fun Short.minus(subtrahend: () -> Expression<RealSort>) =
    RealLiteral(this) minus subtrahend()

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [Int] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.minus(subtrahend: Int) = this minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [Int] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).minus(subtrahend: Int) =
    this() minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [Int] to [IntLiteral].
 */
infix operator fun Int.minus(subtrahend: Expression<RealSort>) = RealLiteral(this) minus subtrahend

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [Int] to [IntLiteral].
 */
infix operator fun Int.minus(subtrahend: () -> Expression<RealSort>) =
    RealLiteral(this) minus subtrahend()

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [Long] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.minus(subtrahend: Long) = this minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [Long] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).minus(subtrahend: Long) =
    this() minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [Long] to [IntLiteral].
 */
infix operator fun Long.minus(subtrahend: Expression<RealSort>) = RealLiteral(this) minus subtrahend

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [Long] to [IntLiteral].
 */
infix operator fun Long.minus(subtrahend: () -> Expression<RealSort>) =
    RealLiteral(this) minus subtrahend()

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [BigInteger] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.minus(subtrahend: BigInteger) =
    this minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [BigInteger] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).minus(subtrahend: BigInteger) =
    this() minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [BigInteger] to [IntLiteral].
 */
infix operator fun BigInteger.minus(subtrahend: Expression<RealSort>) =
    RealLiteral(this) minus subtrahend

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [BigInteger] to [IntLiteral].
 */
infix operator fun BigInteger.minus(subtrahend: () -> Expression<RealSort>) =
    RealLiteral(this) minus subtrahend()

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [Float] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.minus(subtrahend: Float) =
    this minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [Float] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).minus(subtrahend: Float) =
    this() minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [Float] to [IntLiteral].
 */
infix operator fun Float.minus(subtrahend: Expression<RealSort>) =
    RealLiteral(this) minus subtrahend

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [Float] to [IntLiteral].
 */
infix operator fun Float.minus(subtrahend: () -> Expression<RealSort>) =
    RealLiteral(this) minus subtrahend()

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [Double] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.minus(subtrahend: Double) =
    this minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [Double] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).minus(subtrahend: Double) =
    this() minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [Double] to [IntLiteral].
 */
infix operator fun Double.minus(subtrahend: Expression<RealSort>) =
    RealLiteral(this) minus subtrahend

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [Double] to [IntLiteral].
 */
infix operator fun Double.minus(subtrahend: () -> Expression<RealSort>) =
    RealLiteral(this) minus subtrahend()

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [BigDecimal] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.minus(subtrahend: BigDecimal) =
    this minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [BigDecimal] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).minus(subtrahend: BigDecimal) =
    this() minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [BigDecimal] to [IntLiteral].
 */
infix operator fun BigDecimal.minus(subtrahend: Expression<RealSort>) =
    RealLiteral(this) minus subtrahend

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [BigDecimal] to [IntLiteral].
 */
infix operator fun BigDecimal.minus(subtrahend: () -> Expression<RealSort>) =
    RealLiteral(this) minus subtrahend()

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 */
infix operator fun Expression<RealSort>.plus(summand: Expression<RealSort>) =
    if (this is RealAdd) {
      RealAdd(this.children + summand)
    } else {
      RealAdd(this, summand)
    }

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 */
infix operator fun Expression<RealSort>.plus(summand: () -> Expression<RealSort>) =
    this plus summand()

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 */
infix operator fun (() -> Expression<RealSort>).plus(summand: Expression<RealSort>) =
    this() plus summand

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 */
infix operator fun (() -> Expression<RealSort>).plus(summand: () -> Expression<RealSort>) =
    this() plus summand()

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [Byte] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.plus(summand: Byte) = this plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [Byte] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).plus(summand: Byte) =
    this() plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [Byte] to [IntLiteral].
 */
infix operator fun Byte.plus(summand: Expression<RealSort>) = RealLiteral(this) plus summand

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [Byte] to [IntLiteral].
 */
infix operator fun Byte.plus(summand: () -> Expression<RealSort>) = RealLiteral(this) plus summand()

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [Short] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.plus(summand: Short) = this plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [Short] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).plus(summand: Short) =
    this() plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [Short] to [IntLiteral].
 */
infix operator fun Short.plus(summand: Expression<RealSort>) = RealLiteral(this) plus summand

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [Short] to [IntLiteral].
 */
infix operator fun Short.plus(summand: () -> Expression<RealSort>) =
    RealLiteral(this) plus summand()

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [Int] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.plus(summand: Int) = this plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [Int] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).plus(summand: Int) =
    this() plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [Int] to [IntLiteral].
 */
infix operator fun Int.plus(summand: Expression<RealSort>) = RealLiteral(this) plus summand

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [Int] to [IntLiteral].
 */
infix operator fun Int.plus(summand: () -> Expression<RealSort>) = RealLiteral(this) plus summand()

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [Long] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.plus(summand: Long) = this plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [Long] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).plus(summand: Long) =
    this() plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [Long] to [IntLiteral].
 */
infix operator fun Long.plus(summand: Expression<RealSort>) = RealLiteral(this) plus summand

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [Long] to [IntLiteral].
 */
infix operator fun Long.plus(summand: () -> Expression<RealSort>) = RealLiteral(this) plus summand()

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [BigInteger] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.plus(summand: BigInteger) = this plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [BigInteger] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).plus(summand: BigInteger) =
    this() plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [BigInteger] to [IntLiteral].
 */
infix operator fun BigInteger.plus(summand: Expression<RealSort>) = RealLiteral(this) plus summand

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [BigInteger] to [IntLiteral].
 */
infix operator fun BigInteger.plus(summand: () -> Expression<RealSort>) =
    RealLiteral(this) plus summand()

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [Float] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.plus(summand: Float) = this plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [Float] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).plus(summand: Float) =
    this() plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [Float] to [IntLiteral].
 */
infix operator fun Float.plus(summand: Expression<RealSort>) = RealLiteral(this) plus summand

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [Float] to [IntLiteral].
 */
infix operator fun Float.plus(summand: () -> Expression<RealSort>) =
    RealLiteral(this) plus summand()

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [Double] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.plus(summand: Double) = this plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [Double] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).plus(summand: Double) =
    this() plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [Double] to [IntLiteral].
 */
infix operator fun Double.plus(summand: Expression<RealSort>) = RealLiteral(this) plus summand

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [Double] to [IntLiteral].
 */
infix operator fun Double.plus(summand: () -> Expression<RealSort>) =
    RealLiteral(this) plus summand()

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [BigDecimal] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.plus(summand: BigDecimal) = this plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [BigDecimal] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).plus(summand: BigDecimal) =
    this() plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [BigDecimal] to [IntLiteral].
 */
infix operator fun BigDecimal.plus(summand: Expression<RealSort>) = RealLiteral(this) plus summand

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [BigDecimal] to [IntLiteral].
 */
infix operator fun BigDecimal.plus(summand: () -> Expression<RealSort>) =
    RealLiteral(this) plus summand()

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 */
infix operator fun Expression<RealSort>.times(multiplicand: Expression<RealSort>) =
    if (this is RealMul) {
      RealMul(this.children + multiplicand)
    } else {
      RealMul(this, multiplicand)
    }

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 */
infix operator fun Expression<RealSort>.times(multiplicand: () -> Expression<RealSort>) =
    this times multiplicand()

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 */
infix operator fun (() -> Expression<RealSort>).times(multiplicand: Expression<RealSort>) =
    this() times multiplicand

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 */
infix operator fun (() -> Expression<RealSort>).times(multiplicand: () -> Expression<RealSort>) =
    this() times multiplicand()

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [Byte] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.times(multiplicand: Byte) =
    this times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [Byte] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).times(multiplicand: Byte) =
    this() times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [Byte] to [IntLiteral].
 */
infix operator fun Byte.times(multiplicand: Expression<RealSort>) =
    RealLiteral(this) times multiplicand

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [Byte] to [IntLiteral].
 */
infix operator fun Byte.times(multiplicand: () -> Expression<RealSort>) =
    RealLiteral(this) times multiplicand()

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [Short] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.times(multiplicand: Short) =
    this times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [Short] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).times(multiplicand: Short) =
    this() times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [Short] to [IntLiteral].
 */
infix operator fun Short.times(multiplicand: Expression<RealSort>) =
    RealLiteral(this) times multiplicand

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [Short] to [IntLiteral].
 */
infix operator fun Short.times(multiplicand: () -> Expression<RealSort>) =
    RealLiteral(this) times multiplicand()

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [Int] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.times(multiplicand: Int) =
    this times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [Int] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).times(multiplicand: Int) =
    this() times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [Int] to [IntLiteral].
 */
infix operator fun Int.times(multiplicand: Expression<RealSort>) =
    RealLiteral(this) times multiplicand

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [Int] to [IntLiteral].
 */
infix operator fun Int.times(multiplicand: () -> Expression<RealSort>) =
    RealLiteral(this) times multiplicand()

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [Long] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.times(multiplicand: Long) =
    this times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [Long] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).times(multiplicand: Long) =
    this() times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [Long] to [IntLiteral].
 */
infix operator fun Long.times(multiplicand: Expression<RealSort>) =
    RealLiteral(this) times multiplicand

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [Long] to [IntLiteral].
 */
infix operator fun Long.times(multiplicand: () -> Expression<RealSort>) =
    RealLiteral(this) times multiplicand()

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [BigInteger] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.times(multiplicand: BigInteger) =
    this times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [BigInteger] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).times(multiplicand: BigInteger) =
    this() times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [BigInteger] to [IntLiteral].
 */
infix operator fun BigInteger.times(multiplicand: Expression<RealSort>) =
    RealLiteral(this) times multiplicand

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [BigInteger] to [IntLiteral].
 */
infix operator fun BigInteger.times(multiplicand: () -> Expression<RealSort>) =
    RealLiteral(this) times multiplicand()

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [Float] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.times(multiplicand: Float) =
    this times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [Float] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).times(multiplicand: Float) =
    this() times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [Float] to [IntLiteral].
 */
infix operator fun Float.times(multiplicand: Expression<RealSort>) =
    RealLiteral(this) times multiplicand

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [Float] to [IntLiteral].
 */
infix operator fun Float.times(multiplicand: () -> Expression<RealSort>) =
    RealLiteral(this) times multiplicand()

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [Double] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.times(multiplicand: Double) =
    this times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [Double] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).times(multiplicand: Double) =
    this() times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [Double] to [IntLiteral].
 */
infix operator fun Double.times(multiplicand: Expression<RealSort>) =
    RealLiteral(this) times multiplicand

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [Double] to [IntLiteral].
 */
infix operator fun Double.times(multiplicand: () -> Expression<RealSort>) =
    RealLiteral(this) times multiplicand()

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [BigDecimal] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.times(multiplicand: BigDecimal) =
    this times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [BigDecimal] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).times(multiplicand: BigDecimal) =
    this() times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [BigDecimal] to [IntLiteral].
 */
infix operator fun BigDecimal.times(multiplicand: Expression<RealSort>) =
    RealLiteral(this) times multiplicand

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [BigDecimal] to [IntLiteral].
 */
infix operator fun BigDecimal.times(multiplicand: () -> Expression<RealSort>) =
    RealLiteral(this) times multiplicand()

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 */
infix operator fun Expression<RealSort>.div(divisor: Expression<RealSort>) =
    if (this is RealDiv) {
      RealDiv(this.children + divisor)
    } else {
      RealDiv(this, divisor)
    }

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 */
infix operator fun Expression<RealSort>.div(divisor: () -> Expression<RealSort>) =
    this div divisor()

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 */
infix operator fun (() -> Expression<RealSort>).div(divisor: Expression<RealSort>) =
    this() div divisor

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 */
infix operator fun (() -> Expression<RealSort>).div(divisor: () -> Expression<RealSort>) =
    this() div divisor()

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [Byte] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.div(divisor: Byte) = this div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [Byte] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).div(divisor: Byte) = this() div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [Byte] to [IntLiteral].
 */
infix operator fun Byte.div(divisor: Expression<RealSort>) = RealLiteral(this) div divisor

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [Byte] to [IntLiteral].
 */
infix operator fun Byte.div(divisor: () -> Expression<RealSort>) = RealLiteral(this) div divisor()

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [Short] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.div(divisor: Short) = this div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [Short] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).div(divisor: Short) =
    this() div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [Short] to [IntLiteral].
 */
infix operator fun Short.div(divisor: Expression<RealSort>) = RealLiteral(this) div divisor

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [Short] to [IntLiteral].
 */
infix operator fun Short.div(divisor: () -> Expression<RealSort>) = RealLiteral(this) div divisor()

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [Int] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.div(divisor: Int) = this div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [Int] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).div(divisor: Int) = this() div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [Int] to [IntLiteral].
 */
infix operator fun Int.div(divisor: Expression<RealSort>) = RealLiteral(this) div divisor

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [Int] to [IntLiteral].
 */
infix operator fun Int.div(divisor: () -> Expression<RealSort>) = RealLiteral(this) div divisor()

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [Long] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.div(divisor: Long) = this div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [Long] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).div(divisor: Long) = this() div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [Long] to [IntLiteral].
 */
infix operator fun Long.div(divisor: Expression<RealSort>) = RealLiteral(this) div divisor

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [Long] to [IntLiteral].
 */
infix operator fun Long.div(divisor: () -> Expression<RealSort>) = RealLiteral(this) div divisor()

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [BigInteger] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.div(divisor: BigInteger) = this div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [BigInteger] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).div(divisor: BigInteger) =
    this() div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [BigInteger] to [IntLiteral].
 */
infix operator fun BigInteger.div(divisor: Expression<RealSort>) = RealLiteral(this) div divisor

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [BigInteger] to [IntLiteral].
 */
infix operator fun BigInteger.div(divisor: () -> Expression<RealSort>) =
    RealLiteral(this) div divisor()

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [Float] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.div(divisor: Float) = this div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [Float] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).div(divisor: Float) =
    this() div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [Float] to [IntLiteral].
 */
infix operator fun Float.div(divisor: Expression<RealSort>) = RealLiteral(this) div divisor

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [Float] to [IntLiteral].
 */
infix operator fun Float.div(divisor: () -> Expression<RealSort>) = RealLiteral(this) div divisor()

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [Double] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.div(divisor: Double) = this div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [Double] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).div(divisor: Double) =
    this() div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [Double] to [IntLiteral].
 */
infix operator fun Double.div(divisor: Expression<RealSort>) = RealLiteral(this) div divisor

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [Double] to [IntLiteral].
 */
infix operator fun Double.div(divisor: () -> Expression<RealSort>) = RealLiteral(this) div divisor()

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [BigDecimal] to [IntLiteral].
 */
infix operator fun Expression<RealSort>.div(divisor: BigDecimal) = this div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [BigDecimal] to [IntLiteral].
 */
infix operator fun (() -> Expression<RealSort>).div(divisor: BigDecimal) =
    this() div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [BigDecimal] to [IntLiteral].
 */
infix operator fun BigDecimal.div(divisor: Expression<RealSort>) = RealLiteral(this) div divisor

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [BigDecimal] to [IntLiteral].
 */
infix operator fun BigDecimal.div(divisor: () -> Expression<RealSort>) =
    RealLiteral(this) div divisor()

/** Greater operator for RealSort Expressions: [this] > [other]. */
infix fun Expression<RealSort>.greater(other: Expression<RealSort>) = RealGreater(this, other)

/** Greater operator for RealSort Expressions: [this] > [block]. */
infix fun Expression<RealSort>.greater(block: () -> Expression<RealSort>) = this greater block()

/** Greater operator for RealSort Expressions: [this] > [other]. */
infix fun (() -> Expression<RealSort>).greater(other: Expression<RealSort>) = this() greater other

/** Greater operator for RealSort Expressions: [this] > [block]. */
infix fun (() -> Expression<RealSort>).greater(block: () -> Expression<RealSort>) =
    this() greater block()

/** Greater operator for RealSort Expressions: [this] > [other]. */
infix fun RealGreater.greater(other: Expression<RealSort>) = RealGreater(this.children + other)

/** Greater operator for RealSort Expressions: [this] > [block]. */
infix fun RealGreater.greater(block: () -> Expression<RealSort>) =
    RealGreater(this.children + block())

/**
 * Greater operator for RealSort Expressions: [this] > [other]. other is converted from [Byte] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.greater(other: Byte) = this greater RealLiteral(other)

/**
 * Greater operator for RealSort Expressions: [this] > [other]. other is converted from [Byte] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).greater(other: Byte) = this() greater RealLiteral(other)

/**
 * Greater operator for RealSort Expressions: [this] > [other]. other is converted from [Byte] to
 * [RealLiteral].
 */
infix fun RealGreater.greater(other: Byte) = RealGreater(this.children + RealLiteral(other))

/**
 * Greater operator for RealSort Expressions: [this] > [other]. [this] is converted from [Byte] to
 * [RealLiteral].
 */
infix fun Byte.greater(other: Expression<RealSort>) = RealLiteral(this) greater other

/**
 * Greater operator for RealSort Expressions: [this] > [block]. [this] is converted from [Byte] to
 * [RealLiteral].
 */
infix fun Byte.greater(block: () -> Expression<RealSort>) = RealLiteral(this) greater block()

/**
 * Greater operator for RealSort Expressions: [this] > [other]. [this] is converted from [Byte] to
 * [RealLiteral].
 */
infix fun Byte.greater(other: RealGreater) = RealGreater(listOf(RealLiteral(this)) + other.children)

/**
 * Greater operator for RealSort Expressions: [this] > [other]. other is converted from [Short] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.greater(other: Short) = this greater RealLiteral(other)

/**
 * Greater operator for RealSort Expressions: [this] > [other]. other is converted from [Short] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).greater(other: Short) = this() greater RealLiteral(other)

/**
 * Greater operator for RealSort Expressions: [this] > [other]. other is converted from [Short] to
 * [RealLiteral].
 */
infix fun RealGreater.greater(other: Short) = RealGreater(this.children + RealLiteral(other))

/**
 * Greater operator for RealSort Expressions: [this] > [other]. [this] is converted from [Short] to
 * [RealLiteral].
 */
infix fun Short.greater(other: Expression<RealSort>) = RealLiteral(this) greater other

/**
 * Greater operator for RealSort Expressions: [this] > [block]. [this] is converted from [Short] to
 * [RealLiteral].
 */
infix fun Short.greater(block: () -> Expression<RealSort>) = RealLiteral(this) greater block()

/**
 * Greater operator for RealSort Expressions: [this] > [other]. [this] is converted from [Short] to
 * [RealLiteral].
 */
infix fun Short.greater(other: RealGreater) =
    RealGreater(listOf(RealLiteral(this)) + other.children)

/**
 * Greater operator for RealSort Expressions: [this] > [other]. other is converted from [Int] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.greater(other: Int) = this greater RealLiteral(other)

/**
 * Greater operator for RealSort Expressions: [this] > [other]. other is converted from [Int] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).greater(other: Int) = this() greater RealLiteral(other)

/**
 * Greater operator for RealSort Expressions: [this] > [other]. other is converted from [Int] to
 * [RealLiteral].
 */
infix fun RealGreater.greater(other: Int) = RealGreater(this.children + RealLiteral(other))

/**
 * Greater operator for RealSort Expressions: [this] > [other]. [this] is converted from [Int] to
 * [RealLiteral].
 */
infix fun Int.greater(other: Expression<RealSort>) = RealLiteral(this) greater other

/**
 * Greater operator for RealSort Expressions: [this] > [block]. [this] is converted from [Int] to
 * [RealLiteral].
 */
infix fun Int.greater(block: () -> Expression<RealSort>) = RealLiteral(this) greater block()

/**
 * Greater operator for RealSort Expressions: [this] > [other]. [this] is converted from [Int] to
 * [RealLiteral].
 */
infix fun Int.greater(other: RealGreater) = RealGreater(listOf(RealLiteral(this)) + other.children)

/**
 * Greater operator for RealSort Expressions: [this] > [other]. other is converted from [Long] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.greater(other: Long) = this greater RealLiteral(other)

/**
 * Greater operator for RealSort Expressions: [this] > [other]. other is converted from [Long] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).greater(other: Long) = this() greater RealLiteral(other)

/**
 * Greater operator for RealSort Expressions: [this] > [other]. other is converted from [Long] to
 * [RealLiteral].
 */
infix fun RealGreater.greater(other: Long) = RealGreater(this.children + RealLiteral(other))

/**
 * Greater operator for RealSort Expressions: [this] > [other]. [this] is converted from [Long] to
 * [RealLiteral].
 */
infix fun Long.greater(other: Expression<RealSort>) = RealLiteral(this) greater other

/**
 * Greater operator for RealSort Expressions: [this] > [block]. [this] is converted from [Long] to
 * [RealLiteral].
 */
infix fun Long.greater(block: () -> Expression<RealSort>) = RealLiteral(this) greater block()

/**
 * Greater operator for RealSort Expressions: [this] > [other]. [this] is converted from [Long] to
 * [RealLiteral].
 */
infix fun Long.greater(other: RealGreater) = RealGreater(listOf(RealLiteral(this)) + other.children)

/**
 * Greater operator for RealSort Expressions: [this] > [other]. other is converted from [BigInteger]
 * to [RealLiteral].
 */
infix fun Expression<RealSort>.greater(other: BigInteger) = this greater RealLiteral(other)

/**
 * Greater operator for RealSort Expressions: [this] > [other]. other is converted from [BigInteger]
 * to [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).greater(other: BigInteger) =
    this() greater RealLiteral(other)

/**
 * Greater operator for RealSort Expressions: [this] > [other]. other is converted from [BigInteger]
 * to [RealLiteral].
 */
infix fun RealGreater.greater(other: BigInteger) = RealGreater(this.children + RealLiteral(other))

/**
 * Greater operator for RealSort Expressions: [this] > [other]. [this] is converted from
 * [BigInteger] to [RealLiteral].
 */
infix fun BigInteger.greater(other: Expression<RealSort>) = RealLiteral(this) greater other

/**
 * Greater operator for RealSort Expressions: [this] > [block]. [this] is converted from
 * [BigInteger] to [RealLiteral].
 */
infix fun BigInteger.greater(block: () -> Expression<RealSort>) = RealLiteral(this) greater block()

/**
 * Greater operator for RealSort Expressions: [this] > [other]. [this] is converted from
 * [BigInteger] to [RealLiteral].
 */
infix fun BigInteger.greater(other: RealGreater) =
    RealGreater(listOf(RealLiteral(this)) + other.children)

/**
 * Greater operator for RealSort Expressions: [this] > [other]. other is converted from [Float] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.greater(other: Float) = this greater RealLiteral(other)

/**
 * Greater operator for RealSort Expressions: [this] > [other]. other is converted from [Float] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).greater(other: Float) = this() greater RealLiteral(other)

/**
 * Greater operator for RealSort Expressions: [this] > [other]. other is converted from [Float] to
 * [RealLiteral].
 */
infix fun RealGreater.greater(other: Float) = RealGreater(this.children + RealLiteral(other))

/**
 * Greater operator for RealSort Expressions: [this] > [other]. [this] is converted from [Float] to
 * [RealLiteral].
 */
infix fun Float.greater(other: Expression<RealSort>) = RealLiteral(this) greater other

/**
 * Greater operator for RealSort Expressions: [this] > [block]. [this] is converted from [Float] to
 * [RealLiteral].
 */
infix fun Float.greater(block: () -> Expression<RealSort>) = RealLiteral(this) greater block()

/**
 * Greater operator for RealSort Expressions: [this] > [other]. [this] is converted from [Float] to
 * [RealLiteral].
 */
infix fun Float.greater(other: RealGreater) =
    RealGreater(listOf(RealLiteral(this)) + other.children)

/**
 * Greater operator for RealSort Expressions: [this] > [other]. other is converted from [Double] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.greater(other: Double) = this greater RealLiteral(other)

/**
 * Greater operator for RealSort Expressions: [this] > [other]. other is converted from [Double] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).greater(other: Double) = this() greater RealLiteral(other)

/**
 * Greater operator for RealSort Expressions: [this] > [other]. other is converted from [Double] to
 * [RealLiteral].
 */
infix fun RealGreater.greater(other: Double) = RealGreater(this.children + RealLiteral(other))

/**
 * Greater operator for RealSort Expressions: [this] > [other]. [this] is converted from [Double] to
 * [RealLiteral].
 */
infix fun Double.greater(other: Expression<RealSort>) = RealLiteral(this) greater other

/**
 * Greater operator for RealSort Expressions: [this] > [block]. [this] is converted from [Double] to
 * [RealLiteral].
 */
infix fun Double.greater(block: () -> Expression<RealSort>) = RealLiteral(this) greater block()

/**
 * Greater operator for RealSort Expressions: [this] > [other]. [this] is converted from [Double] to
 * [RealLiteral].
 */
infix fun Double.greater(other: RealGreater) =
    RealGreater(listOf(RealLiteral(this)) + other.children)

/**
 * Greater operator for RealSort Expressions: [this] > [other]. other is converted from [BigDecimal]
 * to [RealLiteral].
 */
infix fun Expression<RealSort>.greater(other: BigDecimal) = this greater RealLiteral(other)

/**
 * Greater operator for RealSort Expressions: [this] > [other]. other is converted from [BigDecimal]
 * to [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).greater(other: BigDecimal) =
    this() greater RealLiteral(other)

/**
 * Greater operator for RealSort Expressions: [this] > [other]. other is converted from [BigDecimal]
 * to [RealLiteral].
 */
infix fun RealGreater.greater(other: BigDecimal) = RealGreater(this.children + RealLiteral(other))

/**
 * Greater operator for RealSort Expressions: [this] > [other]. [this] is converted from
 * [BigDecimal] to [RealLiteral].
 */
infix fun BigDecimal.greater(other: Expression<RealSort>) = RealLiteral(this) greater other

/**
 * Greater operator for RealSort Expressions: [this] > [block]. [this] is converted from
 * [BigDecimal] to [RealLiteral].
 */
infix fun BigDecimal.greater(block: () -> Expression<RealSort>) = RealLiteral(this) greater block()

/**
 * Greater operator for RealSort Expressions: [this] > [other]. [this] is converted from
 * [BigDecimal] to [RealLiteral].
 */
infix fun BigDecimal.greater(other: RealGreater) =
    RealGreater(listOf(RealLiteral(this)) + other.children)

private fun makeRealOperator(
    init: Builder<RealSort>.() -> Unit,
    op: (List<Expression<RealSort>>) -> Expression<RealSort>
): Expression<RealSort> {
  val builder = Builder<RealSort>()
  builder.init()

  require(builder.children.isNotEmpty())

  return if (builder.children.size == 1) {
    builder.children.single()
  } else {
    op(builder.children)
  }
}

/**
 * Addition operation for RealSort Expressions.
 *
 * Use [Builder.unaryPlus] inside the [init] lambda to add Expressions to the addition operation. If
 * only a single subexpression is added, the expression is returned directly.
 *
 * @throws [IllegalArgumentException] if no expression is added inside the [init] lambda.
 */
fun realadd(init: Builder<RealSort>.() -> Unit) = makeRealOperator(init, ::RealAdd)

/**
 * Subtraction operation for RealSort Expressions.
 *
 * Use [Builder.unaryPlus] inside the [init] lambda to add Expressions to the addition operation. If
 * only a single subexpression is added, the expression is returned directly.
 *
 * @throws [IllegalArgumentException] if no expression is added inside the [init] lambda.
 */
fun realsub(init: Builder<RealSort>.() -> Unit) = makeRealOperator(init, ::RealSub)

/**
 * Multiplication operation for RealSort Expressions.
 *
 * Use [Builder.unaryPlus] inside the [init] lambda to add Expressions to the addition operation. If
 * only a single subexpression is added, the expression is returned directly.
 *
 * @throws [IllegalArgumentException] if no expression is added inside the [init] lambda.
 */
fun realmul(init: Builder<RealSort>.() -> Unit) = makeRealOperator(init, ::RealMul)

/**
 * Division operation for RealSort Expressions.
 *
 * Use [Builder.unaryPlus] inside the [init] lambda to add Expressions to the addition operation. If
 * only a single subexpression is added, the expression is returned directly.
 *
 * @throws [IllegalArgumentException] if no expression is added inside the [init] lambda.
 */
fun realdiv(init: Builder<RealSort>.() -> Unit) = makeRealOperator(init, ::RealDiv)

/** Casting operator from RealSort to RealSort. */
fun toReal(block: () -> Expression<IntSort>) = ToReal(block())

/** Casting operator from RealSort to RealSort. */
fun toReal(expr: Expression<IntSort>) = ToReal(expr)

/** Implements smt is_int operation. */
fun isInt(expr: Expression<RealSort>) = IsInt(expr)

/** Implements smt is_int operation. */
fun isInt(block: () -> Expression<RealSort>) = IsInt(block())

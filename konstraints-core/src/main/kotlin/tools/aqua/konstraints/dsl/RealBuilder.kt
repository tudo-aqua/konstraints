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
import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.smt.IntSort
import tools.aqua.konstraints.smt.IsInt
import tools.aqua.konstraints.smt.RealAdd
import tools.aqua.konstraints.smt.RealDiv
import tools.aqua.konstraints.smt.RealGreater
import tools.aqua.konstraints.smt.RealGreaterEq
import tools.aqua.konstraints.smt.RealLess
import tools.aqua.konstraints.smt.RealLessEq
import tools.aqua.konstraints.smt.RealLiteral
import tools.aqua.konstraints.smt.RealMul
import tools.aqua.konstraints.smt.RealNeg
import tools.aqua.konstraints.smt.RealSort
import tools.aqua.konstraints.smt.RealSub
import tools.aqua.konstraints.smt.ToReal

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
 * Converts subtrahend from [Byte] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.minus(subtrahend: Byte) = this minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [Byte] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).minus(subtrahend: Byte) =
    this() minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [Byte] to [RealLiteral].
 */
infix operator fun Byte.minus(subtrahend: Expression<RealSort>) = RealLiteral(this) minus subtrahend

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [Byte] to [RealLiteral].
 */
infix operator fun Byte.minus(subtrahend: () -> Expression<RealSort>) =
    RealLiteral(this) minus subtrahend()

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [Short] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.minus(subtrahend: Short) =
    this minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [Short] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).minus(subtrahend: Short) =
    this() minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [Short] to [RealLiteral].
 */
infix operator fun Short.minus(subtrahend: Expression<RealSort>) =
    RealLiteral(this) minus subtrahend

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [Short] to [RealLiteral].
 */
infix operator fun Short.minus(subtrahend: () -> Expression<RealSort>) =
    RealLiteral(this) minus subtrahend()

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [Int] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.minus(subtrahend: Int) = this minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [Int] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).minus(subtrahend: Int) =
    this() minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [Int] to [RealLiteral].
 */
infix operator fun Int.minus(subtrahend: Expression<RealSort>) = RealLiteral(this) minus subtrahend

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [Int] to [RealLiteral].
 */
infix operator fun Int.minus(subtrahend: () -> Expression<RealSort>) =
    RealLiteral(this) minus subtrahend()

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [Long] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.minus(subtrahend: Long) = this minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [Long] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).minus(subtrahend: Long) =
    this() minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [Long] to [RealLiteral].
 */
infix operator fun Long.minus(subtrahend: Expression<RealSort>) = RealLiteral(this) minus subtrahend

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [Long] to [RealLiteral].
 */
infix operator fun Long.minus(subtrahend: () -> Expression<RealSort>) =
    RealLiteral(this) minus subtrahend()

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [BigInteger] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.minus(subtrahend: BigInteger) =
    this minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [BigInteger] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).minus(subtrahend: BigInteger) =
    this() minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [BigInteger] to [RealLiteral].
 */
infix operator fun BigInteger.minus(subtrahend: Expression<RealSort>) =
    RealLiteral(this) minus subtrahend

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [BigInteger] to [RealLiteral].
 */
infix operator fun BigInteger.minus(subtrahend: () -> Expression<RealSort>) =
    RealLiteral(this) minus subtrahend()

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [Float] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.minus(subtrahend: Float) =
    this minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [Float] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).minus(subtrahend: Float) =
    this() minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [Float] to [RealLiteral].
 */
infix operator fun Float.minus(subtrahend: Expression<RealSort>) =
    RealLiteral(this) minus subtrahend

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [Float] to [RealLiteral].
 */
infix operator fun Float.minus(subtrahend: () -> Expression<RealSort>) =
    RealLiteral(this) minus subtrahend()

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [Double] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.minus(subtrahend: Double) =
    this minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [Double] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).minus(subtrahend: Double) =
    this() minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [Double] to [RealLiteral].
 */
infix operator fun Double.minus(subtrahend: Expression<RealSort>) =
    RealLiteral(this) minus subtrahend

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [Double] to [RealLiteral].
 */
infix operator fun Double.minus(subtrahend: () -> Expression<RealSort>) =
    RealLiteral(this) minus subtrahend()

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [BigDecimal] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.minus(subtrahend: BigDecimal) =
    this minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [BigDecimal] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).minus(subtrahend: BigDecimal) =
    this() minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [BigDecimal] to [RealLiteral].
 */
infix operator fun BigDecimal.minus(subtrahend: Expression<RealSort>) =
    RealLiteral(this) minus subtrahend

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [BigDecimal] to [RealLiteral].
 */
infix operator fun BigDecimal.minus(subtrahend: () -> Expression<RealSort>) =
    RealLiteral(this) minus subtrahend()

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [String] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.minus(subtrahend: String) =
    this minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts subtrahend from [String] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).minus(subtrahend: String) =
    this() minus RealLiteral(subtrahend)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [String] to [RealLiteral].
 */
infix operator fun String.minus(subtrahend: Expression<RealSort>) =
    RealLiteral(this) minus subtrahend

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined [RealSub].
 * Converts [this] from [String] to [RealLiteral].
 */
infix operator fun String.minus(subtrahend: () -> Expression<RealSort>) =
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
 * Converts summand from [Byte] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.plus(summand: Byte) = this plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [Byte] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).plus(summand: Byte) =
    this() plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [Byte] to [RealLiteral].
 */
infix operator fun Byte.plus(summand: Expression<RealSort>) = RealLiteral(this) plus summand

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [Byte] to [RealLiteral].
 */
infix operator fun Byte.plus(summand: () -> Expression<RealSort>) = RealLiteral(this) plus summand()

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [Short] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.plus(summand: Short) = this plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [Short] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).plus(summand: Short) =
    this() plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [Short] to [RealLiteral].
 */
infix operator fun Short.plus(summand: Expression<RealSort>) = RealLiteral(this) plus summand

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [Short] to [RealLiteral].
 */
infix operator fun Short.plus(summand: () -> Expression<RealSort>) =
    RealLiteral(this) plus summand()

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [Int] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.plus(summand: Int) = this plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [Int] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).plus(summand: Int) =
    this() plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [Int] to [RealLiteral].
 */
infix operator fun Int.plus(summand: Expression<RealSort>) = RealLiteral(this) plus summand

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [Int] to [RealLiteral].
 */
infix operator fun Int.plus(summand: () -> Expression<RealSort>) = RealLiteral(this) plus summand()

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [Long] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.plus(summand: Long) = this plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [Long] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).plus(summand: Long) =
    this() plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [Long] to [RealLiteral].
 */
infix operator fun Long.plus(summand: Expression<RealSort>) = RealLiteral(this) plus summand

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [Long] to [RealLiteral].
 */
infix operator fun Long.plus(summand: () -> Expression<RealSort>) = RealLiteral(this) plus summand()

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [BigInteger] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.plus(summand: BigInteger) = this plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [BigInteger] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).plus(summand: BigInteger) =
    this() plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [BigInteger] to [RealLiteral].
 */
infix operator fun BigInteger.plus(summand: Expression<RealSort>) = RealLiteral(this) plus summand

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [BigInteger] to [RealLiteral].
 */
infix operator fun BigInteger.plus(summand: () -> Expression<RealSort>) =
    RealLiteral(this) plus summand()

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [Float] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.plus(summand: Float) = this plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [Float] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).plus(summand: Float) =
    this() plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [Float] to [RealLiteral].
 */
infix operator fun Float.plus(summand: Expression<RealSort>) = RealLiteral(this) plus summand

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [Float] to [RealLiteral].
 */
infix operator fun Float.plus(summand: () -> Expression<RealSort>) =
    RealLiteral(this) plus summand()

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [Double] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.plus(summand: Double) = this plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [Double] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).plus(summand: Double) =
    this() plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [Double] to [RealLiteral].
 */
infix operator fun Double.plus(summand: Expression<RealSort>) = RealLiteral(this) plus summand

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [Double] to [RealLiteral].
 */
infix operator fun Double.plus(summand: () -> Expression<RealSort>) =
    RealLiteral(this) plus summand()

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [BigDecimal] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.plus(summand: BigDecimal) = this plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [BigDecimal] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).plus(summand: BigDecimal) =
    this() plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [BigDecimal] to [RealLiteral].
 */
infix operator fun BigDecimal.plus(summand: Expression<RealSort>) = RealLiteral(this) plus summand

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [BigDecimal] to [RealLiteral].
 */
infix operator fun BigDecimal.plus(summand: () -> Expression<RealSort>) =
    RealLiteral(this) plus summand()

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [String] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.plus(summand: String) = this plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts summand from [String] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).plus(summand: String) =
    this() plus RealLiteral(summand)

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [String] to [RealLiteral].
 */
infix operator fun String.plus(summand: Expression<RealSort>) = RealLiteral(this) plus summand

/**
 * Addition operator for RealSort Expressions: [this] - [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined [RealAdd].
 * Converts [this] from [String] to [RealLiteral].
 */
infix operator fun String.plus(summand: () -> Expression<RealSort>) =
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
 * Converts multiplicand from [Byte] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.times(multiplicand: Byte) =
    this times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [Byte] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).times(multiplicand: Byte) =
    this() times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [Byte] to [RealLiteral].
 */
infix operator fun Byte.times(multiplicand: Expression<RealSort>) =
    RealLiteral(this) times multiplicand

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [Byte] to [RealLiteral].
 */
infix operator fun Byte.times(multiplicand: () -> Expression<RealSort>) =
    RealLiteral(this) times multiplicand()

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [Short] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.times(multiplicand: Short) =
    this times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [Short] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).times(multiplicand: Short) =
    this() times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [Short] to [RealLiteral].
 */
infix operator fun Short.times(multiplicand: Expression<RealSort>) =
    RealLiteral(this) times multiplicand

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [Short] to [RealLiteral].
 */
infix operator fun Short.times(multiplicand: () -> Expression<RealSort>) =
    RealLiteral(this) times multiplicand()

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [Int] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.times(multiplicand: Int) =
    this times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [Int] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).times(multiplicand: Int) =
    this() times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [Int] to [RealLiteral].
 */
infix operator fun Int.times(multiplicand: Expression<RealSort>) =
    RealLiteral(this) times multiplicand

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [Int] to [RealLiteral].
 */
infix operator fun Int.times(multiplicand: () -> Expression<RealSort>) =
    RealLiteral(this) times multiplicand()

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [Long] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.times(multiplicand: Long) =
    this times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [Long] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).times(multiplicand: Long) =
    this() times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [Long] to [RealLiteral].
 */
infix operator fun Long.times(multiplicand: Expression<RealSort>) =
    RealLiteral(this) times multiplicand

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [Long] to [RealLiteral].
 */
infix operator fun Long.times(multiplicand: () -> Expression<RealSort>) =
    RealLiteral(this) times multiplicand()

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [BigInteger] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.times(multiplicand: BigInteger) =
    this times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [BigInteger] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).times(multiplicand: BigInteger) =
    this() times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [BigInteger] to [RealLiteral].
 */
infix operator fun BigInteger.times(multiplicand: Expression<RealSort>) =
    RealLiteral(this) times multiplicand

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [BigInteger] to [RealLiteral].
 */
infix operator fun BigInteger.times(multiplicand: () -> Expression<RealSort>) =
    RealLiteral(this) times multiplicand()

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [Float] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.times(multiplicand: Float) =
    this times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [Float] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).times(multiplicand: Float) =
    this() times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [Float] to [RealLiteral].
 */
infix operator fun Float.times(multiplicand: Expression<RealSort>) =
    RealLiteral(this) times multiplicand

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [Float] to [RealLiteral].
 */
infix operator fun Float.times(multiplicand: () -> Expression<RealSort>) =
    RealLiteral(this) times multiplicand()

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [Double] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.times(multiplicand: Double) =
    this times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [Double] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).times(multiplicand: Double) =
    this() times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [Double] to [RealLiteral].
 */
infix operator fun Double.times(multiplicand: Expression<RealSort>) =
    RealLiteral(this) times multiplicand

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [Double] to [RealLiteral].
 */
infix operator fun Double.times(multiplicand: () -> Expression<RealSort>) =
    RealLiteral(this) times multiplicand()

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [BigDecimal] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.times(multiplicand: BigDecimal) =
    this times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [BigDecimal] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).times(multiplicand: BigDecimal) =
    this() times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [BigDecimal] to [RealLiteral].
 */
infix operator fun BigDecimal.times(multiplicand: Expression<RealSort>) =
    RealLiteral(this) times multiplicand

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [BigDecimal] to [RealLiteral].
 */
infix operator fun BigDecimal.times(multiplicand: () -> Expression<RealSort>) =
    RealLiteral(this) times multiplicand()

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [String] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.times(multiplicand: String) =
    this times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts multiplicand from [String] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).times(multiplicand: String) =
    this() times RealLiteral(multiplicand)

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [String] to [RealLiteral].
 */
infix operator fun String.times(multiplicand: Expression<RealSort>) =
    RealLiteral(this) times multiplicand

/**
 * Multiplication operator for RealSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined [RealMul].
 * Converts [this] from [String] to [RealLiteral].
 */
infix operator fun String.times(multiplicand: () -> Expression<RealSort>) =
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
 * Converts divisor from [Byte] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.div(divisor: Byte) = this div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [Byte] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).div(divisor: Byte) = this() div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [Byte] to [RealLiteral].
 */
infix operator fun Byte.div(divisor: Expression<RealSort>) = RealLiteral(this) div divisor

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [Byte] to [RealLiteral].
 */
infix operator fun Byte.div(divisor: () -> Expression<RealSort>) = RealLiteral(this) div divisor()

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [Short] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.div(divisor: Short) = this div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [Short] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).div(divisor: Short) =
    this() div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [Short] to [RealLiteral].
 */
infix operator fun Short.div(divisor: Expression<RealSort>) = RealLiteral(this) div divisor

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [Short] to [RealLiteral].
 */
infix operator fun Short.div(divisor: () -> Expression<RealSort>) = RealLiteral(this) div divisor()

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [Int] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.div(divisor: Int) = this div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [Int] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).div(divisor: Int) = this() div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [Int] to [RealLiteral].
 */
infix operator fun Int.div(divisor: Expression<RealSort>) = RealLiteral(this) div divisor

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [Int] to [RealLiteral].
 */
infix operator fun Int.div(divisor: () -> Expression<RealSort>) = RealLiteral(this) div divisor()

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [Long] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.div(divisor: Long) = this div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [Long] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).div(divisor: Long) = this() div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [Long] to [RealLiteral].
 */
infix operator fun Long.div(divisor: Expression<RealSort>) = RealLiteral(this) div divisor

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [Long] to [RealLiteral].
 */
infix operator fun Long.div(divisor: () -> Expression<RealSort>) = RealLiteral(this) div divisor()

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [BigInteger] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.div(divisor: BigInteger) = this div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [BigInteger] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).div(divisor: BigInteger) =
    this() div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [BigInteger] to [RealLiteral].
 */
infix operator fun BigInteger.div(divisor: Expression<RealSort>) = RealLiteral(this) div divisor

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [BigInteger] to [RealLiteral].
 */
infix operator fun BigInteger.div(divisor: () -> Expression<RealSort>) =
    RealLiteral(this) div divisor()

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [Float] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.div(divisor: Float) = this div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [Float] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).div(divisor: Float) =
    this() div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [Float] to [RealLiteral].
 */
infix operator fun Float.div(divisor: Expression<RealSort>) = RealLiteral(this) div divisor

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [Float] to [RealLiteral].
 */
infix operator fun Float.div(divisor: () -> Expression<RealSort>) = RealLiteral(this) div divisor()

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [Double] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.div(divisor: Double) = this div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [Double] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).div(divisor: Double) =
    this() div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [Double] to [RealLiteral].
 */
infix operator fun Double.div(divisor: Expression<RealSort>) = RealLiteral(this) div divisor

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [Double] to [RealLiteral].
 */
infix operator fun Double.div(divisor: () -> Expression<RealSort>) = RealLiteral(this) div divisor()

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [BigDecimal] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.div(divisor: BigDecimal) = this div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [BigDecimal] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).div(divisor: BigDecimal) =
    this() div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [BigDecimal] to [RealLiteral].
 */
infix operator fun BigDecimal.div(divisor: Expression<RealSort>) = RealLiteral(this) div divisor

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [BigDecimal] to [RealLiteral].
 */
infix operator fun BigDecimal.div(divisor: () -> Expression<RealSort>) =
    RealLiteral(this) div divisor()

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [String] to [RealLiteral].
 */
infix operator fun Expression<RealSort>.div(divisor: String) = this div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts divisor from [String] to [RealLiteral].
 */
infix operator fun (() -> Expression<RealSort>).div(divisor: String) =
    this() div RealLiteral(divisor)

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [String] to [RealLiteral].
 */
infix operator fun String.div(divisor: Expression<RealSort>) = RealLiteral(this) div divisor

/**
 * Divison operator for RealSort Expressions: [this] - [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined [RealDiv].
 * Converts [this] from [String] to [RealLiteral].
 */
infix operator fun String.div(divisor: () -> Expression<RealSort>) = RealLiteral(this) div divisor()

/** Gt operator for RealSort Expressions: [this] > [other]. */
infix fun Expression<RealSort>.gt(other: Expression<RealSort>) = RealGreater(this, other)

/** Gt operator for RealSort Expressions: [this] > [block]. */
infix fun Expression<RealSort>.gt(block: () -> Expression<RealSort>) = this gt block()

/** Gt operator for RealSort Expressions: [this] > [other]. */
infix fun (() -> Expression<RealSort>).gt(other: Expression<RealSort>) = this() gt other

/** Gt operator for RealSort Expressions: [this] > [block]. */
infix fun (() -> Expression<RealSort>).gt(block: () -> Expression<RealSort>) = this() gt block()

/** Gt operator for RealSort Expressions: [this] > [other]. */
infix fun RealGreater.gt(other: Expression<RealSort>) = RealGreater(this.children + other)

/** Gt operator for RealSort Expressions: [this] > [block]. */
infix fun RealGreater.gt(block: () -> Expression<RealSort>) = RealGreater(this.children + block())

/**
 * Gt operator for RealSort Expressions: [this] > [other]. other is converted from [Byte] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.gt(other: Byte) = this gt RealLiteral(other)

/**
 * Gt operator for RealSort Expressions: [this] > [other]. other is converted from [Byte] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).gt(other: Byte) = this() gt RealLiteral(other)

/**
 * Gt operator for RealSort Expressions: [this] > [other]. other is converted from [Byte] to
 * [RealLiteral].
 */
infix fun RealGreater.gt(other: Byte) = RealGreater(this.children + RealLiteral(other))

/**
 * Gt operator for RealSort Expressions: [this] > [other]. [this] is converted from [Byte] to
 * [RealLiteral].
 */
infix fun Byte.gt(other: Expression<RealSort>) = RealLiteral(this) gt other

/**
 * Gt operator for RealSort Expressions: [this] > [block]. [this] is converted from [Byte] to
 * [RealLiteral].
 */
infix fun Byte.gt(block: () -> Expression<RealSort>) = RealLiteral(this) gt block()

/**
 * Gt operator for RealSort Expressions: [this] > [other]. [this] is converted from [Byte] to
 * [RealLiteral].
 */
infix fun Byte.gt(other: RealGreater) = RealGreater(listOf(RealLiteral(this)) + other.children)

/**
 * Gt operator for RealSort Expressions: [this] > [other]. other is converted from [Short] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.gt(other: Short) = this gt RealLiteral(other)

/**
 * Gt operator for RealSort Expressions: [this] > [other]. other is converted from [Short] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).gt(other: Short) = this() gt RealLiteral(other)

/**
 * Gt operator for RealSort Expressions: [this] > [other]. other is converted from [Short] to
 * [RealLiteral].
 */
infix fun RealGreater.gt(other: Short) = RealGreater(this.children + RealLiteral(other))

/**
 * Gt operator for RealSort Expressions: [this] > [other]. [this] is converted from [Short] to
 * [RealLiteral].
 */
infix fun Short.gt(other: Expression<RealSort>) = RealLiteral(this) gt other

/**
 * Gt operator for RealSort Expressions: [this] > [block]. [this] is converted from [Short] to
 * [RealLiteral].
 */
infix fun Short.gt(block: () -> Expression<RealSort>) = RealLiteral(this) gt block()

/**
 * Gt operator for RealSort Expressions: [this] > [other]. [this] is converted from [Short] to
 * [RealLiteral].
 */
infix fun Short.gt(other: RealGreater) = RealGreater(listOf(RealLiteral(this)) + other.children)

/**
 * Gt operator for RealSort Expressions: [this] > [other]. other is converted from [Int] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.gt(other: Int) = this gt RealLiteral(other)

/**
 * Gt operator for RealSort Expressions: [this] > [other]. other is converted from [Int] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).gt(other: Int) = this() gt RealLiteral(other)

/**
 * Gt operator for RealSort Expressions: [this] > [other]. other is converted from [Int] to
 * [RealLiteral].
 */
infix fun RealGreater.gt(other: Int) = RealGreater(this.children + RealLiteral(other))

/**
 * Gt operator for RealSort Expressions: [this] > [other]. [this] is converted from [Int] to
 * [RealLiteral].
 */
infix fun Int.gt(other: Expression<RealSort>) = RealLiteral(this) gt other

/**
 * Gt operator for RealSort Expressions: [this] > [block]. [this] is converted from [Int] to
 * [RealLiteral].
 */
infix fun Int.gt(block: () -> Expression<RealSort>) = RealLiteral(this) gt block()

/**
 * Gt operator for RealSort Expressions: [this] > [other]. [this] is converted from [Int] to
 * [RealLiteral].
 */
infix fun Int.gt(other: RealGreater) = RealGreater(listOf(RealLiteral(this)) + other.children)

/**
 * Gt operator for RealSort Expressions: [this] > [other]. other is converted from [Long] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.gt(other: Long) = this gt RealLiteral(other)

/**
 * Gt operator for RealSort Expressions: [this] > [other]. other is converted from [Long] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).gt(other: Long) = this() gt RealLiteral(other)

/**
 * Gt operator for RealSort Expressions: [this] > [other]. other is converted from [Long] to
 * [RealLiteral].
 */
infix fun RealGreater.gt(other: Long) = RealGreater(this.children + RealLiteral(other))

/**
 * Gt operator for RealSort Expressions: [this] > [other]. [this] is converted from [Long] to
 * [RealLiteral].
 */
infix fun Long.gt(other: Expression<RealSort>) = RealLiteral(this) gt other

/**
 * Gt operator for RealSort Expressions: [this] > [block]. [this] is converted from [Long] to
 * [RealLiteral].
 */
infix fun Long.gt(block: () -> Expression<RealSort>) = RealLiteral(this) gt block()

/**
 * Gt operator for RealSort Expressions: [this] > [other]. [this] is converted from [Long] to
 * [RealLiteral].
 */
infix fun Long.gt(other: RealGreater) = RealGreater(listOf(RealLiteral(this)) + other.children)

/**
 * Gt operator for RealSort Expressions: [this] > [other]. other is converted from [BigInteger] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.gt(other: BigInteger) = this gt RealLiteral(other)

/**
 * Gt operator for RealSort Expressions: [this] > [other]. other is converted from [BigInteger] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).gt(other: BigInteger) = this() gt RealLiteral(other)

/**
 * Gt operator for RealSort Expressions: [this] > [other]. other is converted from [BigInteger] to
 * [RealLiteral].
 */
infix fun RealGreater.gt(other: BigInteger) = RealGreater(this.children + RealLiteral(other))

/**
 * Gt operator for RealSort Expressions: [this] > [other]. [this] is converted from [BigInteger] to
 * [RealLiteral].
 */
infix fun BigInteger.gt(other: Expression<RealSort>) = RealLiteral(this) gt other

/**
 * Gt operator for RealSort Expressions: [this] > [block]. [this] is converted from [BigInteger] to
 * [RealLiteral].
 */
infix fun BigInteger.gt(block: () -> Expression<RealSort>) = RealLiteral(this) gt block()

/**
 * Gt operator for RealSort Expressions: [this] > [other]. [this] is converted from [BigInteger] to
 * [RealLiteral].
 */
infix fun BigInteger.gt(other: RealGreater) =
    RealGreater(listOf(RealLiteral(this)) + other.children)

/**
 * Gt operator for RealSort Expressions: [this] > [other]. other is converted from [Float] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.gt(other: Float) = this gt RealLiteral(other)

/**
 * Gt operator for RealSort Expressions: [this] > [other]. other is converted from [Float] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).gt(other: Float) = this() gt RealLiteral(other)

/**
 * Gt operator for RealSort Expressions: [this] > [other]. other is converted from [Float] to
 * [RealLiteral].
 */
infix fun RealGreater.gt(other: Float) = RealGreater(this.children + RealLiteral(other))

/**
 * Gt operator for RealSort Expressions: [this] > [other]. [this] is converted from [Float] to
 * [RealLiteral].
 */
infix fun Float.gt(other: Expression<RealSort>) = RealLiteral(this) gt other

/**
 * Gt operator for RealSort Expressions: [this] > [block]. [this] is converted from [Float] to
 * [RealLiteral].
 */
infix fun Float.gt(block: () -> Expression<RealSort>) = RealLiteral(this) gt block()

/**
 * Gt operator for RealSort Expressions: [this] > [other]. [this] is converted from [Float] to
 * [RealLiteral].
 */
infix fun Float.gt(other: RealGreater) = RealGreater(listOf(RealLiteral(this)) + other.children)

/**
 * Gt operator for RealSort Expressions: [this] > [other]. other is converted from [Double] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.gt(other: Double) = this gt RealLiteral(other)

/**
 * Gt operator for RealSort Expressions: [this] > [other]. other is converted from [Double] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).gt(other: Double) = this() gt RealLiteral(other)

/**
 * Gt operator for RealSort Expressions: [this] > [other]. other is converted from [Double] to
 * [RealLiteral].
 */
infix fun RealGreater.gt(other: Double) = RealGreater(this.children + RealLiteral(other))

/**
 * Gt operator for RealSort Expressions: [this] > [other]. [this] is converted from [Double] to
 * [RealLiteral].
 */
infix fun Double.gt(other: Expression<RealSort>) = RealLiteral(this) gt other

/**
 * Gt operator for RealSort Expressions: [this] > [block]. [this] is converted from [Double] to
 * [RealLiteral].
 */
infix fun Double.gt(block: () -> Expression<RealSort>) = RealLiteral(this) gt block()

/**
 * Gt operator for RealSort Expressions: [this] > [other]. [this] is converted from [Double] to
 * [RealLiteral].
 */
infix fun Double.gt(other: RealGreater) = RealGreater(listOf(RealLiteral(this)) + other.children)

/**
 * Gt operator for RealSort Expressions: [this] > [other]. other is converted from [BigDecimal] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.gt(other: BigDecimal) = this gt RealLiteral(other)

/**
 * Gt operator for RealSort Expressions: [this] > [other]. other is converted from [BigDecimal] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).gt(other: BigDecimal) = this() gt RealLiteral(other)

/**
 * Gt operator for RealSort Expressions: [this] > [other]. other is converted from [BigDecimal] to
 * [RealLiteral].
 */
infix fun RealGreater.gt(other: BigDecimal) = RealGreater(this.children + RealLiteral(other))

/**
 * Gt operator for RealSort Expressions: [this] > [other]. [this] is converted from [BigDecimal] to
 * [RealLiteral].
 */
infix fun BigDecimal.gt(other: Expression<RealSort>) = RealLiteral(this) gt other

/**
 * Gt operator for RealSort Expressions: [this] > [block]. [this] is converted from [BigDecimal] to
 * [RealLiteral].
 */
infix fun BigDecimal.gt(block: () -> Expression<RealSort>) = RealLiteral(this) gt block()

/**
 * Gt operator for RealSort Expressions: [this] > [other]. [this] is converted from [BigDecimal] to
 * [RealLiteral].
 */
infix fun BigDecimal.gt(other: RealGreater) =
    RealGreater(listOf(RealLiteral(this)) + other.children)

/**
 * Gt operator for RealSort Expressions: [this] > [other]. other is converted from [String] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.gt(other: String) = this gt RealLiteral(other)

/**
 * Gt operator for RealSort Expressions: [this] > [other]. other is converted from [String] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).gt(other: String) = this() gt RealLiteral(other)

/**
 * Gt operator for RealSort Expressions: [this] > [other]. other is converted from [String] to
 * [RealLiteral].
 */
infix fun RealGreater.gt(other: String) = RealGreater(this.children + RealLiteral(other))

/**
 * Gt operator for RealSort Expressions: [this] > [other]. [this] is converted from [String] to
 * [RealLiteral].
 */
infix fun String.gt(other: Expression<RealSort>) = RealLiteral(this) gt other

/**
 * Gt operator for RealSort Expressions: [this] > [block]. [this] is converted from [String] to
 * [RealLiteral].
 */
infix fun String.gt(block: () -> Expression<RealSort>) = RealLiteral(this) gt block()

/**
 * Gt operator for RealSort Expressions: [this] > [other]. [this] is converted from [String] to
 * [RealLiteral].
 */
infix fun String.gt(other: RealGreater) = RealGreater(listOf(RealLiteral(this)) + other.children)

/** Geq operator for RealSort Expressions: [this] >= [other]. */
infix fun Expression<RealSort>.geq(other: Expression<RealSort>) = RealGreaterEq(this, other)

/** Geq operator for RealSort Expressions: [this] >= [block]. */
infix fun Expression<RealSort>.geq(block: () -> Expression<RealSort>) = this geq block()

/** Geq operator for RealSort Expressions: [this] >= [other]. */
infix fun (() -> Expression<RealSort>).geq(other: Expression<RealSort>) = this() geq other

/** Geq operator for RealSort Expressions: [this] >= [block]. */
infix fun (() -> Expression<RealSort>).geq(block: () -> Expression<RealSort>) = this() geq block()

/** Geq operator for RealSort Expressions: [this] >= [other]. */
infix fun RealGreaterEq.geq(other: Expression<RealSort>) = RealGreaterEq(this.children + other)

/** Geq operator for RealSort Expressions: [this] >= [block]. */
infix fun RealGreaterEq.geq(block: () -> Expression<RealSort>) =
    RealGreaterEq(this.children + block())

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. other is converted from [Byte] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.geq(other: Byte) = this geq RealLiteral(other)

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. other is converted from [Byte] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).geq(other: Byte) = this() geq RealLiteral(other)

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. other is converted from [Byte] to
 * [RealLiteral].
 */
infix fun RealGreaterEq.geq(other: Byte) = RealGreaterEq(this.children + RealLiteral(other))

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. [this] is converted from [Byte] to
 * [RealLiteral].
 */
infix fun Byte.geq(other: Expression<RealSort>) = RealLiteral(this) geq other

/**
 * Geq operator for RealSort Expressions: [this] >= [block]. [this] is converted from [Byte] to
 * [RealLiteral].
 */
infix fun Byte.geq(block: () -> Expression<RealSort>) = RealLiteral(this) geq block()

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. [this] is converted from [Byte] to
 * [RealLiteral].
 */
infix fun Byte.geq(other: RealGreaterEq) = RealGreaterEq(listOf(RealLiteral(this)) + other.children)

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. other is converted from [Short] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.geq(other: Short) = this geq RealLiteral(other)

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. other is converted from [Short] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).geq(other: Short) = this() geq RealLiteral(other)

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. other is converted from [Short] to
 * [RealLiteral].
 */
infix fun RealGreaterEq.geq(other: Short) = RealGreaterEq(this.children + RealLiteral(other))

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. [this] is converted from [Short] to
 * [RealLiteral].
 */
infix fun Short.geq(other: Expression<RealSort>) = RealLiteral(this) geq other

/**
 * Geq operator for RealSort Expressions: [this] >= [block]. [this] is converted from [Short] to
 * [RealLiteral].
 */
infix fun Short.geq(block: () -> Expression<RealSort>) = RealLiteral(this) geq block()

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. [this] is converted from [Short] to
 * [RealLiteral].
 */
infix fun Short.geq(other: RealGreaterEq) =
    RealGreaterEq(listOf(RealLiteral(this)) + other.children)

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. other is converted from [Int] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.geq(other: Int) = this geq RealLiteral(other)

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. other is converted from [Int] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).geq(other: Int) = this() geq RealLiteral(other)

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. other is converted from [Int] to
 * [RealLiteral].
 */
infix fun RealGreaterEq.geq(other: Int) = RealGreaterEq(this.children + RealLiteral(other))

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. [this] is converted from [Int] to
 * [RealLiteral].
 */
infix fun Int.geq(other: Expression<RealSort>) = RealLiteral(this) geq other

/**
 * Geq operator for RealSort Expressions: [this] >= [block]. [this] is converted from [Int] to
 * [RealLiteral].
 */
infix fun Int.geq(block: () -> Expression<RealSort>) = RealLiteral(this) geq block()

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. [this] is converted from [Int] to
 * [RealLiteral].
 */
infix fun Int.geq(other: RealGreaterEq) = RealGreaterEq(listOf(RealLiteral(this)) + other.children)

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. other is converted from [Long] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.geq(other: Long) = this geq RealLiteral(other)

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. other is converted from [Long] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).geq(other: Long) = this() geq RealLiteral(other)

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. other is converted from [Long] to
 * [RealLiteral].
 */
infix fun RealGreaterEq.geq(other: Long) = RealGreaterEq(this.children + RealLiteral(other))

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. [this] is converted from [Long] to
 * [RealLiteral].
 */
infix fun Long.geq(other: Expression<RealSort>) = RealLiteral(this) geq other

/**
 * Geq operator for RealSort Expressions: [this] >= [block]. [this] is converted from [Long] to
 * [RealLiteral].
 */
infix fun Long.geq(block: () -> Expression<RealSort>) = RealLiteral(this) geq block()

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. [this] is converted from [Long] to
 * [RealLiteral].
 */
infix fun Long.geq(other: RealGreaterEq) = RealGreaterEq(listOf(RealLiteral(this)) + other.children)

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. other is converted from [BigInteger] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.geq(other: BigInteger) = this geq RealLiteral(other)

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. other is converted from [BigInteger] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).geq(other: BigInteger) = this() geq RealLiteral(other)

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. other is converted from [BigInteger] to
 * [RealLiteral].
 */
infix fun RealGreaterEq.geq(other: BigInteger) = RealGreaterEq(this.children + RealLiteral(other))

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. [this] is converted from [BigInteger]
 * to [RealLiteral].
 */
infix fun BigInteger.geq(other: Expression<RealSort>) = RealLiteral(this) geq other

/**
 * Geq operator for RealSort Expressions: [this] >= [block]. [this] is converted from [BigInteger]
 * to [RealLiteral].
 */
infix fun BigInteger.geq(block: () -> Expression<RealSort>) = RealLiteral(this) geq block()

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. [this] is converted from [BigInteger]
 * to [RealLiteral].
 */
infix fun BigInteger.geq(other: RealGreaterEq) =
    RealGreaterEq(listOf(RealLiteral(this)) + other.children)

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. other is converted from [Float] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.geq(other: Float) = this geq RealLiteral(other)

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. other is converted from [Float] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).geq(other: Float) = this() geq RealLiteral(other)

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. other is converted from [Float] to
 * [RealLiteral].
 */
infix fun RealGreaterEq.geq(other: Float) = RealGreaterEq(this.children + RealLiteral(other))

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. [this] is converted from [Float] to
 * [RealLiteral].
 */
infix fun Float.geq(other: Expression<RealSort>) = RealLiteral(this) geq other

/**
 * Geq operator for RealSort Expressions: [this] >= [block]. [this] is converted from [Float] to
 * [RealLiteral].
 */
infix fun Float.geq(block: () -> Expression<RealSort>) = RealLiteral(this) geq block()

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. [this] is converted from [Float] to
 * [RealLiteral].
 */
infix fun Float.geq(other: RealGreaterEq) =
    RealGreaterEq(listOf(RealLiteral(this)) + other.children)

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. other is converted from [Double] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.geq(other: Double) = this geq RealLiteral(other)

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. other is converted from [Double] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).geq(other: Double) = this() geq RealLiteral(other)

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. other is converted from [Double] to
 * [RealLiteral].
 */
infix fun RealGreaterEq.geq(other: Double) = RealGreaterEq(this.children + RealLiteral(other))

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. [this] is converted from [Double] to
 * [RealLiteral].
 */
infix fun Double.geq(other: Expression<RealSort>) = RealLiteral(this) geq other

/**
 * Geq operator for RealSort Expressions: [this] >= [block]. [this] is converted from [Double] to
 * [RealLiteral].
 */
infix fun Double.geq(block: () -> Expression<RealSort>) = RealLiteral(this) geq block()

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. [this] is converted from [Double] to
 * [RealLiteral].
 */
infix fun Double.geq(other: RealGreaterEq) =
    RealGreaterEq(listOf(RealLiteral(this)) + other.children)

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. other is converted from [BigDecimal] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.geq(other: BigDecimal) = this geq RealLiteral(other)

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. other is converted from [BigDecimal] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).geq(other: BigDecimal) = this() geq RealLiteral(other)

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. other is converted from [BigDecimal] to
 * [RealLiteral].
 */
infix fun RealGreaterEq.geq(other: BigDecimal) = RealGreaterEq(this.children + RealLiteral(other))

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. [this] is converted from [BigDecimal]
 * to [RealLiteral].
 */
infix fun BigDecimal.geq(other: Expression<RealSort>) = RealLiteral(this) geq other

/**
 * Geq operator for RealSort Expressions: [this] >= [block]. [this] is converted from [BigDecimal]
 * to [RealLiteral].
 */
infix fun BigDecimal.geq(block: () -> Expression<RealSort>) = RealLiteral(this) geq block()

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. [this] is converted from [BigDecimal]
 * to [RealLiteral].
 */
infix fun BigDecimal.geq(other: RealGreaterEq) =
    RealGreaterEq(listOf(RealLiteral(this)) + other.children)

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. other is converted from [String] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.geq(other: String) = this geq RealLiteral(other)

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. other is converted from [String] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).geq(other: String) = this() geq RealLiteral(other)

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. other is converted from [String] to
 * [RealLiteral].
 */
infix fun RealGreaterEq.geq(other: String) = RealGreaterEq(this.children + RealLiteral(other))

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. [this] is converted from [String] to
 * [RealLiteral].
 */
infix fun String.geq(other: Expression<RealSort>) = RealLiteral(this) geq other

/**
 * Geq operator for RealSort Expressions: [this] >= [block]. [this] is converted from [String] to
 * [RealLiteral].
 */
infix fun String.geq(block: () -> Expression<RealSort>) = RealLiteral(this) geq block()

/**
 * Geq operator for RealSort Expressions: [this] >= [other]. [this] is converted from [String] to
 * [RealLiteral].
 */
infix fun String.geq(other: RealGreaterEq) =
    RealGreaterEq(listOf(RealLiteral(this)) + other.children)

/** Lt operator for RealSort Expressions: [this] < [other]. */
infix fun Expression<RealSort>.lt(other: Expression<RealSort>) = RealLess(this, other)

/** Lt operator for RealSort Expressions: [this] < [block]. */
infix fun Expression<RealSort>.lt(block: () -> Expression<RealSort>) = this lt block()

/** Lt operator for RealSort Expressions: [this] < [other]. */
infix fun (() -> Expression<RealSort>).lt(other: Expression<RealSort>) = this() lt other

/** Lt operator for RealSort Expressions: [this] < [block]. */
infix fun (() -> Expression<RealSort>).lt(block: () -> Expression<RealSort>) = this() lt block()

/** Lt operator for RealSort Expressions: [this] < [other]. */
infix fun RealLess.lt(other: Expression<RealSort>) = RealLess(this.children + other)

/** Lt operator for RealSort Expressions: [this] < [block]. */
infix fun RealLess.lt(block: () -> Expression<RealSort>) = RealLess(this.children + block())

/**
 * Lt operator for RealSort Expressions: [this] < [other]. other is converted from [Byte] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.lt(other: Byte) = this lt RealLiteral(other)

/**
 * Lt operator for RealSort Expressions: [this] < [other]. other is converted from [Byte] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).lt(other: Byte) = this() lt RealLiteral(other)

/**
 * Lt operator for RealSort Expressions: [this] < [other]. other is converted from [Byte] to
 * [RealLiteral].
 */
infix fun RealLess.lt(other: Byte) = RealLess(this.children + RealLiteral(other))

/**
 * Lt operator for RealSort Expressions: [this] < [other]. [this] is converted from [Byte] to
 * [RealLiteral].
 */
infix fun Byte.lt(other: Expression<RealSort>) = RealLiteral(this) lt other

/**
 * Lt operator for RealSort Expressions: [this] < [block]. [this] is converted from [Byte] to
 * [RealLiteral].
 */
infix fun Byte.lt(block: () -> Expression<RealSort>) = RealLiteral(this) lt block()

/**
 * Lt operator for RealSort Expressions: [this] < [other]. [this] is converted from [Byte] to
 * [RealLiteral].
 */
infix fun Byte.lt(other: RealLess) = RealLess(listOf(RealLiteral(this)) + other.children)

/**
 * Lt operator for RealSort Expressions: [this] < [other]. other is converted from [Short] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.lt(other: Short) = this lt RealLiteral(other)

/**
 * Lt operator for RealSort Expressions: [this] < [other]. other is converted from [Short] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).lt(other: Short) = this() lt RealLiteral(other)

/**
 * Lt operator for RealSort Expressions: [this] < [other]. other is converted from [Short] to
 * [RealLiteral].
 */
infix fun RealLess.lt(other: Short) = RealLess(this.children + RealLiteral(other))

/**
 * Lt operator for RealSort Expressions: [this] < [other]. [this] is converted from [Short] to
 * [RealLiteral].
 */
infix fun Short.lt(other: Expression<RealSort>) = RealLiteral(this) lt other

/**
 * Lt operator for RealSort Expressions: [this] < [block]. [this] is converted from [Short] to
 * [RealLiteral].
 */
infix fun Short.lt(block: () -> Expression<RealSort>) = RealLiteral(this) lt block()

/**
 * Lt operator for RealSort Expressions: [this] < [other]. [this] is converted from [Short] to
 * [RealLiteral].
 */
infix fun Short.lt(other: RealLess) = RealLess(listOf(RealLiteral(this)) + other.children)

/**
 * Lt operator for RealSort Expressions: [this] < [other]. other is converted from [Int] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.lt(other: Int) = this lt RealLiteral(other)

/**
 * Lt operator for RealSort Expressions: [this] < [other]. other is converted from [Int] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).lt(other: Int) = this() lt RealLiteral(other)

/**
 * Lt operator for RealSort Expressions: [this] < [other]. other is converted from [Int] to
 * [RealLiteral].
 */
infix fun RealLess.lt(other: Int) = RealLess(this.children + RealLiteral(other))

/**
 * Lt operator for RealSort Expressions: [this] < [other]. [this] is converted from [Int] to
 * [RealLiteral].
 */
infix fun Int.lt(other: Expression<RealSort>) = RealLiteral(this) lt other

/**
 * Lt operator for RealSort Expressions: [this] < [block]. [this] is converted from [Int] to
 * [RealLiteral].
 */
infix fun Int.lt(block: () -> Expression<RealSort>) = RealLiteral(this) lt block()

/**
 * Lt operator for RealSort Expressions: [this] < [other]. [this] is converted from [Int] to
 * [RealLiteral].
 */
infix fun Int.lt(other: RealLess) = RealLess(listOf(RealLiteral(this)) + other.children)

/**
 * Lt operator for RealSort Expressions: [this] < [other]. other is converted from [Long] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.lt(other: Long) = this lt RealLiteral(other)

/**
 * Lt operator for RealSort Expressions: [this] < [other]. other is converted from [Long] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).lt(other: Long) = this() lt RealLiteral(other)

/**
 * Lt operator for RealSort Expressions: [this] < [other]. other is converted from [Long] to
 * [RealLiteral].
 */
infix fun RealLess.lt(other: Long) = RealLess(this.children + RealLiteral(other))

/**
 * Lt operator for RealSort Expressions: [this] < [other]. [this] is converted from [Long] to
 * [RealLiteral].
 */
infix fun Long.lt(other: Expression<RealSort>) = RealLiteral(this) lt other

/**
 * Lt operator for RealSort Expressions: [this] < [block]. [this] is converted from [Long] to
 * [RealLiteral].
 */
infix fun Long.lt(block: () -> Expression<RealSort>) = RealLiteral(this) lt block()

/**
 * Lt operator for RealSort Expressions: [this] < [other]. [this] is converted from [Long] to
 * [RealLiteral].
 */
infix fun Long.lt(other: RealLess) = RealLess(listOf(RealLiteral(this)) + other.children)

/**
 * Lt operator for RealSort Expressions: [this] < [other]. other is converted from [BigInteger] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.lt(other: BigInteger) = this lt RealLiteral(other)

/**
 * Lt operator for RealSort Expressions: [this] < [other]. other is converted from [BigInteger] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).lt(other: BigInteger) = this() lt RealLiteral(other)

/**
 * Lt operator for RealSort Expressions: [this] < [other]. other is converted from [BigInteger] to
 * [RealLiteral].
 */
infix fun RealLess.lt(other: BigInteger) = RealLess(this.children + RealLiteral(other))

/**
 * Lt operator for RealSort Expressions: [this] < [other]. [this] is converted from [BigInteger] to
 * [RealLiteral].
 */
infix fun BigInteger.lt(other: Expression<RealSort>) = RealLiteral(this) lt other

/**
 * Lt operator for RealSort Expressions: [this] < [block]. [this] is converted from [BigInteger] to
 * [RealLiteral].
 */
infix fun BigInteger.lt(block: () -> Expression<RealSort>) = RealLiteral(this) lt block()

/**
 * Lt operator for RealSort Expressions: [this] < [other]. [this] is converted from [BigInteger] to
 * [RealLiteral].
 */
infix fun BigInteger.lt(other: RealLess) = RealLess(listOf(RealLiteral(this)) + other.children)

/**
 * Lt operator for RealSort Expressions: [this] < [other]. other is converted from [Float] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.lt(other: Float) = this lt RealLiteral(other)

/**
 * Lt operator for RealSort Expressions: [this] < [other]. other is converted from [Float] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).lt(other: Float) = this() lt RealLiteral(other)

/**
 * Lt operator for RealSort Expressions: [this] < [other]. other is converted from [Float] to
 * [RealLiteral].
 */
infix fun RealLess.lt(other: Float) = RealLess(this.children + RealLiteral(other))

/**
 * Lt operator for RealSort Expressions: [this] < [other]. [this] is converted from [Float] to
 * [RealLiteral].
 */
infix fun Float.lt(other: Expression<RealSort>) = RealLiteral(this) lt other

/**
 * Lt operator for RealSort Expressions: [this] < [block]. [this] is converted from [Float] to
 * [RealLiteral].
 */
infix fun Float.lt(block: () -> Expression<RealSort>) = RealLiteral(this) lt block()

/**
 * Lt operator for RealSort Expressions: [this] < [other]. [this] is converted from [Float] to
 * [RealLiteral].
 */
infix fun Float.lt(other: RealLess) = RealLess(listOf(RealLiteral(this)) + other.children)

/**
 * Lt operator for RealSort Expressions: [this] < [other]. other is converted from [Double] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.lt(other: Double) = this lt RealLiteral(other)

/**
 * Lt operator for RealSort Expressions: [this] < [other]. other is converted from [Double] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).lt(other: Double) = this() lt RealLiteral(other)

/**
 * Lt operator for RealSort Expressions: [this] < [other]. other is converted from [Double] to
 * [RealLiteral].
 */
infix fun RealLess.lt(other: Double) = RealLess(this.children + RealLiteral(other))

/**
 * Lt operator for RealSort Expressions: [this] < [other]. [this] is converted from [Double] to
 * [RealLiteral].
 */
infix fun Double.lt(other: Expression<RealSort>) = RealLiteral(this) lt other

/**
 * Lt operator for RealSort Expressions: [this] < [block]. [this] is converted from [Double] to
 * [RealLiteral].
 */
infix fun Double.lt(block: () -> Expression<RealSort>) = RealLiteral(this) lt block()

/**
 * Lt operator for RealSort Expressions: [this] < [other]. [this] is converted from [Double] to
 * [RealLiteral].
 */
infix fun Double.lt(other: RealLess) = RealLess(listOf(RealLiteral(this)) + other.children)

/**
 * Lt operator for RealSort Expressions: [this] < [other]. other is converted from [BigDecimal] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.lt(other: BigDecimal) = this lt RealLiteral(other)

/**
 * Lt operator for RealSort Expressions: [this] < [other]. other is converted from [BigDecimal] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).lt(other: BigDecimal) = this() lt RealLiteral(other)

/**
 * Lt operator for RealSort Expressions: [this] < [other]. other is converted from [BigDecimal] to
 * [RealLiteral].
 */
infix fun RealLess.lt(other: BigDecimal) = RealLess(this.children + RealLiteral(other))

/**
 * Lt operator for RealSort Expressions: [this] < [other]. [this] is converted from [BigDecimal] to
 * [RealLiteral].
 */
infix fun BigDecimal.lt(other: Expression<RealSort>) = RealLiteral(this) lt other

/**
 * Lt operator for RealSort Expressions: [this] < [block]. [this] is converted from [BigDecimal] to
 * [RealLiteral].
 */
infix fun BigDecimal.lt(block: () -> Expression<RealSort>) = RealLiteral(this) lt block()

/**
 * Lt operator for RealSort Expressions: [this] < [other]. [this] is converted from [BigDecimal] to
 * [RealLiteral].
 */
infix fun BigDecimal.lt(other: RealLess) = RealLess(listOf(RealLiteral(this)) + other.children)

/**
 * Lt operator for RealSort Expressions: [this] < [other]. other is converted from [String] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.lt(other: String) = this lt RealLiteral(other)

/**
 * Lt operator for RealSort Expressions: [this] < [other]. other is converted from [String] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).lt(other: String) = this() lt RealLiteral(other)

/**
 * Lt operator for RealSort Expressions: [this] < [other]. other is converted from [String] to
 * [RealLiteral].
 */
infix fun RealLess.lt(other: String) = RealLess(this.children + RealLiteral(other))

/**
 * Lt operator for RealSort Expressions: [this] < [other]. [this] is converted from [String] to
 * [RealLiteral].
 */
infix fun String.lt(other: Expression<RealSort>) = RealLiteral(this) lt other

/**
 * Lt operator for RealSort Expressions: [this] < [block]. [this] is converted from [String] to
 * [RealLiteral].
 */
infix fun String.lt(block: () -> Expression<RealSort>) = RealLiteral(this) lt block()

/**
 * Lt operator for RealSort Expressions: [this] < [other]. [this] is converted from [String] to
 * [RealLiteral].
 */
infix fun String.lt(other: RealLess) = RealLess(listOf(RealLiteral(this)) + other.children)

/** Leq operator for RealSort Expressions: [this] <= [other]. */
infix fun Expression<RealSort>.leq(other: Expression<RealSort>) = RealLessEq(this, other)

/** Leq operator for RealSort Expressions: [this] <= [block]. */
infix fun Expression<RealSort>.leq(block: () -> Expression<RealSort>) = this leq block()

/** Leq operator for RealSort Expressions: [this] <= [other]. */
infix fun (() -> Expression<RealSort>).leq(other: Expression<RealSort>) = this() leq other

/** Leq operator for RealSort Expressions: [this] <= [block]. */
infix fun (() -> Expression<RealSort>).leq(block: () -> Expression<RealSort>) = this() leq block()

/** Leq operator for RealSort Expressions: [this] <= [other]. */
infix fun RealLessEq.leq(other: Expression<RealSort>) = RealLessEq(this.children + other)

/** Leq operator for RealSort Expressions: [this] <= [block]. */
infix fun RealLessEq.leq(block: () -> Expression<RealSort>) = RealLessEq(this.children + block())

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. other is converted from [Byte] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.leq(other: Byte) = this leq RealLiteral(other)

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. other is converted from [Byte] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).leq(other: Byte) = this() leq RealLiteral(other)

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. other is converted from [Byte] to
 * [RealLiteral].
 */
infix fun RealLessEq.leq(other: Byte) = RealLessEq(this.children + RealLiteral(other))

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. [this] is converted from [Byte] to
 * [RealLiteral].
 */
infix fun Byte.leq(other: Expression<RealSort>) = RealLiteral(this) leq other

/**
 * Leq operator for RealSort Expressions: [this] <= [block]. [this] is converted from [Byte] to
 * [RealLiteral].
 */
infix fun Byte.leq(block: () -> Expression<RealSort>) = RealLiteral(this) leq block()

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. [this] is converted from [Byte] to
 * [RealLiteral].
 */
infix fun Byte.leq(other: RealLessEq) = RealLessEq(listOf(RealLiteral(this)) + other.children)

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. other is converted from [Short] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.leq(other: Short) = this leq RealLiteral(other)

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. other is converted from [Short] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).leq(other: Short) = this() leq RealLiteral(other)

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. other is converted from [Short] to
 * [RealLiteral].
 */
infix fun RealLessEq.leq(other: Short) = RealLessEq(this.children + RealLiteral(other))

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. [this] is converted from [Short] to
 * [RealLiteral].
 */
infix fun Short.leq(other: Expression<RealSort>) = RealLiteral(this) leq other

/**
 * Leq operator for RealSort Expressions: [this] <= [block]. [this] is converted from [Short] to
 * [RealLiteral].
 */
infix fun Short.leq(block: () -> Expression<RealSort>) = RealLiteral(this) leq block()

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. [this] is converted from [Short] to
 * [RealLiteral].
 */
infix fun Short.leq(other: RealLessEq) = RealLessEq(listOf(RealLiteral(this)) + other.children)

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. other is converted from [Int] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.leq(other: Int) = this leq RealLiteral(other)

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. other is converted from [Int] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).leq(other: Int) = this() leq RealLiteral(other)

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. other is converted from [Int] to
 * [RealLiteral].
 */
infix fun RealLessEq.leq(other: Int) = RealLessEq(this.children + RealLiteral(other))

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. [this] is converted from [Int] to
 * [RealLiteral].
 */
infix fun Int.leq(other: Expression<RealSort>) = RealLiteral(this) leq other

/**
 * Leq operator for RealSort Expressions: [this] <= [block]. [this] is converted from [Int] to
 * [RealLiteral].
 */
infix fun Int.leq(block: () -> Expression<RealSort>) = RealLiteral(this) leq block()

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. [this] is converted from [Int] to
 * [RealLiteral].
 */
infix fun Int.leq(other: RealLessEq) = RealLessEq(listOf(RealLiteral(this)) + other.children)

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. other is converted from [Long] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.leq(other: Long) = this leq RealLiteral(other)

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. other is converted from [Long] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).leq(other: Long) = this() leq RealLiteral(other)

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. other is converted from [Long] to
 * [RealLiteral].
 */
infix fun RealLessEq.leq(other: Long) = RealLessEq(this.children + RealLiteral(other))

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. [this] is converted from [Long] to
 * [RealLiteral].
 */
infix fun Long.leq(other: Expression<RealSort>) = RealLiteral(this) leq other

/**
 * Leq operator for RealSort Expressions: [this] <= [block]. [this] is converted from [Long] to
 * [RealLiteral].
 */
infix fun Long.leq(block: () -> Expression<RealSort>) = RealLiteral(this) leq block()

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. [this] is converted from [Long] to
 * [RealLiteral].
 */
infix fun Long.leq(other: RealLessEq) = RealLessEq(listOf(RealLiteral(this)) + other.children)

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. other is converted from [BigInteger] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.leq(other: BigInteger) = this leq RealLiteral(other)

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. other is converted from [BigInteger] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).leq(other: BigInteger) = this() leq RealLiteral(other)

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. other is converted from [BigInteger] to
 * [RealLiteral].
 */
infix fun RealLessEq.leq(other: BigInteger) = RealLessEq(this.children + RealLiteral(other))

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. [this] is converted from [BigInteger]
 * to [RealLiteral].
 */
infix fun BigInteger.leq(other: Expression<RealSort>) = RealLiteral(this) leq other

/**
 * Leq operator for RealSort Expressions: [this] <= [block]. [this] is converted from [BigInteger]
 * to [RealLiteral].
 */
infix fun BigInteger.leq(block: () -> Expression<RealSort>) = RealLiteral(this) leq block()

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. [this] is converted from [BigInteger]
 * to [RealLiteral].
 */
infix fun BigInteger.leq(other: RealLessEq) = RealLessEq(listOf(RealLiteral(this)) + other.children)

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. other is converted from [Float] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.leq(other: Float) = this leq RealLiteral(other)

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. other is converted from [Float] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).leq(other: Float) = this() leq RealLiteral(other)

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. other is converted from [Float] to
 * [RealLiteral].
 */
infix fun RealLessEq.leq(other: Float) = RealLessEq(this.children + RealLiteral(other))

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. [this] is converted from [Float] to
 * [RealLiteral].
 */
infix fun Float.leq(other: Expression<RealSort>) = RealLiteral(this) leq other

/**
 * Leq operator for RealSort Expressions: [this] <= [block]. [this] is converted from [Float] to
 * [RealLiteral].
 */
infix fun Float.leq(block: () -> Expression<RealSort>) = RealLiteral(this) leq block()

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. [this] is converted from [Float] to
 * [RealLiteral].
 */
infix fun Float.leq(other: RealLessEq) = RealLessEq(listOf(RealLiteral(this)) + other.children)

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. other is converted from [Double] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.leq(other: Double) = this leq RealLiteral(other)

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. other is converted from [Double] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).leq(other: Double) = this() leq RealLiteral(other)

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. other is converted from [Double] to
 * [RealLiteral].
 */
infix fun RealLessEq.leq(other: Double) = RealLessEq(this.children + RealLiteral(other))

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. [this] is converted from [Double] to
 * [RealLiteral].
 */
infix fun Double.leq(other: Expression<RealSort>) = RealLiteral(this) leq other

/**
 * Leq operator for RealSort Expressions: [this] <= [block]. [this] is converted from [Double] to
 * [RealLiteral].
 */
infix fun Double.leq(block: () -> Expression<RealSort>) = RealLiteral(this) leq block()

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. [this] is converted from [Double] to
 * [RealLiteral].
 */
infix fun Double.leq(other: RealLessEq) = RealLessEq(listOf(RealLiteral(this)) + other.children)

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. other is converted from [BigDecimal] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.leq(other: BigDecimal) = this leq RealLiteral(other)

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. other is converted from [BigDecimal] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).leq(other: BigDecimal) = this() leq RealLiteral(other)

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. other is converted from [BigDecimal] to
 * [RealLiteral].
 */
infix fun RealLessEq.leq(other: BigDecimal) = RealLessEq(this.children + RealLiteral(other))

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. [this] is converted from [BigDecimal]
 * to [RealLiteral].
 */
infix fun BigDecimal.leq(other: Expression<RealSort>) = RealLiteral(this) leq other

/**
 * Leq operator for RealSort Expressions: [this] <= [block]. [this] is converted from [BigDecimal]
 * to [RealLiteral].
 */
infix fun BigDecimal.leq(block: () -> Expression<RealSort>) = RealLiteral(this) leq block()

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. [this] is converted from [BigDecimal]
 * to [RealLiteral].
 */
infix fun BigDecimal.leq(other: RealLessEq) = RealLessEq(listOf(RealLiteral(this)) + other.children)

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. other is converted from [String] to
 * [RealLiteral].
 */
infix fun Expression<RealSort>.leq(other: String) = this leq RealLiteral(other)

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. other is converted from [String] to
 * [RealLiteral].
 */
infix fun (() -> Expression<RealSort>).leq(other: String) = this() leq RealLiteral(other)

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. other is converted from [String] to
 * [RealLiteral].
 */
infix fun RealLessEq.leq(other: String) = RealLessEq(this.children + RealLiteral(other))

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. [this] is converted from [String] to
 * [RealLiteral].
 */
infix fun String.leq(other: Expression<RealSort>) = RealLiteral(this) leq other

/**
 * Leq operator for RealSort Expressions: [this] <= [block]. [this] is converted from [String] to
 * [RealLiteral].
 */
infix fun String.leq(block: () -> Expression<RealSort>) = RealLiteral(this) leq block()

/**
 * Leq operator for RealSort Expressions: [this] <= [other]. [this] is converted from [String] to
 * [RealLiteral].
 */
infix fun String.leq(other: RealLessEq) = RealLessEq(listOf(RealLiteral(this)) + other.children)

private fun makeRealOperator(
    init: Builder<RealSort>.() -> Unit,
    op: (List<Expression<RealSort>>) -> Expression<RealSort>,
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

/** Casting operator from IntSort to RealSort. */
@JvmName("toRealLambdaPrefix")
fun toReal(block: () -> Expression<IntSort>) = ToReal(block())

/** Casting operator from IntSort to RealSort. */
@JvmName("toRealPrefix")
fun toReal(expr: Expression<IntSort>) = ToReal(expr)

/** Casting operator from IntSort to RealSort. */
@JvmName("toRealLambdaPostfix")
fun (() -> Expression<IntSort>).toReal() = ToReal(this())

/** Casting operator from IntSort to RealSort. */
@JvmName("toRealPostfix")
fun Expression<IntSort>.toReal() = ToReal(this)

/** Implements smt is_int operation. */
@JvmName("isIntPrefix")
fun isInt(expr: Expression<RealSort>) = IsInt(expr)

/** Implements smt is_int operation. */
@JvmName("isIntLambdaPrefix")
fun isInt(block: () -> Expression<RealSort>) = IsInt(block())

/** Implements smt is_int operation. */
@JvmName("isIntPostfix")
fun Expression<RealSort>.isInt() = IsInt(this)

/** Implements smt is_int operation. */
@JvmName("isIntLambdaPostfix")
fun (() -> Expression<RealSort>).isInt() = IsInt(this())

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

import java.math.BigInteger
import tools.aqua.konstraints.smt.Abs
import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.smt.IntAdd
import tools.aqua.konstraints.smt.IntDiv
import tools.aqua.konstraints.smt.IntGreater
import tools.aqua.konstraints.smt.IntLiteral
import tools.aqua.konstraints.smt.IntMul
import tools.aqua.konstraints.smt.IntNeg
import tools.aqua.konstraints.smt.IntSort
import tools.aqua.konstraints.smt.IntSub
import tools.aqua.konstraints.smt.Mod
import tools.aqua.konstraints.smt.RealSort
import tools.aqua.konstraints.smt.ToInt

/** Negation operator for IntSort Expressions. */
operator fun Expression<IntSort>.unaryMinus() = IntNeg(this)

/**
 * Subtraction operator for IntSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [IntSub] object, unpacks the children and returns a new combined [IntSub].
 */
infix operator fun Expression<IntSort>.minus(subtrahend: Expression<IntSort>) =
    if (this is IntSub) {
      IntSub(this.children + subtrahend)
    } else {
      IntSub(this, subtrahend)
    }

/**
 * Subtraction operator for IntSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [IntSub] object, unpacks the children and returns a new combined [IntSub].
 */
infix operator fun Expression<IntSort>.minus(subtrahend: () -> Expression<IntSort>) =
    this minus subtrahend()

/**
 * Subtraction operator for IntSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [IntSub] object, unpacks the children and returns a new combined [IntSub].
 */
infix operator fun (() -> Expression<IntSort>).minus(subtrahend: Expression<IntSort>) =
    this() minus subtrahend

/**
 * Subtraction operator for IntSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [IntSub] object, unpacks the children and returns a new combined [IntSub].
 */
infix operator fun (() -> Expression<IntSort>).minus(subtrahend: () -> Expression<IntSort>) =
    this() minus subtrahend()

/**
 * Subtraction operator for IntSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [IntSub] object, unpacks the children and returns a new combined [IntSub].
 * Converts subtrahend from [Byte] to [tools.aqua.konstraints.smt.IntLiteral].
 */
infix operator fun Expression<IntSort>.minus(subtrahend: Byte) = this minus IntLiteral(subtrahend)

/**
 * Subtraction operator for IntSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [IntSub] object, unpacks the children and returns a new combined [IntSub].
 * Converts subtrahend from [Byte] to [IntLiteral].
 */
infix operator fun (() -> Expression<IntSort>).minus(subtrahend: Byte) =
    this() minus IntLiteral(subtrahend)

/**
 * Subtraction operator for IntSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [IntSub] object, unpacks the children and returns a new combined [IntSub].
 * Converts [this] from [Byte] to [IntLiteral].
 */
infix operator fun Byte.minus(subtrahend: Expression<IntSort>) = IntLiteral(this) minus subtrahend

/**
 * Subtraction operator for IntSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [IntSub] object, unpacks the children and returns a new combined [IntSub].
 * Converts [this] from [Byte] to [IntLiteral].
 */
infix operator fun Byte.minus(subtrahend: () -> Expression<IntSort>) =
    IntLiteral(this) minus subtrahend()

/**
 * Subtraction operator for IntSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [IntSub] object, unpacks the children and returns a new combined [IntSub].
 * Converts subtrahend from [Short] to [IntLiteral].
 */
infix operator fun Expression<IntSort>.minus(subtrahend: Short) = this minus IntLiteral(subtrahend)

/**
 * Subtraction operator for IntSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [IntSub] object, unpacks the children and returns a new combined [IntSub].
 * Converts subtrahend from [Short] to [IntLiteral].
 */
infix operator fun (() -> Expression<IntSort>).minus(subtrahend: Short) =
    this() minus IntLiteral(subtrahend)

/**
 * Subtraction operator for IntSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [IntSub] object, unpacks the children and returns a new combined [IntSub].
 * Converts [this] from [Short] to [IntLiteral].
 */
infix operator fun Short.minus(subtrahend: Expression<IntSort>) = IntLiteral(this) minus subtrahend

/**
 * Subtraction operator for IntSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [IntSub] object, unpacks the children and returns a new combined [IntSub].
 * Converts [this] from [Short] to [IntLiteral].
 */
infix operator fun Short.minus(subtrahend: () -> Expression<IntSort>) =
    IntLiteral(this) minus subtrahend()

/**
 * Subtraction operator for IntSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [IntSub] object, unpacks the children and returns a new combined [IntSub].
 * Converts subtrahend from [Int] to [IntLiteral].
 */
infix operator fun Expression<IntSort>.minus(subtrahend: Int) = this minus IntLiteral(subtrahend)

/**
 * Subtraction operator for IntSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [IntSub] object, unpacks the children and returns a new combined [IntSub].
 * Converts subtrahend from [Int] to [IntLiteral].
 */
infix operator fun (() -> Expression<IntSort>).minus(subtrahend: Int) =
    this() minus IntLiteral(subtrahend)

/**
 * Subtraction operator for IntSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [IntSub] object, unpacks the children and returns a new combined [IntSub].
 * Converts [this] from [Int] to [IntLiteral].
 */
infix operator fun Int.minus(subtrahend: Expression<IntSort>) = IntLiteral(this) minus subtrahend

/**
 * Subtraction operator for IntSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [IntSub] object, unpacks the children and returns a new combined [IntSub].
 * Converts [this] from [Int] to [IntLiteral].
 */
infix operator fun Int.minus(subtrahend: () -> Expression<IntSort>) =
    IntLiteral(this) minus subtrahend()

/**
 * Subtraction operator for IntSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [IntSub] object, unpacks the children and returns a new combined [IntSub].
 * Converts subtrahend from [Long] to [IntLiteral].
 */
infix operator fun Expression<IntSort>.minus(subtrahend: Long) = this minus IntLiteral(subtrahend)

/**
 * Subtraction operator for IntSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [IntSub] object, unpacks the children and returns a new combined [IntSub].
 * Converts subtrahend from [Long] to [IntLiteral].
 */
infix operator fun (() -> Expression<IntSort>).minus(subtrahend: Long) =
    this() minus IntLiteral(subtrahend)

/**
 * Subtraction operator for IntSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [IntSub] object, unpacks the children and returns a new combined [IntSub].
 * Converts [this] from [Long] to [IntLiteral].
 */
infix operator fun Long.minus(subtrahend: Expression<IntSort>) = IntLiteral(this) minus subtrahend

/**
 * Subtraction operator for IntSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [IntSub] object, unpacks the children and returns a new combined [IntSub].
 * Converts [this] from [Long] to [IntLiteral].
 */
infix operator fun Long.minus(subtrahend: () -> Expression<IntSort>) =
    IntLiteral(this) minus subtrahend()

/**
 * Subtraction operator for IntSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [IntSub] object, unpacks the children and returns a new combined [IntSub].
 * Converts subtrahend from [BigInteger] to [IntLiteral].
 */
infix operator fun Expression<IntSort>.minus(subtrahend: BigInteger) =
    this minus IntLiteral(subtrahend)

/**
 * Subtraction operator for IntSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [IntSub] object, unpacks the children and returns a new combined [IntSub].
 * Converts subtrahend from [BigInteger] to [IntLiteral].
 */
infix operator fun (() -> Expression<IntSort>).minus(subtrahend: BigInteger) =
    this() minus IntLiteral(subtrahend)

/**
 * Subtraction operator for IntSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [IntSub] object, unpacks the children and returns a new combined [IntSub].
 * Converts [this] from [BigInteger] to [IntLiteral].
 */
infix operator fun BigInteger.minus(subtrahend: Expression<IntSort>) =
    IntLiteral(this) minus subtrahend

/**
 * Subtraction operator for IntSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [IntSub] object, unpacks the children and returns a new combined [IntSub].
 * Converts [this] from [BigInteger] to [IntLiteral].
 */
infix operator fun BigInteger.minus(subtrahend: () -> Expression<IntSort>) =
    IntLiteral(this) minus subtrahend()

/**
 * Addition operator for IntSort Expressions: [this] - [summand].
 *
 * If [this] is an [IntAdd] object, unpacks the children and returns a new combined [IntAdd].
 */
infix operator fun Expression<IntSort>.plus(summand: Expression<IntSort>) =
    if (this is IntAdd) {
      IntAdd(this.children + summand)
    } else {
      IntAdd(this, summand)
    }

/**
 * Addition operator for IntSort Expressions: [this] - [summand].
 *
 * If [this] is an [IntAdd] object, unpacks the children and returns a new combined [IntAdd].
 */
infix operator fun Expression<IntSort>.plus(summand: () -> Expression<IntSort>) =
    this plus summand()

/**
 * Addition operator for IntSort Expressions: [this] - [summand].
 *
 * If [this] is an [IntAdd] object, unpacks the children and returns a new combined [IntAdd].
 */
infix operator fun (() -> Expression<IntSort>).plus(summand: Expression<IntSort>) =
    this() plus summand

/**
 * Addition operator for IntSort Expressions: [this] - [summand].
 *
 * If [this] is an [IntAdd] object, unpacks the children and returns a new combined [IntAdd].
 */
infix operator fun (() -> Expression<IntSort>).plus(summand: () -> Expression<IntSort>) =
    this() plus summand()

/**
 * Addition operator for IntSort Expressions: [this] - [summand].
 *
 * If [this] is an [IntAdd] object, unpacks the children and returns a new combined [IntAdd].
 * Converts summand from [Byte] to [IntLiteral].
 */
infix operator fun Expression<IntSort>.plus(summand: Byte) = this plus IntLiteral(summand)

/**
 * Addition operator for IntSort Expressions: [this] - [summand].
 *
 * If [this] is an [IntAdd] object, unpacks the children and returns a new combined [IntAdd].
 * Converts summand from [Byte] to [IntLiteral].
 */
infix operator fun (() -> Expression<IntSort>).plus(summand: Byte) = this() plus IntLiteral(summand)

/**
 * Addition operator for IntSort Expressions: [this] - [summand].
 *
 * If [this] is an [IntAdd] object, unpacks the children and returns a new combined [IntAdd].
 * Converts [this] from [Byte] to [IntLiteral].
 */
infix operator fun Byte.plus(summand: Expression<IntSort>) = IntLiteral(this) plus summand

/**
 * Addition operator for IntSort Expressions: [this] - [summand].
 *
 * If [this] is an [IntAdd] object, unpacks the children and returns a new combined [IntAdd].
 * Converts [this] from [Byte] to [IntLiteral].
 */
infix operator fun Byte.plus(summand: () -> Expression<IntSort>) = IntLiteral(this) plus summand()

/**
 * Addition operator for IntSort Expressions: [this] - [summand].
 *
 * If [this] is an [IntAdd] object, unpacks the children and returns a new combined [IntAdd].
 * Converts summand from [Short] to [IntLiteral].
 */
infix operator fun Expression<IntSort>.plus(summand: Short) = this plus IntLiteral(summand)

/**
 * Addition operator for IntSort Expressions: [this] - [summand].
 *
 * If [this] is an [IntAdd] object, unpacks the children and returns a new combined [IntAdd].
 * Converts summand from [Short] to [IntLiteral].
 */
infix operator fun (() -> Expression<IntSort>).plus(summand: Short) =
    this() plus IntLiteral(summand)

/**
 * Addition operator for IntSort Expressions: [this] - [summand].
 *
 * If [this] is an [IntAdd] object, unpacks the children and returns a new combined [IntAdd].
 * Converts [this] from [Short] to [IntLiteral].
 */
infix operator fun Short.plus(summand: Expression<IntSort>) = IntLiteral(this) plus summand

/**
 * Addition operator for IntSort Expressions: [this] - [summand].
 *
 * If [this] is an [IntAdd] object, unpacks the children and returns a new combined [IntAdd].
 * Converts [this] from [Short] to [IntLiteral].
 */
infix operator fun Short.plus(summand: () -> Expression<IntSort>) = IntLiteral(this) plus summand()

/**
 * Addition operator for IntSort Expressions: [this] - [summand].
 *
 * If [this] is an [IntAdd] object, unpacks the children and returns a new combined [IntAdd].
 * Converts summand from [Int] to [IntLiteral].
 */
infix operator fun Expression<IntSort>.plus(summand: Int) = this plus IntLiteral(summand)

/**
 * Addition operator for IntSort Expressions: [this] - [summand].
 *
 * If [this] is an [IntAdd] object, unpacks the children and returns a new combined [IntAdd].
 * Converts summand from [Int] to [IntLiteral].
 */
infix operator fun (() -> Expression<IntSort>).plus(summand: Int) = this() plus IntLiteral(summand)

/**
 * Addition operator for IntSort Expressions: [this] - [summand].
 *
 * If [this] is an [IntAdd] object, unpacks the children and returns a new combined [IntAdd].
 * Converts [this] from [Int] to [IntLiteral].
 */
infix operator fun Int.plus(summand: Expression<IntSort>) = IntLiteral(this) plus summand

/**
 * Addition operator for IntSort Expressions: [this] - [summand].
 *
 * If [this] is an [IntAdd] object, unpacks the children and returns a new combined [IntAdd].
 * Converts [this] from [Int] to [IntLiteral].
 */
infix operator fun Int.plus(summand: () -> Expression<IntSort>) = IntLiteral(this) plus summand()

/**
 * Addition operator for IntSort Expressions: [this] - [summand].
 *
 * If [this] is an [IntAdd] object, unpacks the children and returns a new combined [IntAdd].
 * Converts summand from [Long] to [IntLiteral].
 */
infix operator fun Expression<IntSort>.plus(summand: Long) = this plus IntLiteral(summand)

/**
 * Addition operator for IntSort Expressions: [this] - [summand].
 *
 * If [this] is an [IntAdd] object, unpacks the children and returns a new combined [IntAdd].
 * Converts summand from [Long] to [IntLiteral].
 */
infix operator fun (() -> Expression<IntSort>).plus(summand: Long) = this() plus IntLiteral(summand)

/**
 * Addition operator for IntSort Expressions: [this] - [summand].
 *
 * If [this] is an [IntAdd] object, unpacks the children and returns a new combined [IntAdd].
 * Converts [this] from [Long] to [IntLiteral].
 */
infix operator fun Long.plus(summand: Expression<IntSort>) = IntLiteral(this) plus summand

/**
 * Addition operator for IntSort Expressions: [this] - [summand].
 *
 * If [this] is an [IntAdd] object, unpacks the children and returns a new combined [IntAdd].
 * Converts [this] from [Long] to [IntLiteral].
 */
infix operator fun Long.plus(summand: () -> Expression<IntSort>) = IntLiteral(this) plus summand()

/**
 * Addition operator for IntSort Expressions: [this] - [summand].
 *
 * If [this] is an [IntAdd] object, unpacks the children and returns a new combined [IntAdd].
 * Converts summand from [BigInteger] to [IntLiteral].
 */
infix operator fun Expression<IntSort>.plus(summand: BigInteger) = this plus IntLiteral(summand)

/**
 * Addition operator for IntSort Expressions: [this] - [summand].
 *
 * If [this] is an [IntAdd] object, unpacks the children and returns a new combined [IntAdd].
 * Converts summand from [BigInteger] to [IntLiteral].
 */
infix operator fun (() -> Expression<IntSort>).plus(summand: BigInteger) =
    this() plus IntLiteral(summand)

/**
 * Addition operator for IntSort Expressions: [this] - [summand].
 *
 * If [this] is an [IntAdd] object, unpacks the children and returns a new combined [IntAdd].
 * Converts [this] from [BigInteger] to [IntLiteral].
 */
infix operator fun BigInteger.plus(summand: Expression<IntSort>) = IntLiteral(this) plus summand

/**
 * Addition operator for IntSort Expressions: [this] - [summand].
 *
 * If [this] is an [IntAdd] object, unpacks the children and returns a new combined [IntAdd].
 * Converts [this] from [BigInteger] to [IntLiteral].
 */
infix operator fun BigInteger.plus(summand: () -> Expression<IntSort>) =
    IntLiteral(this) plus summand()

/**
 * Multiplication operator for IntSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [IntMul] object, unpacks the children and returns a new combined [IntMul].
 */
infix operator fun Expression<IntSort>.times(multiplicand: Expression<IntSort>) =
    if (this is IntMul) {
      IntMul(this.children + multiplicand)
    } else {
      IntMul(this, multiplicand)
    }

/**
 * Multiplication operator for IntSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [IntMul] object, unpacks the children and returns a new combined [IntMul].
 */
infix operator fun Expression<IntSort>.times(multiplicand: () -> Expression<IntSort>) =
    this times multiplicand()

/**
 * Multiplication operator for IntSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [IntMul] object, unpacks the children and returns a new combined [IntMul].
 */
infix operator fun (() -> Expression<IntSort>).times(multiplicand: Expression<IntSort>) =
    this() times multiplicand

/**
 * Multiplication operator for IntSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [IntMul] object, unpacks the children and returns a new combined [IntMul].
 */
infix operator fun (() -> Expression<IntSort>).times(multiplicand: () -> Expression<IntSort>) =
    this() times multiplicand()

/**
 * Multiplication operator for IntSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [IntMul] object, unpacks the children and returns a new combined [IntMul].
 * Converts multiplicand from [Byte] to [IntLiteral].
 */
infix operator fun Expression<IntSort>.times(multiplicand: Byte) =
    this times IntLiteral(multiplicand)

/**
 * Multiplication operator for IntSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [IntMul] object, unpacks the children and returns a new combined [IntMul].
 * Converts multiplicand from [Byte] to [IntLiteral].
 */
infix operator fun (() -> Expression<IntSort>).times(multiplicand: Byte) =
    this() times IntLiteral(multiplicand)

/**
 * Multiplication operator for IntSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [IntMul] object, unpacks the children and returns a new combined [IntMul].
 * Converts [this] from [Byte] to [IntLiteral].
 */
infix operator fun Byte.times(multiplicand: Expression<IntSort>) =
    IntLiteral(this) times multiplicand

/**
 * Multiplication operator for IntSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [IntMul] object, unpacks the children and returns a new combined [IntMul].
 * Converts [this] from [Byte] to [IntLiteral].
 */
infix operator fun Byte.times(multiplicand: () -> Expression<IntSort>) =
    IntLiteral(this) times multiplicand()

/**
 * Multiplication operator for IntSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [IntMul] object, unpacks the children and returns a new combined [IntMul].
 * Converts multiplicand from [Short] to [IntLiteral].
 */
infix operator fun Expression<IntSort>.times(multiplicand: Short) =
    this times IntLiteral(multiplicand)

/**
 * Multiplication operator for IntSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [IntMul] object, unpacks the children and returns a new combined [IntMul].
 * Converts multiplicand from [Short] to [IntLiteral].
 */
infix operator fun (() -> Expression<IntSort>).times(multiplicand: Short) =
    this() times IntLiteral(multiplicand)

/**
 * Multiplication operator for IntSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [IntMul] object, unpacks the children and returns a new combined [IntMul].
 * Converts [this] from [Short] to [IntLiteral].
 */
infix operator fun Short.times(multiplicand: Expression<IntSort>) =
    IntLiteral(this) times multiplicand

/**
 * Multiplication operator for IntSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [IntMul] object, unpacks the children and returns a new combined [IntMul].
 * Converts [this] from [Short] to [IntLiteral].
 */
infix operator fun Short.times(multiplicand: () -> Expression<IntSort>) =
    IntLiteral(this) times multiplicand()

/**
 * Multiplication operator for IntSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [IntMul] object, unpacks the children and returns a new combined [IntMul].
 * Converts multiplicand from [Int] to [IntLiteral].
 */
infix operator fun Expression<IntSort>.times(multiplicand: Int) =
    this times IntLiteral(multiplicand)

/**
 * Multiplication operator for IntSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [IntMul] object, unpacks the children and returns a new combined [IntMul].
 * Converts multiplicand from [Int] to [IntLiteral].
 */
infix operator fun (() -> Expression<IntSort>).times(multiplicand: Int) =
    this() times IntLiteral(multiplicand)

/**
 * Multiplication operator for IntSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [IntMul] object, unpacks the children and returns a new combined [IntMul].
 * Converts [this] from [Int] to [IntLiteral].
 */
infix operator fun Int.times(multiplicand: Expression<IntSort>) =
    IntLiteral(this) times multiplicand

/**
 * Multiplication operator for IntSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [IntMul] object, unpacks the children and returns a new combined [IntMul].
 * Converts [this] from [Int] to [IntLiteral].
 */
infix operator fun Int.times(multiplicand: () -> Expression<IntSort>) =
    IntLiteral(this) times multiplicand()

/**
 * Multiplication operator for IntSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [IntMul] object, unpacks the children and returns a new combined [IntMul].
 * Converts multiplicand from [Long] to [IntLiteral].
 */
infix operator fun Expression<IntSort>.times(multiplicand: Long) =
    this times IntLiteral(multiplicand)

/**
 * Multiplication operator for IntSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [IntMul] object, unpacks the children and returns a new combined [IntMul].
 * Converts multiplicand from [Long] to [IntLiteral].
 */
infix operator fun (() -> Expression<IntSort>).times(multiplicand: Long) =
    this() times IntLiteral(multiplicand)

/**
 * Multiplication operator for IntSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [IntMul] object, unpacks the children and returns a new combined [IntMul].
 * Converts [this] from [Long] to [IntLiteral].
 */
infix operator fun Long.times(multiplicand: Expression<IntSort>) =
    IntLiteral(this) times multiplicand

/**
 * Multiplication operator for IntSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [IntMul] object, unpacks the children and returns a new combined [IntMul].
 * Converts [this] from [Long] to [IntLiteral].
 */
infix operator fun Long.times(multiplicand: () -> Expression<IntSort>) =
    IntLiteral(this) times multiplicand()

/**
 * Multiplication operator for IntSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [IntMul] object, unpacks the children and returns a new combined [IntMul].
 * Converts multiplicand from [BigInteger] to [IntLiteral].
 */
infix operator fun Expression<IntSort>.times(multiplicand: BigInteger) =
    this times IntLiteral(multiplicand)

/**
 * Multiplication operator for IntSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [IntMul] object, unpacks the children and returns a new combined [IntMul].
 * Converts multiplicand from [BigInteger] to [IntLiteral].
 */
infix operator fun (() -> Expression<IntSort>).times(multiplicand: BigInteger) =
    this() times IntLiteral(multiplicand)

/**
 * Multiplication operator for IntSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [IntMul] object, unpacks the children and returns a new combined [IntMul].
 * Converts [this] from [BigInteger] to [IntLiteral].
 */
infix operator fun BigInteger.times(multiplicand: Expression<IntSort>) =
    IntLiteral(this) times multiplicand

/**
 * Multiplication operator for IntSort Expressions: [this] - [multiplicand].
 *
 * If [this] is an [IntMul] object, unpacks the children and returns a new combined [IntMul].
 * Converts [this] from [BigInteger] to [IntLiteral].
 */
infix operator fun BigInteger.times(multiplicand: () -> Expression<IntSort>) =
    IntLiteral(this) times multiplicand()

/**
 * Divison operator for IntSort Expressions: [this] - [divisor].
 *
 * If [this] is an [IntDiv] object, unpacks the children and returns a new combined [IntDiv].
 */
infix operator fun Expression<IntSort>.div(divisor: Expression<IntSort>) =
    if (this is IntDiv) {
      IntDiv(this.children + divisor)
    } else {
      IntDiv(this, divisor)
    }

/**
 * Divison operator for IntSort Expressions: [this] - [divisor].
 *
 * If [this] is an [IntDiv] object, unpacks the children and returns a new combined [IntDiv].
 */
infix operator fun Expression<IntSort>.div(divisor: () -> Expression<IntSort>) = this div divisor()

/**
 * Divison operator for IntSort Expressions: [this] - [divisor].
 *
 * If [this] is an [IntDiv] object, unpacks the children and returns a new combined [IntDiv].
 */
infix operator fun (() -> Expression<IntSort>).div(divisor: Expression<IntSort>) =
    this() div divisor

/**
 * Divison operator for IntSort Expressions: [this] - [divisor].
 *
 * If [this] is an [IntDiv] object, unpacks the children and returns a new combined [IntDiv].
 */
infix operator fun (() -> Expression<IntSort>).div(divisor: () -> Expression<IntSort>) =
    this() div divisor()

/**
 * Divison operator for IntSort Expressions: [this] - [divisor].
 *
 * If [this] is an [IntDiv] object, unpacks the children and returns a new combined [IntDiv].
 * Converts divisor from [Byte] to [IntLiteral].
 */
infix operator fun Expression<IntSort>.div(divisor: Byte) = this div IntLiteral(divisor)

/**
 * Divison operator for IntSort Expressions: [this] - [divisor].
 *
 * If [this] is an [IntDiv] object, unpacks the children and returns a new combined [IntDiv].
 * Converts divisor from [Byte] to [IntLiteral].
 */
infix operator fun (() -> Expression<IntSort>).div(divisor: Byte) = this() div IntLiteral(divisor)

/**
 * Divison operator for IntSort Expressions: [this] - [divisor].
 *
 * If [this] is an [IntDiv] object, unpacks the children and returns a new combined [IntDiv].
 * Converts [this] from [Byte] to [IntLiteral].
 */
infix operator fun Byte.div(divisor: Expression<IntSort>) = IntLiteral(this) div divisor

/**
 * Divison operator for IntSort Expressions: [this] - [divisor].
 *
 * If [this] is an [IntDiv] object, unpacks the children and returns a new combined [IntDiv].
 * Converts [this] from [Byte] to [IntLiteral].
 */
infix operator fun Byte.div(divisor: () -> Expression<IntSort>) = IntLiteral(this) div divisor()

/**
 * Divison operator for IntSort Expressions: [this] - [divisor].
 *
 * If [this] is an [IntDiv] object, unpacks the children and returns a new combined [IntDiv].
 * Converts divisor from [Short] to [IntLiteral].
 */
infix operator fun Expression<IntSort>.div(divisor: Short) = this div IntLiteral(divisor)

/**
 * Divison operator for IntSort Expressions: [this] - [divisor].
 *
 * If [this] is an [IntDiv] object, unpacks the children and returns a new combined [IntDiv].
 * Converts divisor from [Short] to [IntLiteral].
 */
infix operator fun (() -> Expression<IntSort>).div(divisor: Short) = this() div IntLiteral(divisor)

/**
 * Divison operator for IntSort Expressions: [this] - [divisor].
 *
 * If [this] is an [IntDiv] object, unpacks the children and returns a new combined [IntDiv].
 * Converts [this] from [Short] to [IntLiteral].
 */
infix operator fun Short.div(divisor: Expression<IntSort>) = IntLiteral(this) div divisor

/**
 * Divison operator for IntSort Expressions: [this] - [divisor].
 *
 * If [this] is an [IntDiv] object, unpacks the children and returns a new combined [IntDiv].
 * Converts [this] from [Short] to [IntLiteral].
 */
infix operator fun Short.div(divisor: () -> Expression<IntSort>) = IntLiteral(this) div divisor()

/**
 * Divison operator for IntSort Expressions: [this] - [divisor].
 *
 * If [this] is an [IntDiv] object, unpacks the children and returns a new combined [IntDiv].
 * Converts divisor from [Int] to [IntLiteral].
 */
infix operator fun Expression<IntSort>.div(divisor: Int) = this div IntLiteral(divisor)

/**
 * Divison operator for IntSort Expressions: [this] - [divisor].
 *
 * If [this] is an [IntDiv] object, unpacks the children and returns a new combined [IntDiv].
 * Converts divisor from [Int] to [IntLiteral].
 */
infix operator fun (() -> Expression<IntSort>).div(divisor: Int) = this() div IntLiteral(divisor)

/**
 * Divison operator for IntSort Expressions: [this] - [divisor].
 *
 * If [this] is an [IntDiv] object, unpacks the children and returns a new combined [IntDiv].
 * Converts [this] from [Int] to [IntLiteral].
 */
infix operator fun Int.div(divisor: Expression<IntSort>) = IntLiteral(this) div divisor

/**
 * Divison operator for IntSort Expressions: [this] - [divisor].
 *
 * If [this] is an [IntDiv] object, unpacks the children and returns a new combined [IntDiv].
 * Converts [this] from [Int] to [IntLiteral].
 */
infix operator fun Int.div(divisor: () -> Expression<IntSort>) = IntLiteral(this) div divisor()

/**
 * Divison operator for IntSort Expressions: [this] - [divisor].
 *
 * If [this] is an [IntDiv] object, unpacks the children and returns a new combined [IntDiv].
 * Converts divisor from [Long] to [IntLiteral].
 */
infix operator fun Expression<IntSort>.div(divisor: Long) = this div IntLiteral(divisor)

/**
 * Divison operator for IntSort Expressions: [this] - [divisor].
 *
 * If [this] is an [IntDiv] object, unpacks the children and returns a new combined [IntDiv].
 * Converts divisor from [Long] to [IntLiteral].
 */
infix operator fun (() -> Expression<IntSort>).div(divisor: Long) = this() div IntLiteral(divisor)

/**
 * Divison operator for IntSort Expressions: [this] - [divisor].
 *
 * If [this] is an [IntDiv] object, unpacks the children and returns a new combined [IntDiv].
 * Converts [this] from [Long] to [IntLiteral].
 */
infix operator fun Long.div(divisor: Expression<IntSort>) = IntLiteral(this) div divisor

/**
 * Divison operator for IntSort Expressions: [this] - [divisor].
 *
 * If [this] is an [IntDiv] object, unpacks the children and returns a new combined [IntDiv].
 * Converts [this] from [Long] to [IntLiteral].
 */
infix operator fun Long.div(divisor: () -> Expression<IntSort>) = IntLiteral(this) div divisor()

/**
 * Divison operator for IntSort Expressions: [this] - [divisor].
 *
 * If [this] is an [IntDiv] object, unpacks the children and returns a new combined [IntDiv].
 * Converts divisor from [BigInteger] to [IntLiteral].
 */
infix operator fun Expression<IntSort>.div(divisor: BigInteger) = this div IntLiteral(divisor)

/**
 * Divison operator for IntSort Expressions: [this] - [divisor].
 *
 * If [this] is an [IntDiv] object, unpacks the children and returns a new combined [IntDiv].
 * Converts divisor from [BigInteger] to [IntLiteral].
 */
infix operator fun (() -> Expression<IntSort>).div(divisor: BigInteger) =
    this() div IntLiteral(divisor)

/**
 * Divison operator for IntSort Expressions: [this] - [divisor].
 *
 * If [this] is an [IntDiv] object, unpacks the children and returns a new combined [IntDiv].
 * Converts [this] from [BigInteger] to [IntLiteral].
 */
infix operator fun BigInteger.div(divisor: Expression<IntSort>) = IntLiteral(this) div divisor

/**
 * Divison operator for IntSort Expressions: [this] - [divisor].
 *
 * If [this] is an [IntDiv] object, unpacks the children and returns a new combined [IntDiv].
 * Converts [this] from [BigInteger] to [IntLiteral].
 */
infix operator fun BigInteger.div(divisor: () -> Expression<IntSort>) =
    IntLiteral(this) div divisor()

/** Absolute value operation for IntSort Expressions. */
fun abs(block: () -> Expression<IntSort>) = Abs(block())

/** Absolute value operation for IntSort Expressions. */
fun abs(expr: Expression<IntSort>) = Abs(expr)

/** Modulo operation for IntSort Expressions: [this] mod [divisor]. */
infix fun Expression<IntSort>.mod(divisor: Expression<IntSort>) = Mod(this, divisor)

/** Modulo operation for IntSort Expressions: [this] mod [divisor]. */
infix fun Expression<IntSort>.mod(divisor: () -> Expression<IntSort>) = this mod divisor()

/** Modulo operation for IntSort Expressions: [this] mod [divisor]. */
infix fun (() -> Expression<IntSort>).mod(divisor: Expression<IntSort>) = this() mod divisor

/** Modulo operation for IntSort Expressions: [this] mod [divisor]. */
infix fun (() -> Expression<IntSort>).mod(divisor: () -> Expression<IntSort>) = this() mod divisor()

/** Greater operator for IntSort Expressions: [this] > [other]. */
infix fun Expression<IntSort>.greater(other: Expression<IntSort>) = IntGreater(this, other)

/** Greater operator for IntSort Expressions: [this] > [block]. */
infix fun Expression<IntSort>.greater(block: () -> Expression<IntSort>) = this greater block()

/** Greater operator for IntSort Expressions: [this] > [other]. */
infix fun (() -> Expression<IntSort>).greater(other: Expression<IntSort>) = this() greater other

/** Greater operator for IntSort Expressions: [this] > [block]. */
infix fun (() -> Expression<IntSort>).greater(block: () -> Expression<IntSort>) =
    this() greater block()

/** Greater operator for IntSort Expressions: [this] > [other]. */
infix fun IntGreater.greater(other: Expression<IntSort>) = IntGreater(this.children + other)

/** Greater operator for IntSort Expressions: [this] > [block]. */
infix fun IntGreater.greater(block: () -> Expression<IntSort>) = IntGreater(this.children + block())

/**
 * Greater operator for IntSort Expressions: [this] > [other]. other is converted from [Byte] to
 * [IntLiteral].
 */
infix fun Expression<IntSort>.greater(other: Byte) = this greater IntLiteral(other)

/**
 * Greater operator for IntSort Expressions: [this] > [other]. other is converted from [Byte] to
 * [IntLiteral].
 */
infix fun (() -> Expression<IntSort>).greater(other: Byte) = this() greater IntLiteral(other)

/**
 * Greater operator for IntSort Expressions: [this] > [other]. other is converted from [Byte] to
 * [IntLiteral].
 */
infix fun IntGreater.greater(other: Byte) = IntGreater(this.children + IntLiteral(other))

/**
 * Greater operator for IntSort Expressions: [this] > [other]. [this] is converted from [Byte] to
 * [IntLiteral].
 */
infix fun Byte.greater(other: Expression<IntSort>) = IntLiteral(this) greater other

/**
 * Greater operator for IntSort Expressions: [this] > [block]. [this] is converted from [Byte] to
 * [IntLiteral].
 */
infix fun Byte.greater(block: () -> Expression<IntSort>) = IntLiteral(this) greater block()

/**
 * Greater operator for IntSort Expressions: [this] > [other]. [this] is converted from [Byte] to
 * [IntLiteral].
 */
infix fun Byte.greater(other: IntGreater) = IntGreater(listOf(IntLiteral(this)) + other.children)

/**
 * Greater operator for IntSort Expressions: [this] > [other]. other is converted from [Short] to
 * [IntLiteral].
 */
infix fun Expression<IntSort>.greater(other: Short) = this greater IntLiteral(other)

/**
 * Greater operator for IntSort Expressions: [this] > [other]. other is converted from [Short] to
 * [IntLiteral].
 */
infix fun (() -> Expression<IntSort>).greater(other: Short) = this() greater IntLiteral(other)

/**
 * Greater operator for IntSort Expressions: [this] > [other]. other is converted from [Short] to
 * [IntLiteral].
 */
infix fun IntGreater.greater(other: Short) = IntGreater(this.children + IntLiteral(other))

/**
 * Greater operator for IntSort Expressions: [this] > [other]. [this] is converted from [Short] to
 * [IntLiteral].
 */
infix fun Short.greater(other: Expression<IntSort>) = IntLiteral(this) greater other

/**
 * Greater operator for IntSort Expressions: [this] > [block]. [this] is converted from [Short] to
 * [IntLiteral].
 */
infix fun Short.greater(block: () -> Expression<IntSort>) = IntLiteral(this) greater block()

/**
 * Greater operator for IntSort Expressions: [this] > [other]. [this] is converted from [Short] to
 * [IntLiteral].
 */
infix fun Short.greater(other: IntGreater) = IntGreater(listOf(IntLiteral(this)) + other.children)

/**
 * Greater operator for IntSort Expressions: [this] > [other]. other is converted from [Int] to
 * [IntLiteral].
 */
infix fun Expression<IntSort>.greater(other: Int) = this greater IntLiteral(other)

/**
 * Greater operator for IntSort Expressions: [this] > [other]. other is converted from [Int] to
 * [IntLiteral].
 */
infix fun (() -> Expression<IntSort>).greater(other: Int) = this() greater IntLiteral(other)

/**
 * Greater operator for IntSort Expressions: [this] > [other]. other is converted from [Int] to
 * [IntLiteral].
 */
infix fun IntGreater.greater(other: Int) = IntGreater(this.children + IntLiteral(other))

/**
 * Greater operator for IntSort Expressions: [this] > [other]. [this] is converted from [Int] to
 * [IntLiteral].
 */
infix fun Int.greater(other: Expression<IntSort>) = IntLiteral(this) greater other

/**
 * Greater operator for IntSort Expressions: [this] > [block]. [this] is converted from [Int] to
 * [IntLiteral].
 */
infix fun Int.greater(block: () -> Expression<IntSort>) = IntLiteral(this) greater block()

/**
 * Greater operator for IntSort Expressions: [this] > [other]. [this] is converted from [Int] to
 * [IntLiteral].
 */
infix fun Int.greater(other: IntGreater) = IntGreater(listOf(IntLiteral(this)) + other.children)

/**
 * Greater operator for IntSort Expressions: [this] > [other]. other is converted from [Long] to
 * [IntLiteral].
 */
infix fun Expression<IntSort>.greater(other: Long) = this greater IntLiteral(other)

/**
 * Greater operator for IntSort Expressions: [this] > [other]. other is converted from [Long] to
 * [IntLiteral].
 */
infix fun (() -> Expression<IntSort>).greater(other: Long) = this() greater IntLiteral(other)

/**
 * Greater operator for IntSort Expressions: [this] > [other]. other is converted from [Long] to
 * [IntLiteral].
 */
infix fun IntGreater.greater(other: Long) = IntGreater(this.children + IntLiteral(other))

/**
 * Greater operator for IntSort Expressions: [this] > [other]. [this] is converted from [Long] to
 * [IntLiteral].
 */
infix fun Long.greater(other: Expression<IntSort>) = IntLiteral(this) greater other

/**
 * Greater operator for IntSort Expressions: [this] > [block]. [this] is converted from [Long] to
 * [IntLiteral].
 */
infix fun Long.greater(block: () -> Expression<IntSort>) = IntLiteral(this) greater block()

/**
 * Greater operator for IntSort Expressions: [this] > [other]. [this] is converted from [Long] to
 * [IntLiteral].
 */
infix fun Long.greater(other: IntGreater) = IntGreater(listOf(IntLiteral(this)) + other.children)

/**
 * Greater operator for IntSort Expressions: [this] > [other]. other is converted from [BigInteger]
 * to [IntLiteral].
 */
infix fun Expression<IntSort>.greater(other: BigInteger) = this greater IntLiteral(other)

/**
 * Greater operator for IntSort Expressions: [this] > [other]. other is converted from [BigInteger]
 * to [IntLiteral].
 */
infix fun (() -> Expression<IntSort>).greater(other: BigInteger) = this() greater IntLiteral(other)

/**
 * Greater operator for IntSort Expressions: [this] > [other]. other is converted from [BigInteger]
 * to [IntLiteral].
 */
infix fun IntGreater.greater(other: BigInteger) = IntGreater(this.children + IntLiteral(other))

/**
 * Greater operator for IntSort Expressions: [this] > [other]. [this] is converted from [BigInteger]
 * to [IntLiteral].
 */
infix fun BigInteger.greater(other: Expression<IntSort>) = IntLiteral(this) greater other

/**
 * Greater operator for IntSort Expressions: [this] > [block]. [this] is converted from [BigInteger]
 * to [IntLiteral].
 */
infix fun BigInteger.greater(block: () -> Expression<IntSort>) = IntLiteral(this) greater block()

/**
 * Greater operator for IntSort Expressions: [this] > [other]. [this] is converted from [BigInteger]
 * to [IntLiteral].
 */
infix fun BigInteger.greater(other: IntGreater) =
    IntGreater(listOf(IntLiteral(this)) + other.children)

private fun makeIntOperator(
    init: Builder<IntSort>.() -> Unit,
    op: (List<Expression<IntSort>>) -> Expression<IntSort>
): Expression<IntSort> {
  val builder = Builder<IntSort>()
  builder.init()

  require(builder.children.isNotEmpty())

  return if (builder.children.size == 1) {
    builder.children.single()
  } else {
    op(builder.children)
  }
}

/**
 * Addition operation for IntSort Expressions.
 *
 * Use [Builder.unaryPlus] inside the [init] lambda to add Expressions to the addition operation. If
 * only a single subexpression is added, the expression is returned directly.
 *
 * @throws [IllegalArgumentException] if no expression is added inside the [init] lambda.
 */
fun intadd(init: Builder<IntSort>.() -> Unit) = makeIntOperator(init, ::IntAdd)

/**
 * Subtraction operation for IntSort Expressions.
 *
 * Use [Builder.unaryPlus] inside the [init] lambda to add Expressions to the addition operation. If
 * only a single subexpression is added, the expression is returned directly.
 *
 * @throws [IllegalArgumentException] if no expression is added inside the [init] lambda.
 */
fun intsub(init: Builder<IntSort>.() -> Unit) = makeIntOperator(init, ::IntSub)

/**
 * Multiplication operation for IntSort Expressions.
 *
 * Use [Builder.unaryPlus] inside the [init] lambda to add Expressions to the addition operation. If
 * only a single subexpression is added, the expression is returned directly.
 *
 * @throws [IllegalArgumentException] if no expression is added inside the [init] lambda.
 */
fun intmul(init: Builder<IntSort>.() -> Unit) = makeIntOperator(init, ::IntMul)

/**
 * Division operation for IntSort Expressions.
 *
 * Use [Builder.unaryPlus] inside the [init] lambda to add Expressions to the addition operation. If
 * only a single subexpression is added, the expression is returned directly.
 *
 * @throws [IllegalArgumentException] if no expression is added inside the [init] lambda.
 */
fun intdiv(init: Builder<IntSort>.() -> Unit) = makeIntOperator(init, ::IntDiv)

/** Casting operator from RealSort to IntSort. */
fun toInt(block: () -> Expression<RealSort>) = ToInt(block())

/** Casting operator from RealSort to IntSort. */
fun toInt(expr: Expression<RealSort>) = ToInt(expr)

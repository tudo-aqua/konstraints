/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2024 The Konstraints Authors
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

import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.theories.*

/**
 * Negation operator for RealSort Expressions
 */
operator fun Expression<RealSort>.unaryMinus() = RealNeg(this)

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined RealSub
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
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined RealSub
 */
infix fun Expression<RealSort>.minus(subtrahend: () -> Expression<RealSort>) = this minus subtrahend()

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined RealSub
 */
infix fun (() -> Expression<RealSort>).minus(subtrahend: Expression<RealSort>) = this() minus subtrahend

/**
 * Subtraction operator for RealSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [RealSub] object, unpacks the children and returns a new combined RealSub
 */
infix fun (() -> Expression<RealSort>).minus(subtrahend: () -> Expression<RealSort>) = this() minus subtrahend()

/**
 * Addition operator for RealSort Expressions: [this] + [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined RealAdd
 */
infix operator fun Expression<RealSort>.plus(summand: Expression<RealSort>) =
    if (this is RealAdd) {
        RealAdd(this.children + summand)
    } else {
        RealAdd(this, summand)
    }


/**
 * Addition operator for RealSort Expressions: [this] + [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined RealAdd
 */
infix fun Expression<RealSort>.plus(summand: () -> Expression<RealSort>) = this plus summand()

/**
 * Addition operator for RealSort Expressions: [this] + [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined RealAdd
 */
infix fun (() -> Expression<RealSort>).plus(summand: Expression<RealSort>) = this() plus summand

/**
 * Addition operator for RealSort Expressions: [this] + [summand].
 *
 * If [this] is an [RealAdd] object, unpacks the children and returns a new combined RealAdd
 */
infix fun (() -> Expression<RealSort>).plus(summand: () -> Expression<RealSort>) = this() plus summand()

/**
 * Multiplication operator for RealSort Expressions: [this] * [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined RealMul
 */
infix operator fun Expression<RealSort>.times(multiplicand: Expression<RealSort>) =
    if (this is RealMul) {
        RealMul(this.children + multiplicand)
    } else {
        RealMul(this, multiplicand)
    }

/**
 * Multiplication operator for RealSort Expressions: [this] * [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined RealMul
 */
infix fun Expression<RealSort>.times(multiplicand: () -> Expression<RealSort>) = this times multiplicand()

/**
 * Multiplication operator for RealSort Expressions: [this] * [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined RealMul
 */
infix fun (() -> Expression<RealSort>).times(multiplicand: Expression<RealSort>) = this() times multiplicand

/**
 * Multiplication operator for RealSort Expressions: [this] * [multiplicand].
 *
 * If [this] is an [RealMul] object, unpacks the children and returns a new combined RealMul
 */
infix fun (() -> Expression<RealSort>).times(multiplicand: () -> Expression<RealSort>) = this() times multiplicand()

/**
 * Division operator for RealSort Expressions: [this] / [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined RealMul
 */
infix operator fun Expression<RealSort>.div(divisor: Expression<RealSort>) =
    if (this is RealDiv) {
        RealDiv(this.children + divisor)
    } else {
        RealDiv(this, divisor)
    }

/**
 * Division operator for RealSort Expressions: [this] / [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined RealMul
 */
infix fun Expression<RealSort>.div(divisor: () -> Expression<RealSort>) = this div divisor()

/**
 * Division operator for RealSort Expressions: [this] / [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined RealMul
 */
infix fun (() -> Expression<RealSort>).div(divisor: Expression<RealSort>) = this() div divisor

/**
 * Division operator for RealSort Expressions: [this] / [divisor].
 *
 * If [this] is an [RealDiv] object, unpacks the children and returns a new combined RealMul
 */
infix fun (() -> Expression<RealSort>).div(divisor: () -> Expression<RealSort>) = this() div divisor()

/**
 * Greater operator for RealSort Expressions: [this] > [other].
 */
infix fun Expression<RealSort>.greater(other: Expression<RealSort>) = RealGreater(this, other)

/**
 * Greater operator for RealSort Expressions: [this] > [other].
 */
infix fun Expression<RealSort>.greater(other: () -> Expression<RealSort>) = this greater other()

/**
 * Greater operator for RealSort Expressions: [this] > [other].
 */
infix fun (() -> Expression<RealSort>).greater(other: Expression<RealSort>) = this() greater other

/**
 * Greater operator for RealSort Expressions: [this] > [other].
 */
infix fun (() -> Expression<RealSort>).greater(other: () -> Expression<RealSort>) = this() greater other()

/**
 * Greater operator for RealSort Expressions: [this] > [other].
 */
infix fun RealGreater.greater(other: Expression<RealSort>) = RealGreater(this.children + other)

/**
 * Greater operator for RealSort Expressions: [this] > [block].
 */
infix fun RealGreater.greater(block: () -> Expression<RealSort>) = RealGreater(this.children + block())

/**
 * Greater equals operator for RealSort Expressions: [this] >= [other].
 */
infix fun Expression<RealSort>.greaterEq(other: Expression<RealSort>) = RealGreaterEq(this, other)

/**
 * Greater equals operator for RealSort Expressions: [this] >= [other].
 */
infix fun Expression<RealSort>.greaterEq(other: () -> Expression<RealSort>) = this greaterEq other()

/**
 * Greater equals operator for RealSort Expressions: [this] >= [other].
 */
infix fun (() -> Expression<RealSort>).greaterEq(other: Expression<RealSort>) = this() greaterEq other

/**
 * Greater equals operator for RealSort Expressions: [this] >= [other].
 */
infix fun (() -> Expression<RealSort>).greaterEq(other: () -> Expression<RealSort>) = this() greaterEq other()

/**
 * Greater equals operator for RealSort Expressions: [this] >= [other].
 */
infix fun RealGreaterEq.greaterEq(other: Expression<RealSort>) = RealGreaterEq(this.children + other)

/**
 * Greater equals operator for RealSort Expressions: [this] >= [block].
 */
infix fun RealGreaterEq.greaterEq(block: () -> Expression<RealSort>) = RealGreaterEq(this.children + block())

/**
 * Less operator for RealSort Expressions: [this] < [other].
 */
infix fun Expression<RealSort>.less(other: Expression<RealSort>) = RealLess(this, other)

/**
 * Less operator for RealSort Expressions: [this] < [other].
 */
infix fun Expression<RealSort>.less(other: () -> Expression<RealSort>) = this less other()

/**
 * Less operator for RealSort Expressions: [this] < [other].
 */
infix fun (() -> Expression<RealSort>).less(other: Expression<RealSort>) = this() less other

/**
 * Less operator for RealSort Expressions: [this] < [other].
 */
infix fun (() -> Expression<RealSort>).less(other: () -> Expression<RealSort>) = this() less other()

/**
 * Less operator for RealSort Expressions: [this] < [other].
 */
infix fun RealLess.less(other: Expression<RealSort>) = RealLess(this.children + other)

/**
 * Less operator for RealSort Expressions: [this] < [block].
 */
infix fun RealLess.less(block: () -> Expression<RealSort>) = RealLess(this.children + block())

/**
 * Less equals operator for RealSort Expressions: [this] <= [other].
 */
infix fun Expression<RealSort>.lessEq(other: Expression<RealSort>) = RealLessEq(this, other)

/**
 * Less equals operator for RealSort Expressions: [this] <= [other].
 */
infix fun Expression<RealSort>.lessEq(other: () -> Expression<RealSort>) = this lessEq other()

/**
 * Less equals operator for RealSort Expressions: [this] <= [other].
 */
infix fun (() -> Expression<RealSort>).lessEq(other: Expression<RealSort>) = this() lessEq other

/**
 * Less equals operator for RealSort Expressions: [this] <= [other].
 */
infix fun (() -> Expression<RealSort>).lessEq(other: () -> Expression<RealSort>) = this() lessEq other()

/**
 * Less equals operator for RealSort Expressions: [this] <= [other].
 */
infix fun RealLessEq.lessEq(other: Expression<RealSort>) = RealLessEq(this.children + other)

/**
 * Less equals operator for RealSort Expressions: [this] <= [block].
 */
infix fun RealLessEq.lessEq(block: () -> Expression<RealSort>) = RealLessEq(this.children + block())

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
 * Use [Builder.unaryPlus] inside the [init] lambda to add Expressions to the addition operation.
 * If only a single subexpression is added, the expression is returned directly.
 *
 * @throws [IllegalArgumentException] if no expression is added inside the [init] lambda
 */
fun realadd(init: Builder<RealSort>.() -> Unit) = makeRealOperator(init, ::RealAdd)

/**
 * Subtraction operation for RealSort Expressions.
 *
 * Use [Builder.unaryPlus] inside the [init] lambda to add Expressions to the addition operation.
 * If only a single subexpression is added, the expression is returned directly.
 *
 * @throws [IllegalArgumentException] if no expression is added inside the [init] lambda
 */
fun realsub(init: Builder<RealSort>.() -> Unit) = makeRealOperator(init, ::RealSub)

/**
 * Multiplication operation for RealSort Expressions.
 *
 * Use [Builder.unaryPlus] inside the [init] lambda to add Expressions to the addition operation.
 * If only a single subexpression is added, the expression is returned directly.
 *
 * @throws [IllegalArgumentException] if no expression is added inside the [init] lambda
 */
fun realmul(init: Builder<RealSort>.() -> Unit) = makeRealOperator(init, ::RealMul)

/**
 * Division operation for RealSort Expressions.
 *
 * Use [Builder.unaryPlus] inside the [init] lambda to add Expressions to the addition operation.
 * If only a single subexpression is added, the expression is returned directly.
 *
 * @throws [IllegalArgumentException] if no expression is added inside the [init] lambda
 */
fun realdiv(init: Builder<RealSort>.() -> Unit) = makeRealOperator(init, ::RealDiv)

/**
 * Casting operator from RealSort to RealSort
 */
fun toReal(block: () -> Expression<IntSort>) = ToReal(block())

/**
 * Casting operator from RealSort to RealSort
 */
fun toReal(expr: Expression<IntSort>) = ToReal(expr)

/** Implements smt is_int operation */
fun isInt(expr: Expression<RealSort>) = IsInt(expr)

/** Implements smt is_int operation */
fun isInt(block: () -> Expression<RealSort>) = IsInt(block())

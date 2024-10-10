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
 * Negation operator for IntSort Expressions
 */
operator fun Expression<IntSort>.unaryMinus() = IntNeg(this)

/**
 * Subtraction operator for IntSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [IntSub] object, unpacks the children and returns a new combined IntSub
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
 * If [this] is an [IntSub] object, unpacks the children and returns a new combined IntSub
 */
infix fun Expression<IntSort>.minus(subtrahend: () -> Expression<IntSort>) = this minus subtrahend()

/**
 * Subtraction operator for IntSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [IntSub] object, unpacks the children and returns a new combined IntSub
 */
infix fun (() -> Expression<IntSort>).minus(subtrahend: Expression<IntSort>) = this() minus subtrahend

/**
 * Subtraction operator for IntSort Expressions: [this] - [subtrahend].
 *
 * If [this] is an [IntSub] object, unpacks the children and returns a new combined IntSub
 */
infix fun (() -> Expression<IntSort>).minus(subtrahend: () -> Expression<IntSort>) = this() minus subtrahend()

/**
 * Addition operator for IntSort Expressions: [this] + [summand].
 *
 * If [this] is an [IntAdd] object, unpacks the children and returns a new combined IntAdd
 */
infix operator fun Expression<IntSort>.plus(summand: Expression<IntSort>) =
    if (this is IntAdd) {
      IntAdd(this.children + summand)
    } else {
      IntAdd(this, summand)
    }


/**
 * Addition operator for IntSort Expressions: [this] + [summand].
 *
 * If [this] is an [IntAdd] object, unpacks the children and returns a new combined IntAdd
 */
infix fun Expression<IntSort>.plus(summand: () -> Expression<IntSort>) = this plus summand()

/**
 * Addition operator for IntSort Expressions: [this] + [summand].
 *
 * If [this] is an [IntAdd] object, unpacks the children and returns a new combined IntAdd
 */
infix fun (() -> Expression<IntSort>).plus(summand: Expression<IntSort>) = this() plus summand

/**
 * Addition operator for IntSort Expressions: [this] + [summand].
 *
 * If [this] is an [IntAdd] object, unpacks the children and returns a new combined IntAdd
 */
infix fun (() -> Expression<IntSort>).plus(summand: () -> Expression<IntSort>) = this() plus summand()

/**
 * Multiplication operator for IntSort Expressions: [this] * [multiplicand].
 *
 * If [this] is an [IntMul] object, unpacks the children and returns a new combined IntMul
 */
infix operator fun Expression<IntSort>.times(multiplicand: Expression<IntSort>) =
    if (this is IntMul) {
      IntMul(this.children + multiplicand)
    } else {
      IntMul(this, multiplicand)
    }

/**
 * Multiplication operator for IntSort Expressions: [this] * [multiplicand].
 *
 * If [this] is an [IntMul] object, unpacks the children and returns a new combined IntMul
 */
infix fun Expression<IntSort>.times(multiplicand: () -> Expression<IntSort>) = this times multiplicand()

/**
 * Multiplication operator for IntSort Expressions: [this] * [multiplicand].
 *
 * If [this] is an [IntMul] object, unpacks the children and returns a new combined IntMul
 */
infix fun (() -> Expression<IntSort>).times(multiplicand: Expression<IntSort>) = this() times multiplicand

/**
 * Multiplication operator for IntSort Expressions: [this] * [multiplicand].
 *
 * If [this] is an [IntMul] object, unpacks the children and returns a new combined IntMul
 */
infix fun (() -> Expression<IntSort>).times(multiplicand: () -> Expression<IntSort>) = this() times multiplicand()

/**
 * Division operator for IntSort Expressions: [this] / [divisor].
 *
 * If [this] is an [IntDiv] object, unpacks the children and returns a new combined IntMul
 */
infix operator fun Expression<IntSort>.div(divisor: Expression<IntSort>) =
    if (this is IntDiv) {
      IntDiv(this.children + divisor)
    } else {
      IntDiv(this, divisor)
    }

/**
 * Division operator for IntSort Expressions: [this] / [divisor].
 *
 * If [this] is an [IntDiv] object, unpacks the children and returns a new combined IntMul
 */
infix fun Expression<IntSort>.div(divisor: () -> Expression<IntSort>) = this div divisor()

/**
 * Division operator for IntSort Expressions: [this] / [divisor].
 *
 * If [this] is an [IntDiv] object, unpacks the children and returns a new combined IntMul
 */
infix fun (() -> Expression<IntSort>).div(divisor: Expression<IntSort>) = this() div divisor

/**
 * Division operator for IntSort Expressions: [this] / [divisor].
 *
 * If [this] is an [IntDiv] object, unpacks the children and returns a new combined IntMul
 */
infix fun (() -> Expression<IntSort>).div(divisor: () -> Expression<IntSort>) = this() div divisor()

/**
 * Greater operator for IntSort Expressions: [this] > [other].
 */
infix fun Expression<IntSort>.greater(other: Expression<IntSort>) = IntGreater(this, other)

/**
 * Greater operator for IntSort Expressions: [this] > [other].
 */
infix fun Expression<IntSort>.greater(other: () -> Expression<IntSort>) = this greater other()

/**
 * Greater operator for IntSort Expressions: [this] > [other].
 */
infix fun (() -> Expression<IntSort>).greater(other: Expression<IntSort>) = this() greater other

/**
 * Greater operator for IntSort Expressions: [this] > [other].
 */
infix fun (() -> Expression<IntSort>).greater(other: () -> Expression<IntSort>) = this() greater other()

/**
 * Greater operator for IntSort Expressions: [this] > [other].
 */
infix fun IntGreater.greater(other: Expression<IntSort>) = IntGreater(this.children + other)

/**
 * Greater operator for IntSort Expressions: [this] > [block].
 */
infix fun IntGreater.greater(block: () -> Expression<IntSort>) = IntGreater(this.children + block())

/**
 * Greater equals operator for IntSort Expressions: [this] >= [other].
 */
infix fun Expression<IntSort>.greaterEq(other: Expression<IntSort>) = IntGreaterEq(this, other)

/**
 * Greater equals operator for IntSort Expressions: [this] >= [other].
 */
infix fun Expression<IntSort>.greaterEq(other: () -> Expression<IntSort>) = this greaterEq other()

/**
 * Greater equals operator for IntSort Expressions: [this] >= [other].
 */
infix fun (() -> Expression<IntSort>).greaterEq(other: Expression<IntSort>) = this() greaterEq other

/**
 * Greater equals operator for IntSort Expressions: [this] >= [other].
 */
infix fun (() -> Expression<IntSort>).greaterEq(other: () -> Expression<IntSort>) = this() greaterEq other()

/**
 * Greater equals operator for IntSort Expressions: [this] >= [other].
 */
infix fun IntGreaterEq.greaterEq(other: Expression<IntSort>) = IntGreaterEq(this.children + other)

/**
 * Greater equals operator for IntSort Expressions: [this] >= [block].
 */
infix fun IntGreaterEq.greaterEq(block: () -> Expression<IntSort>) = IntGreaterEq(this.children + block())

/**
 * Less operator for IntSort Expressions: [this] < [other].
 */
infix fun Expression<IntSort>.less(other: Expression<IntSort>) = IntLess(this, other)

/**
 * Less operator for IntSort Expressions: [this] < [other].
 */
infix fun Expression<IntSort>.less(other: () -> Expression<IntSort>) = this less other()

/**
 * Less operator for IntSort Expressions: [this] < [other].
 */
infix fun (() -> Expression<IntSort>).less(other: Expression<IntSort>) = this() less other

/**
 * Less operator for IntSort Expressions: [this] < [other].
 */
infix fun (() -> Expression<IntSort>).less(other: () -> Expression<IntSort>) = this() less other()

/**
 * Less operator for IntSort Expressions: [this] < [other].
 */
infix fun IntLess.less(other: Expression<IntSort>) = IntLess(this.children + other)

/**
 * Less operator for IntSort Expressions: [this] < [block].
 */
infix fun IntLess.less(block: () -> Expression<IntSort>) = IntLess(this.children + block())

/**
 * Less equals operator for IntSort Expressions: [this] <= [other].
 */
infix fun Expression<IntSort>.lessEq(other: Expression<IntSort>) = IntLessEq(this, other)

/**
 * Less equals operator for IntSort Expressions: [this] <= [other].
 */
infix fun Expression<IntSort>.lessEq(other: () -> Expression<IntSort>) = this lessEq other()

/**
 * Less equals operator for IntSort Expressions: [this] <= [other].
 */
infix fun (() -> Expression<IntSort>).lessEq(other: Expression<IntSort>) = this() lessEq other

/**
 * Less equals operator for IntSort Expressions: [this] <= [other].
 */
infix fun (() -> Expression<IntSort>).lessEq(other: () -> Expression<IntSort>) = this() lessEq other()

/**
 * Less equals operator for IntSort Expressions: [this] <= [other].
 */
infix fun IntLessEq.lessEq(other: Expression<IntSort>) = IntLessEq(this.children + other)

/**
 * Less equals operator for IntSort Expressions: [this] <= [block].
 */
infix fun IntLessEq.lessEq(block: () -> Expression<IntSort>) = IntLessEq(this.children + block())

/**
 * Modulo operation for IntSort Expressions: [this] mod [other].
 */
infix fun Expression<IntSort>.mod(other: Expression<IntSort>) = Mod(this, other)

/**
 * Modulo operation for IntSort Expressions: [this] mod [other].
 */
infix fun Expression<IntSort>.mod(other: () -> Expression<IntSort>) = this mod other()

/**
 * Modulo operation for IntSort Expressions: [this] mod [other].
 */
infix fun (() -> Expression<IntSort>).mod(other: Expression<IntSort>) = this() mod other

/**
 * Modulo operation for IntSort Expressions: [this] mod [other].
 */
infix fun (() -> Expression<IntSort>).mod(other: () -> Expression<IntSort>) = this() mod other()

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
 * Use [Builder.unaryPlus] inside the [init] lambda to add Expressions to the addition operation.
 * If only a single subexpression is added, the expression is returned directly.
 *
 * @throws [IllegalArgumentException] if no expression is added inside the [init] lambda
 */
fun intadd(init: Builder<IntSort>.() -> Unit) = makeIntOperator(init, ::IntAdd)

/**
 * Subtraction operation for IntSort Expressions.
 *
 * Use [Builder.unaryPlus] inside the [init] lambda to add Expressions to the addition operation.
 * If only a single subexpression is added, the expression is returned directly.
 *
 * @throws [IllegalArgumentException] if no expression is added inside the [init] lambda
 */
fun intsub(init: Builder<IntSort>.() -> Unit) = makeIntOperator(init, ::IntSub)

/**
 * Multiplication operation for IntSort Expressions.
 *
 * Use [Builder.unaryPlus] inside the [init] lambda to add Expressions to the addition operation.
 * If only a single subexpression is added, the expression is returned directly.
 *
 * @throws [IllegalArgumentException] if no expression is added inside the [init] lambda
 */
fun intmul(init: Builder<IntSort>.() -> Unit) = makeIntOperator(init, ::IntMul)

/**
 * Division operation for IntSort Expressions.
 *
 * Use [Builder.unaryPlus] inside the [init] lambda to add Expressions to the addition operation.
 * If only a single subexpression is added, the expression is returned directly.
 *
 * @throws [IllegalArgumentException] if no expression is added inside the [init] lambda
 */
fun intdiv(init: Builder<IntSort>.() -> Unit) = makeIntOperator(init, ::IntDiv)

/**
 * Absolute value operation for IntSort Expressions.
 */
fun abs(block: () -> Expression<IntSort>) = Abs(block())

/**
 * Absolute value operation for IntSort Expressions.
 */
fun abs(expr: Expression<IntSort>) = Abs(expr)

/**
 * Casting operator from RealSort to IntSort
 */
fun toInt(block: () -> Expression<RealSort>) = ToInt(block())

/**
 * Casting operator from RealSort to IntSort
 */
fun toInt(expr: Expression<RealSort>) = ToInt(expr)

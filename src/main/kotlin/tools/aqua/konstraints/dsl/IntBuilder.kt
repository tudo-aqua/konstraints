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

operator fun Expression<IntSort>.unaryMinus() = IntNeg(this)

infix operator fun Expression<IntSort>.minus(other: Expression<IntSort>): IntSub =
    if (this is IntSub) {
      IntSub(this.children + other)
    } else {
      IntSub(this, other)
    }

infix fun Expression<IntSort>.minus(other: () -> Expression<IntSort>): IntSub = this minus other()

infix fun (() -> Expression<IntSort>).minus(other: Expression<IntSort>): IntSub = this() minus other

infix fun (() -> Expression<IntSort>).minus(other: () -> Expression<IntSort>): IntSub =
    this() minus other()

infix operator fun Expression<IntSort>.plus(other: Expression<IntSort>): IntAdd =
    if (this is IntAdd) {
      IntAdd(this.children + other)
    } else {
      IntAdd(this, other)
    }

infix fun Expression<IntSort>.plus(other: () -> Expression<IntSort>): IntAdd = this plus other()

infix fun (() -> Expression<IntSort>).plus(other: Expression<IntSort>): IntAdd = this() plus other

infix fun (() -> Expression<IntSort>).plus(other: () -> Expression<IntSort>): IntAdd =
    this() plus other()

infix operator fun Expression<IntSort>.times(other: Expression<IntSort>): IntMul =
    if (this is IntMul) {
      IntMul(this.children + other)
    } else {
      IntMul(this, other)
    }

infix fun Expression<IntSort>.times(other: () -> Expression<IntSort>): IntMul = this times other()

infix fun (() -> Expression<IntSort>).times(other: Expression<IntSort>): IntMul = this() times other

infix fun (() -> Expression<IntSort>).times(other: () -> Expression<IntSort>): IntMul =
    this() times other()

infix operator fun Expression<IntSort>.div(other: Expression<IntSort>): IntDiv =
    if (this is IntDiv) {
      IntDiv(this.children + other)
    } else {
      IntDiv(this, other)
    }

infix fun Expression<IntSort>.div(other: () -> Expression<IntSort>): IntDiv = this div other()

infix fun (() -> Expression<IntSort>).div(other: Expression<IntSort>): IntDiv = this() div other

infix fun (() -> Expression<IntSort>).div(other: () -> Expression<IntSort>): IntDiv =
    this() div other()

infix fun Expression<IntSort>.greater(other: Expression<IntSort>) = IntGreater(this, other)

infix fun Expression<IntSort>.greater(other: () -> Expression<IntSort>): IntGreater =
    this greater other()

infix fun (() -> Expression<IntSort>).greater(other: Expression<IntSort>): IntGreater =
    this() greater other

infix fun (() -> Expression<IntSort>).greater(other: () -> Expression<IntSort>): IntGreater =
    this() greater other()

infix fun IntGreater.greater(other: Expression<IntSort>) =
    IntGreater(this.children + other)

infix fun IntGreater.greater(block: () -> Expression<IntSort>) =
    IntGreater(this.children + block())

infix fun Expression<IntSort>.greaterEq(other: Expression<IntSort>) = IntGreaterEq(this, other)

infix fun Expression<IntSort>.greaterEq(other: () -> Expression<IntSort>): IntGreaterEq =
    this greaterEq other()

infix fun (() -> Expression<IntSort>).greaterEq(other: Expression<IntSort>): IntGreaterEq =
    this() greaterEq other

infix fun (() -> Expression<IntSort>).greaterEq(other: () -> Expression<IntSort>): IntGreaterEq =
    this() greaterEq other()

infix fun IntGreaterEq.greaterEq(other: Expression<IntSort>) =
    IntGreaterEq(this.children + other)

infix fun IntGreaterEq.greaterEq(block: () -> Expression<IntSort>) =
    IntGreaterEq(this.children + block())

infix fun Expression<IntSort>.less(other: Expression<IntSort>) = IntLess(this, other)

infix fun Expression<IntSort>.less(other: () -> Expression<IntSort>): IntLess = this less other()

infix fun (() -> Expression<IntSort>).less(other: Expression<IntSort>): IntLess = this() less other

infix fun (() -> Expression<IntSort>).less(other: () -> Expression<IntSort>): IntLess =
    this() less other()

infix fun IntLess.less(other: Expression<IntSort>) = IntLess(this.children + other)

infix fun IntLess.greater(block: () -> Expression<IntSort>) =
    IntLess(this.children + block())

infix fun Expression<IntSort>.lessEq(other: Expression<IntSort>) = IntLessEq(this, other)

infix fun Expression<IntSort>.lessEq(other: () -> Expression<IntSort>): IntLessEq =
    this lessEq other()

infix fun (() -> Expression<IntSort>).lessEq(other: Expression<IntSort>): IntLessEq =
    this() lessEq other

infix fun (() -> Expression<IntSort>).lessEq(other: () -> Expression<IntSort>): IntLessEq =
    this() lessEq other()

infix fun IntLessEq.lessEq(other: Expression<IntSort>) =
    IntLessEq(this.children + other)

infix fun IntLessEq.greater(block: () -> Expression<IntSort>) =
    IntLessEq(this.children + block())

infix fun Expression<IntSort>.mod(other: Expression<IntSort>) = Mod(this, other)

infix fun Expression<IntSort>.mod(other: () -> Expression<IntSort>): Mod = this mod other()

infix fun (() -> Expression<IntSort>).mod(other: Expression<IntSort>): Mod = this() mod other

infix fun (() -> Expression<IntSort>).mod(other: () -> Expression<IntSort>): Mod =
    this() mod other()

private fun makeIntOperator(
    init: Builder<IntSort>.() -> Unit,
    op: (List<Expression<IntSort>>) -> Expression<IntSort>
): Expression<IntSort> {
  val builder = Builder<IntSort>()
  builder.init()

  return op(builder.children)
}

fun intadd(init: Builder<IntSort>.() -> Unit) = makeIntOperator(init, ::IntAdd)

fun intsub(init: Builder<IntSort>.() -> Unit) = makeIntOperator(init, ::IntSub)

fun intmul(init: Builder<IntSort>.() -> Unit) = makeIntOperator(init, ::IntMul)

fun intdiv(init: Builder<IntSort>.() -> Unit) = makeIntOperator(init, ::IntDiv)

fun abs(block: () -> Expression<IntSort>) = Abs(block())

fun abs(expr: Expression<IntSort>) = Abs(expr)

fun toInt(block: () -> Expression<RealSort>) = ToInt(block())

fun toInt(expr: Expression<RealSort>) = ToInt(expr)

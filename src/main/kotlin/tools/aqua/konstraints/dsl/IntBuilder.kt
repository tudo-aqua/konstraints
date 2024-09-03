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
      IntSub(*this.children.toTypedArray(), other)
    } else {
      IntSub(this, other)
    }

infix operator fun Expression<IntSort>.plus(other: Expression<IntSort>): IntAdd =
    if (this is IntAdd) {
      IntAdd(*this.children.toTypedArray(), other)
    } else {
      IntAdd(this, other)
    }

infix operator fun Expression<IntSort>.times(other: Expression<IntSort>): IntMul =
    if (this is IntMul) {
      IntMul(*this.children.toTypedArray(), other)
    } else {
      IntMul(this, other)
    }

infix operator fun Expression<IntSort>.div(other: Expression<IntSort>): IntDiv =
    if (this is IntDiv) {
      IntDiv(*this.children.toTypedArray(), other)
    } else {
      IntDiv(this, other)
    }

infix fun Expression<IntSort>.greater(other: Expression<IntSort>) = IntGreater(this, other)

infix fun IntGreater.greater(other: Expression<IntSort>) =
    IntGreater(*this.children.toTypedArray(), other)

infix fun Expression<IntSort>.greaterEq(other: Expression<IntSort>) = IntGreaterEq(this, other)

infix fun IntGreaterEq.greaterEq(other: Expression<IntSort>) =
    IntGreaterEq(*this.children.toTypedArray(), other)

infix fun Expression<IntSort>.less(other: Expression<IntSort>) = IntLess(this, other)

infix fun IntLess.less(other: Expression<IntSort>) = IntLess(*this.children.toTypedArray(), other)

infix fun Expression<IntSort>.lessEq(other: Expression<IntSort>) = IntLessEq(this, other)

infix fun IntLessEq.lessEq(other: Expression<IntSort>) =
    IntLessEq(*this.children.toTypedArray(), other)

infix fun Expression<IntSort>.mod(other: Expression<IntSort>) = Mod(this, other)

private fun Builder<IntSort>.makeIntOperator(
    init: Builder<IntSort>.() -> Unit,
    op: (List<Expression<IntSort>>) -> Expression<IntSort>
): Expression<IntSort> {
  val builder = Builder<IntSort>()
  builder.init()

  this.children.add(op(builder.children))

  return this.children.last()
}

fun Builder<IntSort>.add(init: Builder<IntSort>.() -> Unit) = this.makeIntOperator(init, ::IntAdd)

fun Builder<IntSort>.sub(init: Builder<IntSort>.() -> Unit) = this.makeIntOperator(init, ::IntSub)

fun Builder<IntSort>.mul(init: Builder<IntSort>.() -> Unit) = this.makeIntOperator(init, ::IntMul)

fun Builder<IntSort>.div(init: Builder<IntSort>.() -> Unit) = this.makeIntOperator(init, ::IntDiv)

fun Builder<IntSort>.abs(block: Builder<IntSort>.() -> Expression<IntSort>): Abs {
  this.children.add(Abs(Builder<IntSort>().block()))

  return this.children.last() as Abs
}

fun Builder<IntSort>.toInt(block: Builder<RealSort>.() -> Expression<RealSort>): ToInt {
  this.children.add(ToInt(Builder<RealSort>().block()))

  return this.children.last() as ToInt
}

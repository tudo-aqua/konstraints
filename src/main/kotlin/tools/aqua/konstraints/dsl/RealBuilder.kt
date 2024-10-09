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

operator fun Expression<RealSort>.unaryMinus() = RealNeg(this)

infix operator fun Expression<RealSort>.minus(other: Expression<RealSort>): RealSub =
    if (this is RealSub) {
      RealSub(*this.children.toTypedArray(), other)
    } else {
      RealSub(this, other)
    }

infix fun Expression<RealSort>.minus(other: () -> Expression<RealSort>): RealSub =
    this minus other()

infix fun (() -> Expression<RealSort>).minus(other: Expression<RealSort>): RealSub =
    this() minus other

infix fun (() -> Expression<RealSort>).minus(other: () -> Expression<RealSort>): RealSub =
    this() minus other()

infix operator fun Expression<RealSort>.plus(other: Expression<RealSort>): RealAdd =
    if (this is RealAdd) {
      RealAdd(*this.children.toTypedArray(), other)
    } else {
      RealAdd(this, other)
    }

infix fun Expression<RealSort>.plus(other: () -> Expression<RealSort>): RealAdd = this plus other()

infix fun (() -> Expression<RealSort>).plus(other: Expression<RealSort>): RealAdd =
    this() plus other

infix fun (() -> Expression<RealSort>).plus(other: () -> Expression<RealSort>): RealAdd =
    this() plus other()

infix operator fun Expression<RealSort>.times(other: Expression<RealSort>): RealMul =
    if (this is RealMul) {
      RealMul(*this.children.toTypedArray(), other)
    } else {
      RealMul(this, other)
    }

infix fun Expression<RealSort>.times(other: () -> Expression<RealSort>): RealMul =
    this times other()

infix fun (() -> Expression<RealSort>).times(other: Expression<RealSort>): RealMul =
    this() times other

infix fun (() -> Expression<RealSort>).times(other: () -> Expression<RealSort>): RealMul =
    this() times other()

infix operator fun Expression<RealSort>.div(other: Expression<RealSort>): RealDiv =
    if (this is RealDiv) {
      RealDiv(*this.children.toTypedArray(), other)
    } else {
      RealDiv(this, other)
    }

infix fun Expression<RealSort>.div(other: () -> Expression<RealSort>): RealDiv = this div other()

infix fun (() -> Expression<RealSort>).div(other: Expression<RealSort>): RealDiv = this() div other

infix fun (() -> Expression<RealSort>).div(other: () -> Expression<RealSort>): RealDiv =
    this() div other()

infix fun Expression<RealSort>.greater(other: Expression<RealSort>) = RealGreater(this, other)

infix fun Expression<RealSort>.greater(other: () -> Expression<RealSort>): RealGreater =
    this greater other()

infix fun (() -> Expression<RealSort>).greater(other: Expression<RealSort>): RealGreater =
    this() greater other

infix fun (() -> Expression<RealSort>).greater(other: () -> Expression<RealSort>): RealGreater =
    this() greater other()

infix fun RealGreater.greater(other: Expression<RealSort>) =
    RealGreater(*this.children.toTypedArray(), other)

infix fun RealGreater.greater(block: () -> Expression<RealSort>) =
    RealGreater(*this.children.toTypedArray(), block())

infix fun Expression<RealSort>.greaterEq(other: Expression<RealSort>) = RealGreaterEq(this, other)

infix fun Expression<RealSort>.greaterEq(other: () -> Expression<RealSort>): RealGreaterEq =
    this greaterEq other()

infix fun (() -> Expression<RealSort>).greaterEq(other: Expression<RealSort>): RealGreaterEq =
    this() greaterEq other

infix fun (() -> Expression<RealSort>).greaterEq(other: () -> Expression<RealSort>): RealGreaterEq =
    this() greaterEq other()

infix fun RealGreaterEq.greaterEq(other: Expression<RealSort>) =
    RealGreaterEq(*this.children.toTypedArray(), other)

infix fun RealGreaterEq.greaterEq(block: () -> Expression<RealSort>) =
    RealGreaterEq(*this.children.toTypedArray(), block())

infix fun Expression<RealSort>.less(other: Expression<RealSort>) = RealLess(this, other)

infix fun Expression<RealSort>.less(other: () -> Expression<RealSort>): RealLess = this less other()

infix fun (() -> Expression<RealSort>).less(other: Expression<RealSort>): RealLess =
    this() less other

infix fun (() -> Expression<RealSort>).less(other: () -> Expression<RealSort>): RealLess =
    this() less other()

infix fun RealLess.less(other: Expression<RealSort>) =
    RealLess(*this.children.toTypedArray(), other)

infix fun RealLess.less(block: () -> Expression<RealSort>) =
    RealLess(*this.children.toTypedArray(), block())

infix fun Expression<RealSort>.lessEq(other: Expression<RealSort>) = RealLessEq(this, other)

infix fun Expression<RealSort>.lessEq(other: () -> Expression<RealSort>): RealLessEq =
    this lessEq other()

infix fun (() -> Expression<RealSort>).lessEq(other: Expression<RealSort>): RealLessEq =
    this() lessEq other

infix fun (() -> Expression<RealSort>).lessEq(other: () -> Expression<RealSort>): RealLessEq =
    this() lessEq other()

infix fun RealLessEq.lessEq(other: Expression<RealSort>) =
    RealLessEq(*this.children.toTypedArray(), other)

infix fun RealLessEq.lessEq(block: () -> Expression<RealSort>) =
    RealLessEq(*this.children.toTypedArray(), block())

private fun makeRealOperator(
    init: Builder<RealSort>.() -> Unit,
    op: (List<Expression<RealSort>>) -> Expression<RealSort>
): Expression<RealSort> {
  val builder = Builder<RealSort>()
  builder.init()

  return op(builder.children)
}

fun realadd(init: Builder<RealSort>.() -> Unit) = makeRealOperator(init, ::RealAdd)

fun realsub(init: Builder<RealSort>.() -> Unit) = makeRealOperator(init, ::RealSub)

fun realmul(init: Builder<RealSort>.() -> Unit) = makeRealOperator(init, ::RealMul)

fun realdiv(init: Builder<RealSort>.() -> Unit) = makeRealOperator(init, ::RealDiv)

fun toReal(block: Builder<IntSort>.() -> Expression<IntSort>) = ToReal(Builder<IntSort>().block())

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

infix operator fun Expression<RealSort>.plus(other: Expression<RealSort>): RealAdd =
    if (this is RealAdd) {
      RealAdd(*this.children.toTypedArray(), other)
    } else {
      RealAdd(this, other)
    }

infix operator fun Expression<RealSort>.times(other: Expression<RealSort>): RealMul =
    if (this is RealMul) {
      RealMul(*this.children.toTypedArray(), other)
    } else {
      RealMul(this, other)
    }

infix operator fun Expression<RealSort>.div(other: Expression<RealSort>): RealDiv =
    if (this is RealDiv) {
      RealDiv(*this.children.toTypedArray(), other)
    } else {
      RealDiv(this, other)
    }

infix fun Expression<RealSort>.greater(other: Expression<RealSort>) = RealGreater(this, other)

infix fun RealGreater.greater(other: Expression<RealSort>) =
    RealGreater(*this.children.toTypedArray(), other)

infix fun Expression<RealSort>.greaterEq(other: Expression<RealSort>) = RealGreaterEq(this, other)

infix fun RealGreaterEq.greaterEq(other: Expression<RealSort>) =
    RealGreaterEq(*this.children.toTypedArray(), other)

infix fun Expression<RealSort>.less(other: Expression<RealSort>) = RealLess(this, other)

infix fun RealLess.less(other: Expression<RealSort>) =
    RealLess(*this.children.toTypedArray(), other)

infix fun Expression<RealSort>.lessEq(other: Expression<RealSort>) = RealLessEq(this, other)

infix fun RealLessEq.lessEq(other: Expression<RealSort>) =
    RealLessEq(*this.children.toTypedArray(), other)

private fun Builder<RealSort>.makeRealOperator(
    init: Builder<RealSort>.() -> Unit,
    op: (List<Expression<RealSort>>) -> Expression<RealSort>
): Expression<RealSort> {
  val builder = Builder<RealSort>()
  builder.init()

  this.children.add(op(builder.children))

  return this.children.last()
}

fun Builder<RealSort>.add(init: Builder<RealSort>.() -> Unit) =
    this.makeRealOperator(init, ::RealAdd)

fun Builder<RealSort>.sub(init: Builder<RealSort>.() -> Unit) =
    this.makeRealOperator(init, ::RealSub)

fun Builder<RealSort>.mul(init: Builder<RealSort>.() -> Unit) =
    this.makeRealOperator(init, ::RealMul)

fun Builder<RealSort>.div(init: Builder<RealSort>.() -> Unit) =
    this.makeRealOperator(init, ::RealDiv)

fun Builder<RealSort>.toReal(block: Builder<IntSort>.() -> Expression<IntSort>): ToReal {
  this.children.add(ToReal(Builder<IntSort>().block()))

  return this.children.last() as ToReal
}

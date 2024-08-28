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
import tools.aqua.konstraints.smt.Sort
import tools.aqua.konstraints.theories.*

infix fun Expression<BoolSort>.implies(other: Expression<BoolSort>): Implies =
    if (this is Implies) {
        Implies(*this.children.toTypedArray(), other)
    } else {
        Implies(this, other)
    }

/**
 * Infix and operator on BoolSort Expressions
 * if the left input is itself an and unpacks the children and returns a new combined and
 */
infix fun Expression<BoolSort>.and(other: Expression<BoolSort>): And =
    if (this is And) {
      And(*this.children.toTypedArray(), other)
    } else {
      And(this, other)
    }

infix fun Expression<BoolSort>.or(other: Expression<BoolSort>): Or =
    if (this is Or) {
        Or(*this.children.toTypedArray(), other)
    } else {
        Or(this, other)
    }

infix fun Expression<BoolSort>.xor(other: Expression<BoolSort>): XOr =
    if (this is XOr) {
        XOr(*this.children.toTypedArray(), other)
    } else {
        XOr(this, other)
    }

infix fun<T : Sort> Expression<T>.eq(other: Expression<T>): Equals =
    if (this is Equals) {
        Equals(*this.children.toTypedArray(), other)
    } else {
        Equals(this, other)
    }

infix fun<T : Sort> Expression<T>.distinct(other: Expression<T>): Distinct =
    if (this is Distinct) {
        Distinct(*this.children.toTypedArray(), other)
    } else {
        Distinct(this, other)
    }

private fun Builder<BoolSort>.makeBoolOperator(init: Builder<BoolSort>.() -> Unit, op: (List<Expression<BoolSort>>) -> Expression<BoolSort>): Expression<BoolSort> {
    val builder = Builder<BoolSort>()
    builder.init()

    this.children.add(op(builder.children))

    return this.children.last()
}

fun Builder<BoolSort>.and(init: Builder<BoolSort>.() -> Unit) = this.makeBoolOperator(init, ::And)
fun Builder<BoolSort>.or(init: Builder<BoolSort>.() -> Unit) = this.makeBoolOperator(init, ::Or)
fun Builder<BoolSort>.xor(init: Builder<BoolSort>.() -> Unit) = this.makeBoolOperator(init, ::XOr)

fun<T : Sort> Builder<BoolSort>.eq(init: Builder<T>.() -> Unit): Equals {
    val builder = Builder<T>()
    builder.init()

    val op = Equals(builder.children)
    this.children.add(op)

    return op
}

fun<T : Sort> Builder<BoolSort>.distinct(init: Builder<T>.() -> Unit): Equals {
    val builder = Builder<T>()
    builder.init()

    val op = Equals(builder.children)
    this.children.add(op)

    return op
}

fun Builder<BoolSort>.not(block: Builder<BoolSort>.() -> Expression<BoolSort>): Not {
    this.children.add(Not(Builder<BoolSort>().block()))

    return this.children.last() as Not
}

fun Builder<BoolSort>.isInt(block: Builder<RealSort>.() -> Expression<RealSort>): IsInt {
    this.children.add(IsInt(Builder<RealSort>().block()))

    return this.children.last() as IsInt
}
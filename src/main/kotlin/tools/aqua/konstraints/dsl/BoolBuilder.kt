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

/**
 * Creates a logical implication: [this] => [other].
 *
 * If [this] is an [Implies] object, unpacks the children and returns a new combined Implies.
 */
infix fun Expression<BoolSort>.implies(other: Expression<BoolSort>): Implies =
    if (this is Implies) {
      Implies(*this.children.toTypedArray(), other)
    } else {
      Implies(this, other)
    }

infix fun Expression<BoolSort>.implies(other: () -> Expression<BoolSort>): Implies =
    this implies other()

infix fun (() -> Expression<BoolSort>).implies(other: Expression<BoolSort>): Implies =
    this() implies other

infix fun (() -> Expression<BoolSort>).implies(other: () -> Expression<BoolSort>): Implies =
    this() implies other()

/**
 * Creates a logical and: [this] and [other].
 *
 * If [this] is an [And] object, unpacks the children and returns a new combined And.
 */
infix fun Expression<BoolSort>.and(other: Expression<BoolSort>): And =
    if (this is And) {
      And(*this.children.toTypedArray(), other)
    } else {
      And(this, other)
    }

infix fun Expression<BoolSort>.and(other: () -> Expression<BoolSort>): And = this and other()

infix fun (() -> Expression<BoolSort>).and(other: Expression<BoolSort>): And = this() and other

infix fun (() -> Expression<BoolSort>).and(other: () -> Expression<BoolSort>): And =
    this() and other()

/**
 * Creates a logical or: [this] or [other].
 *
 * If [this] is an [Or] object, unpacks the children and returns a new combined Or.
 */
infix fun Expression<BoolSort>.or(other: Expression<BoolSort>): Or =
    if (this is Or) {
      Or(*this.children.toTypedArray(), other)
    } else {
      Or(this, other)
    }

infix fun Expression<BoolSort>.or(other: () -> Expression<BoolSort>): Or = this or other()

infix fun (() -> Expression<BoolSort>).or(other: Expression<BoolSort>): Or = this() or other

infix fun (() -> Expression<BoolSort>).or(other: () -> Expression<BoolSort>): Or = this() or other()

/**
 * Creates a logical xor: [this] xor [other].
 *
 * If [this] is an [XOr] object, unpacks the children and returns a new combined XOr.
 */
infix fun Expression<BoolSort>.xor(other: Expression<BoolSort>): XOr =
    if (this is XOr) {
      XOr(*this.children.toTypedArray(), other)
    } else {
      XOr(this, other)
    }

infix fun Expression<BoolSort>.xor(other: () -> Expression<BoolSort>): XOr = this xor other()

infix fun (() -> Expression<BoolSort>).xor(other: Expression<BoolSort>): XOr = this() xor other

infix fun (() -> Expression<BoolSort>).xor(other: () -> Expression<BoolSort>): XOr =
    this() xor other()

/**
 * Creates an equals: [this] equals [other].
 *
 * If [this] is an [Equals] object, unpacks the children and returns a new combined Equals.
 */
infix fun <T : Sort> Expression<T>.eq(other: Expression<T>): Equals =
    if (this is Equals) {
      Equals(*this.children.toTypedArray(), other)
    } else {
      Equals(this, other)
    }

// allow chaining of equals
infix fun <T : Sort> Equals.eq(other: Expression<T>): Equals =
    Equals(*this.children.toTypedArray(), other)

infix fun <T : Sort> Expression<T>.eq(other: () -> Expression<T>): Equals = this eq other()

infix fun <T : Sort> (() -> Expression<T>).eq(other: Expression<T>): Equals = this() eq other

infix fun <T : Sort> (() -> Expression<T>).eq(other: () -> Expression<T>): Equals =
    this() eq other()

/** Creates a distinct: [this] distinct [other]. */
infix fun <T : Sort> Expression<T>.distinct(other: Expression<T>): Distinct = Distinct(this, other)

infix fun <T : Sort> Distinct.distinct(other: Expression<T>): Distinct =
    Distinct(*this.children.toTypedArray(), other)

private fun makeBoolOperator(
    init: Builder<BoolSort>.() -> Unit,
    op: (List<Expression<BoolSort>>) -> Expression<BoolSort>
): Expression<BoolSort> {
  val builder = Builder<BoolSort>()
  builder.init()

  return op(builder.children)
}

/**
 * Lambda version of logical [And].
 *
 * Use [Builder.unaryPlus] inside [init] to add [Expression]s to the 'And' expression.
 */
fun and(init: Builder<BoolSort>.() -> Unit) = makeBoolOperator(init, ::And)

/**
 * Lambda version of logical [Or].
 *
 * Use [Builder.unaryPlus] inside [init] to add [Expression]s to the 'Or' expression.
 */
fun or(init: Builder<BoolSort>.() -> Unit) = makeBoolOperator(init, ::Or)

/**
 * Lambda version of logical [XOr].
 *
 * Use [Builder.unaryPlus] inside [init] to add [Expression]s to the 'XOr' expression.
 */
fun xor(init: Builder<BoolSort>.() -> Unit) = makeBoolOperator(init, ::XOr)

/**
 * Lambda version of logical [Equals].
 *
 * Use [Builder.unaryPlus] inside [init] to add [Expression]s to the 'Equals' expression.
 */
fun <T : Sort> eq(init: Builder<T>.() -> Unit): Equals {
  val builder = Builder<T>()
  builder.init()

  return Equals(builder.children)
}

/**
 * Lambda version of logical [Distinct].
 *
 * Use [Builder.unaryPlus] inside [init] to add [Expression]s to the 'Distinct' expression.
 */
fun <T : Sort> distinct(init: Builder<T>.() -> Unit): Distinct {
  val builder = Builder<T>()
  builder.init()

  return Distinct(builder.children)
}

/** Implements logical not operation */
fun not(block: () -> Expression<BoolSort>): Not = Not(block())

fun not(expr: Expression<BoolSort>): Not = Not(expr)

/** Implements smt is_int operation */
fun isInt(block: Builder<RealSort>.() -> Expression<RealSort>) = IsInt(Builder<RealSort>().block())

/*
 * floating-point classification operations
 */

private fun makeFPOperator(
    block: Builder<FPSort>.() -> Expression<FPSort>,
    op: (Expression<FPSort>) -> Expression<BoolSort>
): Expression<BoolSort> = op(Builder<FPSort>().block())

/** Implements floating point isNormal operation */
fun isNormal(block: Builder<FPSort>.() -> Expression<FPSort>) = makeFPOperator(block, ::FPIsNormal)

/** Implements floating point isSubnormal operation */
fun isSubnormal(block: Builder<FPSort>.() -> Expression<FPSort>) =
    makeFPOperator(block, ::FPIsSubnormal)

/** Implements floating point isZero operation */
fun isZero(block: Builder<FPSort>.() -> Expression<FPSort>) = makeFPOperator(block, ::FPIsZero)

/** Implements floating point isInfinite operation */
fun isInfinite(block: Builder<FPSort>.() -> Expression<FPSort>) =
    makeFPOperator(block, ::FPIsInfinite)

/** Implements floating point isNaN operation */
fun isNaN(block: Builder<FPSort>.() -> Expression<FPSort>) = makeFPOperator(block, ::FPIsNaN)

/** Implements floating point isNegative operation */
fun isNegative(block: Builder<FPSort>.() -> Expression<FPSort>) =
    makeFPOperator(block, ::FPIsNegative)

/** Implements floating point isPositive operation */
fun isPositive(block: Builder<FPSort>.() -> Expression<FPSort>) =
    makeFPOperator(block, ::FPIsPositive)

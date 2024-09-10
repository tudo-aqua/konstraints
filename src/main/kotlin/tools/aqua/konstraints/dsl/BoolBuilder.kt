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

/**
 * Creates a distinct: [this] distinct [other].
 *
 * If [this] is an [Distinct] object, unpacks the children and returns a new combined Distinct.
 */
infix fun <T : Sort> Expression<T>.distinct(other: Expression<T>): Distinct =
    if (this is Distinct) {
      Distinct(*this.children.toTypedArray(), other)
    } else {
      Distinct(this, other)
    }

private fun Builder<BoolSort>.makeBoolOperator(
    init: Builder<BoolSort>.() -> Unit,
    op: (List<Expression<BoolSort>>) -> Expression<BoolSort>
): Expression<BoolSort> {
  val builder = Builder<BoolSort>()
  builder.init()

  this.children.add(op(builder.children))

  return this.children.last()
}

/**
 * Lambda version of logical [And].
 *
 * Use [Builder.unaryPlus] inside [init] to add [Expression]s to the 'And' expression.
 */
fun Builder<BoolSort>.and(init: Builder<BoolSort>.() -> Unit) = this.makeBoolOperator(init, ::And)

/**
 * Lambda version of logical [Or].
 *
 * Use [Builder.unaryPlus] inside [init] to add [Expression]s to the 'Or' expression.
 */
fun Builder<BoolSort>.or(init: Builder<BoolSort>.() -> Unit) = this.makeBoolOperator(init, ::Or)

/**
 * Lambda version of logical [XOr].
 *
 * Use [Builder.unaryPlus] inside [init] to add [Expression]s to the 'XOr' expression.
 */
fun Builder<BoolSort>.xor(init: Builder<BoolSort>.() -> Unit) = this.makeBoolOperator(init, ::XOr)

/**
 * Lambda version of logical [Equals].
 *
 * Use [Builder.unaryPlus] inside [init] to add [Expression]s to the 'Equals' expression.
 */
fun <T : Sort> Builder<BoolSort>.eq(init: Builder<T>.() -> Unit): Equals {
  val builder = Builder<T>()
  builder.init()

  val op = Equals(builder.children)
  this.children.add(op)

  return op
}

/**
 * Lambda version of logical [Distinct].
 *
 * Use [Builder.unaryPlus] inside [init] to add [Expression]s to the 'Distinct' expression.
 */
fun <T : Sort> Builder<BoolSort>.distinct(init: Builder<T>.() -> Unit): Distinct {
  val builder = Builder<T>()
  builder.init()

  val op = Distinct(builder.children)
  this.children.add(op)

  return op
}

/**
 * Implements logical not operation
 */
fun Builder<BoolSort>.not(block: Builder<BoolSort>.() -> Expression<BoolSort>): Not {
  this.children.add(Not(Builder<BoolSort>().block()))

  return this.children.last() as Not
}

/**
 * Implements smt is_int operation
 */
fun Builder<BoolSort>.isInt(block: Builder<RealSort>.() -> Expression<RealSort>): IsInt {
  this.children.add(IsInt(Builder<RealSort>().block()))

  return this.children.last() as IsInt
}

/**
 * Implements unsigned less than operation on bitvectors
 *
 * Use [Builder.unaryPlus] inside [init] to add [Expression]s to the 'bvult' expression.
 */
fun Builder<BoolSort>.bvult(init: Builder<BVSort>.() -> Unit): Expression<BoolSort> {
  val builder = Builder<BVSort>()
  builder.init()

  require(builder.children.size == 2)

  this.children.add(BVUlt(builder.children[0], builder.children[1]))

  return this.children.last() as BVUlt
}

/*
 * floating-point classification operations
 */

private fun Builder<BoolSort>.makeFPOperator(
    block: Builder<FPSort>.() -> Expression<FPSort>,
    op: (Expression<FPSort>) -> Expression<BoolSort>
): Expression<BoolSort> {
  this.children.add(op(Builder<FPSort>().block()))

  return this.children.last()
}

/**
 * Implements floating point isNormal operation
 */
fun Builder<BoolSort>.isNormal(block: Builder<FPSort>.() -> Expression<FPSort>) =
    this.makeFPOperator(block, ::FPIsNormal)

/**
 * Implements floating point isSubnormal operation
 */
fun Builder<BoolSort>.isSubnormal(block: Builder<FPSort>.() -> Expression<FPSort>) =
    this.makeFPOperator(block, ::FPIsSubnormal)

/**
 * Implements floating point isZero operation
 */
fun Builder<BoolSort>.isZero(block: Builder<FPSort>.() -> Expression<FPSort>) =
    this.makeFPOperator(block, ::FPIsZero)

/**
 * Implements floating point isInfinite operation
 */
fun Builder<BoolSort>.isInfinite(block: Builder<FPSort>.() -> Expression<FPSort>) =
    this.makeFPOperator(block, ::FPIsInfinite)

/**
 * Implements floating point isNaN operation
 */
fun Builder<BoolSort>.isNaN(block: Builder<FPSort>.() -> Expression<FPSort>) =
    this.makeFPOperator(block, ::FPIsNaN)

/**
 * Implements floating point isNegative operation
 */
fun Builder<BoolSort>.isNegative(block: Builder<FPSort>.() -> Expression<FPSort>) =
    this.makeFPOperator(block, ::FPIsNegative)

/**
 * Implements floating point isPositive operation
 */
fun Builder<BoolSort>.isPositive(block: Builder<FPSort>.() -> Expression<FPSort>) =
    this.makeFPOperator(block, ::FPIsPositive)

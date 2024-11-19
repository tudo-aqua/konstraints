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

package tools.aqua.konstraints.theories

import java.math.BigInteger
import tools.aqua.konstraints.parser.*
import tools.aqua.konstraints.smt.*

/** Int sort */
object IntSort : Sort("Int")

/**
 * Integer literals
 *
 * (NUMERAL Int)
 */
class IntLiteral(val value: BigInteger) :
    Literal<IntSort>(LiteralString(value.toString()), IntSort) {
  override fun toString(): String = value.toString()

  override fun copy(children: List<Expression<*>>): Expression<IntSort> = this
}

/**
 * Integer negation
 *
 * (- Int Int)
 */
class IntNeg(override val inner: Expression<IntSort>) :
    UnaryExpression<IntSort, IntSort>("-".symbol(), IntSort) {
  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      IntNegDecl.buildExpression(children, emptyList())
}

/**
 * Integer subtraction
 *
 * (- Int Int Int :left-assoc)
 */
class IntSub(val terms: List<Expression<IntSort>>) :
    HomogenousExpression<IntSort, IntSort>("-".symbol(), IntSort) {
  init {
    require(terms.size > 1) {
      "Integer subtraction needs at least 2 terms but ${terms.size} were provided"
    }
  }

  constructor(vararg terms: Expression<IntSort>) : this(terms.toList())

  override val children: List<Expression<IntSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      IntSubDecl.buildExpression(children, emptyList())
}

/**
 * Integer addition
 *
 * (+ Int Int Int :left-assoc)
 */
class IntAdd(val terms: List<Expression<IntSort>>) :
    HomogenousExpression<IntSort, IntSort>("+".symbol(), IntSort) {
  init {
    require(terms.size > 1) {
      "Integer addition needs at least 2 terms but ${terms.size} were provided"
    }
  }

  constructor(vararg terms: Expression<IntSort>) : this(terms.toList())

  override val children: List<Expression<IntSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      IntAddDecl.buildExpression(children, emptyList())
}

/**
 * Integer multiplication
 *
 * (* Int Int Int :left-assoc)
 */
class IntMul(val factors: List<Expression<IntSort>>) :
    HomogenousExpression<IntSort, IntSort>("*".symbol(), IntSort) {
  init {
    require(factors.size > 1) {
      "Integer multiplication needs at least 2 factors but ${factors.size} were provided"
    }
  }

  constructor(vararg factors: Expression<IntSort>) : this(factors.toList())

  override val children: List<Expression<IntSort>> = factors

  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      IntMulDecl.buildExpression(children, emptyList())
}

/**
 * Integer division
 *
 * (div Int Int Int :left-assoc)
 */
class IntDiv(val terms: List<Expression<IntSort>>) :
    HomogenousExpression<IntSort, IntSort>("/".symbol(), IntSort) {
  init {
    require(terms.size > 1) {
      "Integer division needs at least 2 terms but ${terms.size} were provided"
    }
  }

  constructor(vararg terms: Expression<IntSort>) : this(terms.toList())

  override val children: List<Expression<IntSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      IntDivDecl.buildExpression(children, emptyList())
}

/**
 * Modulo
 *
 * (mod Int Int Int)
 */
class Mod(val dividend: Expression<IntSort>, val divisor: Expression<IntSort>) :
    BinaryExpression<IntSort, IntSort, IntSort>("mod".symbol(), IntSort) {

  override val lhs: Expression<IntSort> = dividend

  override val rhs: Expression<IntSort> = divisor

  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      ModDecl.buildExpression(children, emptyList())
}

/**
 * Absolute value
 *
 * (abs Int Int)
 */
class Abs(override val inner: Expression<IntSort>) :
    UnaryExpression<IntSort, IntSort>("abs".symbol(), IntSort) {
  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      AbsDecl.buildExpression(children, emptyList())
}

/**
 * Integer less equals
 *
 * (<= Int Int Bool :chainable)
 */
class IntLessEq(val terms: List<Expression<IntSort>>) :
    HomogenousExpression<BoolSort, IntSort>("<=".symbol(), BoolSort) {
  constructor(vararg terms: Expression<IntSort>) : this(terms.toList())

  init {
    require(terms.size > 1) {
      "Integer comparison needs at least 2 terms but ${terms.size} were provided"
    }
  }

  override val children: List<Expression<IntSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      IntLessEqDecl.buildExpression(children, emptyList())
}

/**
 * Integer less
 *
 * (< Int Int Bool :chainable)
 */
class IntLess(val terms: List<Expression<IntSort>>) :
    HomogenousExpression<BoolSort, IntSort>("<".symbol(), BoolSort) {
  constructor(vararg terms: Expression<IntSort>) : this(terms.toList())

  init {
    require(terms.size > 1) {
      "Integer comparison needs at least 2 terms but ${terms.size} were provided"
    }
  }

  override val children: List<Expression<IntSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      IntLessDecl.buildExpression(children, emptyList())
}

/**
 * Integer greater equals
 *
 * (>= Int Int Bool :chainable)
 */
class IntGreaterEq(val terms: List<Expression<IntSort>>) :
    HomogenousExpression<BoolSort, IntSort>(">=".symbol(), BoolSort) {
  constructor(vararg terms: Expression<IntSort>) : this(terms.toList())

  init {
    require(terms.size > 1) {
      "Integer comparison needs at least 2 terms but ${terms.size} were provided"
    }
  }

  override val children: List<Expression<IntSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      IntGreaterEqDecl.buildExpression(children, emptyList())
}

/**
 * Integer greater
 *
 * (> Int Int Bool :chainable)
 */
class IntGreater(val terms: List<Expression<IntSort>>) :
    HomogenousExpression<BoolSort, IntSort>(">".symbol(), BoolSort) {
  constructor(vararg terms: Expression<IntSort>) : this(terms.toList())

  init {
    require(terms.size > 1) {
      "Integer comparison needs at least 2 terms but ${terms.size} were provided"
    }
  }

  override val children: List<Expression<IntSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      IntGreaterDecl.buildExpression(children, emptyList())
}

/**
 * Divisible predicate,
 *
 * @throws IllegalArgumentException if [n] <= 0
 *
 * ((_ divisible n) Int Bool)
 */
class Divisible(val n: Int, override val inner: Expression<IntSort>) :
    UnaryExpression<BoolSort, IntSort>("divisible".symbol(), BoolSort) {

  init {
    require(n > 0)
  }

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      DivisibleDecl.buildExpression(children, emptyList())
}

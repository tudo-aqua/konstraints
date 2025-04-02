/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2025 The Konstraints Authors
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
object IntSort : Sort("Int") {
  override val theories = setOf(Theories.INTS, Theories.REALS_INTS, Theories.STRINGS)
}

/**
 * Integer literals
 *
 * (NUMERAL Int)
 */
class IntLiteral(val value: BigInteger) :
    Literal<IntSort>(LiteralString(value.toString()), IntSort) {
  override val theories = INTS_REALS_INTS_MARKER_SET

  constructor(value: Byte) : this(value.toInt().toBigInteger())

  constructor(value: Short) : this(value.toInt().toBigInteger())

  constructor(value: Int) : this(value.toBigInteger())

  constructor(value: Long) : this(value.toBigInteger())

  override fun toString(): String = value.toString()

  override fun copy(children: List<Expression<*>>): Expression<IntSort> = this
}

/**
 * Integer negation
 *
 * (- Int Int)
 */
class IntNeg(override val inner: Expression<IntSort>) :
    UnaryExpression<IntSort, IntSort>("-".toSymbolWithQuotes(), IntSort) {
  override val theories = INTS_REALS_INTS_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      IntNegDecl.constructDynamic(children, emptyList())
}

/**
 * Integer subtraction
 *
 * (- Int Int Int :left-assoc)
 */
class IntSub(val terms: List<Expression<IntSort>>) :
    HomogenousExpression<IntSort, IntSort>("-".toSymbolWithQuotes(), IntSort) {
  override val theories = INTS_REALS_INTS_MARKER_SET

  init {
    require(terms.size > 1) {
      "Integer subtraction needs at least 2 terms but ${terms.size} were provided"
    }
  }

  constructor(vararg terms: Expression<IntSort>) : this(terms.toList())

  override val children: List<Expression<IntSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      IntSubDecl.constructDynamic(children, emptyList())
}

/**
 * Integer addition
 *
 * (+ Int Int Int :left-assoc)
 */
class IntAdd(val terms: List<Expression<IntSort>>) :
    HomogenousExpression<IntSort, IntSort>("+".toSymbolWithQuotes(), IntSort) {
  override val theories = INTS_REALS_INTS_MARKER_SET

  init {
    require(terms.size > 1) {
      "Integer addition needs at least 2 terms but ${terms.size} were provided"
    }
  }

  constructor(vararg terms: Expression<IntSort>) : this(terms.toList())

  override val children: List<Expression<IntSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      IntAddDecl.constructDynamic(children, emptyList())
}

/**
 * Integer multiplication
 *
 * (* Int Int Int :left-assoc)
 */
class IntMul(val factors: List<Expression<IntSort>>) :
    HomogenousExpression<IntSort, IntSort>("*".toSymbolWithQuotes(), IntSort) {
  override val theories = INTS_REALS_INTS_MARKER_SET

  init {
    require(factors.size > 1) {
      "Integer multiplication needs at least 2 factors but ${factors.size} were provided"
    }
  }

  constructor(vararg factors: Expression<IntSort>) : this(factors.toList())

  override val children: List<Expression<IntSort>> = factors

  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      IntMulDecl.constructDynamic(children, emptyList())
}

/**
 * Integer division
 *
 * (div Int Int Int :left-assoc)
 */
class IntDiv(val terms: List<Expression<IntSort>>) :
    HomogenousExpression<IntSort, IntSort>("/".toSymbolWithQuotes(), IntSort) {
  override val theories = INTS_REALS_INTS_MARKER_SET

  init {
    require(terms.size > 1) {
      "Integer division needs at least 2 terms but ${terms.size} were provided"
    }
  }

  constructor(vararg terms: Expression<IntSort>) : this(terms.toList())

  override val children: List<Expression<IntSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      IntDivDecl.constructDynamic(children, emptyList())
}

/**
 * Modulo
 *
 * (mod Int Int Int)
 */
class Mod(val dividend: Expression<IntSort>, val divisor: Expression<IntSort>) :
    BinaryExpression<IntSort, IntSort, IntSort>("mod".toSymbolWithQuotes(), IntSort) {
  override val theories = INTS_REALS_INTS_MARKER_SET

  override val lhs: Expression<IntSort> = dividend

  override val rhs: Expression<IntSort> = divisor

  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      ModDecl.constructDynamic(children, emptyList())
}

/**
 * Absolute value
 *
 * (abs Int Int)
 */
class Abs(override val inner: Expression<IntSort>) :
    UnaryExpression<IntSort, IntSort>("abs".toSymbolWithQuotes(), IntSort) {
  override val theories = INTS_REALS_INTS_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      AbsDecl.constructDynamic(children, emptyList())
}

/**
 * Integer less equals
 *
 * (<= Int Int Bool :chainable)
 */
class IntLessEq(val terms: List<Expression<IntSort>>) :
    HomogenousExpression<BoolSort, IntSort>("<=".toSymbolWithQuotes(), BoolSort) {
  override val theories = INTS_REALS_INTS_MARKER_SET

  constructor(vararg terms: Expression<IntSort>) : this(terms.toList())

  init {
    require(terms.size > 1) {
      "Integer comparison needs at least 2 terms but ${terms.size} were provided"
    }
  }

  override val children: List<Expression<IntSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      IntLessEqDecl.constructDynamic(children, emptyList())
}

/**
 * Integer less
 *
 * (< Int Int Bool :chainable)
 */
class IntLess(val terms: List<Expression<IntSort>>) :
    HomogenousExpression<BoolSort, IntSort>("<".toSymbolWithQuotes(), BoolSort) {
  override val theories = INTS_REALS_INTS_MARKER_SET

  constructor(vararg terms: Expression<IntSort>) : this(terms.toList())

  init {
    require(terms.size > 1) {
      "Integer comparison needs at least 2 terms but ${terms.size} were provided"
    }
  }

  override val children: List<Expression<IntSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      IntLessDecl.constructDynamic(children, emptyList())
}

/**
 * Integer greater equals
 *
 * (>= Int Int Bool :chainable)
 */
class IntGreaterEq(val terms: List<Expression<IntSort>>) :
    HomogenousExpression<BoolSort, IntSort>(">=".toSymbolWithQuotes(), BoolSort) {
  override val theories = INTS_REALS_INTS_MARKER_SET

  constructor(vararg terms: Expression<IntSort>) : this(terms.toList())

  init {
    require(terms.size > 1) {
      "Integer comparison needs at least 2 terms but ${terms.size} were provided"
    }
  }

  override val children: List<Expression<IntSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      IntGreaterEqDecl.constructDynamic(children, emptyList())
}

/**
 * Integer greater
 *
 * (> Int Int Bool :chainable)
 */
class IntGreater(val terms: List<Expression<IntSort>>) :
    HomogenousExpression<BoolSort, IntSort>(">".toSymbolWithQuotes(), BoolSort) {
  override val theories = INTS_REALS_INTS_MARKER_SET

  constructor(vararg terms: Expression<IntSort>) : this(terms.toList())

  init {
    require(terms.size > 1) {
      "Integer comparison needs at least 2 terms but ${terms.size} were provided"
    }
  }

  override val children: List<Expression<IntSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      IntGreaterDecl.constructDynamic(children, emptyList())
}

/**
 * Divisible predicate,
 *
 * @throws IllegalArgumentException if [n] <= 0
 *
 * ((_ divisible n) Int Bool)
 */
class Divisible(val n: Int, override val inner: Expression<IntSort>) :
    UnaryExpression<BoolSort, IntSort>("divisible".toSymbolWithQuotes(), BoolSort) {
  override val theories = INTS_REALS_INTS_MARKER_SET

  init {
    require(n > 0)
  }

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      DivisibleDecl.constructDynamic(children, emptyList())
}

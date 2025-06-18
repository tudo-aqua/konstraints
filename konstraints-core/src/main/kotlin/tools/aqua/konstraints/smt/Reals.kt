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

package tools.aqua.konstraints.smt

import java.math.BigDecimal
import java.math.BigInteger
import tools.aqua.konstraints.parser.*

/** Real sort */
sealed class RealSort : Sort("Real") {
  override val theories = REALS_REALS_INTS_MARKER_SET.plus(FLOATING_POINT_MARKER_SET)
}

object Real : RealSort()

/**
 * Real literal
 *
 * (NUMERAL Real) (DECIMAL Real)
 */
class RealLiteral(val value: BigDecimal) :
    Literal<RealSort>(LiteralString(value.toString()), Real) {
  override val theories = REALS_REALS_INTS_MARKER_SET.plus(FLOATING_POINT_MARKER_SET)

  constructor(value: Byte) : this(value.toInt().toBigDecimal())

  constructor(value: Short) : this(value.toInt().toBigDecimal())

  constructor(value: Int) : this(value.toBigDecimal())

  constructor(value: Long) : this(value.toBigDecimal())

  constructor(value: BigInteger) : this(value.toBigDecimal())

  constructor(value: Float) : this(value.toBigDecimal())

  constructor(value: Double) : this(value.toBigDecimal())

  override val sort: RealSort = Real

  override fun toString(): String = value.toString()

  override fun copy(children: List<Expression<*>>): Expression<RealSort> = this
}

/**
 * Real negation
 *
 * (- Real Real)
 */
class RealNeg(override val inner: Expression<RealSort>) :
    UnaryExpression<RealSort, RealSort>("-".toSymbolWithQuotes(), Real) {
  override val theories = REALS_REALS_INTS_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<RealSort> =
      RealNegDecl.constructDynamic(children, emptyList())
}

/**
 * Real subtraction
 *
 * (- Real Real Real :left-assoc)
 */
class RealSub(val terms: List<Expression<RealSort>>) :
    HomogenousExpression<RealSort, RealSort>("-".toSymbolWithQuotes(), Real) {
  override val theories = REALS_REALS_INTS_MARKER_SET

  init {
    require(terms.size > 1) {
      "Integer subtraction needs at least 2 terms but ${terms.size} were provided"
    }
  }

  constructor(vararg terms: Expression<RealSort>) : this(terms.toList())

  override val children: List<Expression<RealSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<RealSort> =
      RealSubDecl.constructDynamic(children, emptyList())
}

/**
 * Real addition
 *
 * (+ Real Real Real :left-assoc)
 */
class RealAdd(val terms: List<Expression<RealSort>>) :
    HomogenousExpression<RealSort, RealSort>("+".toSymbolWithQuotes(), Real) {
  override val theories = REALS_REALS_INTS_MARKER_SET

  init {
    require(terms.size > 1) {
      "Integer addition needs at least 2 terms but ${terms.size} were provided"
    }
  }

  constructor(vararg terms: Expression<RealSort>) : this(terms.toList())

  override val children: List<Expression<RealSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<RealSort> =
      RealAddDecl.constructDynamic(children, emptyList())
}

/**
 * Real multiplication
 *
 * (* Real Real Real :left-assoc)
 */
class RealMul(val factors: List<Expression<RealSort>>) :
    HomogenousExpression<RealSort, RealSort>("*".toSymbolWithQuotes(), Real) {
  override val theories = REALS_REALS_INTS_MARKER_SET

  init {
    require(factors.size > 1) {
      "Integer multiplication needs at least 2 factors but ${factors.size} were provided"
    }
  }

  constructor(vararg factors: Expression<RealSort>) : this(factors.toList())

  override val children: List<Expression<RealSort>> = factors

  override fun copy(children: List<Expression<*>>): Expression<RealSort> =
      RealMulDecl.constructDynamic(children, emptyList())
}

/**
 * Real division
 *
 * (/ Real Real Real :left-assoc)
 */
class RealDiv(val terms: List<Expression<RealSort>>) :
    HomogenousExpression<RealSort, RealSort>("/".toSymbolWithQuotes(), Real) {
  override val theories = REALS_REALS_INTS_MARKER_SET

  init {
    require(terms.size > 1) {
      "Integer division needs at least 2 terms but ${terms.size} were provided"
    }
  }

  constructor(vararg terms: Expression<RealSort>) : this(terms.toList())

  override val children: List<Expression<RealSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<RealSort> =
      RealDivDecl.constructDynamic(children, emptyList())
}

/**
 * Real less equals
 *
 * (<= Real Real Bool :chainable)
 */
class RealLessEq(val terms: List<Expression<RealSort>>) :
    HomogenousExpression<BoolSort, RealSort>("<=".toSymbolWithQuotes(), Bool) {
  override val theories = REALS_REALS_INTS_MARKER_SET

  init {
    require(terms.size > 1) {
      "Integer comparison needs at least 2 terms but ${terms.size} were provided"
    }
  }

  constructor(vararg terms: Expression<RealSort>) : this(terms.toList())

  override val children: List<Expression<RealSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      RealLessEqDecl.constructDynamic(children, emptyList())
}

/**
 * Real less
 *
 * (<= Real Real Bool :chainable)
 */
class RealLess(val terms: List<Expression<RealSort>>) :
    HomogenousExpression<BoolSort, RealSort>("<".toSymbolWithQuotes(), Bool) {
  override val theories = REALS_REALS_INTS_MARKER_SET

  init {
    require(terms.size > 1) {
      "Integer comparison needs at least 2 terms but ${terms.size} were provided"
    }
  }

  constructor(vararg terms: Expression<RealSort>) : this(terms.toList())

  override val children: List<Expression<RealSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      RealLessDecl.constructDynamic(children, emptyList())
}

/**
 * Real greater equals
 *
 * (<= Real Real Bool :chainable)
 */
class RealGreaterEq(val terms: List<Expression<RealSort>>) :
    HomogenousExpression<BoolSort, RealSort>(">=".toSymbolWithQuotes(), Bool) {
  override val theories = REALS_REALS_INTS_MARKER_SET

  init {
    require(terms.size > 1) {
      "Integer comparison needs at least 2 terms but ${terms.size} were provided"
    }
  }

  constructor(vararg terms: Expression<RealSort>) : this(terms.toList())

  override val children: List<Expression<RealSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      RealGreaterEqDecl.constructDynamic(children, emptyList())
}

/**
 * Real greater
 *
 * (<= Real Real Bool :chainable)
 */
class RealGreater(val terms: List<Expression<RealSort>>) :
    HomogenousExpression<BoolSort, RealSort>(">".toSymbolWithQuotes(), Bool) {
  override val theories = REALS_REALS_INTS_MARKER_SET

  init {
    require(terms.size > 1) {
      "Integer comparison needs at least 2 terms but ${terms.size} were provided"
    }
  }

  constructor(vararg terms: Expression<RealSort>) : this(terms.toList())

  override val children: List<Expression<RealSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      RealGreaterDecl.constructDynamic(children, emptyList())
}

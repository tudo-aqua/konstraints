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

import java.math.BigDecimal
import tools.aqua.konstraints.parser.*
import tools.aqua.konstraints.smt.*
import java.math.BigInteger

/** Real sort */
object RealSort : Sort("Real")

/**
 * Real literal
 *
 * (NUMERAL Real) (DECIMAL Real)
 */
class RealLiteral(val value: BigDecimal) :
    Literal<RealSort>(LiteralString(value.toString()), RealSort) {
    companion object {
        private val theoriesSet = setOf(Theories.REALS, Theories.REALS_INTS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

    constructor(value: Byte) : this(value.toInt().toBigDecimal())

    constructor(value: Short) : this(value.toInt().toBigDecimal())

    constructor(value: Int) : this(value.toBigDecimal())

    constructor(value: Long) : this(value.toBigDecimal())

    constructor(value: BigInteger) : this(value.toBigDecimal())

    constructor(value: Float) : this(value.toBigDecimal())

    constructor(value: Double) : this(value.toBigDecimal())

  override val sort: RealSort = RealSort

  override fun toString(): String = value.toString()

  override fun copy(children: List<Expression<*>>): Expression<RealSort> = this
}

/**
 * Real negation
 *
 * (- Real Real)
 */
class RealNeg(override val inner: Expression<RealSort>) :
    UnaryExpression<RealSort, RealSort>("-".symbol(), RealSort) {
    companion object {
        private val theoriesSet = setOf(Theories.REALS, Theories.REALS_INTS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  override fun copy(children: List<Expression<*>>): Expression<RealSort> =
      RealNegDecl.buildExpression(children, emptyList())
}

/**
 * Real subtraction
 *
 * (- Real Real Real :left-assoc)
 */
class RealSub(val terms: List<Expression<RealSort>>) :
    HomogenousExpression<RealSort, RealSort>("-".symbol(), RealSort) {
    companion object {
        private val theoriesSet = setOf(Theories.REALS, Theories.REALS_INTS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  init {
    require(terms.size > 1) {
      "Integer subtraction needs at least 2 terms but ${terms.size} were provided"
    }
  }

  constructor(vararg terms: Expression<RealSort>) : this(terms.toList())

  override val children: List<Expression<RealSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<RealSort> =
      RealSubDecl.buildExpression(children, emptyList())
}

/**
 * Real addition
 *
 * (+ Real Real Real :left-assoc)
 */
class RealAdd(val terms: List<Expression<RealSort>>) :
    HomogenousExpression<RealSort, RealSort>("+".symbol(), RealSort) {
    companion object {
        private val theoriesSet = setOf(Theories.REALS, Theories.REALS_INTS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  init {
    require(terms.size > 1) {
      "Integer addition needs at least 2 terms but ${terms.size} were provided"
    }
  }

  constructor(vararg terms: Expression<RealSort>) : this(terms.toList())

  override val children: List<Expression<RealSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<RealSort> =
      RealAddDecl.buildExpression(children, emptyList())
}

/**
 * Real multiplication
 *
 * (* Real Real Real :left-assoc)
 */
class RealMul(val factors: List<Expression<RealSort>>) :
    HomogenousExpression<RealSort, RealSort>("*".symbol(), RealSort) {
    companion object {
        private val theoriesSet = setOf(Theories.REALS, Theories.REALS_INTS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  init {
    require(factors.size > 1) {
      "Integer multiplication needs at least 2 factors but ${factors.size} were provided"
    }
  }

  constructor(vararg factors: Expression<RealSort>) : this(factors.toList())

  override val children: List<Expression<RealSort>> = factors

  override fun copy(children: List<Expression<*>>): Expression<RealSort> =
      RealMulDecl.buildExpression(children, emptyList())
}

/**
 * Real division
 *
 * (/ Real Real Real :left-assoc)
 */
class RealDiv(val terms: List<Expression<RealSort>>) :
    HomogenousExpression<RealSort, RealSort>("/".symbol(), RealSort) {
    companion object {
        private val theoriesSet = setOf(Theories.REALS, Theories.REALS_INTS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  init {
    require(terms.size > 1) {
      "Integer division needs at least 2 terms but ${terms.size} were provided"
    }
  }

  constructor(vararg terms: Expression<RealSort>) : this(terms.toList())

  override val children: List<Expression<RealSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<RealSort> =
      RealDivDecl.buildExpression(children, emptyList())
}

/**
 * Real less equals
 *
 * (<= Real Real Bool :chainable)
 */
class RealLessEq(val terms: List<Expression<RealSort>>) :
    HomogenousExpression<BoolSort, RealSort>("<=".symbol(), BoolSort) {
    companion object {
        private val theoriesSet = setOf(Theories.REALS, Theories.REALS_INTS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  init {
    require(terms.size > 1) {
      "Integer comparison needs at least 2 terms but ${terms.size} were provided"
    }
  }

  constructor(vararg terms: Expression<RealSort>) : this(terms.toList())

  override val children: List<Expression<RealSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      RealLessEqDecl.buildExpression(children, emptyList())
}

/**
 * Real less
 *
 * (<= Real Real Bool :chainable)
 */
class RealLess(val terms: List<Expression<RealSort>>) :
    HomogenousExpression<BoolSort, RealSort>("<".symbol(), BoolSort) {
    companion object {
        private val theoriesSet = setOf(Theories.REALS, Theories.REALS_INTS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  init {
    require(terms.size > 1) {
      "Integer comparison needs at least 2 terms but ${terms.size} were provided"
    }
  }

  constructor(vararg terms: Expression<RealSort>) : this(terms.toList())

  override val children: List<Expression<RealSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      RealLessDecl.buildExpression(children, emptyList())
}

/**
 * Real greater equals
 *
 * (<= Real Real Bool :chainable)
 */
class RealGreaterEq(val terms: List<Expression<RealSort>>) :
    HomogenousExpression<BoolSort, RealSort>(">=".symbol(), BoolSort) {
    companion object {
        private val theoriesSet = setOf(Theories.REALS, Theories.REALS_INTS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  init {
    require(terms.size > 1) {
      "Integer comparison needs at least 2 terms but ${terms.size} were provided"
    }
  }

  constructor(vararg terms: Expression<RealSort>) : this(terms.toList())

  override val children: List<Expression<RealSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      RealGreaterEqDecl.buildExpression(children, emptyList())
}

/**
 * Real greater
 *
 * (<= Real Real Bool :chainable)
 */
class RealGreater(val terms: List<Expression<RealSort>>) :
    HomogenousExpression<BoolSort, RealSort>(">".symbol(), BoolSort) {
    companion object {
        private val theoriesSet = setOf(Theories.REALS, Theories.REALS_INTS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  init {
    require(terms.size > 1) {
      "Integer comparison needs at least 2 terms but ${terms.size} were provided"
    }
  }

  constructor(vararg terms: Expression<RealSort>) : this(terms.toList())

  override val children: List<Expression<RealSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      RealGreaterDecl.buildExpression(children, emptyList())
}

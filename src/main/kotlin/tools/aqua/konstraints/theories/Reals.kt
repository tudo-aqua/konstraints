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
import tools.aqua.konstraints.parser.SortDecl
import tools.aqua.konstraints.smt.*

/** Reals theory object */
object RealsTheory : Theory {
  override val functions =
      listOf(
              RealNegSubDecl,
              RealAddDecl,
              RealMulDecl,
              RealDivDecl,
              RealLessEqDecl,
              RealLessDecl,
              RealGreaterEqDecl,
              RealGreaterDecl)
          .associateBy { it.name.toString() }

  override val sorts: Map<String, SortDecl<*>> = mapOf(Pair("Real", RealSortDecl))
}

/** Real sort */
object RealSort : Sort("Real")

internal object RealSortDecl : SortDecl<RealSort>("Real".symbol(), emptySet(), emptySet()) {
  override fun getSort(bindings: Bindings): RealSort = RealSort
}

/**
 * Real literal
 *
 * (NUMERAL Real) (DECIMAL Real)
 */
class RealLiteral(val value: BigDecimal) :
    Literal<RealSort>(LiteralString(value.toString()), RealSort) {
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
  override fun copy(children: List<Expression<*>>): Expression<RealSort> =
      RealNegDecl.buildExpression(children, emptyList())
}

object RealNegDecl :
    FunctionDecl1<RealSort, RealSort>(
        "-".symbol(), emptySet(), RealSort, emptySet(), emptySet(), RealSort) {
  override fun buildExpression(
      param: Expression<RealSort>,
      bindings: Bindings
  ): Expression<RealSort> = RealNeg(param)
}

/**
 * Real subtraction
 *
 * (- Real Real Real :left-assoc)
 */
class RealSub(val terms: List<Expression<RealSort>>) :
    HomogenousExpression<RealSort, RealSort>("-".symbol(), RealSort) {
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

object RealSubDecl :
    FunctionDeclLeftAssociative<RealSort, RealSort, RealSort>(
        "-".symbol(), emptySet(), RealSort, RealSort, emptySet(), emptySet(), RealSort) {
  override fun buildExpression(
      param1: Expression<RealSort>,
      param2: Expression<RealSort>,
      varargs: List<Expression<RealSort>>,
      bindings: Bindings
  ): Expression<RealSort> = RealSub(listOf(param1, param2) + varargs)
}

/** Combined function declaration for overloaded '-' operator */
object RealNegSubDecl :
    FunctionDecl<RealSort>(
        "-".symbol(),
        emptySet(),
        listOf(RealSort),
        emptySet(),
        emptySet(),
        RealSort,
        Associativity.NONE) {
  override fun buildExpression(
      args: List<Expression<*>>,
      functionIndices: List<NumeralIndex>
  ): Expression<RealSort> {
    require(args.isNotEmpty())

    return if (args.size == 1) {
      RealNegDecl.buildExpression(args, functionIndices)
    } else {
      RealSubDecl.buildExpression(args, functionIndices)
    }
  }

  override fun bindParametersTo(args: List<Sort>, indices: List<NumeralIndex>) =
      if (args.size == 1) {
        RealNegDecl.bindParametersTo(args, indices)
      } else {
        RealSubDecl.bindParametersTo(args, indices)
      }

  override fun accepts(args: List<Sort>, indices: List<NumeralIndex>) =
      if (args.size == 1) {
        RealNegDecl.accepts(args, indices)
      } else {
        RealSubDecl.accepts(args, indices)
      }
}

/**
 * Real addition
 *
 * (+ Real Real Real :left-assoc)
 */
class RealAdd(val terms: List<Expression<RealSort>>) :
    HomogenousExpression<RealSort, RealSort>("+".symbol(), RealSort) {
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

object RealAddDecl :
    FunctionDeclLeftAssociative<RealSort, RealSort, RealSort>(
        "+".symbol(), emptySet(), RealSort, RealSort, emptySet(), emptySet(), RealSort) {
  override fun buildExpression(
      param1: Expression<RealSort>,
      param2: Expression<RealSort>,
      varargs: List<Expression<RealSort>>,
      bindings: Bindings
  ): Expression<RealSort> = RealAdd(listOf(param1, param2) + varargs)
}

/**
 * Real multiplication
 *
 * (* Real Real Real :left-assoc)
 */
class RealMul(val factors: List<Expression<RealSort>>) :
    HomogenousExpression<RealSort, RealSort>("*".symbol(), RealSort) {
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

object RealMulDecl :
    FunctionDeclLeftAssociative<RealSort, RealSort, RealSort>(
        "*".symbol(), emptySet(), RealSort, RealSort, emptySet(), emptySet(), RealSort) {
  override fun buildExpression(
      param1: Expression<RealSort>,
      param2: Expression<RealSort>,
      varargs: List<Expression<RealSort>>,
      bindings: Bindings
  ): Expression<RealSort> = RealMul(listOf(param1, param2) + varargs)
}

/**
 * Real division
 *
 * (/ Real Real Real :left-assoc)
 */
class RealDiv(val terms: List<Expression<RealSort>>) :
    HomogenousExpression<RealSort, RealSort>("/".symbol(), RealSort) {
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

object RealDivDecl :
    FunctionDeclLeftAssociative<RealSort, RealSort, RealSort>(
        "/".symbol(), emptySet(), RealSort, RealSort, emptySet(), emptySet(), RealSort) {
  override fun buildExpression(
      param1: Expression<RealSort>,
      param2: Expression<RealSort>,
      varargs: List<Expression<RealSort>>,
      bindings: Bindings
  ): Expression<RealSort> = RealDiv(listOf(param1, param2) + varargs)
}

/**
 * Real less equals
 *
 * (<= Real Real Bool :chainable)
 */
class RealLessEq(val terms: List<Expression<RealSort>>) :
    HomogenousExpression<BoolSort, RealSort>("<=".symbol(), BoolSort) {
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

object RealLessEqDecl :
    FunctionDeclChainable<RealSort>(
        "<=".symbol(), emptySet(), RealSort, RealSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<RealSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = RealLessEq(varargs)
}

/**
 * Real less
 *
 * (<= Real Real Bool :chainable)
 */
class RealLess(val terms: List<Expression<RealSort>>) :
    HomogenousExpression<BoolSort, RealSort>("<".symbol(), BoolSort) {
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

object RealLessDecl :
    FunctionDeclChainable<RealSort>(
        "<".symbol(), emptySet(), RealSort, RealSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<RealSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = RealLess(varargs)
}

/**
 * Real greater equals
 *
 * (<= Real Real Bool :chainable)
 */
class RealGreaterEq(val terms: List<Expression<RealSort>>) :
    HomogenousExpression<BoolSort, RealSort>(">=".symbol(), BoolSort) {
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

object RealGreaterEqDecl :
    FunctionDeclChainable<RealSort>(
        ">=".symbol(), emptySet(), RealSort, RealSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<RealSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = RealGreaterEq(varargs)
}

/**
 * Real greater
 *
 * (<= Real Real Bool :chainable)
 */
class RealGreater(val terms: List<Expression<RealSort>>) :
    HomogenousExpression<BoolSort, RealSort>(">".symbol(), BoolSort) {
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

object RealGreaterDecl :
    FunctionDeclChainable<RealSort>(
        ">".symbol(), emptySet(), RealSort, RealSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<RealSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = RealGreater(varargs)
}

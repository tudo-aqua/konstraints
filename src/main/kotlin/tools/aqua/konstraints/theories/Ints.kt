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

/** Ints theory object */
object IntsTheory : Theory {
  override val functions =
      listOf(
              IntNegDecl,
              IntSubDecl,
              IntAddDecl,
              IntMulDecl,
              IntDivDecl,
              ModDecl,
              AbsDecl,
              IntLessEqDecl,
              IntLessDecl,
              IntGreaterEqDecl,
              IntGreaterDecl,
              DivisibleDecl)
          .associateBy { it.name.toString() }

  override val sorts: Map<String, SortDecl<*>> = mapOf(Pair("Int", IntSortDecl))
}

/** Int sort */
object IntSort : Sort("Int")

internal object IntSortDecl : SortDecl<IntSort>("Int".symbol(), emptySet(), emptySet()) {
  override fun getSort(bindings: Bindings): IntSort = IntSort
}

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
      IntNegDecl.buildExpression(children, emptySet())
}

object IntNegDecl :
    FunctionDecl1<IntSort, IntSort>(
        "-".symbol(), emptySet(), IntSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param: Expression<IntSort>,
      bindings: Bindings
  ): Expression<IntSort> = IntNeg(param)
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

  override val children: List<Expression<IntSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      IntSubDecl.buildExpression(children, emptySet())
}

object IntSubDecl :
    FunctionDeclLeftAssociative<IntSort, IntSort, IntSort>(
        "-".symbol(), emptySet(), IntSort, IntSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param1: Expression<IntSort>,
      param2: Expression<IntSort>,
      varargs: List<Expression<IntSort>>,
      bindings: Bindings
  ): Expression<IntSort> = IntSub(listOf(param1, param2) + varargs)
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

  override val children: List<Expression<IntSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      IntAddDecl.buildExpression(children, emptySet())
}

object IntAddDecl :
    FunctionDeclLeftAssociative<IntSort, IntSort, IntSort>(
        "+".symbol(), emptySet(), IntSort, IntSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param1: Expression<IntSort>,
      param2: Expression<IntSort>,
      varargs: List<Expression<IntSort>>,
      bindings: Bindings
  ): Expression<IntSort> = IntAdd(listOf(param1, param2) + varargs)
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

  override val children: List<Expression<IntSort>> = factors

  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      IntMulDecl.buildExpression(children, emptySet())
}

object IntMulDecl :
    FunctionDeclLeftAssociative<IntSort, IntSort, IntSort>(
        "*".symbol(), emptySet(), IntSort, IntSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param1: Expression<IntSort>,
      param2: Expression<IntSort>,
      varargs: List<Expression<IntSort>>,
      bindings: Bindings
  ): Expression<IntSort> = IntMul(listOf(param1, param2) + varargs)
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

  override val children: List<Expression<IntSort>> = terms

  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      IntDivDecl.buildExpression(children, emptySet())
}

object IntDivDecl :
    FunctionDeclLeftAssociative<IntSort, IntSort, IntSort>(
        "div".symbol(), emptySet(), IntSort, IntSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param1: Expression<IntSort>,
      param2: Expression<IntSort>,
      varargs: List<Expression<IntSort>>,
      bindings: Bindings
  ): Expression<IntSort> = IntDiv(listOf(param1, param2) + varargs)
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
      ModDecl.buildExpression(children, emptySet())
}

object ModDecl :
    FunctionDecl2<IntSort, IntSort, IntSort>(
        "mod".symbol(), emptySet(), IntSort, IntSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param1: Expression<IntSort>,
      param2: Expression<IntSort>,
      bindings: Bindings
  ): Expression<IntSort> = Mod(param1, param2)
}

/**
 * Absolute value
 *
 * (abs Int Int)
 */
class Abs(override val inner: Expression<IntSort>) :
    UnaryExpression<IntSort, IntSort>("abs".symbol(), IntSort) {
  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      AbsDecl.buildExpression(children, emptySet())
}

object AbsDecl :
    FunctionDecl1<IntSort, IntSort>(
        "abs".symbol(), emptySet(), IntSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param: Expression<IntSort>,
      bindings: Bindings
  ): Expression<IntSort> = Abs(param)
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
      IntLessEqDecl.buildExpression(children, emptySet())
}

object IntLessEqDecl :
    FunctionDeclChainable<IntSort>(
        "<=".symbol(), emptySet(), IntSort, IntSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<IntSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = IntLessEq(varargs)
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
      IntLessDecl.buildExpression(children, emptySet())
}

object IntLessDecl :
    FunctionDeclChainable<IntSort>(
        "<".symbol(), emptySet(), IntSort, IntSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<IntSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = IntLess(varargs)
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
      IntGreaterEqDecl.buildExpression(children, emptySet())
}

object IntGreaterEqDecl :
    FunctionDeclChainable<IntSort>(
        ">=".symbol(), emptySet(), IntSort, IntSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<IntSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = IntGreaterEq(varargs)
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
      IntGreaterDecl.buildExpression(children, emptySet())
}

object IntGreaterDecl :
    FunctionDeclChainable<IntSort>(
        ">".symbol(), emptySet(), IntSort, IntSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<IntSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = IntGreater(varargs)
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
      DivisibleDecl.buildExpression(children, emptySet())
}

object DivisibleDecl :
    FunctionDecl1<IntSort, BoolSort>(
        "divisible".symbol(), emptySet(), IntSort, setOf(SymbolIndex("n")), emptySet(), BoolSort) {
  override fun buildExpression(
      param: Expression<IntSort>,
      bindings: Bindings
  ): Expression<BoolSort> = Divisible(bindings["n"].numeral, param)
}

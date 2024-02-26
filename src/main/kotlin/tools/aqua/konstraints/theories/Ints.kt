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

import tools.aqua.konstraints.parser.*
import tools.aqua.konstraints.smt.*

internal object IntsContext : TheoryContext {
  override val functions: HashSet<FunctionDecl<*>> =
      hashSetOf(
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

  override val sorts: Map<String, SortDecl<*>> = mapOf(Pair("Int", IntSortDecl))
}

object IntSort : Sort("Int")

internal object IntSortDecl : SortDecl<IntSort>("Int") {
  override fun getSort(sort: ProtoSort): IntSort = IntSort
}

class IntLiteral(val value: Int) : Expression<IntSort>() {
  override val symbol: String = value.toString()
  override val sort: IntSort = IntSort

  override fun toString(): String = symbol
}

class IntNeg(val inner: Expression<IntSort>) : Expression<IntSort>() {
  override val symbol: String = "(- $inner)"
  override val sort: IntSort = IntSort

  override fun toString(): String = symbol
}

object IntNegDecl :
    FunctionDecl1<IntSort, IntSort>("-", emptySet(), IntSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param: Expression<IntSort>,
      bindings: Bindings
  ): Expression<IntSort> = IntNeg(param)
}

class IntSub(val terms: List<Expression<IntSort>>) : Expression<IntSort>() {
  override val symbol: String = "(- ${terms.joinToString(separator = " ")})"
  override val sort: IntSort = IntSort

  init {
    require(terms.size > 1) {
      "Integer subtraction needs at least 2 terms but ${terms.size} were provided"
    }
  }

  override fun toString(): String = symbol
}

object IntSubDecl :
    FunctionDeclLeftAssociative<IntSort, IntSort, IntSort>(
        "-", emptySet(), IntSort, IntSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param1: Expression<IntSort>,
      param2: Expression<IntSort>,
      varargs: List<Expression<IntSort>>,
      bindings: Bindings
  ): Expression<IntSort> = IntSub(listOf(param1, param2) + varargs)
}

class IntAdd(val terms: List<Expression<IntSort>>) : Expression<IntSort>() {
  override val symbol: String = "(+ ${terms.joinToString(separator = " ")})"
  override val sort: IntSort = IntSort

  init {
    require(terms.size > 1) {
      "Integer addition needs at least 2 terms but ${terms.size} were provided"
    }
  }

  override fun toString(): String = symbol
}

object IntAddDecl :
    FunctionDeclLeftAssociative<IntSort, IntSort, IntSort>(
        "-", emptySet(), IntSort, IntSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param1: Expression<IntSort>,
      param2: Expression<IntSort>,
      varargs: List<Expression<IntSort>>,
      bindings: Bindings
  ): Expression<IntSort> = IntAdd(listOf(param1, param2) + varargs)
}

class IntMul(val factors: List<Expression<IntSort>>) : Expression<IntSort>() {
  override val symbol: String = "(* ${factors.joinToString(separator = " ")})"
  override val sort: IntSort = IntSort

  init {
    require(factors.size > 1) {
      "Integer multiplication needs at least 2 factors but ${factors.size} were provided"
    }
  }

  override fun toString(): String = symbol
}

object IntMulDecl :
    FunctionDeclLeftAssociative<IntSort, IntSort, IntSort>(
        "-", emptySet(), IntSort, IntSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param1: Expression<IntSort>,
      param2: Expression<IntSort>,
      varargs: List<Expression<IntSort>>,
      bindings: Bindings
  ): Expression<IntSort> = IntMul(listOf(param1, param2) + varargs)
}

class IntDiv(val terms: List<Expression<IntSort>>) : Expression<IntSort>() {
  override val symbol: String = "(/ ${terms.joinToString(separator = " ")})"
  override val sort: IntSort = IntSort

  init {
    require(terms.size > 1) {
      "Integer division needs at least 2 terms but ${terms.size} were provided"
    }
  }

  override fun toString(): String = symbol
}

object IntDivDecl :
    FunctionDeclLeftAssociative<IntSort, IntSort, IntSort>(
        "-", emptySet(), IntSort, IntSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param1: Expression<IntSort>,
      param2: Expression<IntSort>,
      varargs: List<Expression<IntSort>>,
      bindings: Bindings
  ): Expression<IntSort> = IntDiv(listOf(param1, param2) + varargs)
}

class Mod(val dividend: Expression<IntSort>, val divisor: Expression<IntSort>) :
    Expression<IntSort>() {
  override val symbol: String = "(mod $dividend $divisor)"
  override val sort: IntSort = IntSort

  override fun toString(): String = symbol
}

object ModDecl :
    FunctionDecl2<IntSort, IntSort, IntSort>(
        "mod", emptySet(), IntSort, IntSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param1: Expression<IntSort>,
      param2: Expression<IntSort>,
      bindings: Bindings
  ): Expression<IntSort> = Mod(param1, param2)
}

class Abs(val inner: Expression<IntSort>) : Expression<IntSort>() {
  override val symbol: String = "(abs $inner)"
  override val sort: IntSort = IntSort

  override fun toString(): String = symbol
}

object AbsDecl :
    FunctionDecl1<IntSort, IntSort>("abs", emptySet(), IntSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param: Expression<IntSort>,
      bindings: Bindings
  ): Expression<IntSort> = Abs(param)
}

class IntLessEq(val terms: List<Expression<IntSort>>) : Expression<BoolSort>() {
  override val symbol: String = "(<= ${terms.joinToString(separator = " ")})"
  override val sort: BoolSort = BoolSort

  init {
    require(terms.size > 1) {
      "Integer comparison needs at least 2 terms but ${terms.size} were provided"
    }
  }

  override fun toString(): String = symbol
}

object IntLessEqDecl :
    FunctionDeclChainable<IntSort>("<=", emptySet(), IntSort, IntSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<IntSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = IntLessEq(varargs)
}

class IntLess(val terms: List<Expression<IntSort>>) : Expression<BoolSort>() {
  override val symbol: String = "(< ${terms.joinToString(separator = " ")})"
  override val sort: BoolSort = BoolSort

  init {
    require(terms.size > 1) {
      "Integer comparison needs at least 2 terms but ${terms.size} were provided"
    }
  }

  override fun toString(): String = symbol
}

object IntLessDecl :
    FunctionDeclChainable<IntSort>("<", emptySet(), IntSort, IntSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<IntSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = IntLess(varargs)
}

class IntGreaterEq(val terms: List<Expression<IntSort>>) : Expression<BoolSort>() {
  override val symbol: String = "(>= ${terms.joinToString(separator = " ")})"
  override val sort: BoolSort = BoolSort

  init {
    require(terms.size > 1) {
      "Integer comparison needs at least 2 terms but ${terms.size} were provided"
    }
  }

  override fun toString(): String = symbol
}

object IntGreaterEqDecl :
    FunctionDeclChainable<IntSort>(">=", emptySet(), IntSort, IntSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<IntSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = IntGreaterEq(varargs)
}

class IntGreater(val terms: List<Expression<IntSort>>) : Expression<BoolSort>() {
  override val symbol: String = "(> ${terms.joinToString(separator = " ")})"
  override val sort: BoolSort = BoolSort

  init {
    require(terms.size > 1) {
      "Integer comparison needs at least 2 terms but ${terms.size} were provided"
    }
  }

  override fun toString(): String = symbol
}

object IntGreaterDecl :
    FunctionDeclChainable<IntSort>(">", emptySet(), IntSort, IntSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<IntSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = IntGreater(varargs)
}

class Divisible(val n: Int, val inner: Expression<IntSort>) : Expression<BoolSort>() {
  override val symbol: String = "((_ divisible $n) $inner)"
  override val sort: BoolSort = BoolSort
}

object DivisibleDecl :
    FunctionDecl1<IntSort, BoolSort>(
        "divisible", emptySet(), IntSort, setOf(SymbolIndex("n")), emptySet(), BoolSort) {
  override fun buildExpression(
      param: Expression<IntSort>,
      bindings: Bindings
  ): Expression<BoolSort> = Divisible(bindings["n"].numeral, param)
}

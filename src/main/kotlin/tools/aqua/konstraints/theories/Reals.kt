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
import tools.aqua.konstraints.parser.ProtoSort
import tools.aqua.konstraints.parser.SortDecl
import tools.aqua.konstraints.smt.BoolSort
import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.smt.Sort

internal object RealsContext : TheoryContext {
  override val functions: HashSet<FunctionDecl<*>> =
      hashSetOf(
          RealNegDecl,
          RealSubDecl,
          RealAddDecl,
          RealMulDecl,
          RealDivDecl,
          RealLessEqDecl,
          RealLessDecl,
          RealGreaterEqDecl,
          RealGreaterDecl)

  override val sorts: Map<String, SortDecl<*>> = mapOf(Pair("Real", RealSortDecl))
}

object RealSort : Sort("Real")

internal object RealSortDecl : SortDecl<RealSort>("Real") {
  override fun getSort(sort: ProtoSort) = RealSort
}

class RealLiteral(val value: BigDecimal) : Expression<RealSort>() {
  override val symbol: String = value.toString()
  override val sort: RealSort = RealSort

  override fun toString(): String = symbol
}

class RealNeg(val inner: Expression<RealSort>) : Expression<RealSort>() {
  override val symbol: String = "(- $inner)"
  override val sort: RealSort = RealSort

  override fun toString(): String = symbol
}

object RealNegDecl :
    FunctionDecl1<RealSort, RealSort>("-", emptySet(), RealSort, emptySet(), emptySet(), RealSort) {
  override fun buildExpression(
      param: Expression<RealSort>,
      bindings: Bindings
  ): Expression<RealSort> = RealNeg(param)
}

class RealSub(val terms: List<Expression<RealSort>>) : Expression<RealSort>() {
  override val symbol: String = "(- ${terms.joinToString(separator = " ")})"
  override val sort: RealSort = RealSort

  init {
    require(terms.size > 1) {
      "Integer subtraction needs at least 2 terms but ${terms.size} were provided"
    }
  }

  override fun toString(): String = symbol
}

object RealSubDecl :
    FunctionDeclLeftAssociative<RealSort, RealSort, RealSort>(
        "-", emptySet(), RealSort, RealSort, emptySet(), emptySet(), RealSort) {
  override fun buildExpression(
      param1: Expression<RealSort>,
      param2: Expression<RealSort>,
      varargs: List<Expression<RealSort>>,
      bindings: Bindings
  ): Expression<RealSort> = RealSub(listOf(param1, param2) + varargs)
}

class RealAdd(val terms: List<Expression<RealSort>>) : Expression<RealSort>() {
  override val symbol: String = "(+ ${terms.joinToString(separator = " ")})"
  override val sort: RealSort = RealSort

  init {
    require(terms.size > 1) {
      "Integer addition needs at least 2 terms but ${terms.size} were provided"
    }
  }

  override fun toString(): String = symbol
}

object RealAddDecl :
    FunctionDeclLeftAssociative<RealSort, RealSort, RealSort>(
        "-", emptySet(), RealSort, RealSort, emptySet(), emptySet(), RealSort) {
  override fun buildExpression(
      param1: Expression<RealSort>,
      param2: Expression<RealSort>,
      varargs: List<Expression<RealSort>>,
      bindings: Bindings
  ): Expression<RealSort> = RealAdd(listOf(param1, param2) + varargs)
}

class RealMul(val factors: List<Expression<RealSort>>) : Expression<RealSort>() {
  override val symbol: String = "(* ${factors.joinToString(separator = " ")})"
  override val sort: RealSort = RealSort

  init {
    require(factors.size > 1) {
      "Integer multiplication needs at least 2 factors but ${factors.size} were provided"
    }
  }

  override fun toString(): String = symbol
}

object RealMulDecl :
    FunctionDeclLeftAssociative<RealSort, RealSort, RealSort>(
        "-", emptySet(), RealSort, RealSort, emptySet(), emptySet(), RealSort) {
  override fun buildExpression(
      param1: Expression<RealSort>,
      param2: Expression<RealSort>,
      varargs: List<Expression<RealSort>>,
      bindings: Bindings
  ): Expression<RealSort> = RealMul(listOf(param1, param2) + varargs)
}

class RealDiv(val terms: List<Expression<RealSort>>) : Expression<RealSort>() {
  override val symbol: String = "(/ ${terms.joinToString(separator = " ")})"
  override val sort: RealSort = RealSort

  init {
    require(terms.size > 1) {
      "Integer division needs at least 2 terms but ${terms.size} were provided"
    }
  }

  override fun toString(): String = symbol
}

object RealDivDecl :
    FunctionDeclLeftAssociative<RealSort, RealSort, RealSort>(
        "-", emptySet(), RealSort, RealSort, emptySet(), emptySet(), RealSort) {
  override fun buildExpression(
      param1: Expression<RealSort>,
      param2: Expression<RealSort>,
      varargs: List<Expression<RealSort>>,
      bindings: Bindings
  ): Expression<RealSort> = RealDiv(listOf(param1, param2) + varargs)
}

class RealLessEq(val terms: List<Expression<RealSort>>) : Expression<BoolSort>() {
  override val symbol: String = "(<= ${terms.joinToString(separator = " ")})"
  override val sort: BoolSort = BoolSort

  init {
    require(terms.size > 1) {
      "Integer comparison needs at least 2 terms but ${terms.size} were provided"
    }
  }

  override fun toString(): String = symbol
}

object RealLessEqDecl :
    FunctionDeclChainable<RealSort>("<=", emptySet(), RealSort, RealSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<RealSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = RealLessEq(varargs)
}

class RealLess(val terms: List<Expression<RealSort>>) : Expression<BoolSort>() {
  override val symbol: String = "(< ${terms.joinToString(separator = " ")})"
  override val sort: BoolSort = BoolSort

  init {
    require(terms.size > 1) {
      "Integer comparison needs at least 2 terms but ${terms.size} were provided"
    }
  }

  override fun toString(): String = symbol
}

object RealLessDecl :
    FunctionDeclChainable<RealSort>("<", emptySet(), RealSort, RealSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<RealSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = RealLess(varargs)
}

class RealGreaterEq(val terms: List<Expression<RealSort>>) : Expression<BoolSort>() {
  override val symbol: String = "(>= ${terms.joinToString(separator = " ")})"
  override val sort: BoolSort = BoolSort

  init {
    require(terms.size > 1) {
      "Integer comparison needs at least 2 terms but ${terms.size} were provided"
    }
  }

  override fun toString(): String = symbol
}

object RealGreaterEqDecl :
    FunctionDeclChainable<RealSort>(">=", emptySet(), RealSort, RealSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<RealSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = RealGreaterEq(varargs)
}

class RealGreater(val terms: List<Expression<RealSort>>) : Expression<BoolSort>() {
  override val symbol: String = "(> ${terms.joinToString(separator = " ")})"
  override val sort: BoolSort = BoolSort

  init {
    require(terms.size > 1) {
      "Integer comparison needs at least 2 terms but ${terms.size} were provided"
    }
  }

  override fun toString(): String = symbol
}

object RealGreaterDecl :
    FunctionDeclChainable<RealSort>(">", emptySet(), RealSort, RealSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<RealSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = RealGreater(varargs)
}

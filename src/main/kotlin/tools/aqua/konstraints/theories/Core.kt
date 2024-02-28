/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2023 The Konstraints Authors
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
import tools.aqua.konstraints.smt.SortParameter

/*
 * This file implements the SMT core theory
 * http://smtlib.cs.uiowa.edu/theories-Core.shtml
 */

internal object CoreContext : TheoryContext {
  override val functions: HashSet<FunctionDecl<*>> =
      hashSetOf(
          FalseDecl, TrueDecl, NotDecl, AndDecl, OrDecl, XOrDecl, EqualsDecl, DistinctDecl, IteDecl)
  override val sorts = mapOf(Pair("Bool", BoolSortDecl))
}

internal object BoolSortDecl : SortDecl<BoolSort>("Bool") {
  override fun getSort(sort: ProtoSort): BoolSort {
    return BoolSort
  }
}

/** Object for SMT true */
object True : Expression<BoolSort>() {
  override val symbol: Symbol = "true".symbol()
  override val sort = BoolSort
}

object TrueDecl : FunctionDecl0<BoolSort>("true".symbol(), emptySet(), emptySet(), BoolSort) {
  override fun buildExpression(bindings: Bindings): Expression<BoolSort> = True
}

/** Object for SMT false */
object False : Expression<BoolSort>() {
  override val symbol: Symbol = "false".symbol()
  override val sort = BoolSort
}

object FalseDecl : FunctionDecl0<BoolSort>("false".symbol(), emptySet(), emptySet(), BoolSort) {
  override fun buildExpression(bindings: Bindings): Expression<BoolSort> = False
}

/**
 * Implements not according to Core theory (not Bool Bool)
 *
 * @param inner [Expression] of [BoolSort] to be negated
 */
class Not(val inner: Expression<BoolSort>) : Expression<BoolSort>() {
  override val sort: BoolSort = BoolSort
  override val symbol: Symbol = "not".symbol()

  override fun toString(): String = "(not $inner)"
}

/** FunctionDecl Object for Not */
object NotDecl :
    FunctionDecl1<BoolSort, BoolSort>(
        "not".symbol(), emptySet(), BoolSort, emptySet(), emptySet(), BoolSort) {
  override fun buildExpression(
      param: Expression<BoolSort>,
      bindings: Bindings
  ): Expression<BoolSort> = Not(param)
}

/**
 * Implements implication according to Core theory (=> Bool Bool Bool :right-assoc)
 *
 * @param statements multiple [Expression] of [BoolSort] to be checked in implies statement
 */
class Implies(val statements: List<Expression<BoolSort>>) : Expression<BoolSort>() {
  constructor(vararg statements: Expression<BoolSort>) : this(statements.toList())

  override val sort: BoolSort = BoolSort
  override val symbol: Symbol = "=>".symbol()

  override fun toString(): String = "(=> ${statements.joinToString(" ")})"
}

object ImpliesDecl :
    FunctionDeclRightAssociative<BoolSort, BoolSort, BoolSort>(
        "=>".symbol(), emptySet(), BoolSort, BoolSort, emptySet(), emptySet(), BoolSort) {
  override fun buildExpression(
      param1: Expression<BoolSort>,
      param2: Expression<BoolSort>,
      varargs: List<Expression<BoolSort>>,
      bindings: Bindings
  ) = Implies(listOf(param1, param2).plus(varargs))
}

/**
 * Implements and according to Core theory (and Bool Bool Bool :left-assoc)
 *
 * @param conjuncts multiple [Expression] of [BoolSort] to be joined in and statement
 */
class And(val conjuncts: List<Expression<BoolSort>>) : Expression<BoolSort>() {
  constructor(vararg conjuncts: Expression<BoolSort>) : this(conjuncts.toList())

  override val sort: BoolSort = BoolSort
  override val symbol: Symbol = "and".symbol()

  override fun toString() = "(and ${conjuncts.joinToString(" ")})"
}

object AndDecl :
    FunctionDeclLeftAssociative<BoolSort, BoolSort, BoolSort>(
        "and".symbol(), emptySet(), BoolSort, BoolSort, emptySet(), emptySet(), BoolSort) {
  override fun buildExpression(
      param1: Expression<BoolSort>,
      param2: Expression<BoolSort>,
      varargs: List<Expression<BoolSort>>,
      bindings: Bindings
  ) = And(listOf(param1, param2).plus(varargs))
}

/**
 * Implements or according to Core theory (or Bool Bool Bool :left-assoc)
 *
 * @param disjuncts multiple [Expression] of [BoolSort] to be joined in or statement
 */
class Or(val disjuncts: List<Expression<BoolSort>>) : Expression<BoolSort>() {
  constructor(vararg disjuncts: Expression<BoolSort>) : this(disjuncts.toList())

  override val sort: BoolSort = BoolSort
  override val symbol: Symbol = "or".symbol()

  override fun toString(): String = "(or ${disjuncts.joinToString(" ")})"
}

object OrDecl :
    FunctionDeclLeftAssociative<BoolSort, BoolSort, BoolSort>(
        "or".symbol(), emptySet(), BoolSort, BoolSort, emptySet(), emptySet(), BoolSort) {
  override fun buildExpression(
      param1: Expression<BoolSort>,
      param2: Expression<BoolSort>,
      varargs: List<Expression<BoolSort>>,
      bindings: Bindings
  ) = Or(listOf(param1, param2).plus(varargs))
}

/**
 * Implements xor according to Core theory (xor Bool Bool Bool :left-assoc)
 *
 * @param disjuncts multiple [Expression] of [BoolSort] to be joined in xor statement
 */
class XOr(val disjuncts: List<Expression<BoolSort>>) : Expression<BoolSort>() {
  constructor(vararg disjuncts: Expression<BoolSort>) : this(disjuncts.toList())

  override val sort: BoolSort = BoolSort
  override val symbol: Symbol = "xor".symbol()

  override fun toString(): String = "(xor ${disjuncts.joinToString(" ")})"
}

object XOrDecl :
    FunctionDeclLeftAssociative<BoolSort, BoolSort, BoolSort>(
        "xor".symbol(), emptySet(), BoolSort, BoolSort, emptySet(), emptySet(), BoolSort) {
  override fun buildExpression(
      param1: Expression<BoolSort>,
      param2: Expression<BoolSort>,
      varargs: List<Expression<BoolSort>>,
      bindings: Bindings
  ) = XOr(listOf(param1, param2).plus(varargs))
}

/**
 * Implements equals according to Core theory (par (A) (= A A Bool :chainable))
 *
 * @param statements multiple [Expression] of [BoolSort] to be checked in equals statement
 */
class Equals(val statements: List<Expression<*>>) : Expression<BoolSort>() {
  constructor(vararg statements: Expression<*>) : this(statements.toList())

  override val sort: BoolSort = BoolSort

  /** The symbol uses the :chainable short form (= A B C) is short for (and (= A B) (= B C)) */
  override val symbol: Symbol = "=".symbol()

  override fun toString(): String = "(= ${statements.joinToString(" ")})"
}

object EqualsDecl :
    FunctionDeclChainable<Sort>(
        "=".symbol(),
        setOf(SortParameter("A")),
        SortParameter("A"),
        SortParameter("A"),
        emptySet(),
        emptySet()) {

  override fun buildExpression(
      varargs: List<Expression<Sort>>,
      bindings: Bindings
  ): Expression<BoolSort> = Equals(varargs)
}

/**
 * Implements distinct according to Core theory (par (A) (distinct A A Bool :pairwise))
 *
 * @param statements multiple [Expression] of [BoolSort] to be checked in distinct statement
 */
class Distinct(val statements: List<Expression<*>>) : Expression<BoolSort>() {
  constructor(vararg statements: Expression<BoolSort>) : this(statements.toList())

  override val sort: BoolSort = BoolSort

  /**
   * The symbol uses the :pairwise short form (distinct A B C) is short for (and (distinct A B)
   * (distinct A C) (distinct B C))
   */
  override val symbol: Symbol = "distinct".symbol()

  override fun toString(): String = "(distinct ${statements.joinToString(" ")})"
}

object DistinctDecl :
    FunctionDeclPairwise<Sort>(
        "distinct".symbol(),
        setOf(SortParameter("A")),
        SortParameter("A"),
        SortParameter("A"),
        emptySet(),
        emptySet()) {

  override fun buildExpression(
      args: List<Expression<*>>,
      functionIndices: Set<NumeralIndex>
  ): Expression<BoolSort> {
    val bindings = signature.bindParameters(args.map { it.sort }, functionIndices)

    return buildExpression(args as List<Expression<Sort>>, bindings)
  }

  override fun buildExpression(
      varargs: List<Expression<Sort>>,
      bindings: Bindings
  ): Expression<BoolSort> = Distinct(varargs)
}

/**
 * Implements ite according to Core theory (par (A) (ite Bool A A A))
 *
 * @param statement indicates whether [then] or [els] should be returned
 * @param then value to be returned if [statement] is true
 * @param els value to be returned if [statement] is false
 */
class Ite(val statement: Expression<BoolSort>, val then: Expression<*>, val els: Expression<*>) :
    Expression<Sort>() {
  override val sort: BoolSort = BoolSort
  override val symbol: Symbol = "ite".symbol()

  override fun toString(): String = "(ite $statement $then $els)"
}

object IteDecl :
    FunctionDecl3<BoolSort, Sort, Sort, Sort>(
        "ite".symbol(),
        setOf(SortParameter("A")),
        BoolSort,
        SortParameter("A"),
        SortParameter("A"),
        emptySet(),
        emptySet(),
        SortParameter("A")) {
  override fun buildExpression(
      param1: Expression<BoolSort>,
      param2: Expression<Sort>,
      param3: Expression<Sort>,
      bindings: Bindings
  ): Expression<Sort> = Ite(param1, param2, param3)
}

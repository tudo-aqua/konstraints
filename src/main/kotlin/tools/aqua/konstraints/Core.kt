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

package tools.aqua.konstraints

import tools.aqua.konstraints.parser.*

/*
 * This file implements the SMT core theory
 * http://smtlib.cs.uiowa.edu/theories-Core.shtml
 */

// TODO implement casting for none homogeneous lists
@Suppress("UNCHECKED_CAST")
inline fun <reified T : Any> List<*>.checkedCast(): List<T> =
    if (all { it is T }) this as List<T> else throw TypeCastException("")

object CoreContext : TheoryContext {
  override val functions: HashSet<FunctionDecl<*>> = hashSetOf(NotDecl, AndDecl, OrDecl, XOrDecl)
  override val sorts = mapOf(Pair("Bool", BoolSortDecl))
}

object BoolSortDecl : SortDecl<BoolSort>("Bool") {
  override fun getSort(sort: ProtoSort): BoolSort {
    return BoolSort
  }
}

/** Object for SMT true */
object True : Expression<BoolSort>() {
  override val symbol = "true"
  override val sort = BoolSort
}

/** Object for SMT false */
object False : Expression<BoolSort>() {
  override val symbol = "false"
  override val sort = BoolSort
}

/**
 * Implements not according to Core theory (not Bool Bool)
 *
 * @param inner [Expression] of [BoolSort] to be negated
 */
class Not(val inner: Expression<BoolSort>) : Expression<BoolSort>() {
  override val sort: BoolSort = BoolSort
  override val symbol = "(not $inner)"

  override fun toString(): String = symbol
}

/** FunctionDecl Object for Not */
object NotDecl : FunctionDecl<BoolSort>("not", listOf(BoolSort), BoolSort) {
  override fun getExpression(args: List<Expression<*>>): Expression<BoolSort> {
    // TODO implement sorting exception
    require(args.size == 1) { "Not only accepts 1 argument but ${args.size} were provided" }
    require(args[0].sort == BoolSort) {
      "Not only accepts arguments of Sort BoolSort but ${args[0].sort} was provided"
    }

    @Suppress("UNCHECKED_CAST") val inner = args[0] as Expression<BoolSort>

    return Not(inner)
  }
}

/**
 * Implements implication according to Core theory (=> Bool Bool Bool :right-assoc)
 *
 * @param statements multiple [Expression] of [BoolSort] to be checked in implies statement
 */
class Implies(val statements: List<Expression<BoolSort>>) : Expression<BoolSort>() {
  constructor(vararg statements: Expression<BoolSort>) : this(statements.toList())

  override val sort: BoolSort = BoolSort
  override val symbol = "(=> ${statements.joinToString(" ")})"

  override fun toString(): String = symbol
}

/**
 * Implements and according to Core theory (and Bool Bool Bool :left-assoc)
 *
 * @param conjuncts multiple [Expression] of [BoolSort] to be joined in and statement
 */
class And(val conjuncts: List<Expression<BoolSort>>) : Expression<BoolSort>() {
  constructor(vararg conjuncts: Expression<BoolSort>) : this(conjuncts.toList())

  override val sort: BoolSort = BoolSort
  override val symbol = "(and ${conjuncts.joinToString(" ")})"

  override fun toString() = symbol
}

// TODO handle vararg parameters
object AndDecl : FunctionDecl<BoolSort>("and", listOf(BoolSort, BoolSort), BoolSort) {
  override fun getExpression(args: List<Expression<*>>): Expression<BoolSort> {
    require(args.size >= 2) {
      "And accepts at least 2 arguments but ${args.size} have been provided"
    }
    require(args.all { it.sort == BoolSort }) { "And only accepts arguments of Sort BoolSort" }

    @Suppress("UNCHECKED_CAST") return And(args as List<Expression<BoolSort>>)
  }

  override fun checkRequirements(args: List<Expression<*>>) {
    require(args.size >= 2)

    require(args.all { it.sort == BoolSort })
  }
}

/**
 * Implements or according to Core theory (or Bool Bool Bool :left-assoc)
 *
 * @param disjuncts multiple [Expression] of [BoolSort] to be joined in or statement
 */
class Or(val disjuncts: List<Expression<BoolSort>>) : Expression<BoolSort>() {
  constructor(vararg disjuncts: Expression<BoolSort>) : this(disjuncts.toList())

  override val sort: BoolSort = BoolSort
  override val symbol = "(or ${disjuncts.joinToString(" ")})"

  override fun toString(): String = symbol
}

object OrDecl : FunctionDecl<BoolSort>("or", listOf(BoolSort, BoolSort), BoolSort) {
  override fun getExpression(args: List<Expression<*>>): Expression<BoolSort> {
    require(args.size >= 2) {
      "Or accepts at least 2 arguments but ${args.size} have been provided"
    }
    require(args.all { it.sort == BoolSort }) { "Or only accepts arguments of Sort BoolSort" }

    @Suppress("UNCHECKED_CAST") return Or(args as List<Expression<BoolSort>>)
  }

  override fun checkRequirements(args: List<Expression<*>>) {
    require(args.size >= 2)

    require(args.all { it.sort == BoolSort })
  }
}

/**
 * Implements xor according to Core theory (xor Bool Bool Bool :left-assoc)
 *
 * @param disjuncts multiple [Expression] of [BoolSort] to be joined in xor statement
 */
class XOr(val disjuncts: List<Expression<BoolSort>>) : Expression<BoolSort>() {
  constructor(vararg disjuncts: Expression<BoolSort>) : this(disjuncts.toList())

  override val sort: BoolSort = BoolSort
  override val symbol = "(xor ${disjuncts.joinToString(" ")})"

  override fun toString(): String = symbol
}

object XOrDecl : FunctionDecl<BoolSort>("xor", listOf(BoolSort, BoolSort), BoolSort) {
  override fun getExpression(args: List<Expression<*>>): Expression<BoolSort> {
    require(args.size >= 2) {
      "Xor accepts at least 2 arguments but ${args.size} have been provided"
    }
    require(args.all { it.sort == BoolSort }) { "Xor only accepts arguments of Sort BoolSort" }

    @Suppress("UNCHECKED_CAST") return XOr(args as List<Expression<BoolSort>>)
  }

  override fun checkRequirements(args: List<Expression<*>>) {
    require(args.size >= 2)

    require(args.all { it.sort == BoolSort })
  }
}

/**
 * Implements equals according to Core theory (par (A) (= A A Bool :chainable))
 *
 * @param statements multiple [Expression] of [BoolSort] to be checked in equals statement
 */
class Equals(val statements: List<Expression<BoolSort>>) : Expression<BoolSort>() {
  constructor(vararg statements: Expression<BoolSort>) : this(statements.toList())

  override val sort: BoolSort = BoolSort

  /** The symbol uses the :chainable short form (= A B C) is short for (and (= A B) (= B C)) */
  override val symbol = "(= ${statements.joinToString(" ")})"

  override fun toString(): String = symbol
}

/**
 * Implements distinct according to Core theory (par (A) (distinct A A Bool :pairwise))
 *
 * @param statements multiple [Expression] of [BoolSort] to be checked in distinct statement
 */
class Distinct(val statements: List<Expression<BoolSort>>) : Expression<BoolSort>() {
  constructor(vararg statements: Expression<BoolSort>) : this(statements.toList())

  override val sort: BoolSort = BoolSort

  /**
   * The symbol uses the :pairwise short form (distinct A B C) is short for (and (distinct A B)
   * (distinct A C) (distinct B C))
   */
  override val symbol by lazy { "(distinct ${statements.joinToString(" ")})" }

  override fun toString(): String = symbol
}

/**
 * Implements ite according to Core theory (par (A) (ite Bool A A A))
 *
 * @param statement indicates whether [then] or [els] should be returned
 * @param then value to be returned if [statement] is true
 * @param els value to be returned if [statement] is false
 */
class Ite(
    val statement: Expression<BoolSort>,
    val then: Expression<BoolSort>,
    val els: Expression<BoolSort>
) : Expression<BoolSort>() {
  override val sort: BoolSort = BoolSort
  override val symbol = "(ite $statement $then $els)"

  override fun toString(): String = symbol
}

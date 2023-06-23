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

/** Definition of SMTLib Core theory according to http://smtlib.cs.uiowa.edu/theories-Core.shtml */

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

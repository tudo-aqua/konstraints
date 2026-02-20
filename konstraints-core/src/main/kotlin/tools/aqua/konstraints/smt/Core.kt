/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2026 The Konstraints Authors
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

import tools.aqua.konstraints.parser.*

/*
 * This file implements the SMT core theory
 * http://smtlib.cs.uiowa.edu/theories-Core.shtml
 */

/** Object for SMT true. */
object True : ConstantExpression<BoolSort>("true".toSymbol(), SMTBool) {
  override val theories = CORE_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> = this

    fun toBoolean() = true
}

/** Object for SMT false. */
object False : ConstantExpression<BoolSort>("false".toSymbol(), SMTBool) {
  override val theories = CORE_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> = this

    fun toBoolean() = false
}

fun Boolean.toSMTBool() = if (this) True else False

/**
 * Boolean negation.
 * - `(not Bool Bool)`
 * - `(not [inner])`.
 */
class Not(override val inner: Expression<BoolSort>) :
    UnaryExpression<BoolSort, BoolSort>("not".toSymbol(), SMTBool) {
  override val theories = CORE_MARKER_SET

  override fun toString(): String = "(not $inner)"

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      NotDecl.constructDynamic(children, emptyList())
}

/**
 * Boolean implication.
 * - `(=> Bool Bool Bool :right-assoc)`
 * - `(=> [statements])`.
 */
class Implies(val statements: List<Expression<BoolSort>>) :
    HomogenousExpression<BoolSort, BoolSort>("=>".toSymbol(), SMTBool) {
  override val theories = CORE_MARKER_SET

  constructor(vararg statements: Expression<BoolSort>) : this(statements.toList())

  override val children: List<Expression<BoolSort>> = statements

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      ImpliesDecl.constructDynamic(children, emptyList())
}

/**
 * Boolean conjunction.
 * - `(and Bool Bool Bool :left-assoc)`
 * - `(and [conjuncts])`.
 */
class And(val conjuncts: List<Expression<BoolSort>>) :
    HomogenousExpression<BoolSort, BoolSort>("and".toSymbol(), SMTBool) {
  override val theories = CORE_MARKER_SET

  constructor(vararg conjuncts: Expression<BoolSort>) : this(conjuncts.toList())

  override val children: List<Expression<BoolSort>> = conjuncts

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      AndDecl.constructDynamic(children, emptyList())
}

/**
 * Boolean disjunction.
 * - `(or Bool Bool Bool :left-assoc)`
 * - `(or [disjuncts])`.
 */
class Or(val disjuncts: List<Expression<BoolSort>>) :
    HomogenousExpression<BoolSort, BoolSort>("or".toSymbol(), SMTBool) {
  override val theories = CORE_MARKER_SET

  constructor(vararg disjuncts: Expression<BoolSort>) : this(disjuncts.toList())

  override val children: List<Expression<BoolSort>> = disjuncts

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      OrDecl.constructDynamic(children, emptyList())
}

/**
 * Boolean exclusive or.
 * - `(xor Bool Bool Bool :left-assoc)`
 * - `(xor [disjuncts])`.
 */
class XOr(val disjuncts: List<Expression<BoolSort>>) :
    HomogenousExpression<BoolSort, BoolSort>("xor".toSymbol(), SMTBool) {
  override val theories = CORE_MARKER_SET

  constructor(vararg disjuncts: Expression<BoolSort>) : this(disjuncts.toList())

  override val children: List<Expression<BoolSort>> = disjuncts

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      XOrDecl.constructDynamic(children, emptyList())
}

/**
 * Equality.
 * - `(par (A) (= A A :chainable))`
 * - `(= [statements])`
 */
class Equals<T : Sort>(val statements: List<Expression<T>>) :
    HomogenousExpression<BoolSort, Sort>("=".toSymbol(), SMTBool) {
  override val theories = CORE_MARKER_SET

  constructor(vararg statements: Expression<T>) : this(statements.toList())

  override val children: List<Expression<T>> = statements

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      EqualsDecl.constructDynamic(children, emptyList())
}

/**
 * Distinct.
 * - `(par (A) (distinct A A :pairwise))`
 * - `(distinct [statements])`
 */
class Distinct<T : Sort>(val statements: List<Expression<T>>) :
    HomogenousExpression<BoolSort, T>("distinct".toSymbol(), SMTBool) {
  override val theories = CORE_MARKER_SET

  constructor(vararg statements: Expression<T>) : this(statements.toList())

  override val children: List<Expression<T>> = statements

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      DistinctDecl.constructDynamic(children, emptyList())
}

/**
 * If-then-else.
 * - `(par (A) (ite Bool A A A))`
 * - `(ite [condition] [then] [otherwise])`
 */
class Ite<out T : Sort>(
    val condition: Expression<BoolSort>,
    val then: Expression<T>,
    val otherwise: Expression<T>,
) : Expression<T>() {
  init {
    require(then.sort == otherwise.sort)
  }

  override val sort: T = then.sort
  override val theories = CORE_MARKER_SET
  override val func = null

  override fun copy(children: List<Expression<*>>): Expression<T> =
      IteDecl.constructDynamic(children, emptyList()) as Expression<T>

  override val name: Symbol = "ite".toSymbol()

  override val children: List<Expression<*>> = listOf(condition, then, otherwise)

  override fun toString(): String = "(ite $condition $then $otherwise)"
}

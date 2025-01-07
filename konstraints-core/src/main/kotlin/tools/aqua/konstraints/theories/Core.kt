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

package tools.aqua.konstraints.theories

import tools.aqua.konstraints.parser.*
import tools.aqua.konstraints.smt.*

/*
 * This file implements the SMT core theory
 * http://smtlib.cs.uiowa.edu/theories-Core.shtml
 */

/** Object for SMT true */
object True : ConstantExpression<BoolSort>("true".symbol(), BoolSort) {
  override val theories = setOf(Theories.CORE)

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> = this
}

/** Object for SMT false */
object False : ConstantExpression<BoolSort>("false".symbol(), BoolSort) {
  override val theories = setOf(Theories.CORE)

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> = this
}

/**
 * Implements not according to Core theory (not Bool Bool)
 *
 * @param inner [Expression] of [BoolSort] to be negated
 */
class Not(override val inner: Expression<BoolSort>) :
    UnaryExpression<BoolSort, BoolSort>("not".symbol(), BoolSort) {
  companion object {
    private val theoriesSet = setOf(Theories.CORE)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override fun toString(): String = "(not $inner)"

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      NotDecl.buildExpression(children, emptyList())
}

/**
 * Implements implication according to Core theory (=> Bool Bool Bool :right-assoc)
 *
 * @param statements multiple [Expression] of [BoolSort] to be checked in implies statement
 */
class Implies(val statements: List<Expression<BoolSort>>) :
    HomogenousExpression<BoolSort, BoolSort>("=>".symbol(), BoolSort) {
  companion object {
    private val theoriesSet = setOf(Theories.CORE)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  constructor(vararg statements: Expression<BoolSort>) : this(statements.toList())

  override val children: List<Expression<BoolSort>> = statements

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      ImpliesDecl.buildExpression(children, emptyList())
}

/**
 * Implements and according to Core theory (and Bool Bool Bool :left-assoc)
 *
 * @param conjuncts multiple [Expression] of [BoolSort] to be joined in and statement
 */
class And(val conjuncts: List<Expression<BoolSort>>) :
    HomogenousExpression<BoolSort, BoolSort>("and".symbol(), BoolSort) {
  companion object {
    private val theoriesSet = setOf(Theories.CORE)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  constructor(vararg conjuncts: Expression<BoolSort>) : this(conjuncts.toList())

  override val children: List<Expression<BoolSort>> = conjuncts

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      AndDecl.buildExpression(children, emptyList())
}

/**
 * Implements or according to Core theory (or Bool Bool Bool :left-assoc)
 *
 * @param disjuncts multiple [Expression] of [BoolSort] to be joined in or statement
 */
class Or(val disjuncts: List<Expression<BoolSort>>) :
    HomogenousExpression<BoolSort, BoolSort>("or".symbol(), BoolSort) {
  companion object {
    private val theoriesSet = setOf(Theories.CORE)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  constructor(vararg disjuncts: Expression<BoolSort>) : this(disjuncts.toList())

  override val children: List<Expression<BoolSort>> = disjuncts

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      OrDecl.buildExpression(children, emptyList())
}

/**
 * Implements xor according to Core theory (xor Bool Bool Bool :left-assoc)
 *
 * @param disjuncts multiple [Expression] of [BoolSort] to be joined in xor statement
 */
class XOr(val disjuncts: List<Expression<BoolSort>>) :
    HomogenousExpression<BoolSort, BoolSort>("xor".symbol(), BoolSort) {
  companion object {
    private val theoriesSet = setOf(Theories.CORE)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  constructor(vararg disjuncts: Expression<BoolSort>) : this(disjuncts.toList())

  override val children: List<Expression<BoolSort>> = disjuncts

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      XOrDecl.buildExpression(children, emptyList())
}

/**
 * Implements equals according to Core theory (par (A) (= A A Bool :chainable))
 *
 * @param statements multiple [Expression] of [BoolSort] to be checked in equals statement
 */
class Equals<T : Sort>(val statements: List<Expression<T>>) :
    HomogenousExpression<BoolSort, Sort>("=".symbol(), BoolSort) {
  companion object {
    private val theoriesSet = setOf(Theories.CORE)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  constructor(vararg statements: Expression<T>) : this(statements.toList())

  override val children: List<Expression<T>> = statements

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      EqualsDecl.buildExpression(children, emptyList())
}

/**
 * Implements distinct according to Core theory (par (A) (distinct A A Bool :pairwise))
 *
 * @param statements multiple [Expression] of [BoolSort] to be checked in distinct statement
 */
class Distinct(val statements: List<Expression<*>>) :
    HomogenousExpression<BoolSort, Sort>("distinct".symbol(), BoolSort) {
  companion object {
    private val theoriesSet = setOf(Theories.CORE)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  constructor(vararg statements: Expression<*>) : this(statements.toList())

  override val children: List<Expression<Sort>> = statements as List<Expression<Sort>>

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      DistinctDecl.buildExpression(children, emptyList())
}

/** Bool sort */
object BoolSort : Sort("Bool") {
  override val theories = emptySet<Theories>()
}

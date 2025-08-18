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

package tools.aqua.konstraints.smt

import tools.aqua.konstraints.parser.*

/*
 * This file implements the SMT core theory
 * http://smtlib.cs.uiowa.edu/theories-Core.shtml
 */

/** Object for SMT true. */
object True : ConstantExpression<BoolSort>("true".toSymbolWithQuotes(), Bool) {
  override val theories = CORE_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> = this
}

/** Object for SMT false. */
object False : ConstantExpression<BoolSort>("false".toSymbolWithQuotes(), Bool) {
  override val theories = CORE_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> = this
}

/** (not [inner]). */
class Not(override val inner: Expression<BoolSort>) :
    UnaryExpression<BoolSort, BoolSort>("not".toSymbolWithQuotes(), Bool) {
  override val theories = CORE_MARKER_SET

  override fun toString(): String = "(not $inner)"

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      NotDecl.constructDynamic(children, emptyList())
}

/** (=> [statements] :right-assoc). */
class Implies(val statements: List<Expression<BoolSort>>) :
    HomogenousExpression<BoolSort, BoolSort>("=>".toSymbolWithQuotes(), Bool) {
  override val theories = CORE_MARKER_SET

  constructor(vararg statements: Expression<BoolSort>) : this(statements.toList())

  override val children: List<Expression<BoolSort>> = statements

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      ImpliesDecl.constructDynamic(children, emptyList())
}

/** (and [conjuncts] :left-assoc). */
class And(val conjuncts: List<Expression<BoolSort>>) :
    HomogenousExpression<BoolSort, BoolSort>("and".toSymbolWithQuotes(), Bool) {
  override val theories = CORE_MARKER_SET

  constructor(vararg conjuncts: Expression<BoolSort>) : this(conjuncts.toList())

  override val children: List<Expression<BoolSort>> = conjuncts

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      AndDecl.constructDynamic(children, emptyList())
}

/** (or [disjuncts] :left-assoc). */
class Or(val disjuncts: List<Expression<BoolSort>>) :
    HomogenousExpression<BoolSort, BoolSort>("or".toSymbolWithQuotes(), Bool) {
  override val theories = CORE_MARKER_SET

  constructor(vararg disjuncts: Expression<BoolSort>) : this(disjuncts.toList())

  override val children: List<Expression<BoolSort>> = disjuncts

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      OrDecl.constructDynamic(children, emptyList())
}

/** (xor [disjuncts] :left-assoc). */
class XOr(val disjuncts: List<Expression<BoolSort>>) :
    HomogenousExpression<BoolSort, BoolSort>("xor".toSymbolWithQuotes(), Bool) {
  override val theories = CORE_MARKER_SET

  constructor(vararg disjuncts: Expression<BoolSort>) : this(disjuncts.toList())

  override val children: List<Expression<BoolSort>> = disjuncts

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      XOrDecl.constructDynamic(children, emptyList())
}

/** (par (A) (= [statements] :chainable)). */
class Equals<T : Sort>(val statements: List<Expression<T>>) :
    HomogenousExpression<BoolSort, Sort>("=".toSymbolWithQuotes(), Bool) {
  override val theories = CORE_MARKER_SET

  constructor(vararg statements: Expression<T>) : this(statements.toList())

  override val children: List<Expression<T>> = statements

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      EqualsDecl.constructDynamic(children, emptyList())
}

/** (par (A) (distinct [statements] :pairwise)). */
class Distinct<T : Sort>(val statements: List<Expression<T>>) :
    HomogenousExpression<BoolSort, T>("distinct".toSymbolWithQuotes(), Bool) {
  override val theories = CORE_MARKER_SET

  constructor(vararg statements: Expression<T>) : this(statements.toList())

  override val children: List<Expression<T>> = statements

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      DistinctDecl.constructDynamic(children, emptyList())
}

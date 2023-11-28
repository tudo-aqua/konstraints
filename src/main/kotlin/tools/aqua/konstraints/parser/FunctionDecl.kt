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

package tools.aqua.konstraints.parser

import tools.aqua.konstraints.*

enum class Associativity {
  LEFT_ASSOC,
  RIGHT_ASSOC,
  PAIRWISE,
  CHAINABLE,
  NONE
}

open class FunctionDecl<S : Sort>(
    val name: String,
    val parametricSorts: Set<Sort>,
    val params: List<Sort>,
    val indices: Set<SymbolIndex>,
    val sort: S,
    val associativity: Associativity
) {
  val signature = Signature(parametricSorts, indices, params, sort)

  open fun buildExpression(args: List<Expression<*>>): Expression<S> {
    bindParametersToWithExpressions(args)

    return NAryExpression(name, sort, args)
  }

  open fun bindParametersToWithExpressions(args: List<Expression<*>>) =
      when (associativity) {
        Associativity.LEFT_ASSOC -> {
          args.slice(2 ..< args.size).forEach { require(args[0].sort == it.sort) }
          signature.bindParameters(args.slice(0..1).map { it.sort })
        }
        Associativity.RIGHT_ASSOC -> {
          args.slice(2 ..< args.size).forEach { require(args[1].sort == it.sort) }
          signature.bindParameters(args.slice(0..1).map { it.sort })
        }
        Associativity.PAIRWISE -> {
          args.forEach { require(args[0].sort == it.sort) }
          signature.bindParameters(args.slice(0..1).map { it.sort })
        }
        Associativity.CHAINABLE -> {
          args.forEach { require(args[0].sort == it.sort) }
          signature.bindParameters(args.slice(0..1).map { it.sort })
        }
        Associativity.NONE -> signature.bindParameters(args.map { it.sort })
      }

  /** Returns true if the function accepts the arguments provided */
  fun acceptsExpressions(args: List<Expression<*>>): Boolean {
    try {
      bindParametersToWithExpressions(args)
    } catch (e: Exception) {
      return false
    }

    return true
  }

  fun bindParametersTo(args: List<Sort>) =
      when (associativity) {
        Associativity.LEFT_ASSOC -> {
          args.slice(2 ..< args.size).forEach { require(args[0] == it) }
          signature.bindParameters(args.slice(0..1))
        }
        Associativity.RIGHT_ASSOC -> {
          args.slice(2 ..< args.size).forEach { require(args[1] == it) }
          signature.bindParameters(args.slice(0..1))
        }
        Associativity.PAIRWISE -> {
          args.forEach { require(args[0] == it) }
          signature.bindTo(args.slice(0..1), sort)
        }
        Associativity.CHAINABLE -> {
          args.forEach { require(args[0] == it) }
          signature.bindTo(args.slice(0..1), sort)
        }
        Associativity.NONE -> signature.bindParameters(args)
      }

  fun accepts(args: List<Sort>): Boolean {
    try {
      bindParametersTo(args)
    } catch (e: Exception) {
      return false
    }

    return true
  }

  override fun equals(other: Any?): Boolean =
      when {
        this === other -> true
        other !is FunctionDecl<*> -> false
        else -> (name == other.name) && (params == other.params) && (sort == other.sort)
      }

  override fun hashCode(): Int = name.hashCode() * 961 + params.hashCode() * 31 + sort.hashCode()

  override fun toString() = "($name (${params.joinToString(" ")}) $sort)"
}

// TODO are indices necessary here (dont think so)
abstract class FunctionDecl0<S : Sort>(
    name: String,
    parametricSorts: Set<Sort>,
    indices: Set<SymbolIndex>,
    sort: S
) : FunctionDecl<S>(name, parametricSorts, emptyList(), indices, sort, Associativity.NONE) {

  override fun buildExpression(args: List<Expression<*>>): Expression<S> {
    require(args.isEmpty())

    return buildExpression()
  }

  abstract fun buildExpression(): Expression<S>
}

// TODO refactor sort into more meaningful name i.e. return
abstract class FunctionDecl1<P : Sort, S : Sort>(
    name: String,
    parametricSorts: Set<Sort>,
    param: P,
    indices: Set<SymbolIndex>,
    sort: S
) : FunctionDecl<S>(name, parametricSorts, listOf(param), indices, sort, Associativity.NONE) {

  override fun buildExpression(args: List<Expression<*>>): Expression<S> {
    require(args.size == 1)
    val bindings = bindParametersToWithExpressions(args)

    return buildExpression(args.single() as Expression<P>, bindings)
  }

  abstract fun buildExpression(param: Expression<P>, bindings: Bindings): Expression<S>
}

abstract class FunctionDecl2<P1 : Sort, P2 : Sort, S : Sort>(
    name: String,
    parametricSorts: Set<Sort>,
    param1: P1,
    param2: P2,
    indices: Set<SymbolIndex>,
    sort: S
) :
    FunctionDecl<S>(
        name, parametricSorts, listOf(param1, param2), indices, sort, Associativity.NONE) {
  override fun buildExpression(args: List<Expression<*>>): Expression<S> {
    require(args.size == 2)
    val bindings = bindParametersToWithExpressions(args)

    // TODO suppress unchecked cast warning
    return buildExpression(args[0] as Expression<P1>, args[1] as Expression<P2>, bindings)
  }

  abstract fun buildExpression(
      param1: Expression<P1>,
      param2: Expression<P2>,
      bindings: Bindings
  ): Expression<S>
}

abstract class FunctionDecl3<P1 : Sort, P2 : Sort, P3 : Sort, S : Sort>(
    name: String,
    parametricSorts: Set<Sort>,
    param1: P1,
    param2: P2,
    param3: P3,
    indices: Set<SymbolIndex>,
    sort: S
) :
    FunctionDecl<S>(
        name, parametricSorts, listOf(param1, param2, param3), indices, sort, Associativity.NONE) {
  override fun buildExpression(args: List<Expression<*>>): Expression<S> {
    require(args.size == 3)
    val bindings = bindParametersToWithExpressions(args)

    // TODO suppress unchecked cast warning
    return buildExpression(
        args[0] as Expression<P1>, args[1] as Expression<P2>, args[2] as Expression<P3>, bindings)
  }

  abstract fun buildExpression(
      param1: Expression<P1>,
      param2: Expression<P2>,
      param3: Expression<P3>,
      bindings: Bindings
  ): Expression<S>
}

abstract class FunctionDecl4<P1 : Sort, P2 : Sort, P3 : Sort, P4 : Sort, S : Sort>(
    name: String,
    parametricSorts: Set<Sort>,
    param1: P1,
    param2: P2,
    param3: P3,
    param4: P4,
    indices: Set<SymbolIndex>,
    sort: S
) :
    FunctionDecl<S>(
        name,
        parametricSorts,
        listOf(param1, param2, param3, param4),
        indices,
        sort,
        Associativity.NONE) {
  override fun buildExpression(args: List<Expression<*>>): Expression<S> {
    require(args.size == 4)
    val bindings = bindParametersToWithExpressions(args)

    // TODO suppress unchecked cast warning
    return buildExpression(
        args[0] as Expression<P1>,
        args[1] as Expression<P2>,
        args[2] as Expression<P3>,
        args[3] as Expression<P4>,
        bindings)
  }

  abstract fun buildExpression(
      param1: Expression<P1>,
      param2: Expression<P2>,
      param3: Expression<P3>,
      param4: Expression<P4>,
      bindings: Bindings
  ): Expression<S>
}

abstract class FunctionDeclLeftAssociative<P1 : Sort, P2 : Sort, S : Sort>(
    name: String,
    parametricSorts: Set<Sort>,
    param1: Sort,
    param2: Sort,
    indices: Set<SymbolIndex>,
    sort: S
) :
    FunctionDecl<S>(
        name, parametricSorts, listOf(param1, param2), indices, sort, Associativity.LEFT_ASSOC) {
  override fun buildExpression(args: List<Expression<*>>): Expression<S> {
    val bindings = bindParametersToWithExpressions(args)

    return buildExpression(
        args[0] as Expression<P1>,
        args[1] as Expression<P2>,
        args.slice(2 ..< args.size) as List<Expression<P1>>,
        bindings)
  }

  abstract fun buildExpression(
      param1: Expression<P1>,
      param2: Expression<P2>,
      varargs: List<Expression<P1>>,
      bindings: Bindings
  ): Expression<S>
}

abstract class FunctionDeclRightAssociative<P1 : Sort, P2 : Sort, S : Sort>(
    name: String,
    parametricSorts: Set<Sort>,
    param1: P1,
    param2: P2,
    indices: Set<SymbolIndex>,
    sort: S
) :
    FunctionDecl<S>(
        name, parametricSorts, listOf(param1, param2), indices, sort, Associativity.RIGHT_ASSOC) {
  override fun buildExpression(args: List<Expression<*>>): Expression<S> {
    val bindings = bindParametersToWithExpressions(args)

    return buildExpression(
        args[0] as Expression<P1>,
        args[1] as Expression<P2>,
        args.slice(2 ..< args.size) as List<Expression<P2>>,
        bindings)
  }

  abstract fun buildExpression(
      param1: Expression<P1>,
      param2: Expression<P2>,
      varargs: List<Expression<P2>>,
      bindings: Bindings
  ): Expression<S>
}

abstract class FunctionDeclChainable<P : Sort>(
    name: String,
    parametricSorts: Set<Sort>,
    param1: P,
    param2: P,
    indices: Set<SymbolIndex>,
) :
    FunctionDecl<BoolSort>(
        name, parametricSorts, listOf(param1, param2), indices, BoolSort, Associativity.CHAINABLE) {
  override fun buildExpression(args: List<Expression<*>>): Expression<BoolSort> {
    val bindings = bindParametersToWithExpressions(args)

    return buildExpression(args as List<Expression<P>>, bindings)
  }

  abstract fun buildExpression(
      varargs: List<Expression<P>>,
      bindings: Bindings
  ): Expression<BoolSort>
}

abstract class FunctionDeclPairwise<P : Sort>(
    name: String,
    parametricSorts: Set<Sort>,
    param1: P,
    param2: P,
    indices: Set<SymbolIndex>,
) :
    FunctionDecl<BoolSort>(
        name, parametricSorts, listOf(param1, param2), indices, BoolSort, Associativity.PAIRWISE) {
  override fun buildExpression(args: List<Expression<*>>): Expression<BoolSort> {
    val bindings = bindParametersToWithExpressions(args)

    return buildExpression(args as List<Expression<P>>, bindings)
  }

  abstract fun buildExpression(
      varargs: List<Expression<P>>,
      bindings: Bindings
  ): Expression<BoolSort>
}

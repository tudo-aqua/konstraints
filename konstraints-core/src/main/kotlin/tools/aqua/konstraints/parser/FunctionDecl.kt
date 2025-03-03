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

package tools.aqua.konstraints.parser

import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.theories.BoolSort

enum class Associativity {
  LEFT_ASSOC,
  RIGHT_ASSOC,
  PAIRWISE,
  CHAINABLE,
  NONE
}

/*internal*/ open class FunctionDecl<S : Sort>(
    override val symbol: Symbol,
    val parametricSorts: Set<Sort>,
    override val parameters: List<Sort>,
    val functionIndices: Set<SymbolIndex>,
    val paramIndices: Set<SymbolIndex>,
    override val sort: S,
    val associativity: Associativity,
    override val definition: FunctionDef<S>?
) : SMTFunction<S>() {

  override val name = symbol.toString()
  val signature = Signature(parametricSorts, functionIndices, paramIndices, parameters, sort)

  open fun buildExpression(
      args: List<Expression<*>>,
      functionIndices: List<NumeralIndex>
  ): Expression<S> {
    bindParametersToExpressions(args, functionIndices)

    return UserDeclaredExpression(symbol, sort, args, this)
  }

  fun bindParametersToExpressions(args: List<Expression<*>>, indices: List<NumeralIndex>) =
      bindParametersTo(args.map { it.sort }, indices)

  /** Returns true if the function accepts the arguments provided */
  fun acceptsExpressions(args: List<Expression<*>>, indices: List<NumeralIndex>): Boolean =
      accepts(args.map { it.sort }, indices)

  open fun bindParametersTo(args: List<Sort>, indices: List<NumeralIndex>) =
      when (associativity) {
        Associativity.LEFT_ASSOC -> {
          args.slice(2..<args.size).forEach { require(args[0] == it) }
          signature.bindParameters(args.slice(0..1), indices)
        }
        Associativity.RIGHT_ASSOC -> {
          args.slice(2..<args.size).forEach { require(args[1] == it) }
          signature.bindParameters(args.slice(0..1), indices)
        }
        Associativity.PAIRWISE -> {
          args.forEach { require(args[0] == it) }
          signature.bindTo(args.slice(0..1), indices, sort)
        }
        Associativity.CHAINABLE -> {
          args.forEach { require(args[0] == it) }
          signature.bindTo(args.slice(0..1), indices, sort)
        }
        Associativity.NONE -> signature.bindParameters(args, indices)
      }

  open fun accepts(args: List<Sort>, indices: List<NumeralIndex>): Boolean {
    try {
      bindParametersTo(args, indices)
    } catch (e: Exception) {
      return false
    }

    return true
  }

  override fun toString() = "($symbol (${parameters.joinToString(" ")}) $sort)"
}

internal class FunctionDefinition<S : Sort>(override val definition: FunctionDef<S>) :
    FunctionDecl<S>(
        definition.name,
        emptySet(),
        definition.parameters.map { it.sort },
        emptySet(),
        emptySet(),
        definition.sort,
        Associativity.NONE,
        definition) {

  override fun buildExpression(
      args: List<Expression<*>>,
      functionIndices: List<NumeralIndex>
  ): Expression<S> = UserDefinedExpression(symbol, sort, args, definition, this)
}

/*internal*/ abstract class FunctionDecl0<S : Sort>(
    name: Symbol,
    parametricSorts: Set<Sort>,
    functionIndices: Set<SymbolIndex>,
    sort: S
) :
    FunctionDecl<S>(
        name,
        parametricSorts,
        emptyList(),
        functionIndices,
        emptySet(),
        sort,
        Associativity.NONE,
        null) {

  override fun buildExpression(
      args: List<Expression<*>>,
      functionIndices: List<NumeralIndex>
  ): Expression<S> {
    require(args.isEmpty())
    val bindings = bindParametersToExpressions(args, functionIndices)

    return buildExpression(bindings)
  }

  abstract fun buildExpression(bindings: Bindings): Expression<S>
}

// TODO refactor sort into more meaningful name i.e. return
internal abstract class FunctionDecl1<P : Sort, S : Sort>(
    name: Symbol,
    parametricSorts: Set<Sort>,
    param: P,
    functionIndices: Set<SymbolIndex>,
    indices: Set<SymbolIndex>,
    sort: S
) :
    FunctionDecl<S>(
        name,
        parametricSorts,
        listOf(param),
        functionIndices,
        indices,
        sort,
        Associativity.NONE,
        null) {

  override fun buildExpression(
      args: List<Expression<*>>,
      functionIndices: List<NumeralIndex>
  ): Expression<S> {
    require(args.size == 1)
    val bindings = bindParametersToExpressions(args, functionIndices)

    return buildExpression(args.single() as Expression<P>, bindings)
  }

  abstract fun buildExpression(param: Expression<P>, bindings: Bindings): Expression<S>
}

internal abstract class FunctionDecl2<P1 : Sort, P2 : Sort, S : Sort>(
    name: Symbol,
    parametricSorts: Set<Sort>,
    param1: P1,
    param2: P2,
    functionIndices: Set<SymbolIndex>,
    indices: Set<SymbolIndex>,
    sort: S
) :
    FunctionDecl<S>(
        name,
        parametricSorts,
        listOf(param1, param2),
        functionIndices,
        indices,
        sort,
        Associativity.NONE,
        null) {
  override fun buildExpression(
      args: List<Expression<*>>,
      functionIndices: List<NumeralIndex>
  ): Expression<S> {
    require(args.size == 2)
    val bindings = bindParametersToExpressions(args, functionIndices)

    // TODO suppress unchecked cast warning
    return buildExpression(args[0] as Expression<P1>, args[1] as Expression<P2>, bindings)
  }

  abstract fun buildExpression(
      param1: Expression<P1>,
      param2: Expression<P2>,
      bindings: Bindings
  ): Expression<S>
}

internal abstract class FunctionDecl3<P1 : Sort, P2 : Sort, P3 : Sort, S : Sort>(
    name: Symbol,
    parametricSorts: Set<Sort>,
    param1: P1,
    param2: P2,
    param3: P3,
    functionIndices: Set<SymbolIndex>,
    indices: Set<SymbolIndex>,
    sort: S
) :
    FunctionDecl<S>(
        name,
        parametricSorts,
        listOf(param1, param2, param3),
        functionIndices,
        indices,
        sort,
        Associativity.NONE,
        null) {
  override fun buildExpression(
      args: List<Expression<*>>,
      functionIndices: List<NumeralIndex>
  ): Expression<S> {
    require(args.size == 3)
    val bindings = bindParametersToExpressions(args, functionIndices)

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

internal abstract class FunctionDecl4<P1 : Sort, P2 : Sort, P3 : Sort, P4 : Sort, S : Sort>(
    name: Symbol,
    parametricSorts: Set<Sort>,
    param1: P1,
    param2: P2,
    param3: P3,
    param4: P4,
    functionIndices: Set<SymbolIndex>,
    indices: Set<SymbolIndex>,
    sort: S
) :
    FunctionDecl<S>(
        name,
        parametricSorts,
        listOf(param1, param2, param3, param4),
        functionIndices,
        indices,
        sort,
        Associativity.NONE,
        null) {
  override fun buildExpression(
      args: List<Expression<*>>,
      functionIndices: List<NumeralIndex>
  ): Expression<S> {
    require(args.size == 4) { "$symbol expected 4 arguments but got ${args.size}: $args" }
    val bindings = bindParametersToExpressions(args, functionIndices)

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

internal abstract class FunctionDeclLeftAssociative<P1 : Sort, P2 : Sort, S : Sort>(
    name: Symbol,
    parametricSorts: Set<Sort>,
    param1: Sort,
    param2: Sort,
    functionIndices: Set<SymbolIndex>,
    indices: Set<SymbolIndex>,
    sort: S
) :
    FunctionDecl<S>(
        name,
        parametricSorts,
        listOf(param1, param2),
        functionIndices,
        indices,
        sort,
        Associativity.LEFT_ASSOC,
        null) {
  override fun buildExpression(
      args: List<Expression<*>>,
      functionIndices: List<NumeralIndex>
  ): Expression<S> {
    val bindings = bindParametersToExpressions(args, functionIndices)

    return buildExpression(
        args[0] as Expression<P1>,
        args[1] as Expression<P2>,
        args.slice(2..<args.size) as List<Expression<P1>>,
        bindings)
  }

  abstract fun buildExpression(
      param1: Expression<P1>,
      param2: Expression<P2>,
      varargs: List<Expression<P1>>,
      bindings: Bindings
  ): Expression<S>
}

internal abstract class FunctionDeclRightAssociative<P1 : Sort, P2 : Sort, S : Sort>(
    name: Symbol,
    parametricSorts: Set<Sort>,
    param1: P1,
    param2: P2,
    functionIndices: Set<SymbolIndex>,
    indices: Set<SymbolIndex>,
    sort: S
) :
    FunctionDecl<S>(
        name,
        parametricSorts,
        listOf(param1, param2),
        functionIndices,
        indices,
        sort,
        Associativity.RIGHT_ASSOC,
        null) {
  override fun buildExpression(
      args: List<Expression<*>>,
      functionIndices: List<NumeralIndex>
  ): Expression<S> {
    val bindings = bindParametersToExpressions(args, functionIndices)

    return buildExpression(
        args[0] as Expression<P1>,
        args[1] as Expression<P2>,
        args.slice(2..<args.size) as List<Expression<P2>>,
        bindings)
  }

  abstract fun buildExpression(
      param1: Expression<P1>,
      param2: Expression<P2>,
      varargs: List<Expression<P2>>,
      bindings: Bindings
  ): Expression<S>
}

internal abstract class FunctionDeclChainable<P : Sort>(
    name: Symbol,
    parametricSorts: Set<Sort>,
    param1: P,
    param2: P,
    functionIndices: Set<SymbolIndex>,
    indices: Set<SymbolIndex>
) :
    FunctionDecl<BoolSort>(
        name,
        parametricSorts,
        listOf(param1, param2),
        functionIndices,
        indices,
        BoolSort,
        Associativity.CHAINABLE,
        null) {
  override fun buildExpression(
      args: List<Expression<*>>,
      functionIndices: List<NumeralIndex>
  ): Expression<BoolSort> {
    val bindings = bindParametersToExpressions(args, functionIndices)

    return buildExpression(args as List<Expression<P>>, bindings)
  }

  abstract fun buildExpression(
      varargs: List<Expression<P>>,
      bindings: Bindings
  ): Expression<BoolSort>
}

internal abstract class FunctionDeclPairwise<P : Sort>(
    name: Symbol,
    parametricSorts: Set<Sort>,
    param1: P,
    param2: P,
    functionIndices: Set<SymbolIndex>,
    indices: Set<SymbolIndex>
) :
    FunctionDecl<BoolSort>(
        name,
        parametricSorts,
        listOf(param1, param2),
        functionIndices,
        indices,
        BoolSort,
        Associativity.PAIRWISE,
        null) {
  override fun buildExpression(
      args: List<Expression<*>>,
      functionIndices: List<NumeralIndex>
  ): Expression<BoolSort> {
    val bindings = bindParametersToExpressions(args, functionIndices)

    return buildExpression(args as List<Expression<P>>, bindings)
  }

  abstract fun buildExpression(
      varargs: List<Expression<P>>,
      bindings: Bindings
  ): Expression<BoolSort>
}

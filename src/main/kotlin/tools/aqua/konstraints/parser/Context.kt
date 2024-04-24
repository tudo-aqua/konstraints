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

import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.theories.CoreContext
import tools.aqua.konstraints.util.Stack

abstract class SortDecl<T : Sort>(
    val name: Symbol,
    sortParameters: Set<SortParameter>,
    indices: Set<SymbolIndex>,
) {
  val signature = SortSignature(sortParameters, indices)

  open fun buildSort(identifier: Identifier, parameters: List<Sort>): T {
    val indices =
        if (identifier is IndexedIdentifier) {
          require(identifier.indices.all { it is NumeralIndex })
          identifier.indices as List<NumeralIndex>
        } else {
          emptyList()
        }

    return getSort(signature.bindTo(parameters, indices))
  }

  abstract fun getSort(bindings: Bindings): T
}

/**
 * Context class manages the currently loaded logic/theory and all the Assertion-Levels (including
 * global eventually but this option is currently not supported)
 */
class Context(theory: Theory) {
  // theory setter is private to disallow changing the theory manually
  // this should only be changed when (set-logic) is used or when reset is called
  var theory: Theory = theory
    private set

  val assertionLevels = Stack<Subcontext>()

  init {
    // core theory is always loaded QF_UF and UF are the only logics that load core "manually"
    // as it is the only theory they rely on, for all other logics core is loaded before
    // the other theory is loaded
    if (theory != CoreContext) {
      assertionLevels.push(CoreContext)
    }

    assertionLevels.push(theory)
    assertionLevels.push(AssertionLevel())
  }

  var numeralSort: Sort? = null

  fun <T> let(varBindings: List<VarBinding<*>>, block: (Context) -> T): T {
    varBindings.forEach {
      if (theory.contains(it.name))
          throw IllegalFunctionOverloadException(
              it.name.toString(), "Can not override theory symbol ${it.name}")
    }

    if (theory != CoreContext) {
      varBindings.forEach {
        if (CoreContext.contains(it.name))
            throw IllegalFunctionOverloadException(
                it.name.toString(), "Can not override theory symbol ${it.name}")
      }
    }

    assert(varBindings.distinctBy { it.name }.size == varBindings.size)

    assertionLevels.push(LetLevel(varBindings))
    val result = block(this)
    assertionLevels.pop()

    return result
  }

  fun contains(expression: Expression<*>): Boolean =
      getFunction(expression.symbol.toString(), expression.subexpressions) != null

  fun registerFunction(function: DeclareConst) {
    registerFunction(
        FunctionDecl(
            function.name,
            emptySet(),
            emptyList(),
            emptySet(),
            emptySet(),
            function.sort,
            Associativity.NONE))
  }

  fun registerFunction(function: DeclareFun) {
    registerFunction(
        FunctionDecl(
            function.name,
            emptySet(),
            function.parameters,
            emptySet(),
            emptySet(),
            function.sort,
            Associativity.NONE))
  }

  fun registerFunction(function: FunctionDecl<*>) {
    assertionLevels.forEach { level ->
      if (level.contains(function.name)) {
        throw IllegalFunctionOverloadException(
            function.name.toString(), "Can not override symbol ${function.name}")
      }
    }

    assertionLevels.peek().add(function)
  }

  internal fun registerFunction(const: ProtoDeclareConst, sort: Sort) {
    registerFunction(
        FunctionDecl(
            const.name.symbol(),
            emptySet(),
            listOf(),
            emptySet(),
            emptySet(),
            sort,
            Associativity.NONE))
  }

  internal fun registerFunction(function: ProtoDeclareFun, parameters: List<Sort>, sort: Sort) {
    if (parameters.isEmpty()) {
      registerFunction(function.name, listOf(), sort)
    } else {
      registerFunction(function.name, parameters, sort)
    }
  }

  fun registerFunction(name: String, params: List<Sort>, sort: Sort) {
    this.registerFunction(
        FunctionDecl(
            name.symbol(), emptySet(), params, emptySet(), emptySet(), sort, Associativity.NONE))
  }

  fun registerSort(sort: DeclareSort) {
    registerSort(sort.name, sort.arity)
  }

  fun registerSort(sort: SortDecl<*>) {
    if (theory.contains(sort)) {
      throw SortAlreadyDeclaredException(sort.name, sort.signature.sortParameter.size)
    }

    // TODO enforce all overloading/shadowing rules
    assertionLevels.peek().add(sort)
  }

  fun registerSort(name: Symbol, arity: Int) {
    val sort = UserDefinedSortDecl(name, arity)

    registerSort(sort)
  }

  /**
   * Returns a function matching the identifier, which accepts the provided arguments Function must
   * not be ambiguous
   */
  fun getFunction(name: Identifier, args: List<Expression<*>>): FunctionDecl<*>? {
    return getFunction(name.symbol.toString(), args)
  }

  /**
   * Returns a function matching the name, which accepts the provided arguments Function must not be
   * ambiguous
   *
   * @throws IllegalArgumentException if the function specified by name and args is ambiguous
   */
  fun getFunction(name: String, args: List<Expression<*>>): FunctionDecl<*>? {
    return assertionLevels.find { it.contains(name, args) }?.get(name, args)
  }

  internal fun getSort(protoSort: ProtoSort): Sort {
    // build all sort parameters first
    val parameters = protoSort.sorts.map { getSort(it) }
    val sort =
        assertionLevels.find { it.containsSort(protoSort.name) }?.sorts?.get(protoSort.name)
            ?: throw NoSuchElementException()

    return sort.buildSort(protoSort.identifier, parameters)
  }
}

/**
 * Parent class of all assertion levels (this includes the default assertion levels and binder
 * assertion levels, as well as theory objects)
 */
interface Subcontext {
  fun contains(function: FunctionDecl<*>) = functions.contains(function)

  fun contains(function: String, args: List<Expression<*>>) = get(function, args) != null

  fun contains(function: Symbol) =
      functions.find { it.name.toString() == function.toString() } != null

  fun get(function: String, args: List<Expression<*>>) =
      functions.find { it.name.toString() == function && it.acceptsExpressions(args, emptySet()) }

  fun contains(sort: SortDecl<*>) = sorts.containsKey(sort.name.toString())

  fun contains(sort: Sort) = sorts.containsKey(sort.name.toString())

  fun containsSort(sort: String) = sorts.containsKey(sort)

  fun add(function: FunctionDecl<*>): Boolean

  fun add(sort: SortDecl<*>): SortDecl<*>?

  val functions: List<FunctionDecl<*>>
  val sorts: Map<String, SortDecl<*>>
}

/** Represents a single assertion level */
class AssertionLevel : Subcontext {
  override fun add(function: FunctionDecl<*>) = functions.add(function)

  override fun add(sort: SortDecl<*>) = sorts.put(sort.name.toString(), sort)

  override val functions: MutableList<FunctionDecl<*>> = mutableListOf()
  override val sorts: MutableMap<String, SortDecl<*>> = mutableMapOf()
}

class VarBinding<T : Sort>(symbol: Symbol, val term: Expression<T>) :
    FunctionDecl0<T>(symbol, emptySet(), emptySet(), term.sort) {
  override fun buildExpression(bindings: Bindings): Expression<T> =
      LocalExpression(name, sort, term)
}

class LetLevel(varBindings: List<VarBinding<*>>) : Subcontext {
  override fun add(function: FunctionDecl<*>): Boolean =
      throw IllegalOperationException(
          "LetLevel.add", "Can not add new functions to let assertion level")

  override fun add(sort: SortDecl<*>): SortDecl<*> =
      throw IllegalOperationException(
          "LetLevel.add", "Can not add new sorts to let assertion level")

  override val functions: List<FunctionDecl<*>> = varBindings
  override val sorts: Map<String, SortDecl<*>> = emptyMap()
}

interface Theory : Subcontext {
  override fun add(function: FunctionDecl<*>) =
      throw IllegalOperationException("Theory.add", "Can not add new functions to SMT theories")

  override fun add(sort: SortDecl<*>) =
      throw IllegalOperationException("Theory.add", "Can not add new sorts to SMT theories")

  override val functions: List<FunctionDecl<*>>
  override val sorts: Map<String, SortDecl<*>>
}

class IllegalFunctionOverloadException(func: String, msg: String) :
    RuntimeException("Illegal overload of $func: $msg.")

class FunctionAlreadyDeclaredException(func: FunctionDecl<*>) :
    RuntimeException("Function $func has already been declared")

class SortAlreadyDeclaredException(sort: Symbol, arity: Int) :
    RuntimeException("Sort ($sort $arity) has already been declared")

class TheoryAlreadySetException :
    RuntimeException(
        "Theory has already been set, use the smt-command (reset) before using a new logic or theory")

class IllegalOperationException(operation: String, reason: String) :
    RuntimeException("Illegal Operation $operation: $reason.")

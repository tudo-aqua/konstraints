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

package tools.aqua.konstraints.parser

import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.theories.*
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
/*internal*/ class Context(val logic: Logic) {
  val assertionLevels = Stack<Subcontext>()
  val numeralSort: Sort? =
      when {
        logic.theories.contains(IntsTheory) -> IntSort
        logic.theories.contains(RealsTheory) || logic.theories.contains(RealsIntsTheory) -> RealSort
        else -> null
      }

  init {
    logic.theories.forEach { assertionLevels.push(it) }
    assertionLevels.push(AssertionLevel())
  }

  fun <T> let(varBindings: List<VarBinding<*>>, block: (Context) -> T): T {
    logic.theories.forEach { theory ->
      varBindings.forEach {
        if (theory.contains(it.symbol))
            throw IllegalFunctionOverloadException(
                it.symbol.toString(), "Can not override theory symbol ${it.symbol}")
      }
    }

    assert(varBindings.distinctBy { it.symbol }.size == varBindings.size)

    assertionLevels.push(LetLevel(varBindings.map { VarBindingDecl(it) }))
    val result = block(this)
    assertionLevels.pop()

    return result
  }

  fun <T> bindVars(sortedVars: List<SortedVar<*>>, block: (Context) -> T): T {
    assertionLevels.push(LocalLevel(sortedVars.map { SortedVarDecl(it) }))
    val result = block(this)
    assertionLevels.pop()

    return result
  }

  fun push(n: Int) {
    (0 ..< n).forEach { _ -> assertionLevels.push(AssertionLevel()) }
  }

  fun pop(n: Int) {
    if (n > assertionLevels.size)
        throw IllegalArgumentException(
            "Tried to pop $n assertion levels, but only ${assertionLevels.size} were on the stack!")

    (0 ..< n).forEach { _ ->
      if (assertionLevels.peek() is Theory) {
        throw IllegalStateException("Tried to pop theory assertion level!")
      }

      assertionLevels.pop()
    }
  }

  fun contains(expression: Expression<*>): Boolean =
      getFunction(expression.name.toString(), expression.children) != null

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

  fun registerFunction(def: FunctionDef<*>) {
    registerFunction(FunctionDefinition(def))
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
    logic.theories.forEach { theory ->
      if (theory.contains(sort)) {
        throw SortAlreadyDeclaredException(sort.name, sort.signature.sortParameter.size)
      }
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
/*internal*/ interface Subcontext {
  fun contains(function: FunctionDecl<*>) = functions.contains(function.name.toString())

  fun contains(function: String, args: List<Expression<*>>) = get(function, args) != null

  fun contains(function: Symbol) = functions.contains(function.toString())

  fun get(function: String, args: List<Expression<*>>) =
      functions[function]?.takeIf { it.acceptsExpressions(args, emptyList()) }

  fun contains(sort: SortDecl<*>) = sorts.containsKey(sort.name.toString())

  fun contains(sort: Sort) = sorts.containsKey(sort.name.toString())

  fun containsSort(sort: String) = sorts.containsKey(sort)

  fun add(function: FunctionDecl<*>): Boolean

  fun add(sort: SortDecl<*>): SortDecl<*>?

  val functions: Map<String, FunctionDecl<*>>
  val sorts: Map<String, SortDecl<*>>
}

/** Represents a single assertion level */
internal class AssertionLevel : Subcontext {
  override fun add(function: FunctionDecl<*>) =
      functions.put(function.name.toString(), function) != null

  override fun add(sort: SortDecl<*>) = sorts.put(sort.name.toString(), sort)

  override val functions: MutableMap<String, FunctionDecl<*>> = mutableMapOf()
  override val sorts: MutableMap<String, SortDecl<*>> = mutableMapOf()
}

/** Allows context to use [VarBinding] as [FunctionDecl0]. */
internal class VarBindingDecl<T : Sort>(val binding: VarBinding<T>) :
    FunctionDecl0<T>(binding.symbol, emptySet(), emptySet(), binding.term.sort) {

  override fun buildExpression(bindings: Bindings): Expression<T> = binding.instance
}

internal class LetLevel(varBindings: List<VarBindingDecl<*>>) : Subcontext {
  override fun add(function: FunctionDecl<*>): Boolean =
      throw IllegalOperationException(
          "LetLevel.add", "Can not add new functions to let assertion level")

  override fun add(sort: SortDecl<*>): SortDecl<*> =
      throw IllegalOperationException(
          "LetLevel.add", "Can not add new sorts to let assertion level")

  override val functions: Map<String, FunctionDecl<*>> =
      varBindings.associateBy { it.name.toString() }
  override val sorts: Map<String, SortDecl<*>> = emptyMap()
}

/** This class allows the context to use [SortedVar] as [FunctionDecl0]. */
/*internal*/ class SortedVarDecl<T : Sort>(val sortedVar: SortedVar<T>) :
    FunctionDecl0<T>(sortedVar.name, emptySet(), emptySet(), sortedVar.sort) {
  override fun toString(): String = "($name $sort)"

  override fun buildExpression(bindings: Bindings): Expression<T> = sortedVar.instance
}

internal class LocalLevel(localVars: List<SortedVarDecl<*>>) : Subcontext {
  override fun add(function: FunctionDecl<*>): Boolean =
      throw IllegalOperationException(
          "LocalLevel.add", "Can not add new functions to local assertion level")

  override fun add(sort: SortDecl<*>): SortDecl<*> =
      throw IllegalOperationException(
          "LocalLevel.add", "Can not add new sorts to local assertion level")

  override val functions: Map<String, FunctionDecl<*>> =
      localVars.associateBy { it.name.toString() }
  override val sorts: Map<String, SortDecl<*>> = emptyMap()
}

/*internal*/ interface Theory : Subcontext {
  override fun add(function: FunctionDecl<*>) =
      throw IllegalOperationException("Theory.add", "Can not add new functions to SMT theories")

  override fun add(sort: SortDecl<*>) =
      throw IllegalOperationException("Theory.add", "Can not add new sorts to SMT theories")

  override val functions: Map<String, FunctionDecl<*>>
  override val sorts: Map<String, SortDecl<*>>
}

class IllegalFunctionOverloadException(func: String, msg: String) :
    RuntimeException("Illegal overload of $func: $msg.")

internal class FunctionAlreadyDeclaredException(func: FunctionDecl<*>) :
    RuntimeException("Function $func has already been declared")

class SortAlreadyDeclaredException(sort: Symbol, arity: Int) :
    RuntimeException("Sort ($sort $arity) has already been declared")

class TheoryAlreadySetException :
    RuntimeException(
        "Theory has already been set, use the smt-command (reset) before using a new logic or theory")

class IllegalOperationException(operation: String, reason: String) :
    RuntimeException("Illegal Operation $operation: $reason.")

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
class Context {
  // theory setter is private to disallow changing the theory manually
  // this should only be changed when (set-logic) is used or when reset is called
  var theory: Theory? = null
    private set

  // core theory is always loaded
  val core = CoreContext

  val assertionLevels = Stack<Subcontext>()

  init {
    assertionLevels.push(core)
  }

  var numeralSort: Sort? = null

  fun contains(expression: Expression<*>): Boolean =
      getFunction(expression.symbol.toString(), expression.subexpressions) != null

  fun registerTheory(theory: Theory) {
    if (this.theory != null) {
      throw TheoryAlreadySetException()
    }

    this.theory = theory
    assertionLevels.push(this.theory!!)

    // add a new level for user definitions above theory
    assertionLevels.push(AssertionLevel())
  }

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
    if (theory?.contains(function) == true) {
      throw IllegalFunctionOverloadException(
          function.name.toString(), "Can not overload theory symbols")
    }

    // TODO enforce all overloading/shadowing rules
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
    if (theory?.contains(sort) == true) {
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
    return assertionLevels.find { it.containsFunction(name) }?.functions?.get(name)
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
  fun contains(function: FunctionDecl<*>) = functions.containsKey(function.name.toString())

  fun contains(function: Expression<*>) = functions.containsKey(function.symbol.toString())

  fun containsFunction(function: String) = functions.containsKey(function)

  fun contains(sort: SortDecl<*>) = sorts.containsKey(sort.name.toString())

  fun contains(sort: Sort) = sorts.containsKey(sort.name.toString())

  fun containsSort(sort: String) = sorts.containsKey(sort)

  fun add(function: FunctionDecl<*>): FunctionDecl<*>?

  fun add(sort: SortDecl<*>): SortDecl<*>?

  val functions: Map<String, FunctionDecl<*>>
  val sorts: Map<String, SortDecl<*>>
}

/** Represents a single assertion level */
class AssertionLevel : Subcontext {
  override fun add(function: FunctionDecl<*>) = functions.put(function.name.toString(), function)

  override fun add(sort: SortDecl<*>) = sorts.put(sort.name.toString(), sort)

  override val functions: MutableMap<String, FunctionDecl<*>> = mutableMapOf()
  override val sorts: MutableMap<String, SortDecl<*>> = mutableMapOf()
}

interface Theory : Subcontext {
  override fun add(function: FunctionDecl<*>) = null

  override fun add(sort: SortDecl<*>) = null

  override val functions: Map<String, FunctionDecl<*>>
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

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

class Context {
  // store the sort of numeral expressions either (NUMERAL Int) or (NUMERAL Real) depending on the
  // loaded logic
  var numeralSort: Sort? = null

  fun registerTheory(other: TheoryContext) {
    other.functions.forEach { func ->
      if (func.name.toString() in functionLookup) {
        functionLookup[func.name.toString()]?.add(func)
      } else {
        functionLookup[func.name.toString()] = mutableListOf(func)
      }
    }

    other.sorts.forEach { registerSort(it.value) }
  }

  fun registerFunction(function: FunctionDecl<*>) {
    val conflicts = functionLookup[function.name.toString()]

    if (conflicts != null) {
      val conflictParams = conflicts.filter { it.accepts(function.params, emptySet()) }

      if (conflictParams.isNotEmpty()) {
        val conflictReturns =
            conflictParams.filter { it.signature.bindReturnOrNull(function.sort) != null }

        if (conflictReturns.isNotEmpty()) {
          throw FunctionAlreadyDeclaredException(function)
        } else {
          conflicts.add(function)
        }
      } else {
        conflicts.add(function)
      }
    } else {
      functionLookup[function.name.toString()] = mutableListOf(function)
    }
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

  fun registerSort(sort: SortDecl<*>) {
    if (sorts.containsKey(sort.name.toString()))
        throw Exception("Sort ${sort.name} is already defined in context")

    sorts[sort.name.toString()] = sort
  }

  fun registerSort(name: Symbol, arity: Int) {
    if (sorts.containsKey(name.toString()))
        throw Exception("Sort $name is already defined in context")

    sorts[name.toString()] = UserDefinedSortDecl(name, arity)
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
    return functionLookup[name]?.single { func -> func.accepts(args.map { it.sort }, emptySet()) }
  }

  internal fun getSort(protoSort: ProtoSort): Sort {
    // build all sort parameters first
    val parameters = protoSort.sorts.map { getSort(it) }

    return sorts[protoSort.name]?.buildSort(protoSort.identifier, parameters)
        ?: throw Exception("Unknown sort ${protoSort.identifier.symbol}")
  }

  private val sorts: MutableMap<String, SortDecl<*>> = mutableMapOf()

  /*
   * Lookup for all simple functions
   * excludes indexed functions of the form e.g. ((_ extract i j) (_ BitVec m) (_ BitVec n))
   */
  val functionLookup: MutableMap<String, MutableList<FunctionDecl<*>>> = mutableMapOf()
}

interface TheoryContext {
  val functions: HashSet<FunctionDecl<*>>
  val sorts: Map<String, SortDecl<*>>
}

class FunctionAlreadyDeclaredException(func: FunctionDecl<*>) :
    RuntimeException("Function $func has already been declared")

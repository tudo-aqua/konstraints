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

internal abstract class SortDecl<T : Sort>(val name: String) {
  abstract fun getSort(sort: ProtoSort): T
}

internal class Context {
  fun registerTheory(other: TheoryContext) {
    other.functions.forEach { func ->
      if (func.name in functionLookup) {
        functionLookup[func.name]?.add(func)
      } else {
        functionLookup[func.name] = mutableListOf(func)
      }
    }

    other.sorts.forEach { registerSort(it.value) }
  }

  fun registerFunction(function: FunctionDecl<*>) {
    val conflicts = functionLookup[function.name]

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
      functionLookup[function.name] = mutableListOf(function)
    }
  }

  fun registerFunction(const: ProtoDeclareConst, sort: Sort) {
    registerFunction(
        FunctionDecl(
            const.name, emptySet(), listOf(), emptySet(), emptySet(), sort, Associativity.NONE))
  }

  fun registerFunction(function: ProtoDeclareFun, parameters: List<Sort>, sort: Sort) {
    if (parameters.isEmpty()) {
      registerFunction(function.name, listOf(), sort)
    } else {
      registerFunction(function.name, parameters, sort)
    }
  }

  fun registerFunction(name: String, params: List<Sort>, sort: Sort) {
    this.registerFunction(
        FunctionDecl(name, emptySet(), params, emptySet(), emptySet(), sort, Associativity.NONE))
  }

  fun registerSort(sort: SortDecl<*>) {
    if (sorts.containsKey(sort.name))
        throw Exception("Sort ${sort.name} is already defined in context")

    sorts[sort.name] = sort
  }

  /**
   * Returns a function matching the identifier, which accepts the provided arguments Function must
   * not be ambiguous
   */
  fun getFunction(name: Identifier, args: List<Expression<*>>): FunctionDecl<*>? {
    return getFunction(name.symbol.token.getValue<String>(), args)
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

  fun getSort(protoSort: ProtoSort): Sort {
    return sorts[protoSort.identifier.symbol.token.getValue()]?.getSort(protoSort)
        ?: throw Exception("Unknown sort ${protoSort.identifier.symbol.token.getValue<String>()}")
  }

  private val sorts: MutableMap<String, SortDecl<*>> = mutableMapOf()

  /*
   * Lookup for all simple functions
   * excludes indexed functions of the form e.g. ((_ extract i j) (_ BitVec m) (_ BitVec n))
   */
  val functionLookup: MutableMap<String, MutableList<FunctionDecl<*>>> = mutableMapOf()
}

internal interface TheoryContext {
  val functions: HashSet<FunctionDecl<*>>
  val sorts: Map<String, SortDecl<*>>
}

class FunctionAlreadyDeclaredException(func: FunctionDecl<*>) :
    RuntimeException("Function $func has already been declared")

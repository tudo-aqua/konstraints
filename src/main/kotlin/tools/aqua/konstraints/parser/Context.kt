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

// TODO ambiguous lookup with params and return type
internal abstract class SortDecl<T : Sort>(val name: String) {
  abstract fun getSort(sort: ProtoSort): T
}

internal class Context {
  fun registerTheory(other: TheoryContext) {
    functions.addAll(other.functions)
    other.sorts.forEach { registerSort(it.value) }
  }

  /* Function is private to not allow illegal FunctionDecl to be registered */
  fun registerFunction(function: FunctionDecl<*>) {
    val other = functions.find { it.name == function.name && it.params == function.params }
    if (other != null) {
      if (other.sort == function.sort) {
        throw Exception(
            "Function (${function.name} (${function.params.joinToString(" ")}) ${function.sort}) is already in context")
      } else {
        TODO("Implement ambiguous function overloading")
      }
    } else {
      functions.add(function)
    }
  }

  fun registerFunction(const: ProtoDeclareConst, sort: Sort) {
    functions.add(FunctionDecl(const.name.token.getValue(), listOf(), emptySet(), sort))
  }

  fun registerFunction(function: ProtoDeclareFun, parameters: List<Sort>, sort: Sort) {
    if (parameters.isEmpty()) {
      registerFunction(function.name.token.getValue<String>(), listOf(), sort)
    } else {
      registerFunction(function.name.token.getValue<String>(), parameters, sort)
    }
  }

  fun registerFunction(name: String, params: List<Sort>, sort: Sort) {
    registerFunction(FunctionDecl(name, params, emptySet(), sort))
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
   */
  fun getFunction(name: String, args: List<Expression<*>>): FunctionDecl<*>? {
    return functions.find { (it.name == name) && (it.accepts(args)) && !it.isAmbiguous }
  }

  /**
   * Returns a function matching the name and sort, which accepts the provided arguments Function
   * can be ambiguous
   */
  fun getFunction(name: String, args: List<Expression<*>>, sort: Sort): FunctionDecl<*>? {
    return functions.find { (it.name == name) && (it.accepts(args)) && it.sort == sort }
  }

  fun getSort(protoSort: ProtoSort): Sort {
    return sorts[protoSort.identifier.symbol.token.getValue()]?.getSort(protoSort)
        ?: throw Exception("Unknown sort ${protoSort.identifier.symbol.token.getValue<String>()}")
  }

  private val functions: HashSet<FunctionDecl<*>> = hashSetOf()
  private val sorts: MutableMap<String, SortDecl<*>> = mutableMapOf()
}

internal interface TheoryContext {
  val functions: HashSet<FunctionDecl<*>>
  val sorts: Map<String, SortDecl<*>>
}

class BindException(val key: Any, val existing: Any, val new: Any) :
    RuntimeException("$new could not be bound to $key; already bound to $existing")

fun <K : Any, V : Any> MutableMap<K, V>.bindTo(key: K, value: V) {
  putIfAbsent(key, value)?.let { if (it != value) throw BindException(key, it, value) }
}

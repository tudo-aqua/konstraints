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

import tools.aqua.konstraints.BasicExpression
import tools.aqua.konstraints.Expression
import tools.aqua.konstraints.Sort

// TODO ambiguous lookup with params and return type

open class FunctionDecl<T : Sort>(
    val name: String,
    val params: List<Sort>,
    val sort: T,
    val isAmbiguous: Boolean = false
) {
  open fun getExpression(args: List<Expression<*>>): Expression<T> {
    return BasicExpression(name, sort)
  }

  /** Returns true if the function accepts the arguments provided */
  open fun accepts(args: List<Expression<*>>): Boolean {
    if (args.size != params.size) return false

    return args.zip(params).all { it.first.sort == it.second }
  }

  override fun equals(other: Any?): Boolean =
      when {
        this === other -> true
        other !is FunctionDecl<*> -> false
        else -> (name == other.name) && (params == other.params) && (sort == other.sort)
      }

  override fun hashCode(): Int = name.hashCode() * 961 + params.hashCode() * 31 + sort.hashCode()
}

abstract class SortDecl<T : Sort>(val name: String) {
  abstract fun getSort(sort: ProtoSort): T
}

class Context {
  fun registerTheory(other: TheoryContext) {
    functions.addAll(other.functions.values)
    other.sorts.forEach { registerSort(it.value) }
  }

  /* Function is private to not allow illegal FunctionDecl to be registered */
  private fun registerFunction(function: FunctionDecl<*>) {
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
    functions.add(FunctionDecl(const.name.token.getValue(), listOf(), sort))
  }

  fun registerFunction(function: ProtoDeclareFun, parameters: List<Sort>, sort: Sort) {
    if (parameters.isEmpty()) {
      registerFunction(function.name.token.getValue<String>(), listOf(), sort)
    } else {
      registerFunction(function.name.token.getValue<String>(), parameters, sort)
    }
  }

  fun registerFunction(name: String, params: List<Sort>, sort: Sort) {
    registerFunction(FunctionDecl(name, params, sort))
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

  fun getSort(protoSort: ProtoSort): Sort? {
    return sorts[protoSort.identifier.symbol.token.getValue()]?.getSort(protoSort)
  }

  private val functions: HashSet<FunctionDecl<*>> = hashSetOf()
  private val sorts: MutableMap<String, SortDecl<*>> = mutableMapOf()
}

interface TheoryContext {
  val functions: Map<String, FunctionDecl<*>>
  val sorts: Map<String, SortDecl<*>>
}

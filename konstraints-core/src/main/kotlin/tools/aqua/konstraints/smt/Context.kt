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

package tools.aqua.konstraints.smt

import tools.aqua.konstraints.util.Stack
import tools.aqua.konstraints.util.zipWithSameLength

class Context {
  private val functionNameLookup = mutableMapOf<String, Int>()
  private val sortNameLookup = mutableMapOf<String, Int>()
  private val assertionStack = Stack<AssertionLevel<SMTFunction<Sort>, Sort>>()

  fun<T : Sort> addFun(func: SMTFunction<T>) {
    if (functionNameLookup.containsKey(func.name)) {
      // possible name conflict

      // theory symbol can not be shadowed
      if(assertionStack.bottom().contains(func.name)) {
        throw IllegalStateException("Can not shadow theory symbol ${func.name}!")
      }
    }

    val top = assertionStack.peek()

    if(top is MutableAssertionLevel) {
      top.addFun(func)
    } else {
      throw IllegalStateException("Can not add $func to none mutable stack level!")
    }
  }

  fun contains(expression: Expression<*>): Boolean {
    // check if any function matching the name exists
    if(!functionNameLookup.containsKey(expression.name.toString())) {
      return false
    }

    // TODO this should be optimized
    // check if any function matches name and parameters
    return assertionStack.any { level -> level.contains(expression.name.toString(), expression.children) }
  }

  fun contains(sort: Sort): Boolean {
    // check if any function matching the name exists
    if(!sortNameLookup.containsKey(sort.name.toString())) {
      return false
    }

    // TODO this should be optimized
    // check if any function matches name and parameters
    return assertionStack.any { level -> level.contains(sort) }
  }
}

interface AssertionLevel<out FuncType : ContextFunction<*>, out SortType : ContextSort> {
  fun contains(function: String, args: List<Expression<*>>) = get(function, args) != null

  fun contains(function: Symbol) = functions.contains(function.toString())

  fun contains(function: String) = functions.contains(function)

  fun get(function: String, args: List<Expression<*>>) =
      functions[function]?.takeIf { func ->
        (func.parameters zipWithSameLength args.map { it.sort }).all { (param, actual) ->
          param == actual
        }
      }

  fun contains(sort: Sort) = sorts.containsKey(sort.symbol.toString())

  fun containsSort(sort: String) = sorts.containsKey(sort)

  val functions: Map<String, FuncType>
  val sorts: Map<String, SortType>
}

fun <SortType : ContextSort> AssertionLevel<*, SortType>.contains(sort: SortType) =
    sorts.containsKey(sort.name.toString())

interface ContextFunction<S> {
  val name: String
  val parameters: List<S>
  val sort: Sort
}

interface ContextSort {
  val name: String
  val arity: Int
}

class MutableAssertionLevel : AssertionLevel<ContextFunction<Sort>, ContextSort> {
  override val functions: MutableMap<String, ContextFunction<Sort>> = mutableMapOf()
  override val sorts: MutableMap<String, ContextSort> = mutableMapOf()

  fun addFun(func: ContextFunction<Sort>) = functions.put(func.name.toString(), func)

  fun addSort(func: ContextSort) = sorts.put(func.name.toString(), func)
}

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

abstract class Context {
  private val nameLookup = mutableMapOf<String, Int>()
  private val assertionStack = Stack<AssertionLevel<SMTFunction<Sort>, Sort>>()

  abstract fun let(bindings: List<VarBinding<*>>, lambda: (List<VarBinding<*>>) -> Unit)

  abstract fun exists(locals: List<SortedVar<*>>)

  abstract fun forall(locals: List<SortedVar<*>>)
}

interface AssertionLevel<out FuncType : ContextFunction<*>, out SortType : ContextSort> {
  fun contains(function: String, args: List<Expression<*>>) = get(function, args) != null

  fun contains(function: Symbol) = functions.contains(function.toString())

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

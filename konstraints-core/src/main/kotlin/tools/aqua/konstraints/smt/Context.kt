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

package tools.aqua.konstraints.smt

import tools.aqua.konstraints.theories.Theories
import tools.aqua.konstraints.util.Stack
import tools.aqua.konstraints.util.zipWithSameLength

typealias StackLevel = AssertionLevel<SMTFunction<*>, Sort>

private class CurrentContext {
  val functions = mutableMapOf<String, SMTFunction<*>>()
  val sorts = mutableMapOf<String, Sort>()
}

class Context {
  private val forbiddenNames = mutableSetOf<String>()
  private val currentContext = CurrentContext()
  private val shadowingMap = Stack<MutableMap<SMTFunction<*>, SMTFunction<*>>>()
  private val undoStack = Stack<MutableSet<SMTFunction<*>>>()

  // true if we are currently in any binder (let/exists/forall/par/match)
  private var activeBinderState = false

  fun <T : Sort> addFunOrNull(func: SMTFunction<T>): SMTFunction<T>? {
    return try {
      addFun(func)
    } catch (_: IllegalArgumentException) {
      return null
    } catch (_: IllegalStateException) {
      return null
    }
  }

  fun <T : Sort> addFun(func: SMTFunction<T>): SMTFunction<T> {
    require(func.name !in forbiddenNames) {
      "Can not overload or shadow theory symbol ${func.name}!"
    }
    require(func.name !in currentContext.functions) {
      "Can not overload or shadow user defined symbol ${func.name}!"
    }
    check(!activeBinderState) { "Can not add functions to the current context in this state!" }

    currentContext.functions[func.name] = func

    // if the undoStack is not empty, and we are not currently inside any binder
    // there was at least one push, so we save the added func to remove on the appropriate pop
    if (undoStack.isNotEmpty()) {
      undoStack.peek().add(func)
    }

    return func
  }

  // TODO this should consider more than just the name
  fun contains(func: String) = currentContext.functions[func] != null

  fun contains(expression: Expression<*>) = expression.func in currentContext.functions.values

  fun contains(sort: Sort): Boolean = sort in currentContext.sorts.values

  fun <T : Sort> getFuncOrNull(name: String, sort: T) =
      try {
        getFunc(name, sort)
      } catch (_: FunctionNotFoundException) {
        null
      }

  fun <T : Sort> getFunc(name: String, sort: T) =
      currentContext.functions[name]?.castTo(sort) ?: throw FunctionNotFoundException(name)

  fun getFuncOrNull(name: String): SMTFunction<*>? {
    return try {
      getFunc(name)
    } catch (_: FunctionNotFoundException) {
      null
    }
  }

  fun getFunc(name: String) =
      currentContext.functions[name] ?: throw FunctionNotFoundException(name)

  fun push(block: Context.() -> Unit) {
    undoStack.push(mutableSetOf<SMTFunction<*>>())
    block()
    pop(1)
  }

  fun pop(n: Int) {
    check(n <= undoStack.size)
    check(!activeBinderState) { "Can not pop inside binder!" }

    (0 ..< n).forEach { _ ->
      currentContext.functions.values.removeAll(undoStack.pop())
    }
  }

  fun setLogic(logic: Logic) {
    logic.theories.forEach {
      when (it) {
        Theories.ARRAYS_EX -> forbiddenNames.addAll(listOf("select", "store"))
        Theories.FIXED_SIZE_BIT_VECTORS ->
            forbiddenNames.addAll(
                listOf(
                    "bvult",
                    "concat",
                    "bvand",
                    "bvneg",
                    "bvnot",
                    "bvor",
                    "bvadd",
                    "bvmul",
                    "bvudiv",
                    "bvurem",
                    "bvshl",
                    "bvlshr",
                    "extract",
                    "bvnand",
                    "bvnor",
                    "bvxor",
                    "bvxnor",
                    "bvcomp",
                    "bvsub",
                    "bvsdiv",
                    "bvsrem",
                    "bvsmod",
                    "bvashr",
                    "repeat",
                    "zero_extend",
                    "sign_extend",
                    "rotate_left",
                    "rotate_right",
                    "bvule",
                    "bvugt",
                    "bvuge",
                    "bvslt",
                    "bvsle",
                    "bvsgt",
                    "bvsge"))
        Theories.CORE ->
            forbiddenNames.addAll(
                listOf("false", "true", "not", "and", "or", "xor", "=", "distinct", "ite", "=>"))
        Theories.FLOATING_POINT ->
            forbiddenNames.addAll(
                listOf(
                    "roundNearestTiesToEven",
                    "RNE",
                    "roundNearestTiesToAway",
                    "RNA",
                    "roundTowardPositive",
                    "RTP",
                    "RoundTowardNegative",
                    "RTN",
                    "RoundTowardZero",
                    "RTZ",
                    "fp",
                    "+oo",
                    "-oo",
                    "+zero",
                    "-zero",
                    "NaN",
                    "fp.abs",
                    "fp.neg",
                    "fp.add",
                    "fp.sub",
                    "fp.mul",
                    "fp.div",
                    "fp.fma",
                    "fp.sqrt",
                    "fp.rem",
                    "fp.roundToIntegral",
                    "fp.min",
                    "fp.max",
                    "fp.leq",
                    "fp.lt",
                    "fp.geq",
                    "fp.gt",
                    "fp.eq",
                    "fp.isNormal",
                    "fp.isSubormal",
                    "fp.isZero",
                    "fp.isInfinite",
                    "fp.isNan",
                    "fp.isNegative",
                    "fp.isPositive",
                    "to_fp",
                    "to_fp_unsigned",
                    "fp.to_ubv",
                    "fp.to_real"))
        Theories.INTS ->
            forbiddenNames.addAll(
                listOf("-", "+", "*", "div", "mod", "abs", "<=", "<", ">=", ">", "divisible"))
        Theories.REALS -> forbiddenNames.addAll(listOf("-", "+", "*", "/", "<=", "<", ">=", ">"))
        Theories.REALS_INTS ->
            forbiddenNames.addAll(
                listOf(
                    "-",
                    "+",
                    "*",
                    "div",
                    "mod",
                    "abs",
                    "<=",
                    "<",
                    ">=",
                    ">",
                    "divisible",
                    "/",
                    "to_real"))
        Theories.STRINGS ->
            forbiddenNames.addAll(
                listOf(
                    "char",
                    "str.++",
                    "str.len",
                    "str.<",
                    "str.<=",
                    "str.at",
                    "str.substr",
                    "str.prefixof",
                    "str.suffixof",
                    "str.contains",
                    "str.indexof",
                    "str.replace",
                    "str.replace_re",
                    "str.is_digit",
                    "str.to_code",
                    "str.from_code",
                    "re.none",
                    "re.all",
                    "re.allchar",
                    "re.++",
                    "re.union",
                    "re.inter",
                    "re.*",
                    "re.comp",
                    "re.diff",
                    "re.+",
                    "re.opt",
                    "re.range",
                    "re.^",
                    "re.loop"))
      }
    }
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

class MutableAssertionLevel : AssertionLevel<SMTFunction<*>, Sort> {
  override val functions: MutableMap<String, SMTFunction<*>> = mutableMapOf()
  override val sorts: MutableMap<String, Sort> = mutableMapOf()

  fun <T : Sort> addFun(func: SMTFunction<T>) = functions.put(func.name.toString(), func)

  fun addSort(func: Sort) = sorts.put(func.name.toString(), func)
}

class FunctionNotFoundException(name: String) : NoSuchElementException("Function $name not found")

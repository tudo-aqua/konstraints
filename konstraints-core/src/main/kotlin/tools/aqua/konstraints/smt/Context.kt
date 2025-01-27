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

import tools.aqua.konstraints.dsl.SMTFunctionN
import tools.aqua.konstraints.theories.Theories
import tools.aqua.konstraints.util.Stack
import tools.aqua.konstraints.util.zipWithSameLength

typealias StackLevel = AssertionLevel<SMTFunction<*>, Sort>

class Context {
  // lookup smt functions by name
  private val functionNameLookup = mutableMapOf<String, MutableSet<SMTFunction<*>>>()

  // lookup assertion level by smt function
  private val functionLevelLookup = mutableMapOf<SMTFunction<*>, MutableSet<StackLevel>>()
  private val sortNameLookup = mutableSetOf<String>()
  private val assertionStack = Stack<StackLevel>()
  private val forbiddenNames = mutableSetOf<String>()

  init {
    assertionStack.push(MutableAssertionLevel())
  }

  fun <T : Sort> addFunOrNull(func: SMTFunction<T>): SMTFunction<T>? {
    try {
      addFun(func)
      return func
    } catch (_: IllegalArgumentException) {
      return null
    } catch (_: IllegalStateException) {
      return null
    }
  }

  fun <T : Sort> addFun(func: SMTFunction<T>) {
    require(func.name !in forbiddenNames) { "Can not shadow theory symbol ${func.name}!" }

      // TODO check if require(functionNameLookup[func.name] == null) works
    functionNameLookup[func.name]?.let { funcs ->
      require(!funcs.any { function -> assertionStack.peek().contains(function.name) }) {
        "Can not overload function ${func.name}!"
      }
    }

    assertionStack.peek().let { top ->
      check(top is MutableAssertionLevel) { "Can not add $func to none mutable stack level!" }

      top.addFun(func)

      functionNameLookup.computeIfAbsent(func.name) { mutableSetOf() }.add(func)
      functionLevelLookup.computeIfAbsent(func) { mutableSetOf() }.add(top)
    }
  }

    // TODO this should consider more than just the name
  fun contains(func: String) = functionNameLookup[func] != null

  fun contains(expression: Expression<*>) = functionLevelLookup[expression.func] != null

  fun contains(sort: Sort): Boolean {
    // check if any sort matching the name exists
    if (!sortNameLookup.contains(sort.name)) {
      return false
    }

    // TODO this should be optimized (maybe even removed)
    // check if any sort matches name and parameters
    return assertionStack.any { level -> level.contains(sort) }
  }

  fun <T : Sort> getFuncOrNull(name: String, sort: T, parameters: List<Sort>): SMTFunction<T>? {
    return try {
      getFunc(name, sort, parameters)
    } catch (_: FunctionNotFoundException) {
      null
    }
  }

  fun <T : Sort> getFunc(name: String, sort: T, parameters: List<Sort>): SMTFunction<T> {
    functionNameLookup[name]?.let { set ->
      set.find { it == SMTFunctionN(name.symbol(), sort, parameters, null) }
          ?.let { func ->
            return func.castTo(sort)
          }
    }

    throw FunctionNotFoundException(name, sort, parameters)
  }

    fun push(block: Context.() -> Unit) {
        assertionStack.push(MutableAssertionLevel())
        block()
        pop(1)
    }

    fun pop(n: Int) {
        require(n < assertionStack.size)

        (0..<n).forEach { _ ->
            assertionStack.peek().functions.forEach { _, function ->
                functionNameLookup[function.name]?.remove(function)
                functionNameLookup.entries.removeIf { (_, set) -> set.isEmpty() }

                functionLevelLookup.remove(function)
            }

            assertionStack.peek().sorts.forEach { _, sort ->
                sortNameLookup.remove(sort.name)
            }

            assertionStack.pop()
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

class FunctionNotFoundException(name: String, sort: Sort, parameters: List<Sort>) :
    NoSuchElementException("Function ($name (${parameters.joinToString(" ")}) $sort) not found")

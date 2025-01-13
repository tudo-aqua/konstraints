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

class Context {
    // lookup smt functions by name
  private val functionNameLookup = mutableMapOf<String, MutableSet<SMTFunction<Sort>>>()

    // lookup assertion level by smt function
    private val functionLevelLookup = mutableMapOf<SMTFunction<Sort>, MutableSet<AssertionLevel<SMTFunction<Sort>, Sort>>>()
  private val sortNameLookup = mutableMapOf<String, Int>()
  private val assertionStack = Stack<AssertionLevel<SMTFunction<Sort>, Sort>>()
  private val forbiddenNames = mutableSetOf<String>()

  fun addFunOrNull(func: SMTFunction<Sort>): SMTFunction<Sort>? {
    try {
      addFun(func)
      return func
    } catch (e: Exception) {
      return null
    }
  }

  fun addFun(func: SMTFunction<Sort>) {
    if (forbiddenNames.contains(func.name)) {
      throw IllegalStateException("Can not shadow theory symbol ${func.name}!")
    }

    if (functionNameLookup.containsKey(func.name) && functionNameLookup[func.name]!!.contains(func)) {
      // possible name conflict
        // check if the function is in the top stack level
        if(functionLevelLookup[func]!!.contains(assertionStack.peek())) {
            throw IllegalStateException("Can not overload function ${func.name}!")
        }
    }

    val top = assertionStack.peek()

    if (top is MutableAssertionLevel) {
      top.addFun(func)
        if(functionNameLookup[func.name] == null) {
            functionNameLookup[func.name] = mutableSetOf()
        }

        functionNameLookup[func.name]?.add(func)

        if (functionLevelLookup[func] == null) {
            functionLevelLookup[func] = mutableSetOf()
        }

        functionLevelLookup[func]?.add(top)
    } else {
      throw IllegalStateException("Can not add $func to none mutable stack level!")
    }
  }

  fun contains(expression: Expression<*>): Boolean {
    // check if any function matching the name exists
    if (!functionNameLookup.containsKey(expression.name.toString())) {
      return false
    }

    // TODO this should be optimized
    // check if any function matches name and parameters
    return assertionStack.any { level ->
      level.contains(expression.name.toString(), expression.children)
    }
  }

  fun contains(sort: Sort): Boolean {
    // check if any function matching the name exists
    if (!sortNameLookup.containsKey(sort.name.toString())) {
      return false
    }

    // TODO this should be optimized
    // check if any function matches name and parameters
    return assertionStack.any { level -> level.contains(sort) }
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

class MutableAssertionLevel : AssertionLevel<ContextFunction<Sort>, ContextSort> {
  override val functions: MutableMap<String, ContextFunction<Sort>> = mutableMapOf()
  override val sorts: MutableMap<String, ContextSort> = mutableMapOf()

  fun addFun(func: ContextFunction<Sort>) = functions.put(func.name.toString(), func)

  fun addSort(func: ContextSort) = sorts.put(func.name.toString(), func)
}

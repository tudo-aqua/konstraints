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

package tools.aqua.konstraints.solvers.z3

import com.microsoft.z3.Context
import com.microsoft.z3.Expr
import com.microsoft.z3.FuncDecl
import com.microsoft.z3.Sort as Z3Sort
import tools.aqua.konstraints.parser.SortedVar
import tools.aqua.konstraints.parser.VarBinding
import tools.aqua.konstraints.smt.Sort
import tools.aqua.konstraints.smt.Symbol
import tools.aqua.konstraints.util.Stack

class Z3Context {
  val context = Context()

  internal val constants = HashMap<String, Expr<*>>()
  internal val functions = HashMap<String, FuncDecl<*>>()
  internal val sorts = HashMap<Sort, Z3Sort>()
  private val letStack = Stack<Map<String, Expr<*>>>()
  private val boundVars = Stack<Map<String, Expr<*>>>()

  /** Create Z3 expressions for all local variables in [bindings]. */
  fun <T> let(bindings: List<VarBinding<*>>, block: () -> T): T {
    letStack.push(
        mapOf(
            *bindings
                .map { binding -> binding.name.toString() to binding.term.z3ify(this) }
                .toTypedArray()))

    val expr = block()

    letStack.pop()

    return expr
  }

  fun <T> bind(sortedVars: List<SortedVar<*>>, block: (List<Expr<*>>) -> T): T {
    boundVars.push(
        mapOf(
            *sortedVars
                .map { sortedVar ->
                  sortedVar.name.toString() to
                      context.mkConst(sortedVar.name.toSMTString(), sortedVar.sort.z3ify(this))
                }
                .toTypedArray()))

    val expr = block(boundVars.peek().values.toList())

    boundVars.pop()

    return expr
  }

  /**
   * Get a local variable [symbol] from the cache. This also safely casts the expression to [sort]
   *
   * @throws RuntimeException if the local variable is unknown
   * @throws RuntimeException if the local variable is not of sort [T]
   */
  fun <T : Z3Sort> localVariable(symbol: Symbol, sort: T): Expr<T> {
    val level =
        letStack.find { it.containsKey(symbol.toString()) }
            ?: throw RuntimeException("Unknown local variable $symbol")

    // this exception here should never be thrown, because we checked that the local variable is in
    // this stack level
    val localVar = level[symbol.toString()] ?: throw RuntimeException()

    if (localVar.sort != sort)
        throw RuntimeException(
            "Local variable $symbol had unexpected sort: expected $sort but was ${localVar.sort}")

    // conversion should not fail as we checked the sort for localVar matches expected sort
    @Suppress("UNCHECKED_CAST") return localVar as Expr<T>
  }

  fun <T : Z3Sort> boundVariable(symbol: Symbol, sort: T): Expr<T> {
    val level =
        boundVars.find { it.containsKey(symbol.toString()) }
            ?: throw RuntimeException("Unknown local variable $symbol")

    // this exception here should never be thrown, because we checked that the bound variable is in
    // this stack level
    val boundVar = level[symbol.toString()] ?: throw RuntimeException()

    if (boundVar.sort != sort)
        throw RuntimeException(
            "Bound variable $symbol had unexpected sort: expected $sort but was ${boundVar.sort}")

    // conversion should not fail as we checked the sort for localVar matches expected sort
    @Suppress("UNCHECKED_CAST") return boundVar as Expr<T>
  }

  fun <T : Z3Sort> getConstant(symbol: Symbol, sort: T): Expr<T> {
    val constant = constants[symbol.toString()] ?: throw UnknownFunctionException(symbol)

    if (constant.sort != sort) {
      throw UnexpectedSortException(
          "Constant $symbol had unexpected sort: expected $sort but was ${constant.sort}")
    }

    @Suppress("UNCHECKED_CAST") return constant as Expr<T>
  }

  fun <T : Z3Sort> getConstantOrNull(symbol: Symbol, sort: T): Expr<T>? =
      try {
        getConstant(symbol, sort)
      } catch (e: UnexpectedSortException) {
        // rethrown this exception because wrong sorting is a strong error
        throw e
      } catch (e: UnknownFunctionException) {
        null
      }

  fun <T : Z3Sort> getFunction(symbol: Symbol, args: List<Expr<*>>, sort: T): Expr<T> {
    val functionDef = functions[symbol.toString()] ?: throw UnknownFunctionException(symbol)

    val function = functionDef.apply(*args.toTypedArray())

    if (function.sort != sort) {
      throw UnexpectedSortException(
          "Function $symbol had unexpected sort: expected $sort but was ${function.sort}")
    }

    @Suppress("UNCHECKED_CAST") return function as Expr<T>
  }

  fun <T : Z3Sort> getFunctionOrNull(symbol: Symbol, args: List<Expr<*>>, sort: T): Expr<T>? =
      try {
        getFunction(symbol, args, sort)
      } catch (e: UnexpectedSortException) {
        // rethrown this exception because wrong sorting is a strong error
        throw e
      } catch (e: UnknownFunctionException) {
        null
      }
}

class UnexpectedSortException(msg: String) : RuntimeException(msg)

class UnknownFunctionException(symbol: Symbol) : RuntimeException("Unknown function $symbol")

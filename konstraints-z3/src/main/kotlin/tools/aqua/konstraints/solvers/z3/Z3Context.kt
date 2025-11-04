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

package tools.aqua.konstraints.solvers.z3

import com.microsoft.z3.Context
import com.microsoft.z3.Expr
import com.microsoft.z3.FuncDecl
import com.microsoft.z3.Sort as Z3Sort
import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.smt.SMTFunction
import tools.aqua.konstraints.smt.Sort
import tools.aqua.konstraints.smt.SortedVar
import tools.aqua.konstraints.smt.Symbol
import tools.aqua.konstraints.smt.VarBinding
import tools.aqua.konstraints.util.LeveledMap

class Z3Context {
  val context = Context()

  internal val constants = LeveledMap<Expression<*>, Expr<*>>()
  internal val functions = LeveledMap<SMTFunction<*>, FuncDecl<*>>()
  internal val sorts = HashMap<Sort, Z3Sort>()
  private val letStack = LeveledMap<VarBinding<*>, Expr<*>>()
  private val boundVars = LeveledMap<SortedVar<*>, Expr<*>>()

  /** Create Z3 expressions for all local variables in [bindings]. */
  fun <T> let(bindings: List<VarBinding<*>>, block: () -> T): T {
    letStack.push()
    letStack.putAll(bindings zip bindings.map { binding -> binding.term.z3ify(this) })

    val expr = block()

    letStack.pop()

    return expr
  }

  fun <T> bind(sortedVars: List<SortedVar<*>>, block: (List<Expr<*>>) -> T): T {
    val vars =
        sortedVars.map { sortedVar ->
          context.mkConst(sortedVar.symbol.toString(), sortedVar.sort.z3ify(this))
        }

    boundVars.push()
    boundVars.putAll(sortedVars zip vars)

    val expr = block(vars)

    boundVars.pop()

    return expr
  }

  /**
   * Get a local variable [binding] from the cache. This also safely casts the expression to [T]
   *
   * @throws RuntimeException if the local variable is unknown
   * @throws RuntimeException if the local variable is not of sort [T]
   */
  fun <T : Z3Sort> localVariable(binding: VarBinding<*>, sort: T): Expr<T> {
    val localVar = letStack[binding] ?: throw RuntimeException()

    if (localVar.sort != sort)
        throw RuntimeException(
            "Local variable ${binding.name} had unexpected sort: expected $sort but was ${localVar.sort}"
        )

    // conversion should not fail as we checked the sort for localVar matches expected sort
    @Suppress("UNCHECKED_CAST")
    return localVar as Expr<T>
  }

  fun <T : Z3Sort> boundVariable(sortedVar: SortedVar<*>, sort: T): Expr<T> {
    val boundVar = boundVars[sortedVar] ?: throw RuntimeException()

    if (boundVar.sort != sort)
        throw RuntimeException(
            "Bound variable ${sortedVar.symbol} had unexpected sort: expected $sort but was ${boundVar.sort}"
        )

    // conversion should not fail as we checked the sort for localVar matches expected sort
    @Suppress("UNCHECKED_CAST")
    return boundVar as Expr<T>
  }

  fun <T : Z3Sort> getConstant(expr: Expression<*>): Expr<T> {
    // val constant = constants[expr] ?: (functions[expr.func]?.apply() ?: throw
    // UnknownFunctionException(expr.name as Symbol))

    // constant may have been declared via declare-fun as function of arity 0 or via
    // declare-constant
    // so we have to search in both the constant and function lookup
    val constant =
        if (functions[expr.func] != null) {
          functions[expr.func]?.apply()
        } else {
          constants[expr]
        } ?: throw UnknownFunctionException(expr.name as Symbol)

    // FIXME this sort here might be wrong
    if (constant.sort != sorts[expr.sort]) {
      throw UnexpectedSortException(
          "Constant ${expr.name} had unexpected sort: expected ${expr.sort} but was ${constant.sort}"
      )
    }

    @Suppress("UNCHECKED_CAST")
    return constant as Expr<T>
  }

  fun <T : Z3Sort> getConstantOrNull(expr: Expression<*>): Expr<T>? =
      try {
        getConstant(expr)
      } catch (e: UnexpectedSortException) {
        // rethrown this exception because wrong sorting is a strong error
        throw e
      } catch (e: UnknownFunctionException) {
        null
      }

  fun <T : Z3Sort> getFunction(func: SMTFunction<*>, args: List<Expr<*>>, sort: T): Expr<T> {
    val functionDef = functions[func] ?: throw UnknownFunctionException(func.symbol)

    val function = functionDef.apply(*args.toTypedArray())

    if (function.sort != sort) {
      throw UnexpectedSortException(
          "Function ${func.symbol} had unexpected sort: expected $sort but was ${function.sort}"
      )
    }

    @Suppress("UNCHECKED_CAST")
    return function as Expr<T>
  }

  fun <T : Z3Sort> getFunctionOrNull(func: SMTFunction<*>, args: List<Expr<*>>, sort: T): Expr<T>? =
      try {
        getFunction(func, args, sort)
      } catch (e: UnexpectedSortException) {
        // rethrown this exception because wrong sorting is a strong error
        throw e
      } catch (e: UnknownFunctionException) {
        null
      }

  fun reset() {
    constants.clear()
    functions.clear()
    sorts.clear()
    letStack.clear()
    boundVars.clear()
  }
}

class UnexpectedSortException(msg: String) : RuntimeException(msg)

class UnknownFunctionException(symbol: Symbol) : RuntimeException("Unknown function $symbol")

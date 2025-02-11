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

import java.util.*
import tools.aqua.konstraints.util.zipWithSameLength

/**
 * SMTFunction of any arity.
 *
 * Use [invoke] to generate an expression with the given parameters applied.
 */
abstract class SMTFunction<out T : Sort> : ContextFunction<Sort> {
  abstract val symbol: Symbol
  override val name: String
    get() = symbol.toString()

  abstract override val sort: T
  abstract override val parameters: List<Sort>
  abstract val definition: FunctionDef<T>?

  open operator fun invoke(args: List<Expression<*>>): Expression<T> {
    require(args.size == parameters.size)
    require((args zipWithSameLength parameters).all { (par, sort) -> par.sort == sort })

    return if (definition == null) {
      UserDeclaredExpression(symbol, sort, args, this)
    } else {
      UserDefinedExpression(symbol, sort, emptyList(), definition!!, this)
    }
  }

  final override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (other !is SMTFunction<*>) return false
    if(this is VarBinding && other !is VarBinding<*>) return false
    if(this !is VarBinding && other is VarBinding<*>) return false
    if(this is SortedVar && other !is SortedVar<*>) return false
    if(this !is SortedVar && other is SortedVar<*>) return false
    else if (symbol == other.symbol && // symbol equality
        sort == other.sort && // same sort
        parameters.size == other.parameters.size && // same number of parameters
        (parameters zip other.parameters).all { (s1, s2) -> s1 == s2 } // pairwise equal parameters
    ) return true
    return false

    // does not consider definition for equality because two functions
    // with the exact same signature (name, sort and parameters) can not be
    // overloaded by a differing definition
  }

  final override fun hashCode(): Int = Objects.hash(symbol, name, sort, parameters, definition)

  infix fun <T : Sort> castTo(to: T): SMTFunction<T> {
    if (sort != to) {
      throw FunctionCastException(sort, to.toString())
    }

    @Suppress("UNCHECKED_CAST") return this as SMTFunction<T>
  }
}

class FunctionCastException(from: Sort, to: String) :
    ClassCastException("Can not cast expression from $from to $to")

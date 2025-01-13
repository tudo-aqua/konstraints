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

import tools.aqua.konstraints.util.zipWithSameLength

/**
 * SMTFunction of any arity.
 *
 * Use [invoke] to generate an expression with the given parameters applied.
 */
abstract class SMTFunction<T : Sort> : ContextFunction<Sort> {
  abstract val symbol: Symbol
  override val name: String
    get() = symbol.toString()

  abstract override val sort: T
  abstract override val parameters: List<Sort>
  abstract val definition: FunctionDef<T>?

  operator fun invoke(args: List<Expression<*>>): Expression<T> {
    require(args.size == parameters.size)
    require((args zipWithSameLength parameters).all { (par, sort) -> par.sort == sort })

    return if (definition == null) {
      UserDeclaredExpression(symbol, sort, args, this)
    } else {
      UserDefinedExpression(symbol, sort, emptyList(), definition!!, this)
    }
  }

  override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (other !is SMTFunction<*>) return false
    else if (
      symbol == other.symbol && // symbol equality
      sort == other.sort && // same sort
      parameters.size == other.parameters.size && // same number of parameters
      (parameters zip other.parameters).all {(s1, s2) -> s1 == s2} // pairwise equal parameters
      ) return true
    return false
  }

  override fun hashCode(): Int {
    var result = symbol.hashCode()
    result = 31 * result + name.hashCode()
    result = 31 * result + sort.hashCode()
    result = 31 * result + parameters.hashCode()
    result = 31 * result + (definition?.hashCode() ?: 0)
    return result
  }
}

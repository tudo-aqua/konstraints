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
interface SMTFunction<T : Sort> : ContextFunction<Sort> {
  val symbol: Symbol
  override val name: String
    get() = symbol.toString()

  override val sort: T
  override val parameters: List<Sort>
  val definition: FunctionDef<T>?

  operator fun invoke(args: List<Expression<*>>): Expression<T> {
    require(args.size == parameters.size)
    require((args zipWithSameLength parameters).all { (par, sort) -> par.sort == sort })

    return if (definition == null) {
      UserDeclaredExpression(symbol, sort, args)
    } else {
      UserDefinedExpression(symbol, sort, emptyList(), definition!!)
    }
  }
}

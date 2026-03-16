/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2026 The Konstraints Authors
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

/** Model class holding the data of solver return get-model. */
data class Model(val definitions: Map<Symbol, FunctionDef<*>>) {
  constructor(definitions: List<FunctionDef<*>>) : this(definitions.associateBy { def -> def.name })

  fun getDefinition(symbol: Symbol) = definitions[symbol]!!
  fun getDefinition(symbol: String) = definitions[symbol.toSymbol()]!!

  fun getDefinitionOrNull(symbol: Symbol) = definitions[symbol]
  fun getDefinitionOrNull(symbol: String) = definitions[symbol.toSymbol()]

  fun getTerm(symbol: Symbol) = getDefinition(symbol).term
  fun getTerm(symbol: String) = getDefinition(symbol).term

  fun getTermOrNull(symbol: Symbol) = getDefinitionOrNull(symbol)?.term
  fun getTermOrNull(symbol: String) = getDefinitionOrNull(symbol)?.term

  inline fun<reified T : Sort> castTerm(symbol: Symbol) = getDefinition(symbol).term.cast<T>()
  inline fun<reified T : Sort> castTerm(symbol: String) = getDefinition(symbol).term.cast<T>()

  inline fun<reified T : Sort> castTermOrNull(symbol: Symbol) = getDefinitionOrNull(symbol)?.term?.cast<T>()
  inline fun<reified T : Sort> castTermOrNull(symbol: String) = getDefinitionOrNull(symbol)?.term?.cast<T>()

  /**
   * This will later hold the functions to convert from solver models to a generic konstraints
   * model.
   */
  companion object
}

fun main(model : Model) {
  val x = model.castTerm<BoolSort>("x")
}

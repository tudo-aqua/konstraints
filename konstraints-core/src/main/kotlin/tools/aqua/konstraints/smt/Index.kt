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

/** Extension method to conveniently create a [NumeralIndex] from an Integer. */
fun Int.idx(): NumeralIndex = NumeralIndex(this)

/**
 * Extension method to conveniently create a [SymbolIndex] from a String.
 *
 * @throws IllegalSymbolException if the string is not a valid SMT Symbol
 */
fun String.idx(): SymbolIndex = SymbolIndex(this)

/** Interface for all SMT Indices. */
sealed interface Index

/** SMT Index containing a Numeral. */
data class NumeralIndex(val numeral: Int) : Index {
  override fun toString() = numeral.toString()
}

/** SMT Index containing an SMT [Symbol]. */
data class SymbolIndex(val symbol: Symbol) : Index {

  /**
   * Directly construct the Index from a String.
   *
   * @throws IllegalSymbolException if the string is not a valid SMT Symbol
   */
  constructor(symbol: String) : this(symbol.toSymbolWithQuotes())

  override fun toString() = symbol.toString()
}

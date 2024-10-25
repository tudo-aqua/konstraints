/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2024 The Konstraints Authors
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

package tools.aqua.konstraints.parser

import tools.aqua.konstraints.smt.IllegalSymbolException
import tools.aqua.konstraints.smt.NumeralIndex
import tools.aqua.konstraints.smt.Sort
import tools.aqua.konstraints.smt.SymbolIndex

data class Bindings(val parametric: Map<Sort, Sort>, val indices: Map<SymbolIndex, NumeralIndex>) {
  /**
   * Returns the NumeralIndex that the Symbol is bound to
   *
   * @param symbol String specifying the SymbolIndex to get the binding for
   * @throws IndexNotBoundException if the SymbolIndex is not bound
   * @throws IllegalSymbolException if [symbol] is not a valid SMTSymbol
   */
  operator fun get(symbol: String): NumeralIndex = get(SymbolIndex(symbol))

  operator fun get(symbol: SymbolIndex): NumeralIndex {
    return indices[symbol] ?: throw IndexNotBoundException(symbol)
  }

  fun getOrNull(symbol: String): NumeralIndex? = getOrNull(SymbolIndex(symbol))

  fun getOrNull(symbol: SymbolIndex): NumeralIndex? {
    return try {
      this[symbol]
    } catch (_: Exception) {
      null
    }
  }

  operator fun get(sort: Sort): Sort {
    return parametric[sort] ?: throw SortNotBoundException(sort)
  }

  fun getOrNull(sort: Sort): Sort? {
    return try {
      this[sort]
    } catch (_: Exception) {
      null
    }
  }
}

class IndexNotBoundException(symbolIndex: SymbolIndex) :
    RuntimeException("$symbolIndex is not bound")

class SortNotBoundException(sort: Sort) : RuntimeException("$sort is not bound")

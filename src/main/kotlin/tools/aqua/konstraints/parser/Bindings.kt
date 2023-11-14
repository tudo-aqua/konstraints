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

package tools.aqua.konstraints.parser

import tools.aqua.konstraints.NumeralIndex
import tools.aqua.konstraints.Sort
import tools.aqua.konstraints.SymbolIndex

// TODO add parametric bindings
data class Bindings(val parametric: Map<Sort, Sort>, val indices: Map<SymbolIndex, NumeralIndex>) {
  fun getBinding(symbol: String): NumeralIndex = getBinding(SymbolIndex(symbol))

  fun getBinding(symbol: SymbolIndex): NumeralIndex {
    return indices[symbol] ?: throw NotBoundException(symbol)
  }
}

class NotBoundException(val symbolIndex: SymbolIndex) :
    RuntimeException("$symbolIndex is not bound")

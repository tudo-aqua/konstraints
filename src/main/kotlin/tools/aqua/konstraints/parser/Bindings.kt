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

import tools.aqua.konstraints.BVSort
import tools.aqua.konstraints.NumeralIndex
import tools.aqua.konstraints.SymbolIndex
import tools.aqua.konstraints.SymbolicBVSort

data class IndexBindings(val indices: Map<SymbolIndex, NumeralIndex>) {
  fun get(symbolic: SymbolicBVSort): BVSort {
    if (symbolic.symbolicBits in indices) {
      return BVSort(indices[symbolic.symbolicBits]!!.numeral)
    }

    throw NotBoundException(symbolic.symbolicBits)
  }
}

class NotBoundException(val symbolIndex: SymbolIndex) :
    RuntimeException("$symbolIndex is not bound")

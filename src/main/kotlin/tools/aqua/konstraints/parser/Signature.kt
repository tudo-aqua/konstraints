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

import tools.aqua.konstraints.Index
import tools.aqua.konstraints.NumeralIndex
import tools.aqua.konstraints.Sort
import tools.aqua.konstraints.SymbolIndex
import tools.aqua.konstraints.util.zipWithSameLength

data class Signature(
    val parametricSorts: Set<Sort>,
    val indices: Set<SymbolIndex>,
    val parameters: List<Sort>,
    val sort: Sort
) {
  fun bindToOrNull(
      actualParameters: List<Sort>,
      actualReturn: Sort
  ): Pair<Map<Sort, Sort>, Map<SymbolIndex, NumeralIndex>>? =
      try {
        bindTo(actualParameters, actualReturn)
      } catch (exception: Exception) {
        null
      }

  fun bindTo(
      actualParameters: List<Sort>,
      actualReturn: Sort
  ): Pair<Map<Sort, Sort>, Map<SymbolIndex, NumeralIndex>> {
    val parametricBindings = mutableMapOf<Sort, Sort>()
    val indexBindings = mutableMapOf<SymbolIndex, NumeralIndex>()

    bindToInternal(parameters, actualParameters, parametricBindings, indexBindings)
    bindToInternal(sort, actualReturn, parametricBindings, indexBindings)

    return parametricBindings to indexBindings
  }

  private fun bindToInternal(
      symbolicParameters: List<Sort>,
      actualParameters: List<Sort>,
      parametricBindings: MutableMap<Sort, Sort>,
      indexBindings: MutableMap<SymbolIndex, NumeralIndex>
  ) {
    (symbolicParameters zipWithSameLength actualParameters).forEach { (symbolic, actual) ->
      bindToInternal(symbolic, actual, parametricBindings, indexBindings)
    }
  }

  private fun bindToInternal(
      symbolic: Sort,
      actual: Sort,
      parametricBindings: MutableMap<Sort, Sort>,
      indexBindings: MutableMap<SymbolIndex, NumeralIndex>
  ) {
    if (symbolic in parametricSorts) {
      // bind if not already bound
      parametricBindings.bindTo(symbolic, actual)
    } else {
      require(symbolic.name == actual.name)

      (symbolic.indices zipWithSameLength actual.indices).forEach { (symbolicIndex, actualIndex) ->
        if (symbolicIndex is SymbolIndex) {
          // try to bind or match if already bound
          bindToInternal(symbolicIndex, actualIndex, indexBindings)
        } else {
          // just try to match
          // TODO require that we are matching NumeralIndices here
          // TODO actual should never be a SymbolIndex
          require((symbolicIndex as NumeralIndex).numeral == (actualIndex as NumeralIndex).numeral)
        }
      }
      bindToInternal(symbolic.parameters, actual.parameters, parametricBindings, indexBindings)
    }
  }

  private fun bindToInternal(
      symbolic: SymbolIndex,
      actual: Index,
      indexBindings: MutableMap<SymbolIndex, NumeralIndex>
  ) {
    require(actual is NumeralIndex)
    if (symbolic in indices) {
      indexBindings.bindTo(symbolic, actual)
    } else {
      require(indexBindings[symbolic]?.numeral == actual.numeral)
    }
  }
}

class BindException(val key: Any, val existing: Any, val new: Any) :
    RuntimeException("$new could not be bound to $key; already bound to $existing")

fun <K : Any, V : Any> MutableMap<K, V>.bindTo(key: K, value: V) {
  putIfAbsent(key, value)?.let { if (it != value) throw BindException(key, it, value) }
}

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

import tools.aqua.konstraints.smt.Index
import tools.aqua.konstraints.smt.NumeralIndex
import tools.aqua.konstraints.smt.Sort
import tools.aqua.konstraints.smt.SymbolIndex
import tools.aqua.konstraints.util.zipWithSameLength

/**
 * data class holding the signature of a [FunctionDecl]
 *
 * @param parametricSorts set of parametric sorts
 * @param functionIndices set of the function name indices (i.e. (_ extract i j))
 * @param parameterIndices set of function parameter indices (i.e. (_ BitVec m))
 * @param parameters list of function parameters
 * @param returnSort sort of the function
 */
data class Signature(
    val parametricSorts: Set<Sort>,
    val functionIndices: Set<SymbolIndex>,
    val parameterIndices: Set<SymbolIndex>,
    val parameters: List<Sort>,
    val returnSort: Sort
) {

  /**
   * Bind the symbolic function indices, parametric sorts and return sort to actual indices and
   * sorts
   *
   * @param actualParameters list of parameters passed to the SMT function
   * @param actualFunctionIndices set of the numeral indices
   * @param actualReturn return sort of the function
   * @return the binding object if binding was successful, null otherwise
   */
  fun bindToOrNull(
      actualParameters: List<Sort>,
      actualFunctionIndices: Set<NumeralIndex>,
      actualReturn: Sort
  ): Bindings? =
      try {
        bindTo(actualParameters, actualFunctionIndices, actualReturn)
      } catch (exception: Exception) {
        null
      }

  /**
   * Bind the symbolic function indices, parametric sorts and return sort to actual indices and
   * sorts
   *
   * @param actualParameters list of parameters passed to the SMT function
   * @param actualFunctionIndices set of the numeral indices
   * @param actualReturn return sort of the function
   * @return the binding object if binding was successful
   * @throws BindException if an index is already bound
   * @throws IllegalArgumentException if length of actualParameters does not match length of
   *   function parameters
   */
  fun bindTo(
      actualParameters: List<Sort>,
      actualFunctionIndices: Set<NumeralIndex>,
      actualReturn: Sort
  ): Bindings {
    val parametricBindings = mutableMapOf<Sort, Sort>()
    val indexBindings = mutableMapOf<SymbolIndex, NumeralIndex>()

    bindToInternal(parameters, actualParameters, parametricBindings, indexBindings)
    bindFunctionIndices(actualFunctionIndices, indexBindings)
    bindParameter(returnSort, actualReturn, parametricBindings, indexBindings)

    return Bindings(parametricBindings, indexBindings)
  }

  /**
   * Bind only the function indices and parametric sorts
   *
   * @param actualParameters list of parameters passed to the SMT function
   * @param actualFunctionIndices set of the numeral indices
   * @return the binding object if binding was successful, null otherwise
   */
  fun bindParametersOrNull(
      actualParameters: List<Sort>,
      actualFunctionIndices: Set<NumeralIndex>
  ): Bindings? =
      try {
        bindParameters(actualParameters, actualFunctionIndices)
      } catch (_: Exception) {
        null
      }

  /**
   * Bind only the function indices and parametric sorts
   *
   * @param actualParameters list of parameters passed to the SMT function
   * @param actualFunctionIndices set of the numeral indices
   * @return the binding object if binding was successful
   * @throws BindException if an index is already bound
   * @throws IllegalArgumentException if length of actualParameters does not match length of
   *   function parameters
   */
  fun bindParameters(
      actualParameters: List<Sort>,
      actualFunctionIndices: Set<NumeralIndex>
  ): Bindings {
    val parametricBindings = mutableMapOf<Sort, Sort>()
    val indexBindings = mutableMapOf<SymbolIndex, NumeralIndex>()

    bindToInternal(parameters, actualParameters, parametricBindings, indexBindings)
    bindFunctionIndices(actualFunctionIndices, indexBindings)

    return Bindings(parametricBindings, indexBindings)
  }

  /**
   * Bind only the return sort of the function
   *
   * @param actualReturn return sort of the function
   * @return the binding object if binding was successful, null otherwise
   */
  fun bindReturnOrNull(actualReturn: Sort): Bindings? =
      try {
        bindReturn(actualReturn)
      } catch (_: Exception) {
        null
      }

  /**
   * Bind only the return sort of the function
   *
   * @param actualReturn return sort of the function
   * @return the binding object if binding was successful
   * @throws BindException if an index is already bound
   * @throws IllegalArgumentException if length of actualParameters does not match length of
   *   function parameters
   */
  fun bindReturn(actualReturn: Sort): Bindings {
    val parametricBindings = mutableMapOf<Sort, Sort>()
    val indexBindings = mutableMapOf<SymbolIndex, NumeralIndex>()

    bindParameter(returnSort, actualReturn, parametricBindings, indexBindings)

    return Bindings(parametricBindings, indexBindings)
  }

  /** zip the symbolicParameters with the actualParameters then try to bind each pair */
  private fun bindToInternal(
      symbolicParameters: List<Sort>,
      actualParameters: List<Sort>,
      parametricBindings: MutableMap<Sort, Sort>,
      indexBindings: MutableMap<SymbolIndex, NumeralIndex>
  ) {
    (symbolicParameters zipWithSameLength actualParameters).forEach { (symbolic, actual) ->
      bindParameter(symbolic, actual, parametricBindings, indexBindings)
    }
  }

  /** bind each function index to [functionIndices] */
  private fun bindFunctionIndices(
      funcIndices: Set<NumeralIndex>,
      indexBindings: MutableMap<SymbolIndex, NumeralIndex>
  ) {
    // TODO handle case of already bound index (exception?)
    (funcIndices zip functionIndices).forEach { (funcIndex, index) ->
      bindIndex(index, funcIndex, functionIndices, indexBindings)
    }
  }

  /**
   * bind a single parameter if its a parametric sort bind it to an actual sort then if present bind
   * all indices or match already bound indices
   */
  private fun bindParameter(
      symbolic: Sort,
      actual: Sort,
      parametricBindings: MutableMap<Sort, Sort>,
      indexBindings: MutableMap<SymbolIndex, NumeralIndex>
  ) {
    if (symbolic in parametricSorts) {
      // bind if not already bound
      parametricBindings.bindParametersTo(symbolic, actual)
    } else {
      require(symbolic.name == actual.name)

      (symbolic.indices zipWithSameLength actual.indices).forEach { (symbolicIndex, actualIndex) ->
        when (symbolicIndex) {
          is SymbolIndex -> {
            // bind the symbolicIndex if it has not been already bound
            bindIndex(symbolicIndex, actualIndex, parameterIndices, indexBindings)
          }
          is NumeralIndex -> {
            // else just try to match
            require(actualIndex is NumeralIndex)
            require(symbolicIndex.numeral == actualIndex.numeral)
          }
        }
      }
      bindToInternal(symbolic.parameters, actual.parameters, parametricBindings, indexBindings)
    }
  }

  /** bind the provided index to the symbolic index of set [targetIndices] */
  private fun bindIndex(
      symbolic: SymbolIndex,
      actual: Index,
      targetIndices: Set<SymbolIndex>,
      indexBindings: MutableMap<SymbolIndex, NumeralIndex>
  ) {
    require(actual is NumeralIndex)
    if (symbolic in targetIndices) {
      indexBindings.bindParametersTo(symbolic, actual)
    }
  }
}

class BindException(val key: Any, val existing: Any, val new: Any) :
    RuntimeException("$new could not be bound to $key; already bound to $existing")

fun <K : Any, V : Any> MutableMap<K, V>.bindParametersTo(key: K, value: V) {
  putIfAbsent(key, value)?.let { if (it != value) throw BindException(key, it, value) }
}

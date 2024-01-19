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

package tools.aqua.konstraints

enum class Logic {
  AUFLIA, // Closed formulas over the theory of linear integer arithmetic and arrays extended with
  // free sort and function symbols but restricted to arrays with integer indices and
  // values.
  AUFLIRA, // Closed linear formulas with free sort and function symbols over one- and
  // two-dimentional arrays of integer index and real value.
  AUFNIRA, // Closed formulas with free function and predicate symbols over a theory of arrays of
  // arrays of integer index and real value.
  LIA, // Closed linear formulas over linear integer arithmetic.
  LRA, // Closed linear formulas in linear real arithmetic.
  QF_ABV, // Closed quantifier-free formulas over the theory of bitvectors and bitvector arrays.
  QF_AUFBV, // Closed quantifier-free formulas over the theory of bitvectors and bitvector arrays
  // extended with free sort and function symbols.
  QF_AUFLIA, // Closed quantifier-free linear formulas over the theory of integer arrays extended
  // with free sort and function symbols.
  QF_AX, // Closed quantifier-free formulas over the theory of arrays with extensionality.
  QF_BV, // Closed quantifier-free formulas over the theory of fixed-size bitvectors.
  QF_IDL, // Difference Logic over the integers. In essence, Boolean combinations of inequations of
  // the form x - y < b where x and y are integer variables and b is an integer constant.
  QF_LIA, // Unquantified linear integer arithmetic. In essence, Boolean combinations of inequations
  // between linear polynomials over integer variables.
  QF_LRA, // Unquantified linear real arithmetic. In essence, Boolean combinations of inequations
  // between linear polynomials over real variables.
  QF_NIA, // Quantifier-free integer arithmetic.
  QF_NRA, // Quantifier-free real arithmetic.
  QF_RDL, // Difference Logic over the reals. In essence, Boolean combinations of inequations of the
  // form x - y < b where x and y are real variables and b is a rational constant.
  QF_UF, // Unquantified formulas built over a signature of uninterpreted (i.e., free) sort and
  // function symbols.
  QF_UFBV, // Unquantified formulas over bitvectors with uninterpreted sort function and symbols.
  QF_UFIDL, // Difference Logic over the integers (in essence) but with uninterpreted sort and
  // function symbols.
  QF_UFLIA, // Unquantified linear integer arithmetic with uninterpreted sort and function symbols.
  QF_UFLRA, // Unquantified linear real arithmetic with uninterpreted sort and function symbols.
  QF_UFNRA, // Unquantified non-linear real arithmetic with uninterpreted sort and function symbols.
  UFLRA, // Linear real arithmetic with uninterpreted sort and function symbols.
  UFNIA; // Non-linear integer arithmetic with uninterpreted sort and function symbols.

  override fun toString(): String =
      when (this) {
        AUFLIA -> "AUFLIA"
        AUFLIRA -> "AUFLIRA"
        AUFNIRA -> "AUFNIRA"
        LIA -> "LIA"
        LRA -> "LRA"
        QF_ABV -> "QF_ABV"
        QF_AUFBV -> "QF_AUFBV"
        QF_AUFLIA -> "QF_AUFLIA"
        QF_AX -> "QF_AX"
        QF_BV -> "QF_BV"
        QF_IDL -> "QF_IDL"
        QF_LIA -> "QF_LIA"
        QF_LRA -> "QF_LRA"
        QF_NIA -> "QF_NIA"
        QF_NRA -> "QF_NRA"
        QF_RDL -> "QF_RDL"
        QF_UF -> "QF_UF"
        QF_UFBV -> "QF_UFBV"
        QF_UFIDL -> "QF_UFIDL"
        QF_UFLIA -> "QF_UFLIA"
        QF_UFLRA -> "QF_UFLRA"
        QF_UFNRA -> "QF_UFNRA"
        UFLRA -> "UFLRA"
        UFNIA -> "UFNIA"
      }
}

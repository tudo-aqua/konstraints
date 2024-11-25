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

package tools.aqua.konstraints.smt

import java.math.BigDecimal

sealed interface SpecConstant

data class StringConstant(val string: String) : SpecConstant

data class NumeralConstant(val numeral: String) : SpecConstant

/* BinaryConstant of the form #b followed by a non-empty sequence of 0 and 1 characters */
data class BinaryConstant(val binary: String) : SpecConstant {
  /* Number of bits for this binary */
  val bits = binary.length - 2
}

/* Hexadecimal constant of the form
 * #x followed by a non-empty sequence of digits and letters from A to F , capitalized or not
 */
data class HexConstant(val hexadecimal: String) : SpecConstant {
  /* Number of bits for this hexadecimal */
  val bits = (hexadecimal.length - 2) * 4
}

data class DecimalConstant(val decimal: BigDecimal) : SpecConstant

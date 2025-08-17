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

/** RoundingMode sort object */
sealed class RoundingModeSort : Sort("RoundingMode") {
  override val theories = FLOATING_POINT_MARKER_SET
}

object RoundingMode : RoundingModeSort()

/**
 * FloatingPoint sort with any positive number of bits
 *
 * (_ FloatingPoint eb sb)
 *
 * @param eb exponent bits
 * @param sb significant bits
 */
sealed class FPSort(eb: Index, sb: Index) : Sort("FloatingPoint") {
  companion object {
    operator fun invoke(eb: Int, sb: Int): FPSort = FloatingPoint(eb, sb)

    operator fun invoke(eb: SymbolIndex, sb: SymbolIndex): FPSort = SymbolicFloatingPoint(eb, sb)
  }

  override val indices = listOf(eb, sb)

  val exponentBits: Int
  val significantBits: Int

  init {
    if (indices.all { index -> index is NumeralIndex }) {
      exponentBits = (eb as NumeralIndex).numeral
      significantBits = (sb as NumeralIndex).numeral

      require(exponentBits > 1)
      require(significantBits > 1)
    } else {
      exponentBits = 0
      significantBits = 0
    }
  }

  override val theories = FLOATING_POINT_MARKER_SET

  override fun equals(other: Any?): Boolean =
      when {
        this === other -> true
        other !is FPSort -> false
        else ->
            this.exponentBits == other.exponentBits && this.significantBits == other.significantBits
      }

  override fun hashCode(): Int {
    var result = super.hashCode()
    result = 31 * result + exponentBits
    result = 31 * result + significantBits
    return result
  }

  /*
  val zero = FPZero(exponentBits, significantBits)
  val minusZero = FPMinusZero(exponentBits, significantBits)
  val infinity = FPInfinity(exponentBits, significantBits)
  val minusInfinity = FPMinusInfinity(exponentBits, significantBits)
  val nan = FPNaN(exponentBits, significantBits)
  */
}

/** Standard 16-bit FloatingPoint sort */
object FP16 : FPSort(5.idx(), 11.idx())

/** Standard 32-bit FloatingPoint sort */
object FP32 : FPSort(8.idx(), 24.idx())

/** Standard 64-bit FloatingPoint sort */
object FP64 : FPSort(11.idx(), 53.idx())

/** Standard 128-bit FloatingPoint sort */
object FP128 : FPSort(15.idx(), 113.idx())

class FloatingPoint(eb: Int, sb: Int) : FPSort(eb.idx(), sb.idx())

internal class SymbolicFloatingPoint(eb: SymbolIndex, sb: SymbolIndex) : FPSort(eb, sb)

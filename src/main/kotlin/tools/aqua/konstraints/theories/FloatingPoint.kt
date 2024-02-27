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

package tools.aqua.konstraints.theories

import tools.aqua.konstraints.smt.*

/*
 * New Sorts defined by FloatingPoint theory
 */

object RoundingMode : Sort("RoundingMode")

sealed class FPBase(eb: Index, sb: Index) : Sort("FloatingPoint", listOf(eb, sb)) {
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

  override fun equals(other: Any?): Boolean =
      when {
        this === other -> true
        other !is FPBase -> false
        else ->
            this.exponentBits == other.exponentBits && this.significantBits == other.significantBits
      }
}

class FPSort private constructor(eb: Index, sb: Index) : FPBase(eb, sb) {
  companion object {
    operator fun invoke(eb: Int, sb: Int): FPSort = FPSort(NumeralIndex(eb), NumeralIndex(sb))

    fun fromSymbol(eb: String, sb: String): FPSort = FPSort(eb.idx(), sb.idx())

    fun fromSymbol(eb: SymbolIndex, sb: SymbolIndex): FPSort = FPSort(eb, sb)
  }
}

object FP16 : FPBase(5.idx(), 11.idx())

object FP32 : FPBase(8.idx(), 24.idx())

object FP64 : FPBase(11.idx(), 53.idx())

object FP128 : FPBase(15.idx(), 113.idx())

/*
 * RoundingMode functions
 */

class RoundNeareastTiesToEven : Expression<RoundingMode>() {
  override val symbol: String = "roundNearestTiesToEven"
  override val sort: RoundingMode = RoundingMode
}

class RNE : Expression<RoundingMode>() {
  override val symbol: String = "RNE"
  override val sort: RoundingMode = RoundingMode
}

class RoundNeareastTiesToAway : Expression<RoundingMode>() {
  override val symbol: String = "roundNearestTiesToAway"
  override val sort: RoundingMode = RoundingMode
}

class RNA : Expression<RoundingMode>() {
  override val symbol: String = "RNA"
  override val sort: RoundingMode = RoundingMode
}

class RoundTowardPositive : Expression<RoundingMode>() {
  override val symbol: String = "roundTowardPositive"
  override val sort: RoundingMode = RoundingMode
}

class RTP : Expression<RoundingMode>() {
  override val symbol: String = "RTP"
  override val sort: RoundingMode = RoundingMode
}

class RoundTowardNegative : Expression<RoundingMode>() {
  override val symbol: String = "roundTowardNegative"
  override val sort: RoundingMode = RoundingMode
}

class RTN : Expression<RoundingMode>() {
  override val symbol: String = "RTN"
  override val sort: RoundingMode = RoundingMode
}

class RoundTowardZero : Expression<RoundingMode>() {
  override val symbol: String = "roundTowardZero"
  override val sort: RoundingMode = RoundingMode
}

class RTZ : Expression<RoundingMode>() {
  override val symbol: String = "RTZ"
  override val sort: RoundingMode = RoundingMode
}

/*
 * Floating Point Literals
 */

class FPLiteral(eb: Int, sb: Int) : Expression<FPSort>() {
  override val symbol: String = TODO()
  override val sort: FPSort = FPSort(eb, sb)
}

/*
 * Infinity
 */

class FPInfinity(eb: Int, sb: Int) : Expression<FPSort>() {
  override val symbol: String = "(_ +oo $eb $sb)"
  override val sort: FPSort = FPSort(eb, sb)
}

class FPMinusInfinity(eb: Int, sb: Int) : Expression<FPSort>() {
  override val symbol: String = "(_ -oo $eb $sb)"
  override val sort: FPSort = FPSort(eb, sb)
}

/*
 * Zero
 */

class FPZero(eb: Int, sb: Int) : Expression<FPSort>() {
  override val symbol: String = "(_ +zero $eb $sb)"
  override val sort: FPSort = FPSort(eb, sb)
}

class FPMinusZero(eb: Int, sb: Int) : Expression<FPSort>() {
  override val symbol: String = "(_ -zero $eb $sb)"
  override val sort: FPSort = FPSort(eb, sb)
}

/*
 * NaN
 */

class FPNaN(eb: Int, sb: Int) : Expression<FPSort>() {
  override val symbol: String = "(_ NaN $eb $sb)"
  override val sort: FPSort = FPSort(eb, sb)
}

/*
 * Operators
 */

class FPAbs(inner: Expression<FPSort>) : Expression<FPSort>() {
  override val symbol: String = "(_ fp.abs $inner)"
  override val sort: FPSort = inner.sort
}

class FPNeg(inner: Expression<FPSort>) : Expression<FPSort>() {
  override val symbol: String = "(_ fp.neg $inner)"
  override val sort: FPSort = inner.sort
}

class FPAdd(lhs: Expression<FPSort>, rhs: Expression<FPSort>) : Expression<FPSort>() {
  override val symbol: String = "(_ fp.add $lhs $rhs)"
  override val sort: FPSort = lhs.sort

  init {
    // this check ensures that lhs and rhs have the same floating point format
    require(lhs.sort == rhs.sort)
  }
}

class FPSub(minuend: Expression<FPSort>, subtrahend: Expression<FPSort>) : Expression<FPSort>() {
  override val symbol: String = "(_ fp.add $minuend $subtrahend)"
  override val sort: FPSort = minuend.sort

  init {
    // this check ensures that lhs and rhs have the same floating point format
    require(minuend.sort == subtrahend.sort)
  }
}

class FPMul(multiplier: Expression<FPSort>, multiplicand: Expression<FPSort>) :
    Expression<FPSort>() {
  override val symbol: String = "(_ fp.add $multiplier $multiplicand)"
  override val sort: FPSort = multiplier.sort

  init {
    // this check ensures that lhs and rhs have the same floating point format
    require(multiplier.sort == multiplicand.sort)
  }
}

class FPDiv(dividend: Expression<FPSort>, divisor: Expression<FPSort>) : Expression<FPSort>() {
  override val symbol: String = "(_ fp.add $dividend $divisor)"
  override val sort: FPSort = dividend.sort

  init {
    // this check ensures that lhs and rhs have the same floating point format
    require(dividend.sort == divisor.sort)
  }
}

class FPFma(
    multiplier: Expression<FPSort>,
    multiplicand: Expression<FPSort>,
    summand: Expression<FPSort>
) : Expression<FPSort>() {
  override val symbol: String = "(fp.fma $multiplier $multiplicand $summand"
  override val sort: FPSort = multiplier.sort

  init {
    require(multiplier.sort == multiplicand.sort)
    require(multiplier.sort == summand.sort)
  }
}

class FPSqrt(inner: Expression<FPSort>) : Expression<FPSort>() {
  override val symbol: String = "(fp.sqrt $inner)"
  override val sort: FPSort = inner.sort
}

class FPRem(dividend: Expression<FPSort>, divisor: Expression<FPSort>) : Expression<FPSort>() {
  override val symbol: String = "(fp.rem $dividend $divisor)"
  override val sort: FPSort = dividend.sort

  init {
    require(dividend.sort == divisor.sort)
  }
}

class FPRoundToIntegral(roundingMode: Expression<RoundingMode>, inner: Expression<FPSort>) :
    Expression<FPSort>() {
  override val symbol: String = "(fp.roundToIntegral $roundingMode $inner)"
  override val sort: FPSort = inner.sort
}

class FPMin(lhs: Expression<FPSort>, rhs: Expression<FPSort>) : Expression<FPSort>() {
  override val symbol: String = "(fp.min $lhs $rhs)"
  override val sort: FPSort = lhs.sort

  init {
    require(lhs.sort == rhs.sort)
  }
}

class FPMax(lhs: Expression<FPSort>, rhs: Expression<FPSort>) : Expression<FPSort>() {
  override val symbol: String = "(fp.max $lhs $rhs)"
  override val sort: FPSort = lhs.sort

  init {
    require(lhs.sort == rhs.sort)
  }
}

class FPLeq(terms: List<Expression<FPSort>>) : Expression<BoolSort>() {
  constructor(vararg terms: Expression<FPSort>) : this(terms.toList())

  override val symbol: String = "(fp.leq ${terms.joinToString(" ")})"
  override val sort: BoolSort = BoolSort

  init {
    require(terms.size > 1)
    terms.zipWithNext { a, b -> require(a.sort == b.sort) }
  }
}

class FPLt(terms: List<Expression<FPSort>>) : Expression<BoolSort>() {
  constructor(vararg terms: Expression<FPSort>) : this(terms.toList())

  override val symbol: String = "(fp.lt ${terms.joinToString(" ")})"
  override val sort: BoolSort = BoolSort

  init {
    require(terms.size > 1)
    terms.zipWithNext { a, b -> require(a.sort == b.sort) }
  }
}

class FPGeq(terms: List<Expression<FPSort>>) : Expression<BoolSort>() {
  constructor(vararg terms: Expression<FPSort>) : this(terms.toList())

  override val symbol: String = "(fp.geq ${terms.joinToString(" ")})"
  override val sort: BoolSort = BoolSort

  init {
    require(terms.size > 1)
    terms.zipWithNext { a, b -> require(a.sort == b.sort) }
  }
}

class FPGt(terms: List<Expression<FPSort>>) : Expression<BoolSort>() {
  constructor(vararg terms: Expression<FPSort>) : this(terms.toList())

  override val symbol: String = "(fp.gt ${terms.joinToString(" ")})"
  override val sort: BoolSort = BoolSort

  init {
    require(terms.size > 1)
    terms.zipWithNext { a, b -> require(a.sort == b.sort) }
  }
}

class FPEq(terms: List<Expression<FPSort>>) : Expression<BoolSort>() {
  constructor(vararg terms: Expression<FPSort>) : this(terms.toList())

  override val symbol: String = "(fp.eq ${terms.joinToString(" ")})"
  override val sort: BoolSort = BoolSort

  init {
    require(terms.size > 1)
    terms.zipWithNext { a, b -> require(a.sort == b.sort) }
  }
}

class FPIsNormal(inner: Expression<FPSort>) : Expression<FPSort>() {
  override val symbol: String = "(fp.isNormal $inner)"
  override val sort: FPSort = inner.sort
}

class FPIsSubnormal(inner: Expression<FPSort>) : Expression<FPSort>() {
  override val symbol: String = "(fp.isSubnormal $inner)"
  override val sort: FPSort = inner.sort
}

class FPIsZero(inner: Expression<FPSort>) : Expression<FPSort>() {
  override val symbol: String = "(fp.isZero $inner)"
  override val sort: FPSort = inner.sort
}

class FPIsInfinite(inner: Expression<FPSort>) : Expression<FPSort>() {
  override val symbol: String = "(fp.isInfinite $inner)"
  override val sort: FPSort = inner.sort
}

class FPIsNaN(inner: Expression<FPSort>) : Expression<FPSort>() {
  override val symbol: String = "(fp.isNaN $inner)"
  override val sort: FPSort = inner.sort
}

class FPIsNegative(inner: Expression<FPSort>) : Expression<FPSort>() {
  override val symbol: String = "(fp.isNegative $inner)"
  override val sort: FPSort = inner.sort
}

class FPIsPositive(inner: Expression<FPSort>) : Expression<FPSort>() {
  override val symbol: String = "(fp.isPositive $inner)"
  override val sort: FPSort = inner.sort
}

/*
 * Conversion from other sorts
 */

class BitVecToFP(other: Expression<BVSort>, eb: Int, sb: Int) : Expression<FPSort>() {
  override val symbol: String = "((_ to_fp $eb $sb) $other)"
  override val sort: FPSort = FPSort(eb, sb)
}

class FPToFP(other: Expression<FPSort>, roundingMode: Expression<RoundingMode>, eb: Int, sb: Int) :
    Expression<FPSort>() {
  override val symbol: String = "((_ to_fp $eb $sb) $roundingMode $other)"
  override val sort: FPSort = FPSort(eb, sb)
}

class RealToFP(
    other: Expression<RealSort>,
    roundingMode: Expression<RoundingMode>,
    eb: Int,
    sb: Int
) : Expression<FPSort>() {
  override val symbol: String = "((_ to_fp $eb $sb) $roundingMode $other)"
  override val sort: FPSort = FPSort(eb, sb)
}

class SBitVecToFP(
    other: Expression<BVSort>,
    roundingMode: Expression<RoundingMode>,
    eb: Int,
    sb: Int
) : Expression<FPSort>() {
  override val symbol: String = "((_ to_fp $eb $sb) $roundingMode $other)"
  override val sort: FPSort = FPSort(eb, sb)
}

class UBitVecToFP(
    other: Expression<BVSort>,
    roundingMode: Expression<RoundingMode>,
    eb: Int,
    sb: Int
) : Expression<FPSort>() {
  override val symbol: String = "((_ to_fp $eb $sb) $roundingMode $other)"
  override val sort: FPSort = FPSort(eb, sb)
}

/*
 * Conversion to other sorts
 */

class FPToUBitVec(other: Expression<FPSort>, roundingMode: Expression<RoundingMode>, m: Int) :
    Expression<BVSort>() {
  override val symbol: String = "((_ fp.to_ubv $m) $roundingMode $other)"
  override val sort: BVSort = BVSort(m)
}

class FPToSBitVec(other: Expression<FPSort>, roundingMode: Expression<RoundingMode>, m: Int) :
    Expression<BVSort>() {
  override val symbol: String = "((_ fp.to_sbv $m) $roundingMode $other)"
  override val sort: BVSort = BVSort(m)
}

class FPToReal(other: Expression<FPSort>) : Expression<RealSort>() {
  override val symbol: String = "(fp.to_real $other)"
  override val sort: RealSort = RealSort
}

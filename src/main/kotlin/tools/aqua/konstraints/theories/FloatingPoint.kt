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

import tools.aqua.konstraints.parser.*
import tools.aqua.konstraints.parser.SortDecl
import tools.aqua.konstraints.smt.*

internal object FloatingPointContext : TheoryContext {
  override val functions: HashSet<FunctionDecl<*>> =
      hashSetOf(
          RoundNearestTiesToEvenDecl,
          RNEDecl,
          RoundNearestTiesToAwayDecl,
          RNADecl,
          RoundTowardPositiveDecl,
          RTPDecl,
          RoundTowardNegativeDecl,
          RTNDecl,
          RoundTowardZeroDecl,
          RTZDecl,
          FPLiteralDecl,
          FPInfinityDecl,
          FPMinusInfinityDecl,
          FPZeroDecl,
          FPMinusZeroDecl,
          FPNaNDecl,
          FPAbsDecl,
          FPNegDecl,
          FPAddDecl,
          FPSubDecl,
          FPMulDecl,
          FPDivDecl,
          FPFmaDecl,
          FPSqrtDecl,
          FPRemDecl,
          FPRoundToIntegralDecl,
          FPMinDecl,
          FPMaxDecl,
          FPLeqDecl,
          FPLtDecl,
          FPGeqDecl,
          FPGtDecl,
          FPEqDecl,
          FPIsNormalDecl,
          FPIsSubormalDecl,
          FPIsZeroDecl,
          FPIsInfiniteDecl,
          FPIsNaNDecl,
          FPIsNegativeDecl,
          FPIsPositiveDecl,
          BitVecToFPDecl,
          FPToFPDecl,
          RealToFPDecl,
          SBitVecToFPDecl,
          UBitVecToFPDecl,
          FPToUBitVecDecl,
          FPToSBitVecDecl,
          FPToRealDecl)

  override val sorts: Map<String, SortDecl<*>> =
      mapOf(
          Pair("RoundingMode", RoundingModeDecl),
          Pair("Real", RealSortDecl),
          Pair("Float16", FP16Decl),
          Pair("Float32", FP32Decl),
          Pair("Float64", FP64Decl),
          Pair("Float128", FP128Decl),
          Pair("BitVec", BVSortDecl),
          Pair("FloatingPoint", FPSortDecl))
}

/*
 * New Sorts defined by FloatingPoint theory
 */

object RoundingMode : Sort("RoundingMode")

internal object RoundingModeDecl :
    SortDecl<RoundingMode>("RoundingMode".symbol(), emptySet(), emptySet()) {
  override fun getSort(bindings: Bindings): RoundingMode = RoundingMode
}

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

  override fun hashCode(): Int {
    var result = super.hashCode()
    result = 31 * result + exponentBits
    result = 31 * result + significantBits
    return result
  }
}

class FPSort private constructor(eb: Index, sb: Index) : FPBase(eb, sb) {
  companion object {
    operator fun invoke(eb: Int, sb: Int): FPSort = FPSort(NumeralIndex(eb), NumeralIndex(sb))

    operator fun invoke(eb: SymbolIndex, sb: SymbolIndex): FPSort = FPSort(eb, sb)

    fun fromSymbol(eb: String, sb: String): FPSort = FPSort(eb.idx(), sb.idx())

    fun fromSymbol(eb: SymbolIndex, sb: SymbolIndex): FPSort = FPSort(eb, sb)
  }
}

internal object FPSortDecl :
    SortDecl<FPSort>("FloatingPoint".symbol(), emptySet(), setOf("eb".idx(), "sb".idx())) {
  override fun getSort(bindings: Bindings): FPSort =
      FPSort(bindings["eb"].numeral, bindings["sb"].numeral)
}

object FP16 : FPBase(5.idx(), 11.idx())

internal object FP16Decl : SortDecl<FPSort>("Float16".symbol(), emptySet(), emptySet()) {
  override fun getSort(bindings: Bindings): FPSort = FPSort(5, 11)
}

object FP32 : FPBase(8.idx(), 24.idx())

internal object FP32Decl : SortDecl<FPSort>("Float32".symbol(), emptySet(), emptySet()) {
  override fun getSort(bindings: Bindings): FPSort = FPSort(8, 24)
}

object FP64 : FPBase(11.idx(), 53.idx())

internal object FP64Decl : SortDecl<FPSort>("Float64".symbol(), emptySet(), emptySet()) {
  override fun getSort(bindings: Bindings): FPSort = FPSort(11, 53)
}

object FP128 : FPBase(15.idx(), 113.idx())

internal object FP128Decl : SortDecl<FPSort>("Float128".symbol(), emptySet(), emptySet()) {
  override fun getSort(bindings: Bindings): FPSort = FPSort(15, 113)
}

/*
 * RoundingMode functions
 */

class RoundNearestTiesToEven : Expression<RoundingMode>() {
  override val symbol: Symbol = "roundNearestTiesToEven".symbol()
  override val sort: RoundingMode = RoundingMode
}

object RoundNearestTiesToEvenDecl :
    FunctionDecl0<RoundingMode>(
        "roundNearestTiesToEven".symbol(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> =
      RoundNearestTiesToEven()
}

class RNE : Expression<RoundingMode>() {
  override val symbol: Symbol = "RNE".symbol()
  override val sort: RoundingMode = RoundingMode
}

object RNEDecl : FunctionDecl0<RoundingMode>("RNE".symbol(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RNE()
}

class RoundNearestTiesToAway : Expression<RoundingMode>() {
  override val symbol: Symbol = "roundNearestTiesToAway".symbol()
  override val sort: RoundingMode = RoundingMode
}

object RoundNearestTiesToAwayDecl :
    FunctionDecl0<RoundingMode>(
        "roundNearestTiesToAway".symbol(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> =
      RoundNearestTiesToAway()
}

class RNA : Expression<RoundingMode>() {
  override val symbol: Symbol = "RNA".symbol()
  override val sort: RoundingMode = RoundingMode
}

object RNADecl : FunctionDecl0<RoundingMode>("RNA".symbol(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RNA()
}

class RoundTowardPositive : Expression<RoundingMode>() {
  override val symbol: Symbol = "roundTowardPositive".symbol()
  override val sort: RoundingMode = RoundingMode
}

object RoundTowardPositiveDecl :
    FunctionDecl0<RoundingMode>(
        "roundTowardPositive".symbol(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RoundTowardPositive()
}

class RTP : Expression<RoundingMode>() {
  override val symbol: Symbol = "RTP".symbol()
  override val sort: RoundingMode = RoundingMode
}

object RTPDecl : FunctionDecl0<RoundingMode>("RTP".symbol(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RTP()
}

class RoundTowardNegative : Expression<RoundingMode>() {
  override val symbol: Symbol = "roundTowardNegative".symbol()
  override val sort: RoundingMode = RoundingMode
}

object RoundTowardNegativeDecl :
    FunctionDecl0<RoundingMode>(
        "RoundTowardNegative".symbol(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RoundTowardNegative()
}

class RTN : Expression<RoundingMode>() {
  override val symbol: Symbol = "RTN".symbol()
  override val sort: RoundingMode = RoundingMode
}

object RTNDecl : FunctionDecl0<RoundingMode>("RTN".symbol(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RTN()
}

class RoundTowardZero : Expression<RoundingMode>() {
  override val symbol: Symbol = "roundTowardZero".symbol()
  override val sort: RoundingMode = RoundingMode
}

object RoundTowardZeroDecl :
    FunctionDecl0<RoundingMode>("RoundTowardZero".symbol(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RoundTowardZero()
}

class RTZ : Expression<RoundingMode>() {
  override val symbol: Symbol = "RTZ".symbol()
  override val sort: RoundingMode = RoundingMode
}

object RTZDecl : FunctionDecl0<RoundingMode>("RTZ".symbol(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RTZ()
}

/*
 * Floating Point Literals
 */

data class FPLiteral(val eb: Int, val sb: Int, val value: Float) : Expression<FPSort>() {
  override val symbol: Symbol = TODO()
  override val sort: FPSort = FPSort(eb, sb)
}

object FPLiteralDecl :
    FunctionDecl3<BVSort, BVSort, BVSort, FPSort>(
        "fp".symbol(),
        emptySet(),
        BVSort(1),
        BVSort.fromSymbol("eb"),
        BVSort.fromSymbol("i"),
        emptySet(),
        setOf("eb".idx(), "i".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<BVSort>,
      param2: Expression<BVSort>,
      param3: Expression<BVSort>,
      bindings: Bindings
  ): Expression<FPSort> {
    return FPLiteral(bindings["eb"].numeral, bindings["i"].numeral + 1, 0.0f)
  }
}

/*
 * Infinity
 */

class FPInfinity(val eb: Int, val sb: Int) : Expression<FPSort>() {
  override val symbol: Symbol = "+oo".symbol()
  override val sort: FPSort = FPSort(eb, sb)

  override fun toString(): String = "(_ +oo $eb $sb)"
}

object FPInfinityDecl :
    FunctionDecl0<FPSort>(
        "+oo".symbol(), emptySet(), setOf("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(bindings: Bindings): Expression<FPSort> =
      FPInfinity(bindings["eb"].numeral, bindings["sb"].numeral)
}

class FPMinusInfinity(val eb: Int, val sb: Int) : Expression<FPSort>() {
  override val symbol: Symbol = "-oo".symbol()
  override val sort: FPSort = FPSort(eb, sb)

  override fun toString(): String = "(_ -oo $eb $sb)"
}

object FPMinusInfinityDecl :
    FunctionDecl0<FPSort>(
        "-oo".symbol(), emptySet(), setOf("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(bindings: Bindings): Expression<FPSort> =
      FPMinusInfinity(bindings["eb"].numeral, bindings["sb"].numeral)
}

/*
 * Zero
 */

class FPZero(val eb: Int, val sb: Int) : Expression<FPSort>() {
  override val symbol: Symbol = "+zero".symbol()
  override val sort: FPSort = FPSort(eb, sb)

  override fun toString(): String = "(_ +zero $eb $sb)"
}

object FPZeroDecl :
    FunctionDecl0<FPSort>(
        "+zero".symbol(),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(bindings: Bindings): Expression<FPSort> =
      FPZero(bindings["eb"].numeral, bindings["sb"].numeral)
}

class FPMinusZero(val eb: Int, val sb: Int) : Expression<FPSort>() {
  override val symbol: Symbol = "-zero".symbol()
  override val sort: FPSort = FPSort(eb, sb)

  override fun toString(): String = "(_ -zero $eb $sb)"
}

object FPMinusZeroDecl :
    FunctionDecl0<FPSort>(
        "-zero".symbol(),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(bindings: Bindings): Expression<FPSort> =
      FPMinusZero(bindings["eb"].numeral, bindings["sb"].numeral)
}

/*
 * NaN
 */

class FPNaN(val eb: Int, val sb: Int) : Expression<FPSort>() {
  override val symbol: Symbol = "NaN".symbol()
  override val sort: FPSort = FPSort(eb, sb)

  override fun toString(): String = "(_ NaN $eb $sb)"
}

object FPNaNDecl :
    FunctionDecl0<FPSort>(
        "NaN".symbol(), emptySet(), setOf("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(bindings: Bindings): Expression<FPSort> =
      FPNaN(bindings["eb"].numeral, bindings["sb"].numeral)
}

/*
 * Operators
 */

class FPAbs(val inner: Expression<FPSort>) : Expression<FPSort>() {
  override val symbol: Symbol = "fp.abs".symbol()
  override val sort: FPSort = inner.sort

  override fun toString(): String = "(fp.abs $inner)"
}

object FPAbsDecl :
    FunctionDecl1<FPSort, FPSort>(
        "fp.abs".symbol(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(param: Expression<FPSort>, bindings: Bindings): Expression<FPSort> =
      FPAbs(param)
}

class FPNeg(val inner: Expression<FPSort>) : Expression<FPSort>() {
  override val symbol: Symbol = "fp.neg".symbol()
  override val sort: FPSort = inner.sort

  override fun toString(): String = "(fp.neg $inner)"
}

object FPNegDecl :
    FunctionDecl1<FPSort, FPSort>(
        "fp.abs".symbol(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(param: Expression<FPSort>, bindings: Bindings): Expression<FPSort> =
      FPNeg(param)
}

class FPAdd(
    val roundingMode: Expression<RoundingMode>,
    val lhs: Expression<FPSort>,
    val rhs: Expression<FPSort>
) : Expression<FPSort>() {
  override val symbol: Symbol = "fp.add".symbol()
  override val sort: FPSort = lhs.sort

  init {
    // this check ensures that lhs and rhs have the same floating point format
    require(lhs.sort == rhs.sort)
  }

  override fun toString(): String = "(fp.add $lhs $rhs)"
}

object FPAddDecl :
    FunctionDecl3<RoundingMode, FPSort, FPSort, FPSort>(
        "fp.add".symbol(),
        emptySet(),
        RoundingMode,
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<RoundingMode>,
      param2: Expression<FPSort>,
      param3: Expression<FPSort>,
      bindings: Bindings
  ): Expression<FPSort> = FPAdd(param1, param2, param3)
}

class FPSub(
    val roundingMode: Expression<RoundingMode>,
    val minuend: Expression<FPSort>,
    val subtrahend: Expression<FPSort>
) : Expression<FPSort>() {
  override val symbol: Symbol = "fp.sub".symbol()
  override val sort: FPSort = minuend.sort

  init {
    // this check ensures that lhs and rhs have the same floating point format
    require(minuend.sort == subtrahend.sort)
  }

  override fun toString(): String = "(fp.sub $minuend $subtrahend)"
}

object FPSubDecl :
    FunctionDecl3<RoundingMode, FPSort, FPSort, FPSort>(
        "fp.sub".symbol(),
        emptySet(),
        RoundingMode,
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<RoundingMode>,
      param2: Expression<FPSort>,
      param3: Expression<FPSort>,
      bindings: Bindings
  ): Expression<FPSort> = FPSub(param1, param2, param3)
}

class FPMul(
    val roundingMode: Expression<RoundingMode>,
    val multiplier: Expression<FPSort>,
    val multiplicand: Expression<FPSort>
) : Expression<FPSort>() {
  override val symbol: Symbol = "fp.mul".symbol()
  override val sort: FPSort = multiplier.sort

  init {
    // this check ensures that lhs and rhs have the same floating point format
    require(multiplier.sort == multiplicand.sort)
  }

  override fun toString(): String = "(fp.mul $multiplier $multiplicand)"
}

object FPMulDecl :
    FunctionDecl3<RoundingMode, FPSort, FPSort, FPSort>(
        "fp.mul".symbol(),
        emptySet(),
        RoundingMode,
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<RoundingMode>,
      param2: Expression<FPSort>,
      param3: Expression<FPSort>,
      bindings: Bindings
  ): Expression<FPSort> = FPMul(param1, param2, param3)
}

class FPDiv(
    val roundingMode: Expression<RoundingMode>,
    val dividend: Expression<FPSort>,
    val divisor: Expression<FPSort>
) : Expression<FPSort>() {
  override val symbol: Symbol = "fp.div".symbol()
  override val sort: FPSort = dividend.sort

  init {
    // this check ensures that lhs and rhs have the same floating point format
    require(dividend.sort == divisor.sort)
  }

  override fun toString(): String = "(fp.div $dividend $divisor)"
}

object FPDivDecl :
    FunctionDecl3<RoundingMode, FPSort, FPSort, FPSort>(
        "fp.div".symbol(),
        emptySet(),
        RoundingMode,
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<RoundingMode>,
      param2: Expression<FPSort>,
      param3: Expression<FPSort>,
      bindings: Bindings
  ): Expression<FPSort> = FPDiv(param1, param2, param3)
}

class FPFma(
    val roundingMode: Expression<RoundingMode>,
    val multiplier: Expression<FPSort>,
    val multiplicand: Expression<FPSort>,
    val summand: Expression<FPSort>
) : Expression<FPSort>() {
  override val symbol: Symbol = "fp.fma".symbol()
  override val sort: FPSort = multiplier.sort

  init {
    require(multiplier.sort == multiplicand.sort)
    require(multiplier.sort == summand.sort)
  }

  override fun toString(): String = "(fp.fma $multiplier $multiplicand $summand)"
}

object FPFmaDecl :
    FunctionDecl4<RoundingMode, FPSort, FPSort, FPSort, FPSort>(
        "fp.div".symbol(),
        emptySet(),
        RoundingMode,
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<RoundingMode>,
      param2: Expression<FPSort>,
      param3: Expression<FPSort>,
      param4: Expression<FPSort>,
      bindings: Bindings
  ): Expression<FPSort> = FPFma(param1, param2, param3, param4)
}

class FPSqrt(val roundingMode: Expression<RoundingMode>, val inner: Expression<FPSort>) :
    Expression<FPSort>() {
  override val symbol: Symbol = "fp.sqrt".symbol()
  override val sort: FPSort = inner.sort

  override fun toString(): String = "(fp.sqrt $inner)"
}

object FPSqrtDecl :
    FunctionDecl2<RoundingMode, FPSort, FPSort>(
        "fp.sqrt".symbol(),
        emptySet(),
        RoundingMode,
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<RoundingMode>,
      param2: Expression<FPSort>,
      bindings: Bindings
  ): Expression<FPSort> = FPSqrt(param1, param2)
}

class FPRem(val dividend: Expression<FPSort>, val divisor: Expression<FPSort>) :
    Expression<FPSort>() {
  override val symbol: Symbol = "fp.rem".symbol()
  override val sort: FPSort = dividend.sort

  init {
    require(dividend.sort == divisor.sort)
  }

  override fun toString(): String = "(fp.rem $dividend $divisor)"
}

object FPRemDecl :
    FunctionDecl2<FPSort, FPSort, FPSort>(
        "fp.rem".symbol(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<FPSort>,
      param2: Expression<FPSort>,
      bindings: Bindings
  ): Expression<FPSort> = FPRem(param1, param2)
}

class FPRoundToIntegral(val roundingMode: Expression<RoundingMode>, val inner: Expression<FPSort>) :
    Expression<FPSort>() {
  override val symbol: Symbol = "fp.roundToIntegral".symbol()
  override val sort: FPSort = inner.sort

  override fun toString(): String = "(fp.roundToIntegral $roundingMode $inner)"
}

object FPRoundToIntegralDecl :
    FunctionDecl2<RoundingMode, FPSort, FPSort>(
        "fp.roundToIntegral".symbol(),
        emptySet(),
        RoundingMode,
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<RoundingMode>,
      param2: Expression<FPSort>,
      bindings: Bindings
  ): Expression<FPSort> = FPRoundToIntegral(param1, param2)
}

class FPMin(val lhs: Expression<FPSort>, val rhs: Expression<FPSort>) : Expression<FPSort>() {
  override val symbol: Symbol = "fp.min".symbol()
  override val sort: FPSort = lhs.sort

  init {
    require(lhs.sort == rhs.sort)
  }

  override fun toString(): String = "(fp.min $lhs $rhs)"
}

object FPMinDecl :
    FunctionDecl2<FPSort, FPSort, FPSort>(
        "fp.min".symbol(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<FPSort>,
      param2: Expression<FPSort>,
      bindings: Bindings
  ): Expression<FPSort> = FPMin(param1, param2)
}

class FPMax(val lhs: Expression<FPSort>, val rhs: Expression<FPSort>) : Expression<FPSort>() {
  override val symbol: Symbol = "fp.max".symbol()
  override val sort: FPSort = lhs.sort

  init {
    require(lhs.sort == rhs.sort)
  }

  override fun toString(): String = "(fp.max $lhs $rhs)"
}

object FPMaxDecl :
    FunctionDecl2<FPSort, FPSort, FPSort>(
        "fp.max".symbol(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<FPSort>,
      param2: Expression<FPSort>,
      bindings: Bindings
  ): Expression<FPSort> = FPMin(param1, param2)
}

class FPLeq(val terms: List<Expression<FPSort>>) : Expression<BoolSort>() {
  constructor(vararg terms: Expression<FPSort>) : this(terms.toList())

  override val symbol: Symbol = "fp.leq".symbol()
  override val sort: BoolSort = BoolSort

  init {
    require(terms.size > 1)
    terms.zipWithNext { a, b -> require(a.sort == b.sort) }
  }

  override fun toString(): String = "(fp.leq ${terms.joinToString(" ")})"
}

object FPLeqDecl :
    FunctionDeclChainable<FPSort>(
        "fp.leq".symbol(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      varargs: List<Expression<FPSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = FPLeq(varargs)
}

class FPLt(val terms: List<Expression<FPSort>>) : Expression<BoolSort>() {
  constructor(vararg terms: Expression<FPSort>) : this(terms.toList())

  override val symbol: Symbol = "fp.lt".symbol()
  override val sort: BoolSort = BoolSort

  init {
    require(terms.size > 1)
    terms.zipWithNext { a, b -> require(a.sort == b.sort) }
  }

  override fun toString(): String = "(fp.lt ${terms.joinToString(" ")})"
}

object FPLtDecl :
    FunctionDeclChainable<FPSort>(
        "fp.lt".symbol(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      varargs: List<Expression<FPSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = FPLt(varargs)
}

class FPGeq(val terms: List<Expression<FPSort>>) : Expression<BoolSort>() {
  constructor(vararg terms: Expression<FPSort>) : this(terms.toList())

  override val symbol: Symbol = "fp.geq".symbol()
  override val sort: BoolSort = BoolSort

  init {
    require(terms.size > 1)
    terms.zipWithNext { a, b -> require(a.sort == b.sort) }
  }

  override fun toString(): String = "(fp.geq ${terms.joinToString(" ")})"
}

object FPGeqDecl :
    FunctionDeclChainable<FPSort>(
        "fp.geq".symbol(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      varargs: List<Expression<FPSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = FPGeq(varargs)
}

class FPGt(val terms: List<Expression<FPSort>>) : Expression<BoolSort>() {
  constructor(vararg terms: Expression<FPSort>) : this(terms.toList())

  override val symbol: Symbol = "fp.gt".symbol()
  override val sort: BoolSort = BoolSort

  init {
    require(terms.size > 1)
    terms.zipWithNext { a, b -> require(a.sort == b.sort) }
  }

  override fun toString(): String = "(fp.gt ${terms.joinToString(" ")})"
}

object FPGtDecl :
    FunctionDeclChainable<FPSort>(
        "fp.gt".symbol(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      varargs: List<Expression<FPSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = FPGt(varargs)
}

class FPEq(val terms: List<Expression<FPSort>>) : Expression<BoolSort>() {
  constructor(vararg terms: Expression<FPSort>) : this(terms.toList())

  override val symbol: Symbol = "fp.eq".symbol()
  override val sort: BoolSort = BoolSort

  init {
    require(terms.size > 1)
    terms.zipWithNext { a, b -> require(a.sort == b.sort) }
  }

  override fun toString(): String = "(fp.eq ${terms.joinToString(" ")})"
}

object FPEqDecl :
    FunctionDeclChainable<FPSort>(
        "fp.eq".symbol(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      varargs: List<Expression<FPSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = FPEq(varargs)
}

class FPIsNormal(val inner: Expression<FPSort>) : Expression<BoolSort>() {
  override val symbol: Symbol = "fp.isNormal".symbol()
  override val sort: BoolSort = BoolSort

  override fun toString(): String = "(fp.isNormal $inner)"
}

object FPIsNormalDecl :
    FunctionDecl1<FPSort, BoolSort>(
        "fp.isNormal".symbol(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        BoolSort) {
  override fun buildExpression(
      param: Expression<FPSort>,
      bindings: Bindings
  ): Expression<BoolSort> = FPIsNormal(param)
}

class FPIsSubnormal(val inner: Expression<FPSort>) : Expression<BoolSort>() {
  override val symbol: Symbol = "fp.isSubnormal".symbol()
  override val sort: BoolSort = BoolSort

  override fun toString(): String = "(fp.isSubnormal $inner)"
}

object FPIsSubormalDecl :
    FunctionDecl1<FPSort, BoolSort>(
        "fp.isSubormal".symbol(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        BoolSort) {
  override fun buildExpression(
      param: Expression<FPSort>,
      bindings: Bindings
  ): Expression<BoolSort> = FPIsSubnormal(param)
}

class FPIsZero(val inner: Expression<FPSort>) : Expression<BoolSort>() {
  override val symbol: Symbol = "fp.isZero".symbol()
  override val sort: BoolSort = BoolSort

  override fun toString(): String = "(fp.isZero $inner)"
}

object FPIsZeroDecl :
    FunctionDecl1<FPSort, BoolSort>(
        "fp.isZero".symbol(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        BoolSort) {
  override fun buildExpression(
      param: Expression<FPSort>,
      bindings: Bindings
  ): Expression<BoolSort> = FPIsZero(param)
}

class FPIsInfinite(val inner: Expression<FPSort>) : Expression<BoolSort>() {
  override val symbol: Symbol = "fp.isInfinite".symbol()
  override val sort: BoolSort = BoolSort

  override fun toString(): String = "(fp.isInfinite $inner)"
}

object FPIsInfiniteDecl :
    FunctionDecl1<FPSort, BoolSort>(
        "fp.isInfinite".symbol(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        BoolSort) {
  override fun buildExpression(
      param: Expression<FPSort>,
      bindings: Bindings
  ): Expression<BoolSort> = FPIsInfinite(param)
}

class FPIsNaN(val inner: Expression<FPSort>) : Expression<BoolSort>() {
  override val symbol: Symbol = "fp.isNaN".symbol()
  override val sort: BoolSort = BoolSort

  override fun toString(): String = "(fp.isNaN $inner)"
}

object FPIsNaNDecl :
    FunctionDecl1<FPSort, BoolSort>(
        "fp.isNan".symbol(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        BoolSort) {
  override fun buildExpression(
      param: Expression<FPSort>,
      bindings: Bindings
  ): Expression<BoolSort> = FPIsNaN(param)
}

class FPIsNegative(val inner: Expression<FPSort>) : Expression<BoolSort>() {
  override val symbol: Symbol = "fp.isNegative".symbol()
  override val sort: BoolSort = BoolSort

  override fun toString(): String = "(fp.isNegative $inner)"
}

object FPIsNegativeDecl :
    FunctionDecl1<FPSort, BoolSort>(
        "fp.isNegative".symbol(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        BoolSort) {
  override fun buildExpression(
      param: Expression<FPSort>,
      bindings: Bindings
  ): Expression<BoolSort> = FPIsNegative(param)
}

class FPIsPositive(val inner: Expression<FPSort>) : Expression<BoolSort>() {
  override val symbol: Symbol = "fp.isPositive".symbol()
  override val sort: BoolSort = BoolSort

  override fun toString(): String = "(fp.isPositive $inner)"
}

object FPIsPositiveDecl :
    FunctionDecl1<FPSort, BoolSort>(
        "fp.isPositive".symbol(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        BoolSort) {
  override fun buildExpression(
      param: Expression<FPSort>,
      bindings: Bindings
  ): Expression<BoolSort> = FPIsPositive(param)
}

/*
 * Conversion from other sorts
 */

class BitVecToFP(val inner: Expression<BVSort>, val eb: Int, val sb: Int) : Expression<FPSort>() {
  override val symbol: Symbol = "to_fp".symbol()
  override val sort: FPSort = FPSort(eb, sb)

  override fun toString(): String = "((_ to_fp $eb $sb) $inner)"
}

object BitVecToFPDecl :
    FunctionDecl1<BVSort, FPSort>(
        "to_fp".symbol(),
        emptySet(),
        BVSort.fromSymbol("m"),
        setOf("eb".idx(), "sb".idx()),
        setOf("m".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(param: Expression<BVSort>, bindings: Bindings): Expression<FPSort> =
      BitVecToFP(param, bindings["eb"].numeral, bindings["sb"].numeral)
}

class FPToFP(
    val roundingMode: Expression<RoundingMode>,
    val inner: Expression<FPSort>,
    val eb: Int,
    val sb: Int
) : Expression<FPSort>() {
  override val symbol: Symbol = "to_fp".symbol()
  override val sort: FPSort = FPSort(eb, sb)

  override fun toString(): String = "((_ to_fp $eb $sb) $roundingMode $inner)"
}

object FPToFPDecl :
    FunctionDecl2<RoundingMode, FPSort, FPSort>(
        "to_fp".symbol(),
        emptySet(),
        RoundingMode,
        FPSort("mb".idx(), "nb".idx()),
        setOf("eb".idx(), "sb".idx()),
        setOf("mb".idx(), "nb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<RoundingMode>,
      param2: Expression<FPSort>,
      bindings: Bindings
  ): Expression<FPSort> = FPToFP(param1, param2, bindings["eb"].numeral, bindings["sb"].numeral)
}

class RealToFP(
    val roundingMode: Expression<RoundingMode>,
    val inner: Expression<RealSort>,
    val eb: Int,
    val sb: Int
) : Expression<FPSort>() {
  override val symbol: Symbol = "to_fp".symbol()
  override val sort: FPSort = FPSort(eb, sb)

  override fun toString(): String = "((_ to_fp $eb $sb) $roundingMode $inner)"
}

object RealToFPDecl :
    FunctionDecl2<RoundingMode, RealSort, FPSort>(
        "to_fp".symbol(),
        emptySet(),
        RoundingMode,
        RealSort,
        setOf("eb".idx(), "sb".idx()),
        emptySet(),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<RoundingMode>,
      param2: Expression<RealSort>,
      bindings: Bindings
  ): Expression<FPSort> = RealToFP(param1, param2, bindings["eb"].numeral, bindings["sb"].numeral)
}

class SBitVecToFP(
    val roundingMode: Expression<RoundingMode>,
    val inner: Expression<BVSort>,
    val eb: Int,
    val sb: Int
) : Expression<FPSort>() {
  override val symbol: Symbol = "to_fp".symbol()
  override val sort: FPSort = FPSort(eb, sb)

  override fun toString(): String = "((_ to_fp $eb $sb) $roundingMode $inner)"
}

object SBitVecToFPDecl :
    FunctionDecl2<RoundingMode, BVSort, FPSort>(
        "to_fp".symbol(),
        emptySet(),
        RoundingMode,
        BVSort.fromSymbol("m"),
        setOf("eb".idx(), "sb".idx()),
        setOf("m".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<RoundingMode>,
      param2: Expression<BVSort>,
      bindings: Bindings
  ): Expression<FPSort> =
      SBitVecToFP(param1, param2, bindings["eb"].numeral, bindings["sb"].numeral)
}

class UBitVecToFP(
    val roundingMode: Expression<RoundingMode>,
    val inner: Expression<BVSort>,
    val eb: Int,
    val sb: Int
) : Expression<FPSort>() {
  override val symbol: Symbol = "to_fp_unsigned".symbol()
  override val sort: FPSort = FPSort(eb, sb)

  override fun toString(): String = "((_ to_fp_unsigned $eb $sb) $roundingMode $inner)"
}

object UBitVecToFPDecl :
    FunctionDecl2<RoundingMode, BVSort, FPSort>(
        "to_fp_unsigned".symbol(),
        emptySet(),
        RoundingMode,
        BVSort.fromSymbol("m"),
        setOf("eb".idx(), "sb".idx()),
        setOf("m".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<RoundingMode>,
      param2: Expression<BVSort>,
      bindings: Bindings
  ): Expression<FPSort> =
      UBitVecToFP(param1, param2, bindings["eb"].numeral, bindings["sb"].numeral)
}

/*
 * Conversion to other sorts
 */

class FPToUBitVec(
    val roundingMode: Expression<RoundingMode>,
    val inner: Expression<FPSort>,
    val m: Int
) : Expression<BVSort>() {
  override val symbol: Symbol = "fp.to_ubv".symbol()
  override val sort: BVSort = BVSort(m)

  override fun toString(): String = "((_ fp.to_ubv $m) $roundingMode $inner)"
}

object FPToUBitVecDecl :
    FunctionDecl2<RoundingMode, FPSort, BVSort>(
        "fp.to_ubv".symbol(),
        emptySet(),
        RoundingMode,
        FPSort("eb".idx(), "sb".idx()),
        setOf("m".idx()),
        setOf("eb".idx(), "sb".idx()),
        BVSort.fromSymbol("m")) {
  override fun buildExpression(
      param1: Expression<RoundingMode>,
      param2: Expression<FPSort>,
      bindings: Bindings
  ): Expression<BVSort> = FPToUBitVec(param1, param2, bindings["m"].numeral)
}

class FPToSBitVec(
    val roundingMode: Expression<RoundingMode>,
    val inner: Expression<FPSort>,
    val m: Int
) : Expression<BVSort>() {
  override val symbol: Symbol = "fp.to_sbv".symbol()
  override val sort: BVSort = BVSort(m)

  override fun toString(): String = "((_ fp.to_sbv $m) $roundingMode $inner)"
}

object FPToSBitVecDecl :
    FunctionDecl2<RoundingMode, FPSort, BVSort>(
        "fp.to_ubv".symbol(),
        emptySet(),
        RoundingMode,
        FPSort("eb".idx(), "sb".idx()),
        setOf("m".idx()),
        setOf("eb".idx(), "sb".idx()),
        BVSort.fromSymbol("m")) {
  override fun buildExpression(
      param1: Expression<RoundingMode>,
      param2: Expression<FPSort>,
      bindings: Bindings
  ): Expression<BVSort> = FPToSBitVec(param1, param2, bindings["m"].numeral)
}

class FPToReal(val inner: Expression<FPSort>) : Expression<RealSort>() {
  override val symbol: Symbol = "fp.to_real".symbol()
  override val sort: RealSort = RealSort

  override fun toString(): String = "(fp.to_real $inner)"
}

object FPToRealDecl :
    FunctionDecl1<FPSort, RealSort>(
        "fp.to_real".symbol(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        RealSort) {
  override fun buildExpression(
      param: Expression<FPSort>,
      bindings: Bindings
  ): Expression<RealSort> = FPToReal(param)
}

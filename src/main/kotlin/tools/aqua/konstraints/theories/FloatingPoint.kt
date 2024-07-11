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

/** FloatingPoint theory object */
object FloatingPointTheory : Theory {
  override val functions =
      listOf(
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
          .associateBy { it.name.toString() }

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

/** RoundingMode sort object */
object RoundingMode : Sort("RoundingMode")

/** RoundíngMode sort declaration object */
internal object RoundingModeDecl :
    SortDecl<RoundingMode>("RoundingMode".symbol(), emptySet(), emptySet()) {
  override fun getSort(bindings: Bindings): RoundingMode = RoundingMode
}

/**
 * Baseclass of all FloatingPoint sorts
 *
 * (_ FloatingPoint eb sb)
 *
 * @param eb: exponent bits
 * @param sb: significant bits
 */
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

/**
 * FloatingPoint sort with any positive number of bits
 *
 * (_ FloatingPoint eb sb)
 *
 * @param eb exponent bits
 * @param sb significant bits
 */
class FPSort private constructor(eb: Index, sb: Index) : FPBase(eb, sb) {
  companion object {
    operator fun invoke(eb: Int, sb: Int): FPSort = FPSort(NumeralIndex(eb), NumeralIndex(sb))

    operator fun invoke(eb: SymbolIndex, sb: SymbolIndex): FPSort = FPSort(eb, sb)

    fun fromSymbol(eb: String, sb: String): FPSort = FPSort(eb.idx(), sb.idx())

    fun fromSymbol(eb: SymbolIndex, sb: SymbolIndex): FPSort = FPSort(eb, sb)
  }
}

/** FloatingPoint sort declaration object */
internal object FPSortDecl :
    SortDecl<FPSort>("FloatingPoint".symbol(), emptySet(), setOf("eb".idx(), "sb".idx())) {
  override fun getSort(bindings: Bindings): FPSort =
      FPSort(bindings["eb"].numeral, bindings["sb"].numeral)
}

/** Standard 16-bit FloatingPoint sort */
object FP16 : FPBase(5.idx(), 11.idx())

/** 16-bit FloatingPoint declaration object */
internal object FP16Decl : SortDecl<FPSort>("Float16".symbol(), emptySet(), emptySet()) {
  override fun getSort(bindings: Bindings): FPSort = FPSort(5, 11)
}

/** Standard 32-bit FloatingPoint sort */
object FP32 : FPBase(8.idx(), 24.idx())

/** 32-bit FloatingPoint declaration object */
internal object FP32Decl : SortDecl<FPSort>("Float32".symbol(), emptySet(), emptySet()) {
  override fun getSort(bindings: Bindings): FPSort = FPSort(8, 24)
}

/** Standard 64-bit FloatingPoint sort */
object FP64 : FPBase(11.idx(), 53.idx())

/** 64-bit FloatingPoint declaration object */
internal object FP64Decl : SortDecl<FPSort>("Float64".symbol(), emptySet(), emptySet()) {
  override fun getSort(bindings: Bindings): FPSort = FPSort(11, 53)
}

/** Standard 128-bit FloatingPoint sort */
object FP128 : FPBase(15.idx(), 113.idx())

/** 128-bit FloatingPoint declaration object */
internal object FP128Decl : SortDecl<FPSort>("Float128".symbol(), emptySet(), emptySet()) {
  override fun getSort(bindings: Bindings): FPSort = FPSort(15, 113)
}

/*
 * RoundingMode functions
 */

object RoundNearestTiesToEven :
    ConstantExpression<RoundingMode>("roundNearestTiesToEven".symbol(), RoundingMode) {
  override fun copy(children: List<Expression<*>>): Expression<RoundingMode> = this
}

object RoundNearestTiesToEvenDecl :
    FunctionDecl0<RoundingMode>(
        "roundNearestTiesToEven".symbol(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> =
      RoundNearestTiesToEven
}

object RNE : ConstantExpression<RoundingMode>("RNE".symbol(), RoundingMode) {
  override fun copy(children: List<Expression<*>>): Expression<RoundingMode> = this
}

object RNEDecl : FunctionDecl0<RoundingMode>("RNE".symbol(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RNE
}

object RoundNearestTiesToAway :
    ConstantExpression<RoundingMode>("roundNearestTiesToAway".symbol(), RoundingMode) {
  override fun copy(children: List<Expression<*>>): Expression<RoundingMode> = this
}

object RoundNearestTiesToAwayDecl :
    FunctionDecl0<RoundingMode>(
        "roundNearestTiesToAway".symbol(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> =
      RoundNearestTiesToAway
}

object RNA : ConstantExpression<RoundingMode>("RNA".symbol(), RoundingMode) {
  override fun copy(children: List<Expression<*>>): Expression<RoundingMode> = this
}

object RNADecl : FunctionDecl0<RoundingMode>("RNA".symbol(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RNA
}

object RoundTowardPositive :
    ConstantExpression<RoundingMode>("roundTowardPositive".symbol(), RoundingMode) {
  override fun copy(children: List<Expression<*>>): Expression<RoundingMode> = this
}

object RoundTowardPositiveDecl :
    FunctionDecl0<RoundingMode>(
        "roundTowardPositive".symbol(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RoundTowardPositive
}

object RTP : ConstantExpression<RoundingMode>("RTP".symbol(), RoundingMode) {
  override fun copy(children: List<Expression<*>>): Expression<RoundingMode> = this
}

object RTPDecl : FunctionDecl0<RoundingMode>("RTP".symbol(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RTP
}

object RoundTowardNegative :
    ConstantExpression<RoundingMode>("roundTowardNegative".symbol(), RoundingMode) {
  override fun copy(children: List<Expression<*>>): Expression<RoundingMode> = this
}

object RoundTowardNegativeDecl :
    FunctionDecl0<RoundingMode>(
        "RoundTowardNegative".symbol(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RoundTowardNegative
}

object RTN : ConstantExpression<RoundingMode>("RTN".symbol(), RoundingMode) {
  override fun copy(children: List<Expression<*>>): Expression<RoundingMode> = this
}

object RTNDecl : FunctionDecl0<RoundingMode>("RTN".symbol(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RTN
}

object RoundTowardZero :
    ConstantExpression<RoundingMode>("roundTowardZero".symbol(), RoundingMode) {
  override fun copy(children: List<Expression<*>>): Expression<RoundingMode> = this
}

object RoundTowardZeroDecl :
    FunctionDecl0<RoundingMode>("RoundTowardZero".symbol(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RoundTowardZero
}

object RTZ : ConstantExpression<RoundingMode>("RTZ".symbol(), RoundingMode) {
  override fun copy(children: List<Expression<*>>): Expression<RoundingMode> = this
}

object RTZDecl : FunctionDecl0<RoundingMode>("RTZ".symbol(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RTZ
}

/*
 * Floating Point Literals
 */

/**
 * Floating-point literal
 *
 * @param sign bitvector of length 1, holding the sign
 * @param exponent bitvector holding the exponent value
 * @param significand bitvector holding the significand value
 */
data class FPLiteral(
    val sign: Expression<BVSort>,
    val exponent: Expression<BVSort>,
    val significand: Expression<BVSort>
) :
    Literal<FPSort>(
        LiteralString("(fp $sign $exponent $significand)"),
        FPSort(exponent.sort.bits, significand.sort.bits + 1)) {
  init {
    require(sign.sort.bits == 1)
  }

  override fun copy(children: List<Expression<*>>): Expression<FPSort> = this
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
    return FPLiteral(param1 as BVLiteral, param2 as BVLiteral, param3 as BVLiteral)
  }
}

/**
 * Representation of plus infinity for a given number of bits
 *
 * ((_ +oo [eb] [sb]) (_ FloatingPoint [eb] [sb]))
 */
class FPInfinity(val eb: Int, val sb: Int) :
    ConstantExpression<FPSort>("+oo".symbol(), FPSort(eb, sb)) {
  override fun toString(): String = "(_ +oo $eb $sb)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> = this
}

/** Plus infinity declaration object */
object FPInfinityDecl :
    FunctionDecl0<FPSort>(
        "+oo".symbol(), emptySet(), setOf("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(bindings: Bindings): Expression<FPSort> =
      FPInfinity(bindings["eb"].numeral, bindings["sb"].numeral)
}

/**
 * Representation of minus infinity for a given number of bits
 *
 * ((_ -oo [eb] [sb]) (_ FloatingPoint [eb] [sb]))
 */
class FPMinusInfinity(val eb: Int, val sb: Int) :
    ConstantExpression<FPSort>("-oo".symbol(), FPSort(eb, sb)) {
  override fun toString(): String = "(_ -oo $eb $sb)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> = this
}

/** Minus infinity declaration object */
object FPMinusInfinityDecl :
    FunctionDecl0<FPSort>(
        "-oo".symbol(), emptySet(), setOf("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(bindings: Bindings): Expression<FPSort> =
      FPMinusInfinity(bindings["eb"].numeral, bindings["sb"].numeral)
}

/**
 * Representation of plus zero for a given number of bits
 *
 * ((_ +zero [eb] [sb]) (_ FloatingPoint [eb] [sb]))
 */
class FPZero(val eb: Int, val sb: Int) :
    ConstantExpression<FPSort>("+zero".symbol(), FPSort(eb, sb)) {
  override fun toString(): String = "(_ +zero $eb $sb)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> = this
}

/** Plus zero declaration object */
object FPZeroDecl :
    FunctionDecl0<FPSort>(
        "+zero".symbol(),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(bindings: Bindings): Expression<FPSort> =
      FPZero(bindings["eb"].numeral, bindings["sb"].numeral)
}

/**
 * Representation of minus zero for a given number of bits
 *
 * ((_ -zero [eb] [sb]) (_ FloatingPoint [eb] [sb]))
 */
class FPMinusZero(val eb: Int, val sb: Int) :
    ConstantExpression<FPSort>("-zero".symbol(), FPSort(eb, sb)) {
  override fun toString(): String = "(_ -zero $eb $sb)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> = this
}

/** Minus zero declaration object */
object FPMinusZeroDecl :
    FunctionDecl0<FPSort>(
        "-zero".symbol(),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(bindings: Bindings): Expression<FPSort> =
      FPMinusZero(bindings["eb"].numeral, bindings["sb"].numeral)
}

/**
 * Representation of NaN for a given number of bits
 *
 * ((_ NaN [eb] [sb]) (_ FloatingPoint [eb] [sb]))
 */
class FPNaN(val eb: Int, val sb: Int) : ConstantExpression<FPSort>("NaN".symbol(), FPSort(eb, sb)) {
  override fun toString(): String = "(_ NaN $eb $sb)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> = this
}

/** NaN declaration object */
object FPNaNDecl :
    FunctionDecl0<FPSort>(
        "NaN".symbol(), emptySet(), setOf("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(bindings: Bindings): Expression<FPSort> =
      FPNaN(bindings["eb"].numeral, bindings["sb"].numeral)
}

/*
 * Operators
 */

/**
 * Floating point absolute value, sort will be automatically determined from [inner]
 *
 * (fp.abs (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
 */
class FPAbs(override val inner: Expression<FPSort>) :
    UnaryExpression<FPSort, FPSort>("fp.abs".symbol(), inner.sort) {
  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPAbsDecl.buildExpression(children, emptyList())
}

/** Absolute value declaration object */
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

/**
 * Floating point negation, sort will be automatically determined from [inner]
 *
 * (fp.neg (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
 */
class FPNeg(override val inner: Expression<FPSort>) :
    UnaryExpression<FPSort, FPSort>("fp.neg".symbol(), inner.sort) {
  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPNegDecl.buildExpression(children, emptyList())
}

/** Negation declaration object */
object FPNegDecl :
    FunctionDecl1<FPSort, FPSort>(
        "fp.neg".symbol(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(param: Expression<FPSort>, bindings: Bindings): Expression<FPSort> =
      FPNeg(param)
}

/**
 * Floating point addition, sort will be automatically determined from [leftTerm]
 *
 * @throws IllegalArgumentException if [leftTerm] and [rightTerm] do not have the same sort
 *
 * (fp.add RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
 */
class FPAdd(
    val roundingMode: Expression<RoundingMode>,
    val leftTerm: Expression<FPSort>,
    val rightTerm: Expression<FPSort>
) : TernaryExpression<FPSort, RoundingMode, FPSort, FPSort>("fp.add".symbol(), leftTerm.sort) {
  override val lhs: Expression<RoundingMode> = roundingMode

  override val mid: Expression<FPSort> = leftTerm

  override val rhs: Expression<FPSort> = rightTerm

  init {
    // this check ensures that lhs and rhs have the same floating point format
    require(leftTerm.sort == rightTerm.sort)
  }

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPAddDecl.buildExpression(children, emptyList())
}

/** Addition declaration object */
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

/**
 * Floating point subtraction, sort will be automatically determined from [minuend]
 *
 * @throws IllegalArgumentException if [minuend] and [subtrahend] do not have the same sort
 *
 * (fp.sub RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
 */
class FPSub(
    val roundingMode: Expression<RoundingMode>,
    val minuend: Expression<FPSort>,
    val subtrahend: Expression<FPSort>
) : TernaryExpression<FPSort, RoundingMode, FPSort, FPSort>("fp.sub".symbol(), minuend.sort) {
  override val lhs: Expression<RoundingMode> = roundingMode

  override val mid: Expression<FPSort> = minuend

  override val rhs: Expression<FPSort> = subtrahend

  init {
    // this check ensures that lhs and rhs have the same floating point format
    require(minuend.sort == subtrahend.sort)
  }

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPSubDecl.buildExpression(children, emptyList())
}

/** Subtraction declaration object */
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

/**
 * Floating point multiplication, sort will be automatically determined from [multiplier]
 *
 * @throws IllegalArgumentException if [multiplier] and [multiplicand] do not have the same sort
 *
 * (fp.mul RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
 */
class FPMul(
    val roundingMode: Expression<RoundingMode>,
    val multiplier: Expression<FPSort>,
    val multiplicand: Expression<FPSort>
) : TernaryExpression<FPSort, RoundingMode, FPSort, FPSort>("fp.mul".symbol(), multiplier.sort) {
  override val lhs: Expression<RoundingMode> = roundingMode

  override val mid: Expression<FPSort> = multiplier

  override val rhs: Expression<FPSort> = multiplicand

  init {
    // this check ensures that lhs and rhs have the same floating point format
    require(multiplier.sort == multiplicand.sort)
  }

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPMulDecl.buildExpression(children, emptyList())
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

/**
 * Floating point division, sort will be automatically determined from [dividend]
 *
 * @throws IllegalArgumentException if [dividend] and [divisor] do not have the same sort
 *
 * (fp.div RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
 */
class FPDiv(
    val roundingMode: Expression<RoundingMode>,
    val dividend: Expression<FPSort>,
    val divisor: Expression<FPSort>
) : TernaryExpression<FPSort, RoundingMode, FPSort, FPSort>("fp.div".symbol(), dividend.sort) {
  override val lhs: Expression<RoundingMode> = roundingMode

  override val mid: Expression<FPSort> = dividend

  override val rhs: Expression<FPSort> = divisor

  init {
    // this check ensures that lhs and rhs have the same floating point format
    require(dividend.sort == divisor.sort)
  }

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPDivDecl.buildExpression(children, emptyList())
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

/**
 * Floating point fused multiplication and addition ([multiplier] * [multiplicand]) + [summand],
 * sort will be automatically determined from [multiplier]
 *
 * @throws IllegalArgumentException if [multiplier], [multiplicand] and [summand] do not have the
 *   same sort
 *
 * (fp.fma RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
 */
class FPFma(
    val roundingMode: Expression<RoundingMode>,
    val multiplier: Expression<FPSort>,
    val multiplicand: Expression<FPSort>,
    val summand: Expression<FPSort>
) : NAryExpression<FPSort>("fp.fma".symbol(), multiplier.sort) {

  init {
    require(multiplier.sort == multiplicand.sort)
    require(multiplier.sort == summand.sort)
  }

  override val children: List<Expression<*>> =
      listOf(roundingMode, multiplier, multiplicand, summand)

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPFmaDecl.buildExpression(children, emptyList())
}

object FPFmaDecl :
    FunctionDecl4<RoundingMode, FPSort, FPSort, FPSort, FPSort>(
        "fp.fma".symbol(),
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

/**
 * Floating point square root, sort will be automatically determined from [inner]
 *
 * (fp.sqrt RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
 */
class FPSqrt(val roundingMode: Expression<RoundingMode>, val inner: Expression<FPSort>) :
    BinaryExpression<FPSort, RoundingMode, FPSort>("fp.sqrt".symbol(), inner.sort) {
  override val lhs: Expression<RoundingMode> = roundingMode

  override val rhs: Expression<FPSort> = inner

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPSqrtDecl.buildExpression(children, emptyList())
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

/**
 * Floating point remainder: [dividend] - [divisor] * n, where n in Z is nearest to
 * [dividend]/[divisor], sort will be automatically determined from [dividend]
 *
 * @throws IllegalArgumentException if [dividend] and [divisor] do not have the same sort
 *
 * (fp.rem (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
 */
class FPRem(val dividend: Expression<FPSort>, val divisor: Expression<FPSort>) :
    BinaryExpression<FPSort, FPSort, FPSort>("fp.rem".symbol(), dividend.sort) {
  override val lhs: Expression<FPSort> = dividend

  override val rhs: Expression<FPSort> = divisor

  init {
    require(dividend.sort == divisor.sort)
  }

  override fun toString(): String = "(fp.rem $dividend $divisor)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPRemDecl.buildExpression(children, emptyList())
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

/**
 * Floating point rounding to integral, sort will be automatically determined from [inner]
 *
 * (fp.roundToIntegral RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
 */
class FPRoundToIntegral(val roundingMode: Expression<RoundingMode>, val inner: Expression<FPSort>) :
    BinaryExpression<FPSort, RoundingMode, FPSort>("fp.roundToIntegral".symbol(), inner.sort) {
  override val lhs: Expression<RoundingMode> = roundingMode

  override val rhs: Expression<FPSort> = inner

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPRoundToIntegralDecl.buildExpression(children, emptyList())
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

/**
 * Floating point minimum, sort will be automatically determined from [lhs]
 *
 * @throws IllegalArgumentException if [lhs] and [rhs] do not have the same sort
 *
 * (fp.min (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
 */
class FPMin(override val lhs: Expression<FPSort>, override val rhs: Expression<FPSort>) :
    BinaryExpression<FPSort, FPSort, FPSort>("fp.min".symbol(), lhs.sort) {

  init {
    require(lhs.sort == rhs.sort)
  }

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPMinDecl.buildExpression(children, emptyList())
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

/**
 * Floating point maximum, sort will be automatically determined from [lhs]
 *
 * @throws IllegalArgumentException if [lhs] and [rhs] do not have the same sort
 *
 * (fp.max (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
 */
class FPMax(override val lhs: Expression<FPSort>, override val rhs: Expression<FPSort>) :
    BinaryExpression<FPSort, FPSort, FPSort>("fp.max".symbol(), lhs.sort) {

  init {
    require(lhs.sort == rhs.sort)
  }

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPMaxDecl.buildExpression(children, emptyList())
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

/**
 * Floating point less equals,
 *
 * @throws IllegalArgumentException if less than 2 [terms] are provided
 * @throws IllegalArgumentException if two [terms] have different sorts
 *
 * (fp.leq (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)
 */
class FPLeq(val terms: List<Expression<FPSort>>) :
    HomogenousExpression<BoolSort, FPSort>("fp.leq".symbol(), BoolSort) {
  constructor(vararg terms: Expression<FPSort>) : this(terms.toList())

  override val children: List<Expression<FPSort>> = terms

  init {
    require(terms.size > 1)
    terms.zipWithNext { a, b -> require(a.sort == b.sort) }
  }

  override fun toString(): String = "(fp.leq ${terms.joinToString(" ")})"

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPLeqDecl.buildExpression(children, emptyList())
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

/**
 * Floating point less,
 *
 * @throws IllegalArgumentException if less than 2 [terms] are provided
 * @throws IllegalArgumentException if two [terms] have different sorts
 *
 * (fp.lt (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)
 */
class FPLt(val terms: List<Expression<FPSort>>) :
    HomogenousExpression<BoolSort, FPSort>("fp.lt".symbol(), BoolSort) {
  constructor(vararg terms: Expression<FPSort>) : this(terms.toList())

  override val children: List<Expression<FPSort>> = terms

  init {
    require(terms.size > 1)
    terms.zipWithNext { a, b -> require(a.sort == b.sort) }
  }

  override fun toString(): String = "(fp.lt ${terms.joinToString(" ")})"

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPLtDecl.buildExpression(children, emptyList())
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

/**
 * Floating point greater equals,
 *
 * @throws IllegalArgumentException if less than 2 [terms] are provided
 * @throws IllegalArgumentException if two [terms] have different sorts
 *
 * (fp.geq (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)
 */
class FPGeq(val terms: List<Expression<FPSort>>) :
    HomogenousExpression<BoolSort, FPSort>("fp.geq".symbol(), BoolSort) {
  constructor(vararg terms: Expression<FPSort>) : this(terms.toList())

  override val children: List<Expression<FPSort>> = terms

  init {
    require(terms.size > 1)
    terms.zipWithNext { a, b -> require(a.sort == b.sort) }
  }

  override fun toString(): String = "(fp.geq ${terms.joinToString(" ")})"

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPGeqDecl.buildExpression(children, emptyList())
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

/**
 * Floating point greater,
 *
 * @throws IllegalArgumentException if less than 2 [terms] are provided
 * @throws IllegalArgumentException if two [terms] have different sorts
 *
 * (fp.gt (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)
 */
class FPGt(val terms: List<Expression<FPSort>>) :
    HomogenousExpression<BoolSort, FPSort>("fp.gt".symbol(), BoolSort) {
  constructor(vararg terms: Expression<FPSort>) : this(terms.toList())

  override val children: List<Expression<FPSort>> = terms

  init {
    require(terms.size > 1)
    terms.zipWithNext { a, b -> require(a.sort == b.sort) }
  }

  override fun toString(): String = "(fp.gt ${terms.joinToString(" ")})"

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPGtDecl.buildExpression(children, emptyList())
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

/**
 * Floating point equality (not SMT equality '='),
 *
 * @throws IllegalArgumentException if less than 2 [terms] are provided
 * @throws IllegalArgumentException if two [terms] have different sorts
 *
 * (fp.eq (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)
 */
class FPEq(val terms: List<Expression<FPSort>>) :
    HomogenousExpression<BoolSort, FPSort>("fp.eq".symbol(), BoolSort) {
  constructor(vararg terms: Expression<FPSort>) : this(terms.toList())

  override val children: List<Expression<FPSort>> = terms

  init {
    require(terms.size > 1)
    terms.zipWithNext { a, b -> require(a.sort == b.sort) }
  }

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPEqDecl.buildExpression(children, emptyList())
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

/** (fp.isNormal (_ FloatingPoint eb sb) Bool) */
class FPIsNormal(override val inner: Expression<FPSort>) :
    UnaryExpression<BoolSort, FPSort>("fp.isNormal".symbol(), BoolSort) {
  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPIsNormalDecl.buildExpression(children, emptyList())
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

/** (fp.isSubnormal (_ FloatingPoint eb sb) Bool) */
class FPIsSubnormal(override val inner: Expression<FPSort>) :
    UnaryExpression<BoolSort, FPSort>("fp.isSubnormal".symbol(), BoolSort) {
  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPIsSubormalDecl.buildExpression(children, emptyList())
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

/** (fp.isZero (_ FloatingPoint eb sb) Bool) */
class FPIsZero(override val inner: Expression<FPSort>) :
    UnaryExpression<BoolSort, FPSort>("fp.isZero".symbol(), BoolSort) {
  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPIsZeroDecl.buildExpression(children, emptyList())
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

/** (fp.isInfinite (_ FloatingPoint eb sb) Bool) */
class FPIsInfinite(override val inner: Expression<FPSort>) :
    UnaryExpression<BoolSort, FPSort>("fp.isInfinite".symbol(), BoolSort) {
  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPIsInfiniteDecl.buildExpression(children, emptyList())
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

/** (fp.isNaN (_ FloatingPoint eb sb) Bool) */
class FPIsNaN(override val inner: Expression<FPSort>) :
    UnaryExpression<BoolSort, FPSort>("fp.isNaN".symbol(), BoolSort) {
  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPIsNaNDecl.buildExpression(children, emptyList())
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

/** (fp.isNegative (_ FloatingPoint eb sb) Bool) */
class FPIsNegative(override val inner: Expression<FPSort>) :
    UnaryExpression<BoolSort, FPSort>("fp.isNegative".symbol(), BoolSort) {
  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPIsNegativeDecl.buildExpression(children, emptyList())
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

/** (fp.isPositive (_ FloatingPoint eb sb) Bool) */
class FPIsPositive(override val inner: Expression<FPSort>) :
    UnaryExpression<BoolSort, FPSort>("fp.isPositive".symbol(), BoolSort) {
  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPIsPositiveDecl.buildExpression(children, emptyList())
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

/**
 * Convert a bitvector [inner] to floating point with given number of bits [eb] and [sb]
 *
 * @throws IllegalArgumentException if number of bits in [inner] is not [eb] + [sb]
 *
 * ((_ to_fp eb sb) (_ BitVec m) (_ FloatingPoint eb sb)), with m = eb + sb
 */
class BitVecToFP(override val inner: Expression<BVSort>, val eb: Int, val sb: Int) :
    UnaryExpression<FPSort, BVSort>("to_fp".symbol(), FPSort(eb, sb)) {

  init {
    require(inner.sort.bits == eb + sb)
  }

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      BitVecToFPDecl.buildExpression(children, emptyList())
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

/**
 * Convert a floating point [inner] to a different floating point with given number of bits [eb] and
 * [sb]
 *
 * ((_ to_fp eb sb) RoundingMode (_ FloatingPoint mb nb) (_ FloatingPoint eb sb))
 */
class FPToFP(
    val roundingMode: Expression<RoundingMode>,
    val inner: Expression<FPSort>,
    val eb: Int,
    val sb: Int
) : BinaryExpression<FPSort, RoundingMode, FPSort>("to_fp".symbol(), FPSort(eb, sb)) {
  override val lhs: Expression<RoundingMode> = roundingMode

  override val rhs: Expression<FPSort> = inner

  override fun toString(): String = "((_ to_fp $eb $sb) $roundingMode $inner)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPToFPDecl.buildExpression(children, emptyList())
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

/**
 * Convert a real [inner] to a floating point with given number of bits [eb] and [sb]
 *
 * ((_ to_fp eb sb) RoundingMode Real (_ FloatingPoint eb sb))
 */
class RealToFP(
    val roundingMode: Expression<RoundingMode>,
    val inner: Expression<RealSort>,
    val eb: Int,
    val sb: Int
) : BinaryExpression<FPSort, RoundingMode, RealSort>("to_fp".symbol(), FPSort(eb, sb)) {
  override val lhs: Expression<RoundingMode> = roundingMode

  override val rhs: Expression<RealSort> = inner

  override fun toString(): String = "((_ to_fp $eb $sb) $roundingMode $inner)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      RealToFPDecl.buildExpression(children, emptyList())
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

/**
 * Convert a signed machine integer, represented as a 2's complement bit vector, [inner] to a
 * floating point with given number of bits [eb] and [sb]
 *
 * ((_ to_fp eb sb) RoundingMode (_ BitVec m) (_ FloatingPoint eb sb))
 */
class SBitVecToFP(
    val roundingMode: Expression<RoundingMode>,
    val inner: Expression<BVSort>,
    val eb: Int,
    val sb: Int
) : BinaryExpression<FPSort, RoundingMode, BVSort>("to_fp".symbol(), FPSort(eb, sb)) {
  override val lhs: Expression<RoundingMode> = roundingMode

  override val rhs: Expression<BVSort> = inner

  override fun toString(): String = "((_ to_fp $eb $sb) $roundingMode $inner)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      SBitVecToFPDecl.buildExpression(children, emptyList())
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

/**
 * Convert an unsigned machine integer, represented as bit vector, [inner] to a floating point with
 * given number of bits [eb] and [sb]
 *
 * ((_ to_fp_unsigned eb sb) RoundingMode (_ BitVec m) (_ FloatingPoint eb sb))
 */
class UBitVecToFP(
    val roundingMode: Expression<RoundingMode>,
    val inner: Expression<BVSort>,
    val eb: Int,
    val sb: Int
) : BinaryExpression<FPSort, RoundingMode, BVSort>("to_fp_unsigned".symbol(), FPSort(eb, sb)) {
  override val lhs: Expression<RoundingMode> = roundingMode

  override val rhs: Expression<BVSort> = inner

  override fun toString(): String = "((_ to_fp_unsigned $eb $sb) $roundingMode $inner)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      UBitVecToFPDecl.buildExpression(children, emptyList())
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

/**
 * Convert a floating point [inner] to an unsigned machine integer, represented as a bit vector of
 * length [m]
 *
 * ((_ fp.to_ubv m) RoundingMode (_ FloatingPoint eb sb) (_ BitVec m))
 */
class FPToUBitVec(
    val roundingMode: Expression<RoundingMode>,
    val inner: Expression<FPSort>,
    val m: Int
) : BinaryExpression<BVSort, RoundingMode, FPSort>("fp.to_ubv".symbol(), BVSort(m)) {
  override val lhs: Expression<RoundingMode> = roundingMode

  override val rhs: Expression<FPSort> = inner

  override fun toString(): String = "((_ fp.to_ubv $m) $roundingMode $inner)"

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      FPToUBitVecDecl.buildExpression(children, emptyList())
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

/**
 * Convert a floating point [inner] to a signed machine integer, represented as a 2's complement bit
 * vector of length [m]
 *
 * ((_ fp.to_ubv m) RoundingMode (_ FloatingPoint eb sb) (_ BitVec m))
 */
class FPToSBitVec(
    val roundingMode: Expression<RoundingMode>,
    val inner: Expression<FPSort>,
    val m: Int
) : BinaryExpression<BVSort, RoundingMode, FPSort>("fp.to_sbv".symbol(), BVSort(m)) {

  override val lhs: Expression<RoundingMode> = roundingMode

  override val rhs: Expression<FPSort> = inner

  override fun toString(): String = "((_ fp.to_sbv $m) $roundingMode $inner)"

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      FPToSBitVecDecl.buildExpression(children, emptyList())
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

/**
 * Convert a floating point [inner] to real
 *
 * (fp.to_real (_ FloatingPoint eb sb) Real)
 */
class FPToReal(override val inner: Expression<FPSort>) :
    UnaryExpression<RealSort, FPSort>("fp.to_real".symbol(), RealSort) {
  override fun copy(children: List<Expression<*>>): Expression<RealSort> =
      FPToRealDecl.buildExpression(children, emptyList())
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

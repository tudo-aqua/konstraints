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
import tools.aqua.konstraints.parser.IndexedIdentifier
import tools.aqua.konstraints.parser.ProtoSort
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

internal object RoundingModeDecl : SortDecl<RoundingMode>("RoundingMode") {
  override fun getSort(sort: ProtoSort): RoundingMode = RoundingMode
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

internal object FPSortDecl : SortDecl<FPSort>("FloatingPoint") {
  override fun getSort(sort: ProtoSort): FPSort {
    require(sort.identifier is IndexedIdentifier)
    require(sort.identifier.indices.size == 2)
    require(sort.identifier.indices[0] is NumeralIndex)
    require(sort.identifier.indices[1] is NumeralIndex)

    return FPSort(
        (sort.identifier.indices[0] as NumeralIndex).numeral,
        (sort.identifier.indices[1] as NumeralIndex).numeral)
  }
}

object FP16 : FPBase(5.idx(), 11.idx())

internal object FP16Decl : SortDecl<FPSort>("Float16") {
  override fun getSort(sort: ProtoSort): FPSort = FPSort(5, 11)
}

object FP32 : FPBase(8.idx(), 24.idx())

internal object FP32Decl : SortDecl<FPSort>("Float16") {
  override fun getSort(sort: ProtoSort): FPSort = FPSort(8, 24)
}

object FP64 : FPBase(11.idx(), 53.idx())

internal object FP64Decl : SortDecl<FPSort>("Float16") {
  override fun getSort(sort: ProtoSort): FPSort = FPSort(11, 53)
}

object FP128 : FPBase(15.idx(), 113.idx())

internal object FP128Decl : SortDecl<FPSort>("Float16") {
  override fun getSort(sort: ProtoSort): FPSort = FPSort(15, 113)
}

/*
 * RoundingMode functions
 */

class RoundNearestTiesToEven : Expression<RoundingMode>() {
  override val symbol: String = "roundNearestTiesToEven"
  override val sort: RoundingMode = RoundingMode
}

object RoundNearestTiesToEvenDecl :
    FunctionDecl0<RoundingMode>("roundNearestTiesToEven", emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> =
      RoundNearestTiesToEven()
}

class RNE : Expression<RoundingMode>() {
  override val symbol: String = "RNE"
  override val sort: RoundingMode = RoundingMode
}

object RNEDecl : FunctionDecl0<RoundingMode>("RNE", emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RNE()
}

class RoundNearestTiesToAway : Expression<RoundingMode>() {
  override val symbol: String = "roundNearestTiesToAway"
  override val sort: RoundingMode = RoundingMode
}

object RoundNearestTiesToAwayDecl :
    FunctionDecl0<RoundingMode>("roundNearestTiesToAway", emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> =
      RoundNearestTiesToAway()
}

class RNA : Expression<RoundingMode>() {
  override val symbol: String = "RNA"
  override val sort: RoundingMode = RoundingMode
}

object RNADecl : FunctionDecl0<RoundingMode>("RNA", emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RNA()
}

class RoundTowardPositive : Expression<RoundingMode>() {
  override val symbol: String = "roundTowardPositive"
  override val sort: RoundingMode = RoundingMode
}

object RoundTowardPositiveDecl :
    FunctionDecl0<RoundingMode>("roundTowardPositive", emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RoundTowardPositive()
}

class RTP : Expression<RoundingMode>() {
  override val symbol: String = "RTP"
  override val sort: RoundingMode = RoundingMode
}

object RTPDecl : FunctionDecl0<RoundingMode>("RTP", emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RTP()
}

class RoundTowardNegative : Expression<RoundingMode>() {
  override val symbol: String = "roundTowardNegative"
  override val sort: RoundingMode = RoundingMode
}

object RoundTowardNegativeDecl :
    FunctionDecl0<RoundingMode>("RoundTowardNegative", emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RoundTowardNegative()
}

class RTN : Expression<RoundingMode>() {
  override val symbol: String = "RTN"
  override val sort: RoundingMode = RoundingMode
}

object RTNDecl : FunctionDecl0<RoundingMode>("RTN", emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RTN()
}

class RoundTowardZero : Expression<RoundingMode>() {
  override val symbol: String = "roundTowardZero"
  override val sort: RoundingMode = RoundingMode
}

object RoundTowardZeroDecl :
    FunctionDecl0<RoundingMode>("RoundTowardZero", emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RoundTowardZero()
}

class RTZ : Expression<RoundingMode>() {
  override val symbol: String = "RTZ"
  override val sort: RoundingMode = RoundingMode
}

object RTZDecl : FunctionDecl0<RoundingMode>("RTZ", emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RTZ()
}

/*
 * Floating Point Literals
 */

data class FPLiteral(val eb: Int, val sb: Int) : Expression<FPSort>() {
  override val symbol: String = TODO()
  override val sort: FPSort = FPSort(eb, sb)
}

object FPLiteralDecl :
    FunctionDecl3<BVSort, BVSort, BVSort, FPSort>(
        "fp",
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
    return FPLiteral(bindings["eb"].numeral, bindings["i"].numeral + 1)
  }
}

/*
 * Infinity
 */

class FPInfinity(eb: Int, sb: Int) : Expression<FPSort>() {
  override val symbol: String = "(_ +oo $eb $sb)"
  override val sort: FPSort = FPSort(eb, sb)
}

object FPInfinityDecl :
    FunctionDecl0<FPSort>(
        "+oo", emptySet(), setOf("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(bindings: Bindings): Expression<FPSort> =
      FPInfinity(bindings["eb"].numeral, bindings["sb"].numeral)
}

class FPMinusInfinity(eb: Int, sb: Int) : Expression<FPSort>() {
  override val symbol: String = "(_ -oo $eb $sb)"
  override val sort: FPSort = FPSort(eb, sb)
}

object FPMinusInfinityDecl :
    FunctionDecl0<FPSort>(
        "-oo", emptySet(), setOf("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(bindings: Bindings): Expression<FPSort> =
      FPMinusInfinity(bindings["eb"].numeral, bindings["sb"].numeral)
}

/*
 * Zero
 */

class FPZero(eb: Int, sb: Int) : Expression<FPSort>() {
  override val symbol: String = "(_ +zero $eb $sb)"
  override val sort: FPSort = FPSort(eb, sb)
}

object FPZeroDecl :
    FunctionDecl0<FPSort>(
        "+zero", emptySet(), setOf("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(bindings: Bindings): Expression<FPSort> =
      FPZero(bindings["eb"].numeral, bindings["sb"].numeral)
}

class FPMinusZero(eb: Int, sb: Int) : Expression<FPSort>() {
  override val symbol: String = "(_ -zero $eb $sb)"
  override val sort: FPSort = FPSort(eb, sb)
}

object FPMinusZeroDecl :
    FunctionDecl0<FPSort>(
        "-zero", emptySet(), setOf("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(bindings: Bindings): Expression<FPSort> =
      FPMinusZero(bindings["eb"].numeral, bindings["sb"].numeral)
}

/*
 * NaN
 */

class FPNaN(eb: Int, sb: Int) : Expression<FPSort>() {
  override val symbol: String = "(_ NaN $eb $sb)"
  override val sort: FPSort = FPSort(eb, sb)
}

object FPNaNDecl :
    FunctionDecl0<FPSort>(
        "NaN", emptySet(), setOf("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(bindings: Bindings): Expression<FPSort> =
      FPNaN(bindings["eb"].numeral, bindings["sb"].numeral)
}

/*
 * Operators
 */

class FPAbs(inner: Expression<FPSort>) : Expression<FPSort>() {
  override val symbol: String = "(fp.abs $inner)"
  override val sort: FPSort = inner.sort
}

object FPAbsDecl :
    FunctionDecl1<FPSort, FPSort>(
        "fp.abs",
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(param: Expression<FPSort>, bindings: Bindings): Expression<FPSort> =
      FPAbs(param)
}

class FPNeg(inner: Expression<FPSort>) : Expression<FPSort>() {
  override val symbol: String = "(fp.neg $inner)"
  override val sort: FPSort = inner.sort
}

object FPNegDecl :
    FunctionDecl1<FPSort, FPSort>(
        "fp.abs",
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(param: Expression<FPSort>, bindings: Bindings): Expression<FPSort> =
      FPNeg(param)
}

class FPAdd(lhs: Expression<FPSort>, rhs: Expression<FPSort>) : Expression<FPSort>() {
  override val symbol: String = "(fp.add $lhs $rhs)"
  override val sort: FPSort = lhs.sort

  init {
    // this check ensures that lhs and rhs have the same floating point format
    require(lhs.sort == rhs.sort)
  }
}

object FPAddDecl :
    FunctionDecl2<FPSort, FPSort, FPSort>(
        "fp.add",
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
  ): Expression<FPSort> = FPAdd(param1, param2)
}

class FPSub(minuend: Expression<FPSort>, subtrahend: Expression<FPSort>) : Expression<FPSort>() {
  override val symbol: String = "(fp.sub $minuend $subtrahend)"
  override val sort: FPSort = minuend.sort

  init {
    // this check ensures that lhs and rhs have the same floating point format
    require(minuend.sort == subtrahend.sort)
  }
}

object FPSubDecl :
    FunctionDecl2<FPSort, FPSort, FPSort>(
        "fp.sub",
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
  ): Expression<FPSort> = FPSub(param1, param2)
}

class FPMul(multiplier: Expression<FPSort>, multiplicand: Expression<FPSort>) :
    Expression<FPSort>() {
  override val symbol: String = "(fp.mul $multiplier $multiplicand)"
  override val sort: FPSort = multiplier.sort

  init {
    // this check ensures that lhs and rhs have the same floating point format
    require(multiplier.sort == multiplicand.sort)
  }
}

object FPMulDecl :
    FunctionDecl2<FPSort, FPSort, FPSort>(
        "fp.mul",
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
  ): Expression<FPSort> = FPMul(param1, param2)
}

class FPDiv(dividend: Expression<FPSort>, divisor: Expression<FPSort>) : Expression<FPSort>() {
  override val symbol: String = "(fp.div $dividend $divisor)"
  override val sort: FPSort = dividend.sort

  init {
    // this check ensures that lhs and rhs have the same floating point format
    require(dividend.sort == divisor.sort)
  }
}

object FPDivDecl :
    FunctionDecl2<FPSort, FPSort, FPSort>(
        "fp.div",
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
  ): Expression<FPSort> = FPDiv(param1, param2)
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

object FPFmaDecl :
    FunctionDecl3<FPSort, FPSort, FPSort, FPSort>(
        "fp.div",
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<FPSort>,
      param2: Expression<FPSort>,
      param3: Expression<FPSort>,
      bindings: Bindings
  ): Expression<FPSort> = FPFma(param1, param2, param3)
}

class FPSqrt(inner: Expression<FPSort>) : Expression<FPSort>() {
  override val symbol: String = "(fp.sqrt $inner)"
  override val sort: FPSort = inner.sort
}

object FPSqrtDecl :
    FunctionDecl1<FPSort, FPSort>(
        "fp.sqrt",
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(param: Expression<FPSort>, bindings: Bindings): Expression<FPSort> =
      FPSqrt(param)
}

class FPRem(dividend: Expression<FPSort>, divisor: Expression<FPSort>) : Expression<FPSort>() {
  override val symbol: String = "(fp.rem $dividend $divisor)"
  override val sort: FPSort = dividend.sort

  init {
    require(dividend.sort == divisor.sort)
  }
}

object FPRemDecl :
    FunctionDecl2<FPSort, FPSort, FPSort>(
        "fp.rem",
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

class FPRoundToIntegral(roundingMode: Expression<RoundingMode>, inner: Expression<FPSort>) :
    Expression<FPSort>() {
  override val symbol: String = "(fp.roundToIntegral $roundingMode $inner)"
  override val sort: FPSort = inner.sort
}

object FPRoundToIntegralDecl :
    FunctionDecl2<RoundingMode, FPSort, FPSort>(
        "fp.roundToIntegral",
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

class FPMin(lhs: Expression<FPSort>, rhs: Expression<FPSort>) : Expression<FPSort>() {
  override val symbol: String = "(fp.min $lhs $rhs)"
  override val sort: FPSort = lhs.sort

  init {
    require(lhs.sort == rhs.sort)
  }
}

object FPMinDecl :
    FunctionDecl2<FPSort, FPSort, FPSort>(
        "fp.min",
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

class FPMax(lhs: Expression<FPSort>, rhs: Expression<FPSort>) : Expression<FPSort>() {
  override val symbol: String = "(fp.max $lhs $rhs)"
  override val sort: FPSort = lhs.sort

  init {
    require(lhs.sort == rhs.sort)
  }
}

object FPMaxDecl :
    FunctionDecl2<FPSort, FPSort, FPSort>(
        "fp.max",
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

class FPLeq(terms: List<Expression<FPSort>>) : Expression<BoolSort>() {
  constructor(vararg terms: Expression<FPSort>) : this(terms.toList())

  override val symbol: String = "(fp.leq ${terms.joinToString(" ")})"
  override val sort: BoolSort = BoolSort

  init {
    require(terms.size > 1)
    terms.zipWithNext { a, b -> require(a.sort == b.sort) }
  }
}

object FPLeqDecl :
    FunctionDeclChainable<FPSort>(
        "fp.leq",
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

class FPLt(terms: List<Expression<FPSort>>) : Expression<BoolSort>() {
  constructor(vararg terms: Expression<FPSort>) : this(terms.toList())

  override val symbol: String = "(fp.lt ${terms.joinToString(" ")})"
  override val sort: BoolSort = BoolSort

  init {
    require(terms.size > 1)
    terms.zipWithNext { a, b -> require(a.sort == b.sort) }
  }
}

object FPLtDecl :
    FunctionDeclChainable<FPSort>(
        "fp.lt",
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

class FPGeq(terms: List<Expression<FPSort>>) : Expression<BoolSort>() {
  constructor(vararg terms: Expression<FPSort>) : this(terms.toList())

  override val symbol: String = "(fp.geq ${terms.joinToString(" ")})"
  override val sort: BoolSort = BoolSort

  init {
    require(terms.size > 1)
    terms.zipWithNext { a, b -> require(a.sort == b.sort) }
  }
}

object FPGeqDecl :
    FunctionDeclChainable<FPSort>(
        "fp.geq",
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

class FPGt(terms: List<Expression<FPSort>>) : Expression<BoolSort>() {
  constructor(vararg terms: Expression<FPSort>) : this(terms.toList())

  override val symbol: String = "(fp.gt ${terms.joinToString(" ")})"
  override val sort: BoolSort = BoolSort

  init {
    require(terms.size > 1)
    terms.zipWithNext { a, b -> require(a.sort == b.sort) }
  }
}

object FPGtDecl :
    FunctionDeclChainable<FPSort>(
        "fp.gt",
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

class FPEq(terms: List<Expression<FPSort>>) : Expression<BoolSort>() {
  constructor(vararg terms: Expression<FPSort>) : this(terms.toList())

  override val symbol: String = "(fp.eq ${terms.joinToString(" ")})"
  override val sort: BoolSort = BoolSort

  init {
    require(terms.size > 1)
    terms.zipWithNext { a, b -> require(a.sort == b.sort) }
  }
}

object FPEqDecl :
    FunctionDeclChainable<FPSort>(
        "fp.eq",
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

class FPIsNormal(inner: Expression<FPSort>) : Expression<BoolSort>() {
  override val symbol: String = "(fp.isNormal $inner)"
  override val sort: BoolSort = BoolSort
}

object FPIsNormalDecl :
    FunctionDecl1<FPSort, BoolSort>(
        "fp.isNormal",
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

class FPIsSubnormal(inner: Expression<FPSort>) : Expression<BoolSort>() {
  override val symbol: String = "(fp.isSubnormal $inner)"
  override val sort: BoolSort = BoolSort
}

object FPIsSubormalDecl :
    FunctionDecl1<FPSort, BoolSort>(
        "fp.isSubormal",
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

class FPIsZero(inner: Expression<FPSort>) : Expression<BoolSort>() {
  override val symbol: String = "(fp.isZero $inner)"
  override val sort: BoolSort = BoolSort
}

object FPIsZeroDecl :
    FunctionDecl1<FPSort, BoolSort>(
        "fp.isZero",
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

class FPIsInfinite(inner: Expression<FPSort>) : Expression<BoolSort>() {
  override val symbol: String = "(fp.isInfinite $inner)"
  override val sort: BoolSort = BoolSort
}

object FPIsInfiniteDecl :
    FunctionDecl1<FPSort, BoolSort>(
        "fp.isInfinite",
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

class FPIsNaN(inner: Expression<FPSort>) : Expression<BoolSort>() {
  override val symbol: String = "(fp.isNaN $inner)"
  override val sort: BoolSort = BoolSort
}

object FPIsNaNDecl :
    FunctionDecl1<FPSort, BoolSort>(
        "fp.isNan",
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

class FPIsNegative(inner: Expression<FPSort>) : Expression<BoolSort>() {
  override val symbol: String = "(fp.isNegative $inner)"
  override val sort: BoolSort = BoolSort
}

object FPIsNegativeDecl :
    FunctionDecl1<FPSort, BoolSort>(
        "fp.isNegative",
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

class FPIsPositive(inner: Expression<FPSort>) : Expression<BoolSort>() {
  override val symbol: String = "(fp.isPositive $inner)"
  override val sort: BoolSort = BoolSort
}

object FPIsPositiveDecl :
    FunctionDecl1<FPSort, BoolSort>(
        "fp.isPositive",
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

class BitVecToFP(inner: Expression<BVSort>, eb: Int, sb: Int) : Expression<FPSort>() {
  override val symbol: String = "((_ to_fp $eb $sb) $inner)"
  override val sort: FPSort = FPSort(eb, sb)
}

object BitVecToFPDecl :
    FunctionDecl1<BVSort, FPSort>(
        "to_fp",
        emptySet(),
        BVSort.fromSymbol("m"),
        setOf("eb".idx(), "sb".idx()),
        setOf("m".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(param: Expression<BVSort>, bindings: Bindings): Expression<FPSort> =
      BitVecToFP(param, bindings["eb"].numeral, bindings["sb"].numeral)
}

class FPToFP(roundingMode: Expression<RoundingMode>, inner: Expression<FPSort>, eb: Int, sb: Int) :
    Expression<FPSort>() {
  override val symbol: String = "((_ to_fp $eb $sb) $roundingMode $inner)"
  override val sort: FPSort = FPSort(eb, sb)
}

object FPToFPDecl :
    FunctionDecl2<RoundingMode, FPSort, FPSort>(
        "to_fp",
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
    roundingMode: Expression<RoundingMode>,
    inner: Expression<RealSort>,
    eb: Int,
    sb: Int
) : Expression<FPSort>() {
  override val symbol: String = "((_ to_fp $eb $sb) $roundingMode $inner)"
  override val sort: FPSort = FPSort(eb, sb)
}

object RealToFPDecl :
    FunctionDecl2<RoundingMode, RealSort, FPSort>(
        "to_fp",
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
    roundingMode: Expression<RoundingMode>,
    inner: Expression<BVSort>,
    eb: Int,
    sb: Int
) : Expression<FPSort>() {
  override val symbol: String = "((_ to_fp $eb $sb) $roundingMode $inner)"
  override val sort: FPSort = FPSort(eb, sb)
}

object SBitVecToFPDecl :
    FunctionDecl2<RoundingMode, BVSort, FPSort>(
        "to_fp",
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
    roundingMode: Expression<RoundingMode>,
    inner: Expression<BVSort>,
    eb: Int,
    sb: Int
) : Expression<FPSort>() {
  override val symbol: String = "((_ to_fp_unsigned $eb $sb) $roundingMode $inner)"
  override val sort: FPSort = FPSort(eb, sb)
}

object UBitVecToFPDecl :
    FunctionDecl2<RoundingMode, BVSort, FPSort>(
        "to_fp_unsigned",
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

class FPToUBitVec(roundingMode: Expression<RoundingMode>, inner: Expression<FPSort>, m: Int) :
    Expression<BVSort>() {
  override val symbol: String = "((_ fp.to_ubv $m) $roundingMode $inner)"
  override val sort: BVSort = BVSort(m)
}

object FPToUBitVecDecl :
    FunctionDecl2<RoundingMode, FPSort, BVSort>(
        "fp.to_ubv",
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

class FPToSBitVec(roundingMode: Expression<RoundingMode>, inner: Expression<FPSort>, m: Int) :
    Expression<BVSort>() {
  override val symbol: String = "((_ fp.to_sbv $m) $roundingMode $inner)"
  override val sort: BVSort = BVSort(m)
}

object FPToSBitVecDecl :
    FunctionDecl2<RoundingMode, FPSort, BVSort>(
        "fp.to_ubv",
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

class FPToReal(inner: Expression<FPSort>) : Expression<RealSort>() {
  override val symbol: String = "(fp.to_real $inner)"
  override val sort: RealSort = RealSort
}

object FPToRealDecl :
    FunctionDecl1<FPSort, RealSort>(
        "fp.to_real",
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

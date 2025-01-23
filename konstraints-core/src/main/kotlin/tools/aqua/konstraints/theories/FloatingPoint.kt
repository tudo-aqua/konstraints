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

package tools.aqua.konstraints.theories

import tools.aqua.konstraints.parser.*
import tools.aqua.konstraints.smt.*

/*
 * New Sorts defined by FloatingPoint theory
 */

/** RoundingMode sort object */
object RoundingMode : Sort("RoundingMode") {
  override val theories = setOf(Theories.FLOATING_POINT)
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

  override val theories = setOf(Theories.FLOATING_POINT)

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

  /*
  val zero = FPZero(exponentBits, significantBits)
  val minusZero = FPMinusZero(exponentBits, significantBits)
  val infinity = FPInfinity(exponentBits, significantBits)
  val minusInfinity = FPMinusInfinity(exponentBits, significantBits)
  val nan = FPNaN(exponentBits, significantBits)
  */
}

/** Standard 16-bit FloatingPoint sort */
object FP16 : FPBase(5.idx(), 11.idx())

/** Standard 32-bit FloatingPoint sort */
object FP32 : FPBase(8.idx(), 24.idx())

/** Standard 64-bit FloatingPoint sort */
object FP64 : FPBase(11.idx(), 53.idx())

/** Standard 128-bit FloatingPoint sort */
object FP128 : FPBase(15.idx(), 113.idx())

/*
 * RoundingMode functions
 */

object RoundNearestTiesToEven :
    ConstantExpression<RoundingMode>("roundNearestTiesToEven".symbol(), RoundingMode) {
  override val theories = setOf(Theories.FLOATING_POINT)

  override fun copy(children: List<Expression<*>>): Expression<RoundingMode> = this
}

object RNE : ConstantExpression<RoundingMode>("RNE".symbol(), RoundingMode) {
  override val theories = setOf(Theories.FLOATING_POINT)

  override fun copy(children: List<Expression<*>>): Expression<RoundingMode> = this
}

object RoundNearestTiesToAway :
    ConstantExpression<RoundingMode>("roundNearestTiesToAway".symbol(), RoundingMode) {
  override val theories = setOf(Theories.FLOATING_POINT)

  override fun copy(children: List<Expression<*>>): Expression<RoundingMode> = this
}

object RNA : ConstantExpression<RoundingMode>("RNA".symbol(), RoundingMode) {
  override val theories = setOf(Theories.FLOATING_POINT)

  override fun copy(children: List<Expression<*>>): Expression<RoundingMode> = this
}

object RoundTowardPositive :
    ConstantExpression<RoundingMode>("roundTowardPositive".symbol(), RoundingMode) {
  override val theories = setOf(Theories.FLOATING_POINT)

  override fun copy(children: List<Expression<*>>): Expression<RoundingMode> = this
}

object RTP : ConstantExpression<RoundingMode>("RTP".symbol(), RoundingMode) {
  override val theories = setOf(Theories.FLOATING_POINT)

  override fun copy(children: List<Expression<*>>): Expression<RoundingMode> = this
}

object RoundTowardNegative :
    ConstantExpression<RoundingMode>("roundTowardNegative".symbol(), RoundingMode) {
  override val theories = setOf(Theories.FLOATING_POINT)

  override fun copy(children: List<Expression<*>>): Expression<RoundingMode> = this
}

object RTN : ConstantExpression<RoundingMode>("RTN".symbol(), RoundingMode) {
  override val theories = setOf(Theories.FLOATING_POINT)

  override fun copy(children: List<Expression<*>>): Expression<RoundingMode> = this
}

object RoundTowardZero :
    ConstantExpression<RoundingMode>("roundTowardZero".symbol(), RoundingMode) {
  override val theories = setOf(Theories.FLOATING_POINT)

  override fun copy(children: List<Expression<*>>): Expression<RoundingMode> = this
}

object RTZ : ConstantExpression<RoundingMode>("RTZ".symbol(), RoundingMode) {
  override val theories = setOf(Theories.FLOATING_POINT)

  override fun copy(children: List<Expression<*>>): Expression<RoundingMode> = this
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

  companion object {
    operator fun invoke(value: Double): FPLiteral {
      // TODO special cases (NaN, Inf etc.)
      val bitvec = value.toRawBits().toString()

      return FPLiteral(
          bitvec.substring(0..0).bitvec(),
          bitvec.substring(1..11).bitvec(),
          bitvec.substring(12).bitvec())
    }

    operator fun invoke(value: Float): FPLiteral {
      // TODO special cases (NaN, Inf etc.)
      val bitvec = value.toRawBits().toString()

      return FPLiteral(
          bitvec.substring(0..0).bitvec(),
          bitvec.substring(1..8).bitvec(),
          bitvec.substring(9).bitvec())
    }

    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override fun copy(children: List<Expression<*>>): Expression<FPSort> = this
}

/**
 * Representation of plus infinity for a given number of bits
 *
 * ((_ +oo [eb] [sb]) (_ FloatingPoint [eb] [sb]))
 */
class FPInfinity(val eb: Int, val sb: Int) :
    ConstantExpression<FPSort>("+oo".symbol(), FPSort(eb, sb)) {
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override fun toString(): String = "(_ +oo $eb $sb)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> = this
}

/**
 * Representation of minus infinity for a given number of bits
 *
 * ((_ -oo [eb] [sb]) (_ FloatingPoint [eb] [sb]))
 */
class FPMinusInfinity(val eb: Int, val sb: Int) :
    ConstantExpression<FPSort>("-oo".symbol(), FPSort(eb, sb)) {
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override fun toString(): String = "(_ -oo $eb $sb)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> = this
}

/**
 * Representation of plus zero for a given number of bits
 *
 * ((_ +zero [eb] [sb]) (_ FloatingPoint [eb] [sb]))
 */
class FPZero(val eb: Int, val sb: Int) :
    ConstantExpression<FPSort>("+zero".symbol(), FPSort(eb, sb)) {
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override fun toString(): String = "(_ +zero $eb $sb)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> = this
}

/**
 * Representation of minus zero for a given number of bits
 *
 * ((_ -zero [eb] [sb]) (_ FloatingPoint [eb] [sb]))
 */
class FPMinusZero(val eb: Int, val sb: Int) :
    ConstantExpression<FPSort>("-zero".symbol(), FPSort(eb, sb)) {
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override fun toString(): String = "(_ -zero $eb $sb)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> = this
}

/**
 * Representation of NaN for a given number of bits
 *
 * ((_ NaN [eb] [sb]) (_ FloatingPoint [eb] [sb]))
 */
class FPNaN(val eb: Int, val sb: Int) : ConstantExpression<FPSort>("NaN".symbol(), FPSort(eb, sb)) {
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override fun toString(): String = "(_ NaN $eb $sb)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> = this
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
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPAbsDecl.buildExpression(children, emptyList())
}

/**
 * Floating point negation, sort will be automatically determined from [inner]
 *
 * (fp.neg (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
 */
class FPNeg(override val inner: Expression<FPSort>) :
    UnaryExpression<FPSort, FPSort>("fp.neg".symbol(), inner.sort) {
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPNegDecl.buildExpression(children, emptyList())
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
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

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
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

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
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

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
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

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
  override val func = null

  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(multiplier.sort == multiplicand.sort)
    require(multiplier.sort == summand.sort)
  }

  override val children: List<Expression<*>> =
      listOf(roundingMode, multiplier, multiplicand, summand)

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPFmaDecl.buildExpression(children, emptyList())
}

/**
 * Floating point square root, sort will be automatically determined from [inner]
 *
 * (fp.sqrt RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
 */
class FPSqrt(val roundingMode: Expression<RoundingMode>, val inner: Expression<FPSort>) :
    BinaryExpression<FPSort, RoundingMode, FPSort>("fp.sqrt".symbol(), inner.sort) {
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override val lhs: Expression<RoundingMode> = roundingMode

  override val rhs: Expression<FPSort> = inner

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPSqrtDecl.buildExpression(children, emptyList())
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
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override val lhs: Expression<FPSort> = dividend

  override val rhs: Expression<FPSort> = divisor

  init {
    require(dividend.sort == divisor.sort)
  }

  override fun toString(): String = "(fp.rem $dividend $divisor)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPRemDecl.buildExpression(children, emptyList())
}

/**
 * Floating point rounding to integral, sort will be automatically determined from [inner]
 *
 * (fp.roundToIntegral RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
 */
class FPRoundToIntegral(val roundingMode: Expression<RoundingMode>, val inner: Expression<FPSort>) :
    BinaryExpression<FPSort, RoundingMode, FPSort>("fp.roundToIntegral".symbol(), inner.sort) {
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override val lhs: Expression<RoundingMode> = roundingMode

  override val rhs: Expression<FPSort> = inner

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPRoundToIntegralDecl.buildExpression(children, emptyList())
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
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(lhs.sort == rhs.sort)
  }

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPMinDecl.buildExpression(children, emptyList())
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
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(lhs.sort == rhs.sort)
  }

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPMaxDecl.buildExpression(children, emptyList())
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
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

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
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

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
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

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
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

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
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  constructor(vararg terms: Expression<FPSort>) : this(terms.toList())

  override val children: List<Expression<FPSort>> = terms

  init {
    require(terms.size > 1)
    terms.zipWithNext { a, b -> require(a.sort == b.sort) }
  }

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPEqDecl.buildExpression(children, emptyList())
}

/** (fp.isNormal (_ FloatingPoint eb sb) Bool) */
class FPIsNormal(override val inner: Expression<FPSort>) :
    UnaryExpression<BoolSort, FPSort>("fp.isNormal".symbol(), BoolSort) {
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPIsNormalDecl.buildExpression(children, emptyList())
}

/** (fp.isSubnormal (_ FloatingPoint eb sb) Bool) */
class FPIsSubnormal(override val inner: Expression<FPSort>) :
    UnaryExpression<BoolSort, FPSort>("fp.isSubnormal".symbol(), BoolSort) {
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPIsSubormalDecl.buildExpression(children, emptyList())
}

/** (fp.isZero (_ FloatingPoint eb sb) Bool) */
class FPIsZero(override val inner: Expression<FPSort>) :
    UnaryExpression<BoolSort, FPSort>("fp.isZero".symbol(), BoolSort) {
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPIsZeroDecl.buildExpression(children, emptyList())
}

/** (fp.isInfinite (_ FloatingPoint eb sb) Bool) */
class FPIsInfinite(override val inner: Expression<FPSort>) :
    UnaryExpression<BoolSort, FPSort>("fp.isInfinite".symbol(), BoolSort) {
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPIsInfiniteDecl.buildExpression(children, emptyList())
}

/** (fp.isNaN (_ FloatingPoint eb sb) Bool) */
class FPIsNaN(override val inner: Expression<FPSort>) :
    UnaryExpression<BoolSort, FPSort>("fp.isNaN".symbol(), BoolSort) {
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPIsNaNDecl.buildExpression(children, emptyList())
}

/** (fp.isNegative (_ FloatingPoint eb sb) Bool) */
class FPIsNegative(override val inner: Expression<FPSort>) :
    UnaryExpression<BoolSort, FPSort>("fp.isNegative".symbol(), BoolSort) {
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPIsNegativeDecl.buildExpression(children, emptyList())
}

/** (fp.isPositive (_ FloatingPoint eb sb) Bool) */
class FPIsPositive(override val inner: Expression<FPSort>) :
    UnaryExpression<BoolSort, FPSort>("fp.isPositive".symbol(), BoolSort) {
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPIsPositiveDecl.buildExpression(children, emptyList())
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
class BitVecToFP(override val inner: Expression<BVSort>, sort: FPSort) :
    UnaryExpression<FPSort, BVSort>("to_fp".symbol(), sort) {
  constructor(inner: Expression<BVSort>, eb: Int, sb: Int) : this(inner, FPSort(eb, sb))

  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(inner.sort.bits == sort.exponentBits + sort.significantBits)
  }

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      BitVecToFPDecl.buildExpression(children, emptyList())
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
    sort: FPSort
) : BinaryExpression<FPSort, RoundingMode, FPSort>("to_fp".symbol(), sort) {
  constructor(
      roundingMode: Expression<RoundingMode>,
      inner: Expression<FPSort>,
      eb: Int,
      sb: Int
  ) : this(roundingMode, inner, FPSort(eb, sb))

  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override val lhs: Expression<RoundingMode> = roundingMode

  override val rhs: Expression<FPSort> = inner

  override fun toString(): String =
      "((_ to_fp ${sort.exponentBits} ${sort.significantBits}) $roundingMode $inner)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPToFPDecl.buildExpression(children, emptyList())
}

/**
 * Convert a real [inner] to a floating point with given number of bits [eb] and [sb]
 *
 * ((_ to_fp eb sb) RoundingMode Real (_ FloatingPoint eb sb))
 */
class RealToFP(
    val roundingMode: Expression<RoundingMode>,
    val inner: Expression<RealSort>,
    sort: FPSort
) : BinaryExpression<FPSort, RoundingMode, RealSort>("to_fp".symbol(), sort) {
  constructor(
      roundingMode: Expression<RoundingMode>,
      inner: Expression<RealSort>,
      eb: Int,
      sb: Int
  ) : this(roundingMode, inner, FPSort(eb, sb))

  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override val lhs: Expression<RoundingMode> = roundingMode

  override val rhs: Expression<RealSort> = inner

  override fun toString(): String =
      "((_ to_fp ${sort.exponentBits} ${sort.significantBits}) $roundingMode $inner)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      RealToFPDecl.buildExpression(children, emptyList())
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
    sort: FPSort
) : BinaryExpression<FPSort, RoundingMode, BVSort>("to_fp".symbol(), sort) {
  constructor(
      roundingMode: Expression<RoundingMode>,
      inner: Expression<BVSort>,
      eb: Int,
      sb: Int
  ) : this(roundingMode, inner, FPSort(eb, sb))

  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override val lhs: Expression<RoundingMode> = roundingMode

  override val rhs: Expression<BVSort> = inner

  override fun toString(): String =
      "((_ to_fp ${sort.exponentBits} ${sort.significantBits}) $roundingMode $inner)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      SBitVecToFPDecl.buildExpression(children, emptyList())
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
    sort: FPSort
) : BinaryExpression<FPSort, RoundingMode, BVSort>("to_fp_unsigned".symbol(), sort) {
  constructor(
      roundingMode: Expression<RoundingMode>,
      inner: Expression<BVSort>,
      eb: Int,
      sb: Int
  ) : this(roundingMode, inner, FPSort(eb, sb))

  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override val lhs: Expression<RoundingMode> = roundingMode

  override val rhs: Expression<BVSort> = inner

  override fun toString(): String =
      "((_ to_fp_unsigned ${sort.exponentBits} ${sort.significantBits}) $roundingMode $inner)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      UBitVecToFPDecl.buildExpression(children, emptyList())
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
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override val lhs: Expression<RoundingMode> = roundingMode

  override val rhs: Expression<FPSort> = inner

  override fun toString(): String = "((_ fp.to_ubv $m) $roundingMode $inner)"

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      FPToUBitVecDecl.buildExpression(children, emptyList())
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
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override val lhs: Expression<RoundingMode> = roundingMode

  override val rhs: Expression<FPSort> = inner

  override fun toString(): String = "((_ fp.to_sbv $m) $roundingMode $inner)"

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      FPToSBitVecDecl.buildExpression(children, emptyList())
}

/**
 * Convert a floating point [inner] to real
 *
 * (fp.to_real (_ FloatingPoint eb sb) Real)
 */
class FPToReal(override val inner: Expression<FPSort>) :
    UnaryExpression<RealSort, FPSort>("fp.to_real".symbol(), RealSort) {
  companion object {
    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override fun copy(children: List<Expression<*>>): Expression<RealSort> =
      FPToRealDecl.buildExpression(children, emptyList())
}

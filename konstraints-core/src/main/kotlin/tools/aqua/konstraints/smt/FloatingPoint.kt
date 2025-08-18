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

import tools.aqua.konstraints.parser.*

/*
 * RoundingMode functions
 */

/** Rounding mode round nearest ties to even. */
object RoundNearestTiesToEven :
    ConstantExpression<RoundingModeSort>(
        "roundNearestTiesToEven".toSymbolWithQuotes(), RoundingMode) {
  override val theories = FLOATING_POINT_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<RoundingModeSort> = this
}

/** Rounding mode round nearest ties to even. */
object RNE : ConstantExpression<RoundingModeSort>("RNE".toSymbolWithQuotes(), RoundingMode) {
  override val theories = FLOATING_POINT_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<RoundingModeSort> = this
}

/** Rounding mode round nearest ties to away. */
object RoundNearestTiesToAway :
    ConstantExpression<RoundingModeSort>(
        "roundNearestTiesToAway".toSymbolWithQuotes(), RoundingMode) {
  override val theories = FLOATING_POINT_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<RoundingModeSort> = this
}

/** Rounding mode round nearest ties to away. */
object RNA : ConstantExpression<RoundingModeSort>("RNA".toSymbolWithQuotes(), RoundingMode) {
  override val theories = FLOATING_POINT_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<RoundingModeSort> = this
}

/** Rounding mode round toward positive. */
object RoundTowardPositive :
    ConstantExpression<RoundingModeSort>("roundTowardPositive".toSymbolWithQuotes(), RoundingMode) {
  override val theories = FLOATING_POINT_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<RoundingModeSort> = this
}

/** Rounding mode round toward positive. */
object RTP : ConstantExpression<RoundingModeSort>("RTP".toSymbolWithQuotes(), RoundingMode) {
  override val theories = FLOATING_POINT_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<RoundingModeSort> = this
}

/** Rounding mode round toward negative. */
object RoundTowardNegative :
    ConstantExpression<RoundingModeSort>("roundTowardNegative".toSymbolWithQuotes(), RoundingMode) {
  override val theories = FLOATING_POINT_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<RoundingModeSort> = this
}

/** Rounding mode round toward negative. */
object RTN : ConstantExpression<RoundingModeSort>("RTN".toSymbolWithQuotes(), RoundingMode) {
  override val theories = FLOATING_POINT_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<RoundingModeSort> = this
}

/** Rounding mode round toward zero. */
object RoundTowardZero :
    ConstantExpression<RoundingModeSort>("roundTowardZero".toSymbolWithQuotes(), RoundingMode) {
  override val theories = FLOATING_POINT_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<RoundingModeSort> = this
}

/** Rounding mode round toward zero. */
object RTZ : ConstantExpression<RoundingModeSort>("RTZ".toSymbolWithQuotes(), RoundingMode) {
  override val theories = FLOATING_POINT_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<RoundingModeSort> = this
}

/*
 * Floating Point Literals
 */

/**
 * Representation of plus infinity for a given number of bits.
 *
 * ((_ +oo [eb] [sb]) (_ FloatingPoint [eb] [sb]))
 */
class FPInfinity(val eb: Int, val sb: Int) :
    ConstantExpression<FPSort>("+oo".toSymbolWithQuotes(), FPSort(eb, sb)) {
  override val theories = FLOATING_POINT_MARKER_SET

  override fun toString(): String = "(_ +oo $eb $sb)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> = this
}

/**
 * Representation of minus infinity for a given number of bits.
 *
 * ((_ -oo [eb] [sb]) (_ FloatingPoint [eb] [sb]))
 */
class FPMinusInfinity(val eb: Int, val sb: Int) :
    ConstantExpression<FPSort>("-oo".toSymbolWithQuotes(), FPSort(eb, sb)) {
  override val theories = FLOATING_POINT_MARKER_SET

  override fun toString(): String = "(_ -oo $eb $sb)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> = this
}

/**
 * Representation of plus zero for a given number of bits.
 *
 * ((_ +zero [eb] [sb]) (_ FloatingPoint [eb] [sb]))
 */
class FPZero(val eb: Int, val sb: Int) :
    ConstantExpression<FPSort>("+zero".toSymbolWithQuotes(), FPSort(eb, sb)) {
  override val theories = FLOATING_POINT_MARKER_SET

  override fun toString(): String = "(_ +zero $eb $sb)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> = this
}

/**
 * Representation of minus zero for a given number of bits.
 *
 * ((_ -zero [eb] [sb]) (_ FloatingPoint [eb] [sb]))
 */
class FPMinusZero(val eb: Int, val sb: Int) :
    ConstantExpression<FPSort>("-zero".toSymbolWithQuotes(), FPSort(eb, sb)) {
  override val theories = FLOATING_POINT_MARKER_SET

  override fun toString(): String = "(_ -zero $eb $sb)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> = this
}

/**
 * Representation of NaN for a given number of bits.
 *
 * ((_ NaN [eb] [sb]) (_ FloatingPoint [eb] [sb]))
 */
class FPNaN(val eb: Int, val sb: Int) :
    ConstantExpression<FPSort>("NaN".toSymbolWithQuotes(), FPSort(eb, sb)) {
  override val theories = FLOATING_POINT_MARKER_SET

  override fun toString(): String = "(_ NaN $eb $sb)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> = this
}

/*
 * Operators
 */

/**
 * Floating point absolute value, sort will be automatically determined from [inner].
 *
 * (fp.abs (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
 */
class FPAbs(override val inner: Expression<FPSort>) :
    UnaryExpression<FPSort, FPSort>("fp.abs".toSymbolWithQuotes(), inner.sort) {
  override val theories = FLOATING_POINT_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPAbsDecl.constructDynamic(children, emptyList())
}

/**
 * Floating point negation, sort will be automatically determined from [inner].
 *
 * (fp.neg (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
 */
class FPNeg(override val inner: Expression<FPSort>) :
    UnaryExpression<FPSort, FPSort>("fp.neg".toSymbolWithQuotes(), inner.sort) {
  override val theories = FLOATING_POINT_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPNegDecl.constructDynamic(children, emptyList())
}

/**
 * Floating point addition, sort will be automatically determined from [leftTerm].
 *
 * @throws IllegalArgumentException if [leftTerm] and [rightTerm] do not have the same sort
 *
 * (fp.add RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
 */
class FPAdd(
    val roundingMode: Expression<RoundingModeSort>,
    val leftTerm: Expression<FPSort>,
    val rightTerm: Expression<FPSort>
) :
    TernaryExpression<FPSort, RoundingModeSort, FPSort, FPSort>(
        "fp.add".toSymbolWithQuotes(), leftTerm.sort) {
  override val theories = FLOATING_POINT_MARKER_SET

  override val lhs: Expression<RoundingModeSort> = roundingMode

  override val mid: Expression<FPSort> = leftTerm

  override val rhs: Expression<FPSort> = rightTerm

  init {
    // this check ensures that lhs and rhs have the same floating point format
    require(leftTerm.sort == rightTerm.sort)
  }

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPAddDecl.constructDynamic(children, emptyList())
}

/**
 * Floating point subtraction, sort will be automatically determined from [minuend].
 *
 * @throws IllegalArgumentException if [minuend] and [subtrahend] do not have the same sort
 *
 * (fp.sub RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
 */
class FPSub(
    val roundingMode: Expression<RoundingModeSort>,
    val minuend: Expression<FPSort>,
    val subtrahend: Expression<FPSort>
) :
    TernaryExpression<FPSort, RoundingModeSort, FPSort, FPSort>(
        "fp.sub".toSymbolWithQuotes(), minuend.sort) {
  override val theories = FLOATING_POINT_MARKER_SET

  override val lhs: Expression<RoundingModeSort> = roundingMode

  override val mid: Expression<FPSort> = minuend

  override val rhs: Expression<FPSort> = subtrahend

  init {
    // this check ensures that lhs and rhs have the same floating point format
    require(minuend.sort == subtrahend.sort)
  }

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPSubDecl.constructDynamic(children, emptyList())
}

/**
 * Floating point multiplication, sort will be automatically determined from [multiplier].
 *
 * @throws IllegalArgumentException if [multiplier] and [multiplicand] do not have the same sort
 *
 * (fp.mul RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
 */
class FPMul(
    val roundingMode: Expression<RoundingModeSort>,
    val multiplier: Expression<FPSort>,
    val multiplicand: Expression<FPSort>
) :
    TernaryExpression<FPSort, RoundingModeSort, FPSort, FPSort>(
        "fp.mul".toSymbolWithQuotes(), multiplier.sort) {
  override val theories = FLOATING_POINT_MARKER_SET

  override val lhs: Expression<RoundingModeSort> = roundingMode

  override val mid: Expression<FPSort> = multiplier

  override val rhs: Expression<FPSort> = multiplicand

  init {
    // this check ensures that lhs and rhs have the same floating point format
    require(multiplier.sort == multiplicand.sort)
  }

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPMulDecl.constructDynamic(children, emptyList())
}

/**
 * Floating point division, sort will be automatically determined from [dividend].
 *
 * @throws IllegalArgumentException if [dividend] and [divisor] do not have the same sort
 *
 * (fp.div RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
 */
class FPDiv(
    val roundingMode: Expression<RoundingModeSort>,
    val dividend: Expression<FPSort>,
    val divisor: Expression<FPSort>
) :
    TernaryExpression<FPSort, RoundingModeSort, FPSort, FPSort>(
        "fp.div".toSymbolWithQuotes(), dividend.sort) {
  override val theories = FLOATING_POINT_MARKER_SET

  override val lhs: Expression<RoundingModeSort> = roundingMode

  override val mid: Expression<FPSort> = dividend

  override val rhs: Expression<FPSort> = divisor

  init {
    // this check ensures that lhs and rhs have the same floating point format
    require(dividend.sort == divisor.sort)
  }

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPDivDecl.constructDynamic(children, emptyList())
}

/**
 * Floating point fused multiplication and addition ([multiplier] * [multiplicand]) + [summand],
 * sort will be automatically determined from [multiplier].
 *
 * @throws IllegalArgumentException if [multiplier], [multiplicand] and [summand] do not have the
 *   same sort
 *
 * (fp.fma RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
 */
class FPFma(
    val roundingMode: Expression<RoundingModeSort>,
    val multiplier: Expression<FPSort>,
    val multiplicand: Expression<FPSort>,
    val summand: Expression<FPSort>
) : NAryExpression<FPSort>("fp.fma".toSymbolWithQuotes(), multiplier.sort) {
  override val func = null

  override val theories = FLOATING_POINT_MARKER_SET

  init {
    require(multiplier.sort == multiplicand.sort)
    require(multiplier.sort == summand.sort)
  }

  override val children: List<Expression<*>> =
      listOf(roundingMode, multiplier, multiplicand, summand)

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPFmaDecl.constructDynamic(children, emptyList())
}

/**
 * Floating point square root, sort will be automatically determined from [inner].
 *
 * (fp.sqrt RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
 */
class FPSqrt(val roundingMode: Expression<RoundingModeSort>, val inner: Expression<FPSort>) :
    BinaryExpression<FPSort, RoundingModeSort, FPSort>("fp.sqrt".toSymbolWithQuotes(), inner.sort) {
  override val theories = FLOATING_POINT_MARKER_SET

  override val lhs: Expression<RoundingModeSort> = roundingMode

  override val rhs: Expression<FPSort> = inner

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPSqrtDecl.constructDynamic(children, emptyList())
}

/**
 * Floating point remainder: [dividend] - [divisor] * n, where n in Z is nearest to
 * [dividend]/[divisor], sort will be automatically determined from [dividend].
 *
 * @throws IllegalArgumentException if [dividend] and [divisor] do not have the same sort
 *
 * (fp.rem (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
 */
class FPRem(val dividend: Expression<FPSort>, val divisor: Expression<FPSort>) :
    BinaryExpression<FPSort, FPSort, FPSort>("fp.rem".toSymbolWithQuotes(), dividend.sort) {
  override val theories = FLOATING_POINT_MARKER_SET

  override val lhs: Expression<FPSort> = dividend

  override val rhs: Expression<FPSort> = divisor

  init {
    require(dividend.sort == divisor.sort)
  }

  override fun toString(): String = "(fp.rem $dividend $divisor)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPRemDecl.constructDynamic(children, emptyList())
}

/**
 * Floating point rounding to integral, sort will be automatically determined from [inner].
 *
 * (fp.roundToIntegral RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
 */
class FPRoundToIntegral(
    val roundingMode: Expression<RoundingModeSort>,
    val inner: Expression<FPSort>
) :
    BinaryExpression<FPSort, RoundingModeSort, FPSort>(
        "fp.roundToIntegral".toSymbolWithQuotes(), inner.sort) {
  override val theories = FLOATING_POINT_MARKER_SET

  override val lhs: Expression<RoundingModeSort> = roundingMode

  override val rhs: Expression<FPSort> = inner

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPRoundToIntegralDecl.constructDynamic(children, emptyList())
}

/**
 * Floating point minimum, sort will be automatically determined from [lhs].
 *
 * @throws IllegalArgumentException if [lhs] and [rhs] do not have the same sort
 *
 * (fp.min (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
 */
class FPMin(override val lhs: Expression<FPSort>, override val rhs: Expression<FPSort>) :
    BinaryExpression<FPSort, FPSort, FPSort>("fp.min".toSymbolWithQuotes(), lhs.sort) {
  override val theories = FLOATING_POINT_MARKER_SET

  init {
    require(lhs.sort == rhs.sort)
  }

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPMinDecl.constructDynamic(children, emptyList())
}

/**
 * Floating point maximum, sort will be automatically determined from [lhs].
 *
 * @throws IllegalArgumentException if [lhs] and [rhs] do not have the same sort
 *
 * (fp.max (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
 */
class FPMax(override val lhs: Expression<FPSort>, override val rhs: Expression<FPSort>) :
    BinaryExpression<FPSort, FPSort, FPSort>("fp.max".toSymbolWithQuotes(), lhs.sort) {
  override val theories = FLOATING_POINT_MARKER_SET

  init {
    require(lhs.sort == rhs.sort)
  }

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPMaxDecl.constructDynamic(children, emptyList())
}

/**
 * Floating point less equals.
 *
 * @throws IllegalArgumentException if less than 2 [terms] are provided
 * @throws IllegalArgumentException if two [terms] have different sorts
 *
 * (fp.leq (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)
 */
class FPLeq(val terms: List<Expression<FPSort>>) :
    HomogenousExpression<BoolSort, FPSort>("fp.leq".toSymbolWithQuotes(), Bool) {
  override val theories = FLOATING_POINT_MARKER_SET

  constructor(vararg terms: Expression<FPSort>) : this(terms.toList())

  override val children: List<Expression<FPSort>> = terms

  init {
    require(terms.size > 1)
    terms.zipWithNext { a, b -> require(a.sort == b.sort) }
  }

  override fun toString(): String = "(fp.leq ${terms.joinToString(" ")})"

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPLeqDecl.constructDynamic(children, emptyList())
}

/**
 * Floating point less.
 *
 * @throws IllegalArgumentException if less than 2 [terms] are provided
 * @throws IllegalArgumentException if two [terms] have different sorts
 *
 * (fp.lt (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)
 */
class FPLt(val terms: List<Expression<FPSort>>) :
    HomogenousExpression<BoolSort, FPSort>("fp.lt".toSymbolWithQuotes(), Bool) {
  override val theories = FLOATING_POINT_MARKER_SET

  constructor(vararg terms: Expression<FPSort>) : this(terms.toList())

  override val children: List<Expression<FPSort>> = terms

  init {
    require(terms.size > 1)
    terms.zipWithNext { a, b -> require(a.sort == b.sort) }
  }

  override fun toString(): String = "(fp.lt ${terms.joinToString(" ")})"

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPLtDecl.constructDynamic(children, emptyList())
}

/**
 * Floating point greater equals.
 *
 * @throws IllegalArgumentException if less than 2 [terms] are provided
 * @throws IllegalArgumentException if two [terms] have different sorts
 *
 * (fp.geq (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)
 */
class FPGeq(val terms: List<Expression<FPSort>>) :
    HomogenousExpression<BoolSort, FPSort>("fp.geq".toSymbolWithQuotes(), Bool) {
  override val theories = FLOATING_POINT_MARKER_SET

  constructor(vararg terms: Expression<FPSort>) : this(terms.toList())

  override val children: List<Expression<FPSort>> = terms

  init {
    require(terms.size > 1)
    terms.zipWithNext { a, b -> require(a.sort == b.sort) }
  }

  override fun toString(): String = "(fp.geq ${terms.joinToString(" ")})"

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPGeqDecl.constructDynamic(children, emptyList())
}

/**
 * Floating point greater.
 *
 * @throws IllegalArgumentException if less than 2 [terms] are provided
 * @throws IllegalArgumentException if two [terms] have different sorts
 *
 * (fp.gt (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)
 */
class FPGt(val terms: List<Expression<FPSort>>) :
    HomogenousExpression<BoolSort, FPSort>("fp.gt".toSymbolWithQuotes(), Bool) {
  override val theories = FLOATING_POINT_MARKER_SET

  constructor(vararg terms: Expression<FPSort>) : this(terms.toList())

  override val children: List<Expression<FPSort>> = terms

  init {
    require(terms.size > 1)
    terms.zipWithNext { a, b -> require(a.sort == b.sort) }
  }

  override fun toString(): String = "(fp.gt ${terms.joinToString(" ")})"

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPGtDecl.constructDynamic(children, emptyList())
}

/**
 * Floating point equality (not SMT equality '=').
 *
 * @throws IllegalArgumentException if less than 2 [terms] are provided
 * @throws IllegalArgumentException if two [terms] have different sorts
 *
 * (fp.eq (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)
 */
class FPEq(val terms: List<Expression<FPSort>>) :
    HomogenousExpression<BoolSort, FPSort>("fp.eq".toSymbolWithQuotes(), Bool) {
  override val theories = FLOATING_POINT_MARKER_SET

  constructor(vararg terms: Expression<FPSort>) : this(terms.toList())

  override val children: List<Expression<FPSort>> = terms

  init {
    require(terms.size > 1)
    terms.zipWithNext { a, b -> require(a.sort == b.sort) }
  }

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPEqDecl.constructDynamic(children, emptyList())
}

/** (fp.isNormal (_ FloatingPoint eb sb) Bool). */
class FPIsNormal(override val inner: Expression<FPSort>) :
    UnaryExpression<BoolSort, FPSort>("fp.isNormal".toSymbolWithQuotes(), Bool) {
  override val theories = FLOATING_POINT_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPIsNormalDecl.constructDynamic(children, emptyList())
}

/** (fp.isSubnormal (_ FloatingPoint eb sb) Bool). */
class FPIsSubnormal(override val inner: Expression<FPSort>) :
    UnaryExpression<BoolSort, FPSort>("fp.isSubnormal".toSymbolWithQuotes(), Bool) {
  override val theories = FLOATING_POINT_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPIsSubormalDecl.constructDynamic(children, emptyList())
}

/** (fp.isZero (_ FloatingPoint eb sb) Bool). */
class FPIsZero(override val inner: Expression<FPSort>) :
    UnaryExpression<BoolSort, FPSort>("fp.isZero".toSymbolWithQuotes(), Bool) {
  override val theories = FLOATING_POINT_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPIsZeroDecl.constructDynamic(children, emptyList())
}

/** (fp.isInfinite (_ FloatingPoint eb sb) Bool). */
class FPIsInfinite(override val inner: Expression<FPSort>) :
    UnaryExpression<BoolSort, FPSort>("fp.isInfinite".toSymbolWithQuotes(), Bool) {
  override val theories = FLOATING_POINT_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPIsInfiniteDecl.constructDynamic(children, emptyList())
}

/** (fp.isNaN (_ FloatingPoint eb sb) Bool). */
class FPIsNaN(override val inner: Expression<FPSort>) :
    UnaryExpression<BoolSort, FPSort>("fp.isNaN".toSymbolWithQuotes(), Bool) {
  override val theories = FLOATING_POINT_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPIsNaNDecl.constructDynamic(children, emptyList())
}

/** (fp.isNegative (_ FloatingPoint eb sb) Bool). */
class FPIsNegative(override val inner: Expression<FPSort>) :
    UnaryExpression<BoolSort, FPSort>("fp.isNegative".toSymbolWithQuotes(), Bool) {
  override val theories = FLOATING_POINT_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPIsNegativeDecl.constructDynamic(children, emptyList())
}

/** (fp.isPositive (_ FloatingPoint eb sb) Bool). */
class FPIsPositive(override val inner: Expression<FPSort>) :
    UnaryExpression<BoolSort, FPSort>("fp.isPositive".toSymbolWithQuotes(), Bool) {
  override val theories = FLOATING_POINT_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      FPIsPositiveDecl.constructDynamic(children, emptyList())
}

/*
 * Conversion from other sorts
 */

/**
 * Convert a bitvector [inner] to floating point with the given [sort].
 *
 * @throws IllegalArgumentException if number of bits in [inner.sort] is not
 *   [sort.exponentBits] + [sort.significantBits]
 *
 * ((_ to_fp eb sb) (_ BitVec m) (_ FloatingPoint eb sb)), with m = eb + sb
 */
class BitVecToFP(override val inner: Expression<BVSort>, sort: FPSort) :
    UnaryExpression<FPSort, BVSort>("to_fp".toSymbolWithQuotes(), sort) {
  constructor(inner: Expression<BVSort>, eb: Int, sb: Int) : this(inner, FPSort(eb, sb))

  override val theories = FLOATING_POINT_MARKER_SET

  init {
    require(inner.sort.bits == sort.exponentBits + sort.significantBits)
  }

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      BitVecToFPDecl.constructDynamic(children, emptyList())
}

/**
 * Convert a floating point [inner] to a different floating point [sort].
 *
 * ((_ to_fp eb sb) RoundingMode (_ FloatingPoint mb nb) (_ FloatingPoint eb sb))
 */
class FPToFP(
    val roundingMode: Expression<RoundingModeSort>,
    val inner: Expression<FPSort>,
    sort: FPSort
) : BinaryExpression<FPSort, RoundingModeSort, FPSort>("to_fp".toSymbolWithQuotes(), sort) {
  constructor(
      roundingMode: Expression<RoundingModeSort>,
      inner: Expression<FPSort>,
      eb: Int,
      sb: Int
  ) : this(roundingMode, inner, FPSort(eb, sb))

  override val theories = FLOATING_POINT_MARKER_SET

  override val lhs: Expression<RoundingModeSort> = roundingMode

  override val rhs: Expression<FPSort> = inner

  override fun toString(): String =
      "((_ to_fp ${sort.exponentBits} ${sort.significantBits}) $roundingMode $inner)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      FPToFPDecl.constructDynamic(children, emptyList())
}

/**
 * Convert a real [inner] to a floating point with the given [sort].
 *
 * ((_ to_fp eb sb) RoundingMode Real (_ FloatingPoint eb sb))
 */
class RealToFP(
    val roundingMode: Expression<RoundingModeSort>,
    val inner: Expression<RealSort>,
    sort: FPSort
) : BinaryExpression<FPSort, RoundingModeSort, RealSort>("to_fp".toSymbolWithQuotes(), sort) {
  constructor(
      roundingMode: Expression<RoundingModeSort>,
      inner: Expression<RealSort>,
      eb: Int,
      sb: Int
  ) : this(roundingMode, inner, FPSort(eb, sb))

  override val theories = FLOATING_POINT_MARKER_SET

  override val lhs: Expression<RoundingModeSort> = roundingMode

  override val rhs: Expression<RealSort> = inner

  override fun toString(): String =
      "((_ to_fp ${sort.exponentBits} ${sort.significantBits}) $roundingMode $inner)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      RealToFPDecl.constructDynamic(children, emptyList())
}

/**
 * Convert a signed machine integer, represented as a 2's complement bit vector, [inner] to a
 * floating point with the given [sort].
 *
 * ((_ to_fp eb sb) RoundingMode (_ BitVec m) (_ FloatingPoint eb sb))
 */
class SBitVecToFP(
    val roundingMode: Expression<RoundingModeSort>,
    val inner: Expression<BVSort>,
    sort: FPSort
) : BinaryExpression<FPSort, RoundingModeSort, BVSort>("to_fp".toSymbolWithQuotes(), sort) {
  constructor(
      roundingMode: Expression<RoundingModeSort>,
      inner: Expression<BVSort>,
      eb: Int,
      sb: Int
  ) : this(roundingMode, inner, FPSort(eb, sb))

  override val theories = FLOATING_POINT_MARKER_SET

  override val lhs: Expression<RoundingModeSort> = roundingMode

  override val rhs: Expression<BVSort> = inner

  override fun toString(): String =
      "((_ to_fp ${sort.exponentBits} ${sort.significantBits}) $roundingMode $inner)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      SBitVecToFPDecl.constructDynamic(children, emptyList())
}

/**
 * Convert an unsigned machine integer, represented as bit vector, [inner] to a floating point with
 * the given [sort].
 *
 * ((_ to_fp_unsigned eb sb) RoundingMode (_ BitVec m) (_ FloatingPoint eb sb))
 */
class UBitVecToFP(
    val roundingMode: Expression<RoundingModeSort>,
    val inner: Expression<BVSort>,
    sort: FPSort
) :
    BinaryExpression<FPSort, RoundingModeSort, BVSort>(
        "to_fp_unsigned".toSymbolWithQuotes(), sort) {
  constructor(
      roundingMode: Expression<RoundingModeSort>,
      inner: Expression<BVSort>,
      eb: Int,
      sb: Int
  ) : this(roundingMode, inner, FPSort(eb, sb))

  override val theories = FLOATING_POINT_MARKER_SET

  override val lhs: Expression<RoundingModeSort> = roundingMode

  override val rhs: Expression<BVSort> = inner

  override fun toString(): String =
      "((_ to_fp_unsigned ${sort.exponentBits} ${sort.significantBits}) $roundingMode $inner)"

  override fun copy(children: List<Expression<*>>): Expression<FPSort> =
      UBitVecToFPDecl.constructDynamic(children, emptyList())
}

/*
 * Conversion to other sorts
 */

/**
 * Convert a floating point [inner] to an unsigned machine integer, represented as a bit vector of
 * length [m].
 *
 * ((_ fp.to_ubv m) RoundingMode (_ FloatingPoint eb sb) (_ BitVec m))
 */
class FPToUBitVec(
    val roundingMode: Expression<RoundingModeSort>,
    val inner: Expression<FPSort>,
    val m: Int
) :
    BinaryExpression<BVSort, RoundingModeSort, FPSort>(
        "fp.to_ubv".toSymbolWithQuotes(), BVSort(m)) {
  override val theories = FLOATING_POINT_MARKER_SET

  override val lhs: Expression<RoundingModeSort> = roundingMode

  override val rhs: Expression<FPSort> = inner

  override fun toString(): String = "((_ fp.to_ubv $m) $roundingMode $inner)"

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      FPToUBitVecDecl.constructDynamic(children, emptyList())
}

/**
 * Convert a floating point [inner] to a signed machine integer, represented as a 2's complement bit
 * vector of length [m].
 *
 * ((_ fp.to_ubv m) RoundingMode (_ FloatingPoint eb sb) (_ BitVec m))
 */
class FPToSBitVec(
    val roundingMode: Expression<RoundingModeSort>,
    val inner: Expression<FPSort>,
    val m: Int
) :
    BinaryExpression<BVSort, RoundingModeSort, FPSort>(
        "fp.to_sbv".toSymbolWithQuotes(), BVSort(m)) {
  override val theories = FLOATING_POINT_MARKER_SET

  override val lhs: Expression<RoundingModeSort> = roundingMode

  override val rhs: Expression<FPSort> = inner

  override fun toString(): String = "((_ fp.to_sbv $m) $roundingMode $inner)"

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      FPToSBitVecDecl.constructDynamic(children, emptyList())
}

/**
 * Convert a floating point [inner] to real.
 *
 * (fp.to_real (_ FloatingPoint eb sb) Real)
 */
class FPToReal(override val inner: Expression<FPSort>) :
    UnaryExpression<RealSort, FPSort>("fp.to_real".toSymbolWithQuotes(), Real) {
  override val theories = FLOATING_POINT_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<RealSort> =
      FPToRealDecl.constructDynamic(children, emptyList())
}

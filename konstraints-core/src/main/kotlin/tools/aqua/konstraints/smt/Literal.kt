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

import java.math.BigDecimal
import java.math.BigInteger

/**
 * Any form of bitvector literals either
 * - All binaries #bX of sort (_ BitVec m) where m is the number of digits in X or
 * - All hexadecimals #xX of sort (_ BitVec m) where m is 4 times the number of digits in X.
 */
class BVLiteral
private constructor(vector: String, val bits: Int, val isBinary: Boolean, val value: BigInteger) :
    Literal<BVSort>(LiteralString(vector), BVSort(bits)) {
  companion object {
    operator fun invoke(vector: String): BVLiteral =
        if (vector.isSMTBinary()) {
          BVLiteral(vector, vector.length - 2)
        } else if (vector.isSMTHex()) {
          BVLiteral(vector, (vector.length - 2) * 4)
        } else if (vector.isSMTBitvecShorthand()) {
          val tokens = vector.split(' ')
          BVLiteral(tokens[1], tokens[2].trim(')').toInt())
        } else {
          throw IllegalArgumentException("$vector is not a valid bitvector literal.")
        }

    operator fun invoke(vector: String, bits: Int) =
        if (vector.isSMTBinary()) {
          require(vector.length - 2 <= bits) {
            "BitVec literal $vector can not fit into request number of $bits bits"
          }
          BVLiteral(vector, bits, true, vector.substring(2).toBigInteger(2))
        } else if (vector.isSMTHex()) {
          require((vector.length - 2) * 4 <= bits) {
            "BitVec literal $vector can not fit into request number of $bits bits"
          }
          BVLiteral(vector, bits, false, vector.substring(2).toBigInteger(16))
        } else if (vector.startsWith("bv") && vector.substring(2).all { it.isDigit() }) {
          BVLiteral("(_ $vector $bits)", bits, false, vector.substring(2).toBigInteger(10))
        } else {
          throw IllegalArgumentException("$vector is not a valid bitvector literal.")
        }

    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS, Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override val sort = BVSort(bits)

  override fun toString() = name.toString()

  override fun copy(children: List<Expression<*>>): Expression<BVSort> = this

  override fun equals(other: Any?) =
      if (this === other) true
      else if (other !is BVLiteral) false else sort.bits == other.sort.bits && value == other.value
}

/**
 * d Floating-point literal.
 *
 * (fp [sign] [exponent] [significand])
 */
data class FPLiteral(
    val sign: Expression<BVSort>,
    val exponent: Expression<BVSort>,
    val significand: Expression<BVSort>,
) :
    Literal<FPSort>(
        LiteralString("(fp $sign $exponent $significand)"),
        FPSort(exponent.sort.bits, significand.sort.bits + 1),
    ) {

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
          bitvec.substring(12).bitvec(),
      )
    }

    operator fun invoke(value: Float): FPLiteral {
      // TODO special cases (NaN, Inf etc.)
      val bitvec = value.toRawBits().toString()

      return FPLiteral(
          bitvec.substring(0..0).bitvec(),
          bitvec.substring(1..8).bitvec(),
          bitvec.substring(9).bitvec(),
      )
    }

    private val theoriesSet = setOf(Theories.FLOATING_POINT)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override fun copy(children: List<Expression<*>>): Expression<FPSort> = this

  override fun equals(other: Any?) =
      if (this === other) true
      else if (other !is FPLiteral) false
      else
          sort.exponentBits == other.sort.exponentBits &&
              sort.significantBits == other.sort.significantBits &&
              sign == other.sign &&
              exponent == other.exponent &&
              significand == other.significand

  override fun toString() = "(fp $sign $exponent $significand)"
}

/**
 * Integer literals.
 *
 * (NUMERAL Int)
 */
class IntLiteral(val value: BigInteger) :
    Literal<IntSort>(LiteralString(value.toString()), SMTInt) {
  override val theories = INTS_REALS_INTS_MARKER_SET + STRINGS_MARKER_SET

  constructor(value: Byte) : this(value.toInt().toBigInteger())

  constructor(value: Short) : this(value.toInt().toBigInteger())

  constructor(value: Int) : this(value.toBigInteger())

  constructor(value: Long) : this(value.toBigInteger())

  override fun toString(): String = value.toString()

  override fun copy(children: List<Expression<*>>): Expression<IntSort> = this

  override fun equals(other: Any?) =
      if (this === other) true else if (other !is IntLiteral) false else value == other.value
}

/**
 * Real literal.
 *
 * (NUMERAL Real) (DECIMAL Real)
 */
class RealLiteral(val value: BigDecimal) :
    Literal<RealSort>(LiteralString(value.toPlainString()), Real) {
  override val theories = REALS_REALS_INTS_MARKER_SET.plus(FLOATING_POINT_MARKER_SET)

  constructor(value: Byte) : this(value.toInt().toBigDecimal())

  constructor(value: Short) : this(value.toInt().toBigDecimal())

  constructor(value: Int) : this(value.toBigDecimal())

  constructor(value: Long) : this(value.toBigDecimal())

  constructor(value: BigInteger) : this(value.toBigDecimal())

  constructor(value: Float) : this(value.toBigDecimal())

  constructor(value: Double) : this(value.toBigDecimal())

  override val sort: RealSort = Real

  override fun toString(): String = value.toPlainString()

  override fun copy(children: List<Expression<*>>): Expression<RealSort> = this

  override fun equals(other: Any?) =
      if (this === other) true else if (other !is RealLiteral) false else value == other.value
}

/**
 * [value] holds the hexadecimal unicode of the character, [character] hold the kotlin
 * representation, possible values range from #x0 to #x2FFFF and are generated by the following
 * grammar.
 *
 * ```
 * ⟨H⟩ ::= #x⟨F⟩ | #x⟨F⟩⟨F⟩ | #x⟨F⟩⟨F⟩⟨F⟩ | #x⟨F⟩⟨F⟩⟨F⟩⟨F⟩ | #x⟨2⟩⟨F⟩⟨F⟩⟨F⟩⟨F⟩
 * ⟨2⟩ ::= 0 | 1 | 2
 * ⟨F⟩ ::= ⟨2⟩ | 3 | 4 | 5 | 6 | 7 | 8 | 9
 *             | a | b | b | d | e | f
 *             | A | B | C | D | E | F
 * ```
 */
class Char(val value: String) : Literal<StringSort>(LiteralString("char"), SMTString) {
  override val theories = STRINGS_MARKER_SET

  val character = Char(Integer.parseInt(value.substring(2)))

  override fun copy(children: List<Expression<*>>): Expression<StringSort> = this

  override fun equals(other: Any?) =
      if (this === other) true else if (other !is Char) false else character == other.character
}

class StringLiteral(val value: String) : Literal<StringSort>(LiteralString("\"$value\""), SMTString) {
  override val theories = STRINGS_MARKER_SET

  // use symbol.toString here to get the unquoted string literal
  override fun toString(): String = "\"$value\""

  override fun toSMTString(quotingRule: QuotingRule) = toString()

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule) =
      builder.append(toString())

  override fun copy(children: List<Expression<*>>): Expression<StringSort> = this

  override fun equals(other: Any?) =
      if (this === other) true else if (other !is StringLiteral) false else value == other.value
}

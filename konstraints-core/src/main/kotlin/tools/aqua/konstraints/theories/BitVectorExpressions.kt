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

import java.math.BigInteger
import tools.aqua.konstraints.parser.*
import tools.aqua.konstraints.smt.*

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
        if (vector[1] == 'b') {
          BVLiteral(vector, vector.length - 2)
        } else if (vector[1] == 'x') {
          BVLiteral(vector, (vector.length - 2) * 4)
        } else {
          throw IllegalArgumentException("$vector is not a valid bitvector literal.")
        }

    operator fun invoke(vector: String, bits: Int) =
        if (vector[1] == 'b') {
          require(vector.length - 2 <= bits) {
            "BitVec literal $vector can not fit into request number of $bits bits"
          }
          BVLiteral(vector, bits, true, vector.substring(2).toBigInteger(2))
        } else if (vector[1] == 'x') {
          require((vector.length - 2) * 4 <= bits) {
            "BitVec literal $vector can not fit into request number of $bits bits"
          }
          BVLiteral(vector, bits, false, vector.substring(2).toBigInteger(16))
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
}

fun String.bitvec() = BVLiteral(this)

fun String.bitvec(bits: Int) = BVLiteral(this, bits)

/**
 * Concatenation of two [Expression]s of [BVSort]
 *
 * @param [lhs] left [Expression]
 * @param [rhs] right [Expression]
 */
class BVConcat(override val lhs: Expression<BVSort>, override val rhs: Expression<BVSort>) :
    BinaryExpression<BVSort, BVSort, BVSort>("concat".symbol(), BVSort(1)) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override val sort: BVSort = BVSort(lhs.sort.bits + rhs.sort.bits)

  override val name: Symbol = "concat".symbol()

  init {
    require(!lhs.sort.isSymbolic())
    require(!rhs.sort.isSymbolic())
  }

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      BVConcatDecl.buildExpression(children, emptyList())
}

/**
 * Extraction of bits from [inner] starting with the [j]th bit until the [i]th
 *
 * @param [i] last bit to be extracted (inclusive)
 * @param [j] first bit to be extracted (inclusive)
 * @param [inner] [Expression] to extract the bits from
 * @throws [IllegalArgumentException] if the constraint m > i ≥ j ≥ 0 is violated, where m is the
 *   number of bits in [inner]
 */
class BVExtract(val i: Int, val j: Int, override val inner: Expression<BVSort>) :
    UnaryExpression<BVSort, BVSort>("extract".symbol(), BVSort(1)) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override val sort: BVSort = BVSort(i - j + 1)

  init {
    require(j >= 0) { "j needs to be greater or equal to 0, but was $j" }
    require(i >= j) { "i needs to be greater or equal to j, but was $i" }
    require(inner.sort.bits > i) {
      "i can not be greater than the number of bits in inner, but was $i"
    }
  }

  override fun toString(): String = "((_ extract $i $j) $inner)"

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      ExtractDecl.buildExpression(children, listOf(i.idx(), j.idx()))
}

/**
 * Bitwise not operation on bitvectors
 *
 * @param [inner] [Expression] to be inverted
 */
class BVNot(override val inner: Expression<BVSort>) :
    UnaryExpression<BVSort, BVSort>("bvnot".symbol(), inner.sort) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(!inner.sort.isSymbolic())
  }

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      BVNotDecl.buildExpression(children, emptyList())
}

/**
 * Negation operation on bitvectors
 *
 * @param [inner] [Expression] to be negated
 */
class BVNeg(override val inner: Expression<BVSort>) :
    UnaryExpression<BVSort, BVSort>("bvneg".symbol(), inner.sort) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(!inner.sort.isSymbolic())
  }

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      BVNegDecl.buildExpression(children, emptyList())
}

/**
 * Bitwise and operation on bitvectors
 *
 * @param [conjuncts] List of [Expression]s to be combined by and
 * @throws [IllegalArgumentException] if two [conjuncts] do not have the same number of bits
 */
class BVAnd(val conjuncts: List<Expression<BVSort>>) :
    HomogenousExpression<BVSort, BVSort>("bvand".symbol(), conjuncts.first().sort) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  /**
   * Bitwise and operation on bitvectors
   *
   * @param [conjuncts] any number of [Expression]s to be combined by and
   * @throws [IllegalArgumentException] if two [conjuncts] do not have the same number of bits
   */
  constructor(vararg conjuncts: Expression<BVSort>) : this(conjuncts.toList())

  init {
    require(conjuncts.all { it.sort.bits == sort.bits }) {
      "All bitvectors must have the same number of bits"
    }

    require(conjuncts.all { !it.sort.isSymbolic() })
  }

  override val children: List<Expression<BVSort>> = conjuncts

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      BVAndDecl.buildExpression(children, emptyList())
}

/**
 * Bitwise or operation on bitvectors
 *
 * @param [disjuncts] List of [Expression]s to be combined by or
 * @throws [IllegalArgumentException] if two [disjuncts] do not have the same number of bits
 */
class BVOr(val disjuncts: List<Expression<BVSort>>) :
    HomogenousExpression<BVSort, BVSort>("bvor".symbol(), disjuncts.first().sort) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  /**
   * Bitwise or operation on bitvectors
   *
   * @param [disjuncts] any number of [Expression]s to be combined by or
   * @throws [IllegalArgumentException] if two [disjuncts] do not have the same number of bits
   */
  constructor(vararg disjuncts: Expression<BVSort>) : this(disjuncts.toList())

  override val children: List<Expression<BVSort>> = disjuncts

  init {
    require(disjuncts.all { it.sort.bits == sort.bits }) {
      "All bitvectors must have the same number of bits"
    }

    require(disjuncts.all { !it.sort.isSymbolic() })
  }

  override fun toString(): String = "(bvor ${disjuncts.joinToString(" ")})"

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      BVOrDecl.buildExpression(children, emptyList())
}

/**
 * Addition operation on bitvectors
 *
 * @param [summands] List of [Expression]s to be added up
 * @throws [IllegalArgumentException] if two [summands] do not have the same number of bits
 */
class BVAdd(val summands: List<Expression<BVSort>>) :
    HomogenousExpression<BVSort, BVSort>("bvadd".symbol(), summands.first().sort) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  /**
   * Addition operation on bitvectors
   *
   * @param [summands] any number of [Expression]s to be added up
   * @throws [IllegalArgumentException] if two [summands] do not have the same number of bits
   */
  constructor(vararg summands: Expression<BVSort>) : this(summands.toList())

  init {
    require(summands.all { it.sort.bits == sort.bits }) {
      "All bitvectors must have the same number of bits"
    }

    require(summands.all { !it.sort.isSymbolic() })
  }

  override val children: List<Expression<BVSort>> = summands

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      BVAddDecl.buildExpression(children, emptyList())
}

/**
 * Multiplication operation on bitvectors
 *
 * @param [factors] List of [Expression]s to be multiplied
 * @throws [IllegalArgumentException] if two [factors] do not have the same number of bits
 */
class BVMul(val factors: List<Expression<BVSort>>) :
    HomogenousExpression<BVSort, BVSort>("bvmul".symbol(), factors.first().sort) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  /**
   * Multiplication operation on bitvectors
   *
   * @param [factors] any number of [Expression]s to be multiplied
   * @throws [IllegalArgumentException] if two [factors] do not have the same number of bits
   */
  constructor(vararg factors: Expression<BVSort>) : this(factors.toList())

  init {
    require(factors.all { it.sort.bits == sort.bits }) {
      "All bitvectors must have the same number of bits"
    }

    require(factors.all { !it.sort.isSymbolic() })
  }

  override val children: List<Expression<BVSort>> = factors

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      BVMulDecl.buildExpression(children, emptyList())
}

/**
 * Unsigned division operation on bitvectors
 *
 * @param [numerator] the operations numerator
 * @param [denominator] the operations denominator
 * @throws [IllegalArgumentException] if [numerator] and [denominator] do not have the same number
 *   of bits
 */
class BVUDiv(val numerator: Expression<BVSort>, val denominator: Expression<BVSort>) :
    BinaryExpression<BVSort, BVSort, BVSort>("bvudiv".symbol(), numerator.sort) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(numerator.sort.bits == denominator.sort.bits) {
      "Numerator and denominator must have the same number of bits, but were ${numerator.sort.bits} and ${denominator.sort.bits}"
    }

    require(!numerator.sort.isSymbolic())
    require(!denominator.sort.isSymbolic())
  }

  override val lhs: Expression<BVSort> = numerator

  override val rhs: Expression<BVSort> = denominator

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      BVUDivDecl.buildExpression(children, emptyList())
}

/**
 * Unsigned remainder operation on bitvectors
 *
 * @throws [IllegalArgumentException] if [numerator] and [denominator] do not have the same number
 *   of bits
 */
class BVURem(val numerator: Expression<BVSort>, val denominator: Expression<BVSort>) :
    BinaryExpression<BVSort, BVSort, BVSort>("bvurem".symbol(), numerator.sort) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(numerator.sort.bits == denominator.sort.bits)
    require(!numerator.sort.isSymbolic())
    require(!denominator.sort.isSymbolic())
  }

  override val lhs: Expression<BVSort> = numerator

  override val rhs: Expression<BVSort> = denominator

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      BVURemDecl.buildExpression(children, emptyList())
}

/**
 * Left shift operation on bitvectors
 *
 * @param [value] to be shifted
 * @param [distance] number of bits [value] is shifted by
 * @throws [IllegalArgumentException] if [value] and [distance] do not have the same number of bits
 */
class BVShl(val value: Expression<BVSort>, val distance: Expression<BVSort>) :
    BinaryExpression<BVSort, BVSort, BVSort>("bvshl".symbol(), value.sort) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(value.sort.bits == distance.sort.bits) {
      "value and distance must have the same number of bits, but were ${value.sort.bits} and ${value.sort.bits}"
    }
    require(!value.sort.isSymbolic())
    require(!distance.sort.isSymbolic())
  }

  override val lhs: Expression<BVSort> = value

  override val rhs: Expression<BVSort> = distance

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      BVShlDecl.buildExpression(children, emptyList())
}

/**
 * Logical right shift operation on bitvectors
 *
 * @param [value] to be shifted
 * @param [distance] number of shifts
 * @throws [IllegalArgumentException] if [value] and [distance] do not have the same number of bits
 */
class BVLShr(val value: Expression<BVSort>, val distance: Expression<BVSort>) :
    BinaryExpression<BVSort, BVSort, BVSort>("bvlshr".symbol(), value.sort) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(value.sort.bits == distance.sort.bits) {
      "value and distance must have the same number of bits, but were ${value.sort.bits} and ${value.sort.bits}"
    }
    require(!value.sort.isSymbolic())
    require(!distance.sort.isSymbolic())
  }

  override val lhs: Expression<BVSort> = value

  override val rhs: Expression<BVSort> = distance

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      BVLShrDecl.buildExpression(children, emptyList())
}

/**
 * Unsigned less-than operation on bitvectors
 *
 * @param [lhs] left value
 * @param [rhs] right value
 * @throws [IllegalArgumentException] if [lhs] and [rhs] do not have the same number of bits
 */
class BVUlt(override val lhs: Expression<BVSort>, override val rhs: Expression<BVSort>) :
    BinaryExpression<BoolSort, BVSort, BVSort>("bvult".symbol(), BoolSort) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(lhs.sort.bits == rhs.sort.bits) {
      "lhs and rhs must have the same number of bits, but were ${lhs.sort.bits} and ${rhs.sort.bits}"
    }
    require(!lhs.sort.isSymbolic())
    require(!rhs.sort.isSymbolic())
  }

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      BVUltDecl.buildExpression(children, emptyList())
}

class BVNAnd(override val lhs: Expression<BVSort>, override val rhs: Expression<BVSort>) :
    BinaryExpression<BVSort, BVSort, BVSort>("bvnand".symbol(), lhs.sort) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(lhs.sort.bits == rhs.sort.bits)
  }

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      BVNAndDecl.buildExpression(children, emptyList())

  fun expand() = BVNot(BVAnd(lhs, rhs))
}

class BVNOr(override val lhs: Expression<BVSort>, override val rhs: Expression<BVSort>) :
    BinaryExpression<BVSort, BVSort, BVSort>("bvnor".symbol(), lhs.sort) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(lhs.sort.bits == rhs.sort.bits)
  }

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      BVNOrDecl.buildExpression(children, emptyList())

  fun expand() = BVNot(BVOr(lhs, rhs))
}

class BVXOr(val disjuncts: List<Expression<BVSort>>) :
    HomogenousExpression<BVSort, BVSort>("bvxor".symbol(), disjuncts[0].sort) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(disjuncts.size > 1)
    require(disjuncts.all { it.sort.bits == sort.bits }) {
      "All bitvectors must have the same number of bits"
    }

    require(disjuncts.all { !it.sort.isSymbolic() })
  }

  constructor(vararg disjuncts: Expression<BVSort>) : this(disjuncts.toList())

  override val children: List<Expression<BVSort>> = disjuncts

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      BVXOrDecl.buildExpression(children, emptyList())

  /*
   * expands left associative xnor
   * (bvxor s_1 s_2 s_3 s_4)
   * (bvxor (bvxor (bvxor s_1 s_2) s_3) s_4)
   * (bvxor (bvxor (bvor (bvand s_1 (bvnot s_2)) (bvand (bvnot s_1) s_2)) s_3) s_4)
   * (bvxor (bvor (bvand (bvor (bvand s_1 (bvnot s_2)) (bvand (bvnot s_1) s_2)) (bvnot s_3)) (bvand (bvnot (bvor (bvand s_1 (bvnot s_2)) (bvand (bvnot s_1) s_2))) s_3)) s_4)
   */
  fun expand() =
      disjuncts.slice(2..<disjuncts.size).fold(
          BVOr(
              BVAnd(disjuncts[0], BVNot(disjuncts[1])),
              BVAnd(BVNot(disjuncts[0]), disjuncts[1]))) { xnor, expr ->
            BVOr(BVAnd(xnor, BVNot(expr)), BVAnd(BVNot(xnor), expr))
          }
}

class BVXNOr(override val lhs: Expression<BVSort>, override val rhs: Expression<BVSort>) :
    BinaryExpression<BVSort, BVSort, BVSort>("bvxnor".symbol(), lhs.sort) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(lhs.sort.bits == rhs.sort.bits)
  }

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      BVXNOrDecl.buildExpression(children, emptyList())

  fun expand() = BVOr(BVAnd(lhs, rhs), BVAnd(BVNot(lhs), BVNot(rhs)))
}

class BVComp(override val lhs: Expression<BVSort>, override val rhs: Expression<BVSort>) :
    BinaryExpression<BVSort, BVSort, BVSort>("bvcomp".symbol(), BVSort(1)) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      BVCompDecl.buildExpression(children, emptyList())

  // recursive expansion as specified in the extension of QF_BV logic
  fun expand(): Expression<BVSort> =
      if (this.sort.bits == 1) {
        BVXNOr(lhs, rhs)
      } else {
        BVAnd(
            BVXNOr(
                BVExtract(this.sort.bits - 1, this.sort.bits - 1, lhs),
                BVExtract(this.sort.bits - 1, this.sort.bits - 1, rhs)),
            BVComp(BVExtract(this.sort.bits - 2, 0, lhs), BVExtract(this.sort.bits - 2, 0, rhs))
                .expand())
      }
}

class BVSub(override val lhs: Expression<BVSort>, override val rhs: Expression<BVSort>) :
    BinaryExpression<BVSort, BVSort, BVSort>("bvsub".symbol(), lhs.sort) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(lhs.sort.bits == rhs.sort.bits)
  }

  override fun copy(children: List<Expression<*>>) =
      BVSubDecl.buildExpression(children, emptyList())

  fun expand() = BVAdd(lhs, BVNeg(rhs))
}

class BVSDiv(val numerator: Expression<BVSort>, val denominator: Expression<BVSort>) :
    BinaryExpression<BVSort, BVSort, BVSort>("bvsub".symbol(), numerator.sort) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(numerator.sort.bits == denominator.sort.bits)
  }

  override val lhs: Expression<BVSort> = numerator
  override val rhs: Expression<BVSort> = denominator

  override fun copy(children: List<Expression<*>>) =
      BVSDivDecl.buildExpression(children, emptyList())

  fun expand(): Expression<BVSort> {
    val msb_s = VarBinding("?msb_s".symbol(), BVExtract(sort.bits - 1, sort.bits - 1, numerator))
    val msb_t = VarBinding("?msb_t".symbol(), BVExtract(sort.bits - 1, sort.bits - 1, denominator))
    return LetExpression(
        listOf(msb_s, msb_t),
        Ite(
            And(Equals(msb_s.instance, BVLiteral("#b0")), Equals(msb_t.instance, BVLiteral("#b0"))),
            BVUDiv(numerator, denominator),
            Ite(
                And(
                    Equals(msb_s.instance, BVLiteral("#b1")),
                    Equals(msb_t.instance, BVLiteral("#b0"))),
                BVNeg(BVUDiv(BVNeg(numerator), denominator)),
                Ite(
                    And(
                        Equals(msb_s.instance, BVLiteral("#b0")),
                        Equals(msb_t.instance, BVLiteral("#b1"))),
                    BVNeg(BVUDiv(numerator, BVNeg(denominator))),
                    BVUDiv(BVNeg(numerator), BVNeg(denominator)),
                ))))
  }
}

class BVSRem(val numerator: Expression<BVSort>, val denominator: Expression<BVSort>) :
    BinaryExpression<BVSort, BVSort, BVSort>("bvsub".symbol(), numerator.sort) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(numerator.sort.bits == denominator.sort.bits)
  }

  override val lhs: Expression<BVSort> = numerator
  override val rhs: Expression<BVSort> = denominator

  override fun copy(children: List<Expression<*>>) =
      BVSRemDecl.buildExpression(children, emptyList())

  fun expand(): Expression<BVSort> {
    val msb_s = VarBinding("?msb_s".symbol(), BVExtract(sort.bits - 1, sort.bits - 1, numerator))
    val msb_t = VarBinding("?msb_t".symbol(), BVExtract(sort.bits - 1, sort.bits - 1, denominator))
    return LetExpression(
        listOf(msb_s, msb_t),
        Ite(
            And(Equals(msb_s.instance, BVLiteral("#b0")), Equals(msb_t.instance, BVLiteral("#b0"))),
            BVURem(numerator, denominator),
            Ite(
                And(
                    Equals(msb_s.instance, BVLiteral("#b1")),
                    Equals(msb_t.instance, BVLiteral("#b0"))),
                BVNeg(BVURem(BVNeg(numerator), denominator)),
                Ite(
                    And(
                        Equals(msb_s.instance, BVLiteral("#b0")),
                        Equals(msb_t.instance, BVLiteral("#b1"))),
                    BVURem(numerator, BVNeg(denominator)),
                    BVNeg(BVURem(BVNeg(numerator), BVNeg(denominator))),
                ))))
  }
}

class BVSMod(override val lhs: Expression<BVSort>, override val rhs: Expression<BVSort>) :
    BinaryExpression<BVSort, BVSort, BVSort>("bvsmod".symbol(), lhs.sort) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(lhs.sort.bits == rhs.sort.bits)
  }

  override fun copy(children: List<Expression<*>>) =
      BVSModDecl.buildExpression(children, emptyList())

  fun expand(): Expression<BVSort> {
    val msb_s = VarBinding("?msb_s".symbol(), BVExtract(sort.bits - 1, sort.bits - 1, lhs))
    val msb_t = VarBinding("?msb_t".symbol(), BVExtract(sort.bits - 1, sort.bits - 1, rhs))
    val abs_s =
        VarBinding(
            "?abs_s".symbol(), Ite(Equals(msb_s.instance, BVLiteral("#b0")), lhs, BVNeg(lhs)))
    val abs_t =
        VarBinding(
            "?abs_t".symbol(), Ite(Equals(msb_s.instance, BVLiteral("#b0")), rhs, BVNeg(rhs)))
    val u = VarBinding("u".symbol(), BVURem(abs_s.instance, abs_t.instance))

    return LetExpression(
        listOf(msb_s, msb_t),
        LetExpression(
            listOf(abs_s, abs_t),
            LetExpression(
                listOf(u),
                Ite(
                    Equals(u.instance, BVLiteral("#b0", sort.bits)),
                    u.instance,
                    Ite(
                        And(
                            Equals(msb_s.instance, BVLiteral("#b0")),
                            Equals(msb_t.instance, BVLiteral("#b0"))),
                        u.instance,
                        Ite(
                            And(
                                Equals(msb_s.instance, BVLiteral("#b1")),
                                Equals(msb_t.instance, BVLiteral("#b0"))),
                            BVAdd(BVNeg(u.instance), rhs),
                            Ite(
                                And(
                                    Equals(msb_s.instance, BVLiteral("#b0")),
                                    Equals(msb_t.instance, BVLiteral("#b1"))),
                                BVAdd(u.instance, rhs),
                                BVNeg(u.instance))))))))
  }
}

class BVULe(override val lhs: Expression<BVSort>, override val rhs: Expression<BVSort>) :
    BinaryExpression<BoolSort, BVSort, BVSort>("bvule".symbol(), BoolSort) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(lhs.sort.bits == rhs.sort.bits)
  }

  override fun copy(children: List<Expression<*>>) =
      BVULeDecl.buildExpression(children, emptyList())

  fun expand() = Or(BVUlt(lhs, rhs), Equals(lhs, rhs))
}

class BVUGt(override val lhs: Expression<BVSort>, override val rhs: Expression<BVSort>) :
    BinaryExpression<BoolSort, BVSort, BVSort>("bvugt".symbol(), BoolSort) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(lhs.sort.bits == rhs.sort.bits)
  }

  override fun copy(children: List<Expression<*>>) =
      BVUGtDecl.buildExpression(children, emptyList())

  fun expand() = BVUlt(rhs, lhs)
}

class BVUGe(override val lhs: Expression<BVSort>, override val rhs: Expression<BVSort>) :
    BinaryExpression<BoolSort, BVSort, BVSort>("bvuge".symbol(), BoolSort) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(lhs.sort.bits == rhs.sort.bits)
  }

  override fun copy(children: List<Expression<*>>) =
      BVUGeDecl.buildExpression(children, emptyList())

  fun expand() = Or(BVUlt(rhs, lhs), Equals(lhs, rhs))
}

class BVSLt(override val lhs: Expression<BVSort>, override val rhs: Expression<BVSort>) :
    BinaryExpression<BoolSort, BVSort, BVSort>("bvslt".symbol(), BoolSort) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(lhs.sort.bits == rhs.sort.bits)
  }

  override fun copy(children: List<Expression<*>>) =
      BVSLtDecl.buildExpression(children, emptyList())

  fun expand() =
      Or(
          And(
              Equals(BVExtract(lhs.sort.bits - 1, lhs.sort.bits - 1, lhs), BVLiteral("#b1")),
              Equals(BVExtract(rhs.sort.bits - 1, rhs.sort.bits - 1, rhs), BVLiteral("#b0"))),
          And(
              Equals(
                  BVExtract(lhs.sort.bits - 1, lhs.sort.bits - 1, lhs),
                  BVExtract(rhs.sort.bits - 1, rhs.sort.bits - 1, rhs)),
              BVUlt(lhs, rhs)))
}

class BVSLe(override val lhs: Expression<BVSort>, override val rhs: Expression<BVSort>) :
    BinaryExpression<BoolSort, BVSort, BVSort>("bvsle".symbol(), BoolSort) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(lhs.sort.bits == rhs.sort.bits)
  }

  override fun copy(children: List<Expression<*>>) =
      BVSLeDecl.buildExpression(children, emptyList())

  fun expand() =
      Or(
          And(
              Equals(BVExtract(lhs.sort.bits - 1, lhs.sort.bits - 1, lhs), BVLiteral("#b1")),
              Equals(BVExtract(rhs.sort.bits - 1, rhs.sort.bits - 1, rhs), BVLiteral("#b0"))),
          And(
              Equals(
                  BVExtract(lhs.sort.bits - 1, lhs.sort.bits - 1, lhs),
                  BVExtract(rhs.sort.bits - 1, rhs.sort.bits - 1, rhs)),
              BVULe(lhs, rhs).expand()))
}

class BVSGt(override val lhs: Expression<BVSort>, override val rhs: Expression<BVSort>) :
    BinaryExpression<BoolSort, BVSort, BVSort>("bvsgt".symbol(), BoolSort) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(lhs.sort.bits == rhs.sort.bits)
  }

  override fun copy(children: List<Expression<*>>) =
      BVSGtDecl.buildExpression(children, emptyList())

  fun expand() = BVSLt(rhs, lhs).expand()
}

class BVSGe(override val lhs: Expression<BVSort>, override val rhs: Expression<BVSort>) :
    BinaryExpression<BoolSort, BVSort, BVSort>("bvsge".symbol(), BoolSort) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(lhs.sort.bits == rhs.sort.bits)
  }

  override fun copy(children: List<Expression<*>>) =
      BVSGeDecl.buildExpression(children, emptyList())

  fun expand() = BVSLe(rhs, lhs).expand()
}

class BVAShr(val value: Expression<BVSort>, val distance: Expression<BVSort>) :
    BinaryExpression<BVSort, BVSort, BVSort>("bvashr".symbol(), value.sort) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(value.sort.bits == distance.sort.bits)
  }

  override val lhs: Expression<BVSort> = value
  override val rhs: Expression<BVSort> = distance

  override fun copy(children: List<Expression<*>>) =
      BVAShrDecl.buildExpression(children, emptyList())

  fun expand() =
      Ite(
          Equals(BVExtract(sort.bits - 1, sort.bits - 1, value), BVLiteral("#b0")),
          BVLShr(value, distance),
          BVNot(BVLShr(BVNot(value), distance)))
}

class Repeat(val j: Int, override val inner: Expression<BVSort>) :
    UnaryExpression<BVSort, BVSort>("repeat".symbol(), BVSort(inner.sort.bits * j)) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(j > 0)
  }

  fun expand() = expand(j)

  private fun expand(i: Int): Expression<BVSort> =
      if (i == 1) {
        BVConcat(inner, inner)
      } else {
        BVConcat(inner, expand(i - 1))
      }

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      RepeatDecl.buildExpression(children, listOf(j.idx()))
}

class ZeroExtend(val i: Int, override val inner: Expression<BVSort>) :
    UnaryExpression<BVSort, BVSort>("zero_extend".symbol(), BVSort(inner.sort.bits + i)) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(i >= 0)
  }

  fun expand() =
      if (i == 0) {
        inner
      } else {
        BVConcat(Repeat(i, BVLiteral("#b0")).expand(), inner)
      }

  override fun copy(children: List<Expression<*>>) =
      ZeroExtendDecl.buildExpression(children, emptyList())
}

class SignExtend(val i: Int, override val inner: Expression<BVSort>) :
    UnaryExpression<BVSort, BVSort>("sign_extend".symbol(), BVSort(inner.sort.bits + i)) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(i >= 0)
  }

  fun expand() =
      if (i == 0) {
        inner
      } else {
        BVConcat(Repeat(i, BVExtract(sort.bits - 1, sort.bits - 1, inner)).expand(), inner)
      }

  override fun copy(children: List<Expression<*>>) =
      SignExtendDecl.buildExpression(children, emptyList())
}

class RotateLeft(val i: Int, override val inner: Expression<BVSort>) :
    UnaryExpression<BVSort, BVSort>("rotate_left".symbol(), inner.sort) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(i >= 0)
  }

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      RotateLeftDecl.buildExpression(children, listOf(i.idx()))

  fun expand() =
      if (i == 0 || sort.bits == 1 || sort.bits == i) {
        inner
      } else {
        val distance = i % sort.bits

        BVConcat(
            BVExtract(sort.bits - distance - 1, 0, inner),
            BVExtract(sort.bits - 1, sort.bits - distance, inner))
      }
}

class RotateRight(val i: Int, override val inner: Expression<BVSort>) :
    UnaryExpression<BVSort, BVSort>("rotate_right".symbol(), inner.sort) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(i >= 0)
  }

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      RotateRightDecl.buildExpression(children, listOf(i.idx()))

  fun expand(): Expression<BVSort> = TODO()
}

/** Bitvector sort with [bits] length */
class BVSort private constructor(index: Index) : Sort("BitVec", listOf(index)) {
  companion object {
    /**
     * Get BitVec sort with the given number of [bits].
     *
     * Currently, this generates a new BitVec every time it is invoked, this should only create a
     * single instance for each length
     */
    // TODO cache BitVec instances so each length has only one instance
    operator fun invoke(bits: Int): BVSort = BVSort(NumeralIndex(bits))

    /**
     * Get a BitVec sort with an unknown number of bits, this is not a valid BitVec sort for SMT but
     * rather just a placeholder for function definitions that take arguments of any BitVec length
     */
    fun fromSymbol(symbol: String): BVSort = BVSort(SymbolIndex(symbol))

    /**
     * Get a BitVec sort with an unknown number of bits, this is not a valid BitVec sort for SMT but
     * rather just a placeholder for function definitions that take arguments of any BitVec length
     */
    fun fromSymbol(symbol: SymbolIndex): BVSort = BVSort(symbol)
  }

  val bits: Int
  override val theories = setOf(Theories.FIXED_SIZE_BIT_VECTORS, Theories.FLOATING_POINT)

  init {
    // indices must either be s single numeral index or a symbolic index
    // if the index is symbolic we set the number of bits to 0 to indicate
    // that this is not a valid BitVec sort in the SMT sense, but rather used internally as
    // placeholder
    if (indices.single() is NumeralIndex) {
      bits = (indices.single() as NumeralIndex).numeral
      require(bits > 0)
    } else {
      bits = 0
    }
  }

  // TODO enforce this on the sort baseclass
  // test for any index to be symbolic
  internal fun isSymbolic() = (indices.single() is SymbolIndex)
}

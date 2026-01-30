/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2026 The Konstraints Authors
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
 * This file implements the SMT FixedSizeBitVectors theory
 * https://smt-lib.org/theories-FixedSizeBitVectors.shtml
 * and its extension defined in QF_BV
 * https://smt-lib.org/logics-all.shtml#QF_BV
 */

/**
 * concatenation of [lhs] and [rhs] of size i and j to get a new bitvector of size m, where `m=i+j`.
 * - `(concat (_ BitVec i) (_ BitVec j) (_ BitVec m))`
 * - `(bvconcat [lhs] [rhs])`
 */
class BVConcat(override val lhs: Expression<BitVecSort>, override val rhs: Expression<BitVecSort>) :
    BinaryExpression<BitVecSort, BitVecSort, BitVecSort>(
        "concat".toSymbol(),
        BitVecSort(lhs.sort.bits + rhs.sort.bits),
    ) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  override val name: Symbol = "concat".toSymbol()

  init {
    require(!lhs.sort.isSymbolic())
    require(!rhs.sort.isSymbolic())
  }

  override fun copy(children: List<Expression<*>>): Expression<BitVecSort> =
      BVConcatDecl.constructDynamic(children, emptyList())
}

/**
 * Extraction of bits [i] down to [j] from [inner] to yield a new bitvector of size n, where
 * `n=i-j+1`.
 * - `((_ extract i j) (_ BitVec m) (_ BitVec n))`
 * - `((_ extract [i] [j]) [inner])`
 *
 * @param [i] last bit to be extracted (inclusive)
 * @param [j] first bit to be extracted (inclusive)
 * @throws [IllegalArgumentException] if the constraint m > i ≥ j ≥ 0 is violated, where m is the
 *   number of bits in [inner]
 */
class BVExtract(val i: Int, val j: Int, override val inner: Expression<BitVecSort>) :
    UnaryExpression<BitVecSort, BitVecSort>("extract".toSymbol(), BitVecSort(i - j + 1)) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET
  override val indices = listOf(i, j)

  init {
    require(j >= 0) { "j needs to be greater or equal to 0, but was $j" }
    require(i >= j) { "i needs to be greater or equal to j, but was $i" }
    require(inner.sort.bits > i) {
      "i can not be greater than the number of bits in inner, but was $i"
    }
  }

  override fun toString(): String = "((_ extract $i $j) $inner)"

  override fun copy(children: List<Expression<*>>): Expression<BitVecSort> =
      ExtractDecl.constructDynamic(children, listOf(i.idx(), j.idx()))
}

/**
 * Bitwise negation.
 * - `(bvnot (_ BitVec m) (_ BitVec m))`
 * - `(bvnot [inner])`
 */
class BVNot(override val inner: Expression<BitVecSort>) :
    UnaryExpression<BitVecSort, BitVecSort>("bvnot".toSymbol(), inner.sort) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  init {
    require(!inner.sort.isSymbolic())
  }

  override fun copy(children: List<Expression<*>>): Expression<BitVecSort> =
      BVNotDecl.constructDynamic(children, emptyList())
}

/**
 * 2's complement unary minus.
 * - `(bvneg (_ BitVec m) (_ BitVec m))`
 * - `(bvneg [inner])`
 */
class BVNeg(override val inner: Expression<BitVecSort>) :
    UnaryExpression<BitVecSort, BitVecSort>("bvneg".toSymbol(), inner.sort) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  init {
    require(!inner.sort.isSymbolic())
  }

  override fun copy(children: List<Expression<*>>): Expression<BitVecSort> =
      BVNegDecl.constructDynamic(children, emptyList())
}

/**
 * Bitwise and.
 * - `(bvand (_ BitVec m) (_ BitVec m) (_ BitVec m))`
 * - `(bvand [conjuncts])`
 *
 * @throws [IllegalArgumentException] if two [conjuncts] do not have the same number of bits
 */
class BVAnd(val conjuncts: List<Expression<BitVecSort>>) :
    HomogenousExpression<BitVecSort, BitVecSort>("bvand".toSymbol(), conjuncts.first().sort) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  /**
   * Bitwise and.
   * - `(bvand (_ BitVec m) (_ BitVec m) (_ BitVec m))`
   * - `(bvand [conjuncts])`
   *
   * @throws [IllegalArgumentException] if two [conjuncts] do not have the same number of bits
   */
  constructor(vararg conjuncts: Expression<BitVecSort>) : this(conjuncts.toList())

  init {
    require(conjuncts.all { it.sort.bits == sort.bits }) {
      "All bitvectors must have the same number of bits"
    }

    require(conjuncts.all { !it.sort.isSymbolic() })
  }

  override val children: List<Expression<BitVecSort>> = conjuncts

  override fun copy(children: List<Expression<*>>): Expression<BitVecSort> =
      BVAndDecl.constructDynamic(children, emptyList())
}

/**
 * Bitwise or.
 * - `(bvor (_ BitVec m) (_ BitVec m) (_ BitVec m))`
 * - `(bvor [disjuncts])`
 *
 * @throws [IllegalArgumentException] if two [disjuncts] do not have the same number of bits
 */
class BVOr(val disjuncts: List<Expression<BitVecSort>>) :
    HomogenousExpression<BitVecSort, BitVecSort>("bvor".toSymbol(), disjuncts.first().sort) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  /**
   * Bitwise or.
   * - `(bvor (_ BitVec m) (_ BitVec m) (_ BitVec m))`
   * - `(bvor [disjuncts])`
   *
   * @throws [IllegalArgumentException] if two [disjuncts] do not have the same number of bits
   */
  constructor(vararg disjuncts: Expression<BitVecSort>) : this(disjuncts.toList())

  override val children: List<Expression<BitVecSort>> = disjuncts

  init {
    require(disjuncts.all { it.sort.bits == sort.bits }) {
      "All bitvectors must have the same number of bits"
    }

    require(disjuncts.all { !it.sort.isSymbolic() })
  }

  override fun toString(): String = "(bvor ${disjuncts.joinToString(" ")})"

  override fun copy(children: List<Expression<*>>): Expression<BitVecSort> =
      BVOrDecl.constructDynamic(children, emptyList())
}

/**
 * Addition modulo 2^m.
 * - `(bvadd (_ BitVec m) (_ BitVec m) (_ BitVec m))`
 * - `(bvadd [summands])`
 *
 * @throws [IllegalArgumentException] if two [summands] do not have the same number of bits
 */
class BVAdd(val summands: List<Expression<BitVecSort>>) :
    HomogenousExpression<BitVecSort, BitVecSort>("bvadd".toSymbol(), summands.first().sort) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  /**
   * Addition modulo 2^m.
   * - `(bvadd (_ BitVec m) (_ BitVec m) (_ BitVec m))`
   * - `(bvadd [summands])`
   *
   * @throws [IllegalArgumentException] if two [summands] do not have the same number of bits
   */
  constructor(vararg summands: Expression<BitVecSort>) : this(summands.toList())

  init {
    require(summands.all { it.sort.bits == sort.bits }) {
      "All bitvectors must have the same number of bits"
    }

    require(summands.all { !it.sort.isSymbolic() })
  }

  override val children: List<Expression<BitVecSort>> = summands

  override fun copy(children: List<Expression<*>>): Expression<BitVecSort> =
      BVAddDecl.constructDynamic(children, emptyList())
}

/**
 * Multiplication modulo 2^m.
 * - `(bvmul (_ BitVec m) (_ BitVec m) (_ BitVec m))`
 * - `(bvmul [factors])`
 *
 * @throws [IllegalArgumentException] if two [factors] do not have the same number of bits
 */
class BVMul(val factors: List<Expression<BitVecSort>>) :
    HomogenousExpression<BitVecSort, BitVecSort>("bvmul".toSymbol(), factors.first().sort) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  /**
   * Multiplication modulo 2^m.
   * - `(bvmul (_ BitVec m) (_ BitVec m) (_ BitVec m))`
   * - `(bvmul [factors])`
   *
   * @throws [IllegalArgumentException] if two [factors] do not have the same number of bits
   */
  constructor(vararg factors: Expression<BitVecSort>) : this(factors.toList())

  init {
    require(factors.all { it.sort.bits == sort.bits }) {
      "All bitvectors must have the same number of bits"
    }

    require(factors.all { !it.sort.isSymbolic() })
  }

  override val children: List<Expression<BitVecSort>> = factors

  override fun copy(children: List<Expression<*>>): Expression<BitVecSort> =
      BVMulDecl.constructDynamic(children, emptyList())
}

/**
 * Unsigned division, truncating towards 0.
 * - `(bvudiv (_ BitVec m) (_ BitVec m) (_ BitVec m))`
 * - `(bvudiv [numerator] [denominator])`
 *
 * @throws [IllegalArgumentException] if [numerator] and [denominator] do not have the same number
 *   of bits
 */
class BVUDiv(val numerator: Expression<BitVecSort>, val denominator: Expression<BitVecSort>) :
    BinaryExpression<BitVecSort, BitVecSort, BitVecSort>("bvudiv".toSymbol(), numerator.sort) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  init {
    require(numerator.sort.bits == denominator.sort.bits) {
      "Numerator and denominator must have the same number of bits, but were ${numerator.sort.bits} and ${denominator.sort.bits}"
    }

    require(!numerator.sort.isSymbolic())
    require(!denominator.sort.isSymbolic())
  }

  override val lhs: Expression<BitVecSort> = numerator

  override val rhs: Expression<BitVecSort> = denominator

  override fun copy(children: List<Expression<*>>): Expression<BitVecSort> =
      BVUDivDecl.constructDynamic(children, emptyList())
}

/**
 * Unsigned remainder from truncating division.
 * - `(bvurem (_ BitVec m) (_ BitVec m) (_ BitVec m))`
 * - `(bvurem [numerator] [denominator])`
 *
 * @throws [IllegalArgumentException] if [numerator] and [denominator] do not have the same number
 *   of bits
 */
class BVURem(val numerator: Expression<BitVecSort>, val denominator: Expression<BitVecSort>) :
    BinaryExpression<BitVecSort, BitVecSort, BitVecSort>("bvurem".toSymbol(), numerator.sort) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  init {
    require(numerator.sort.bits == denominator.sort.bits)
    require(!numerator.sort.isSymbolic())
    require(!denominator.sort.isSymbolic())
  }

  override val lhs: Expression<BitVecSort> = numerator

  override val rhs: Expression<BitVecSort> = denominator

  override fun copy(children: List<Expression<*>>): Expression<BitVecSort> =
      BVURemDecl.constructDynamic(children, emptyList())
}

/**
 * shift left.
 * - equivalent to multiplication by 2^x where x is the value of the second argument
 * - `(bvshl (_ BitVec m) (_ BitVec m) (_ BitVec m))`
 * - `(bvshl [value] [distance])`
 *
 * @throws [IllegalArgumentException] if [value] and [distance] do not have the same number of bits
 */
class BVShl(val value: Expression<BitVecSort>, val distance: Expression<BitVecSort>) :
    BinaryExpression<BitVecSort, BitVecSort, BitVecSort>("bvshl".toSymbol(), value.sort) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  init {
    require(value.sort.bits == distance.sort.bits) {
      "value and distance must have the same number of bits, but were ${value.sort.bits} and ${value.sort.bits}"
    }
    require(!value.sort.isSymbolic())
    require(!distance.sort.isSymbolic())
  }

  override val lhs: Expression<BitVecSort> = value

  override val rhs: Expression<BitVecSort> = distance

  override fun copy(children: List<Expression<*>>): Expression<BitVecSort> =
      BVShlDecl.constructDynamic(children, emptyList())
}

/**
 * Logical shift right.
 * - equivalent to unsigned division by 2^x where x is the value of the second argument
 * - `(bvlshr (_ BitVec m) (_ BitVec m) (_ BitVec m))`
 * - `(bvlshr [value] [distance])`
 *
 * @throws [IllegalArgumentException] if [value] and [distance] do not have the same number of bits
 */
class BVLShr(val value: Expression<BitVecSort>, val distance: Expression<BitVecSort>) :
    BinaryExpression<BitVecSort, BitVecSort, BitVecSort>("bvlshr".toSymbol(), value.sort) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  init {
    require(value.sort.bits == distance.sort.bits) {
      "value and distance must have the same number of bits, but were ${value.sort.bits} and ${value.sort.bits}"
    }
    require(!value.sort.isSymbolic())
    require(!distance.sort.isSymbolic())
  }

  override val lhs: Expression<BitVecSort> = value

  override val rhs: Expression<BitVecSort> = distance

  override fun copy(children: List<Expression<*>>): Expression<BitVecSort> =
      BVLShrDecl.constructDynamic(children, emptyList())
}

/**
 * Binary predicate for unsigned less-than.
 * - `(bvult (_ BitVec m) (_ BitVec m) Bool)`
 * - `(bvult [lhs] [rhs])`
 *
 * @throws [IllegalArgumentException] if [lhs] and [rhs] do not have the same number of bits
 */
class BVUlt(override val lhs: Expression<BitVecSort>, override val rhs: Expression<BitVecSort>) :
    BinaryExpression<BoolSort, BitVecSort, BitVecSort>("bvult".toSymbol(), SMTBool) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  init {
    require(lhs.sort.bits == rhs.sort.bits) {
      "lhs and rhs must have the same number of bits, but were ${lhs.sort.bits} and ${rhs.sort.bits}"
    }
    require(!lhs.sort.isSymbolic())
    require(!rhs.sort.isSymbolic())
  }

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      BVUltDecl.constructDynamic(children, emptyList())
}

/**
 * Bitwise nand.
 * - `(bvnand (_ BitVec m) (_ BitVec m) (_ BitVec m))`
 * - `(bvnand [lhs] [rhs])`
 *
 * @throws [IllegalArgumentException] if [lhs] and [rhs] do not have the same number of bits
 */
class BVNAnd(override val lhs: Expression<BitVecSort>, override val rhs: Expression<BitVecSort>) :
    BinaryExpression<BitVecSort, BitVecSort, BitVecSort>("bvnand".toSymbol(), lhs.sort) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  init {
    require(lhs.sort.bits == rhs.sort.bits)
  }

  override fun copy(children: List<Expression<*>>): Expression<BitVecSort> =
      BVNAndDecl.constructDynamic(children, emptyList())

  /** Express [this] in terms of standard smt fixed size bitvector theory. */
  fun expand() = BVNot(BVAnd(lhs, rhs))
}

/**
 * Bitwise nor.
 * - `(bvnor (_ BitVec m) (_ BitVec m) (_ BitVec m))`
 * - `(bvnor [lhs] [rhs])`
 *
 * @throws [IllegalArgumentException] if [lhs] and [rhs] do not have the same number of bits
 */
class BVNOr(override val lhs: Expression<BitVecSort>, override val rhs: Expression<BitVecSort>) :
    BinaryExpression<BitVecSort, BitVecSort, BitVecSort>("bvnor".toSymbol(), lhs.sort) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  init {
    require(lhs.sort.bits == rhs.sort.bits)
  }

  override fun copy(children: List<Expression<*>>): Expression<BitVecSort> =
      BVNOrDecl.constructDynamic(children, emptyList())

  /** Express [this] in terms of standard smt fixed size bitvector theory. */
  fun expand() = BVNot(BVOr(lhs, rhs))
}

/**
 * Bitwise xor.
 * - `(bvxor (_ BitVec m) (_ BitVec m) (_ BitVec m))`
 * - `(bvxor [disjuncts])`
 *
 * @throws [IllegalArgumentException] if [lhs] and [rhs] do not have the same number of bits
 */
class BVXOr(val disjuncts: List<Expression<BitVecSort>>) :
    HomogenousExpression<BitVecSort, BitVecSort>("bvxor".toSymbol(), disjuncts[0].sort) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  init {
    require(disjuncts.size > 1)
    require(disjuncts.all { it.sort.bits == sort.bits }) {
      "All bitvectors must have the same number of bits"
    }

    require(disjuncts.all { !it.sort.isSymbolic() })
  }

  constructor(vararg disjuncts: Expression<BitVecSort>) : this(disjuncts.toList())

  override val children: List<Expression<BitVecSort>> = disjuncts

  override fun copy(children: List<Expression<*>>): Expression<BitVecSort> =
      BVXOrDecl.constructDynamic(children, emptyList())

  /*
   * expands left associative xnor
   * (bvxor s_1 s_2 s_3 s_4)
   * (bvxor (bvxor (bvxor s_1 s_2) s_3) s_4)
   * (bvxor (bvxor (bvor (bvand s_1 (bvnot s_2)) (bvand (bvnot s_1) s_2)) s_3) s_4)
   * (bvxor (bvor (bvand (bvor (bvand s_1 (bvnot s_2)) (bvand (bvnot s_1) s_2)) (bvnot s_3)) (bvand (bvnot (bvor (bvand s_1 (bvnot s_2)) (bvand (bvnot s_1) s_2))) s_3)) s_4)
   */
  /** Express [this] in terms of standard smt fixed size bitvector theory. */
  fun expand() =
      disjuncts.slice(2..<disjuncts.size).fold(
          BVOr(BVAnd(disjuncts[0], BVNot(disjuncts[1])), BVAnd(BVNot(disjuncts[0]), disjuncts[1]))
      ) { xnor, expr ->
        BVOr(BVAnd(xnor, BVNot(expr)), BVAnd(BVNot(xnor), expr))
      }
}

/**
 * Bitwise xnor.
 * - `(bvxnor (_ BitVec m) (_ BitVec m) (_ BitVec m))`
 * - `(bvxnor [lhs] [rhs])`
 *
 * @throws [IllegalArgumentException] if [lhs] and [rhs] do not have the same number of bits
 */
class BVXNOr(override val lhs: Expression<BitVecSort>, override val rhs: Expression<BitVecSort>) :
    BinaryExpression<BitVecSort, BitVecSort, BitVecSort>("bvxnor".toSymbol(), lhs.sort) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  init {
    require(lhs.sort.bits == rhs.sort.bits)
  }

  override fun copy(children: List<Expression<*>>): Expression<BitVecSort> =
      BVXNOrDecl.constructDynamic(children, emptyList())

  /** Express [this] in terms of standard smt fixed size bitvector theory. */
  fun expand() = BVOr(BVAnd(lhs, rhs), BVAnd(BVNot(lhs), BVNot(rhs)))
}

/**
 * Bit comparator: equals #b1 iff all bits are equal.
 * - `(bvcomp (_ BitVec m) (_ BitVec m) (_ BitVec 1))`
 * - `(bvcomp [lhs] [rhs])`
 *
 * @throws [IllegalArgumentException] if [lhs] and [rhs] do not have the same number of bits
 */
class BVComp(override val lhs: Expression<BitVecSort>, override val rhs: Expression<BitVecSort>) :
    BinaryExpression<BitVecSort, BitVecSort, BitVecSort>("bvcomp".toSymbol(), BitVecSort(1)) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  init {
    require(lhs.sort.bits == rhs.sort.bits)
  }

  override fun copy(children: List<Expression<*>>): Expression<BitVecSort> =
      BVCompDecl.constructDynamic(children, emptyList())

  /** Express [this] in terms of standard smt fixed size bitvector theory. */
  fun expand(): Expression<BitVecSort> =
      if (this.sort.bits == 1) {
        BVXNOr(lhs, rhs)
      } else {
        BVAnd(
            BVXNOr(
                BVExtract(this.sort.bits - 1, this.sort.bits - 1, lhs),
                BVExtract(this.sort.bits - 1, this.sort.bits - 1, rhs),
            ),
            BVComp(BVExtract(this.sort.bits - 2, 0, lhs), BVExtract(this.sort.bits - 2, 0, rhs))
                .expand(),
        )
      }
}

/**
 * 2's complement subtraction modulo 2^m.
 * - `(bvsub (_ BitVec m) (_ BitVec m) (_ BitVec m))`
 * - `(bvsub [lhs] [rhs])`
 *
 * @throws [IllegalArgumentException] if [lhs] and [rhs] do not have the same number of bits
 */
class BVSub(override val lhs: Expression<BitVecSort>, override val rhs: Expression<BitVecSort>) :
    BinaryExpression<BitVecSort, BitVecSort, BitVecSort>("bvsub".toSymbol(), lhs.sort) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  init {
    require(lhs.sort.bits == rhs.sort.bits)
  }

  override fun copy(children: List<Expression<*>>) =
      BVSubDecl.constructDynamic(children, emptyList())

  /** Express [this] in terms of standard smt fixed size bitvector theory. */
  fun expand() = BVAdd(lhs, BVNeg(rhs))
}

/**
 * 2's complement signed division.
 * - `(bvsdiv (_ BitVec m) (_ BitVec m) (_ BitVec m))`
 * - `(bvsdiv [numerator] [denominator])`
 *
 * @throws [IllegalArgumentException] if [numerator] and [denominator] do not have the same number
 *   of bits
 */
class BVSDiv(val numerator: Expression<BitVecSort>, val denominator: Expression<BitVecSort>) :
    BinaryExpression<BitVecSort, BitVecSort, BitVecSort>("bvsdiv".toSymbol(), numerator.sort) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  init {
    require(numerator.sort.bits == denominator.sort.bits)
  }

  override val lhs: Expression<BitVecSort> = numerator
  override val rhs: Expression<BitVecSort> = denominator

  override fun copy(children: List<Expression<*>>) =
      BVSDivDecl.constructDynamic(children, emptyList())

  /** Express [this] in terms of standard smt fixed size bitvector theory. */
  fun expand(): Expression<BitVecSort> {
    val msb_s =
        VarBinding(
            "?msb_s".toSymbol(),
            BVExtract(sort.bits - 1, sort.bits - 1, numerator),
        )
    val msb_t =
        VarBinding(
            "?msb_t".toSymbol(),
            BVExtract(sort.bits - 1, sort.bits - 1, denominator),
        )
    return LetExpression(
        listOf(msb_s, msb_t),
        Ite(
            And(Equals(msb_s.instance, BVLiteral("#b0")), Equals(msb_t.instance, BVLiteral("#b0"))),
            BVUDiv(numerator, denominator),
            Ite(
                And(
                    Equals(msb_s.instance, BVLiteral("#b1")),
                    Equals(msb_t.instance, BVLiteral("#b0")),
                ),
                BVNeg(BVUDiv(BVNeg(numerator), denominator)),
                Ite(
                    And(
                        Equals(msb_s.instance, BVLiteral("#b0")),
                        Equals(msb_t.instance, BVLiteral("#b1")),
                    ),
                    BVNeg(BVUDiv(numerator, BVNeg(denominator))),
                    BVUDiv(BVNeg(numerator), BVNeg(denominator)),
                ),
            ),
        ),
    )
  }
}

/**
 * 2's complement signed remainder.
 * - sign follows [numerator]
 * - `(bvsrem (_ BitVec m) (_ BitVec m) (_ BitVec m))`
 * - `(bvsrem [numerator] [denominator])`
 *
 * @throws [IllegalArgumentException] if [numerator] and [denominator] do not have the same number
 *   of bits
 */
class BVSRem(val numerator: Expression<BitVecSort>, val denominator: Expression<BitVecSort>) :
    BinaryExpression<BitVecSort, BitVecSort, BitVecSort>("bvsrem".toSymbol(), numerator.sort) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  init {
    require(numerator.sort.bits == denominator.sort.bits)
  }

  override val lhs: Expression<BitVecSort> = numerator
  override val rhs: Expression<BitVecSort> = denominator

  override fun copy(children: List<Expression<*>>) =
      BVSRemDecl.constructDynamic(children, emptyList())

  /** Express [this] in terms of standard smt fixed size bitvector theory. */
  fun expand(): Expression<BitVecSort> {
    val msb_s =
        VarBinding(
            "?msb_s".toSymbol(),
            BVExtract(sort.bits - 1, sort.bits - 1, numerator),
        )
    val msb_t =
        VarBinding(
            "?msb_t".toSymbol(),
            BVExtract(sort.bits - 1, sort.bits - 1, denominator),
        )
    return LetExpression(
        listOf(msb_s, msb_t),
        Ite(
            And(Equals(msb_s.instance, BVLiteral("#b0")), Equals(msb_t.instance, BVLiteral("#b0"))),
            BVURem(numerator, denominator),
            Ite(
                And(
                    Equals(msb_s.instance, BVLiteral("#b1")),
                    Equals(msb_t.instance, BVLiteral("#b0")),
                ),
                BVNeg(BVURem(BVNeg(numerator), denominator)),
                Ite(
                    And(
                        Equals(msb_s.instance, BVLiteral("#b0")),
                        Equals(msb_t.instance, BVLiteral("#b1")),
                    ),
                    BVURem(numerator, BVNeg(denominator)),
                    BVNeg(BVURem(BVNeg(numerator), BVNeg(denominator))),
                ),
            ),
        ),
    )
  }
}

/**
 * 2's complement signed remainder.
 * - sign follows [rhs]
 * - `(bvsmod (_ BitVec m) (_ BitVec m) (_ BitVec m))`
 * - `(bvsmod [lhs] [rhs])`
 *
 * @throws [IllegalArgumentException] if [lhs] and [rhs] do not have the same number of bits
 */
class BVSMod(override val lhs: Expression<BitVecSort>, override val rhs: Expression<BitVecSort>) :
    BinaryExpression<BitVecSort, BitVecSort, BitVecSort>("bvsmod".toSymbol(), lhs.sort) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  init {
    require(lhs.sort.bits == rhs.sort.bits)
  }

  override fun copy(children: List<Expression<*>>) =
      BVSModDecl.constructDynamic(children, emptyList())

  /** Express [this] in terms of standard smt fixed size bitvector theory. */
  fun expand(): Expression<BitVecSort> {
    val msb_s = VarBinding("?msb_s".toSymbol(), BVExtract(sort.bits - 1, sort.bits - 1, lhs))
    val msb_t = VarBinding("?msb_t".toSymbol(), BVExtract(sort.bits - 1, sort.bits - 1, rhs))
    val abs_s =
        VarBinding(
            "?abs_s".toSymbol(),
            Ite(Equals(msb_s.instance, BVLiteral("#b0")), lhs, BVNeg(lhs)),
        )
    val abs_t =
        VarBinding(
            "?abs_t".toSymbol(),
            Ite(Equals(msb_s.instance, BVLiteral("#b0")), rhs, BVNeg(rhs)),
        )
    val u = VarBinding("u".toSymbol(), BVURem(abs_s.instance, abs_t.instance))

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
                            Equals(msb_t.instance, BVLiteral("#b0")),
                        ),
                        u.instance,
                        Ite(
                            And(
                                Equals(msb_s.instance, BVLiteral("#b1")),
                                Equals(msb_t.instance, BVLiteral("#b0")),
                            ),
                            BVAdd(BVNeg(u.instance), rhs),
                            Ite(
                                And(
                                    Equals(msb_s.instance, BVLiteral("#b0")),
                                    Equals(msb_t.instance, BVLiteral("#b1")),
                                ),
                                BVAdd(u.instance, rhs),
                                BVNeg(u.instance),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )
  }
}

/**
 * Arithmetic shift right.
 * - like logical shift right except that the most significant bits of the result always copy the
 *   most significant bit of the first argument.
 * - `(bvashr (_ BitVec m) (_ BitVec m) (_ BitVec m))`
 * - `(bvashr [value] [distance])`
 *
 * @throws [IllegalArgumentException] if [value] and [distance] do not have the same number of bits
 */
class BVAShr(val value: Expression<BitVecSort>, val distance: Expression<BitVecSort>) :
    BinaryExpression<BitVecSort, BitVecSort, BitVecSort>("bvashr".toSymbol(), value.sort) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  init {
    require(value.sort.bits == distance.sort.bits)
  }

  override val lhs: Expression<BitVecSort> = value
  override val rhs: Expression<BitVecSort> = distance

  override fun copy(children: List<Expression<*>>) =
      BVAShrDecl.constructDynamic(children, emptyList())

  /** Express [this] in terms of standard smt fixed size bitvector theory. */
  fun expand() =
      Ite(
          Equals(BVExtract(sort.bits - 1, sort.bits - 1, value), BVLiteral("#b0")),
          BVLShr(value, distance),
          BVNot(BVLShr(BVNot(value), distance)),
      )
}

/**
 * Concatenate [i] copies of [inner].
 * - `((_ repeat i) (_ BitVec m) (_ BitVec i*m))`
 * - `((_ repeat [i]) [inner])`
 *
 * @throws [IllegalArgumentException] if [i] <= 0
 */
class Repeat(val i: Int, override val inner: Expression<BitVecSort>) :
    UnaryExpression<BitVecSort, BitVecSort>("repeat".toSymbol(), BitVecSort(inner.sort.bits * i)) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET
  override val indices = listOf(i)

  init {
    require(i > 0)
  }

  /** Express [this] in terms of standard smt fixed size bitvector theory. */
  fun expand() = expand(i)

  /** Expansion for repeat is defined recursively. */
  private fun expand(i: Int): Expression<BitVecSort> =
      if (i == 1) {
        BVConcat(inner, inner)
      } else {
        BVConcat(inner, expand(i - 1))
      }

  override fun copy(children: List<Expression<*>>): Expression<BitVecSort> =
      RepeatDecl.constructDynamic(children, listOf(i.idx()))

  override fun toString() = "((_ repeat $i) $inner)"
}

/**
 * Extend [inner] with zeroes to the (unsigned) equivalent bitvector of size m+i.
 * - `((_ zero_extend i) (_ BitVec m) (_ BitVec m+i))`
 * - `((_ zero_extend [i]) [inner])`
 *
 * @throws [IllegalArgumentException] if [i] < 0
 */
class ZeroExtend(val i: Int, override val inner: Expression<BitVecSort>) :
    UnaryExpression<BitVecSort, BitVecSort>(
        "zero_extend".toSymbol(),
        BitVecSort(inner.sort.bits + i),
    ) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET
  override val indices = listOf(i)

  init {
    require(i >= 0)
  }

  /** Express [this] in terms of standard smt fixed size bitvector theory. */
  fun expand() =
      if (i == 0) {
        inner
      } else {
        BVConcat(Repeat(i, BVLiteral("#b0")).expand(), inner)
      }

  override fun copy(children: List<Expression<*>>) =
      ZeroExtendDecl.constructDynamic(children, emptyList())

  override fun toString() = "((_ zero_extend $i) $inner)"
}

/**
 * Extend [inner] to the (signed) equivalent bitvector of size m+i.
 * - `((_ sign_extend i) (_ BitVec m) (_ BitVec m+i))`
 * - `((_ sign_extend [i]) [inner])`
 *
 * @throws [IllegalArgumentException] if [i] < 0
 */
class SignExtend(val i: Int, override val inner: Expression<BitVecSort>) :
    UnaryExpression<BitVecSort, BitVecSort>(
        "sign_extend".toSymbol(),
        BitVecSort(inner.sort.bits + i),
    ) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET
  override val indices = listOf(i)

  init {
    require(i >= 0)
  }

  /** Express [this] in terms of standard smt fixed size bitvector theory. */
  fun expand() =
      if (i == 0) {
        inner
      } else {
        BVConcat(Repeat(i, BVExtract(sort.bits - 1, sort.bits - 1, inner)).expand(), inner)
      }

  override fun copy(children: List<Expression<*>>) =
      SignExtendDecl.constructDynamic(children, emptyList())

  override fun toString() = "((_ sign_extend $i) $inner)"
}

/**
 * Rotate bits of [inner] to the left [i] times.
 * - `((_ rotate_left i) (_ BitVec m) (_ BitVec m))`
 * - `((_ rotate_left [i]) [inner])`
 *
 * @throws [IllegalArgumentException] if [i] < 0
 */
class RotateLeft(val i: Int, override val inner: Expression<BitVecSort>) :
    UnaryExpression<BitVecSort, BitVecSort>("rotate_left".toSymbol(), inner.sort) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET
  override val indices = listOf(i)

  init {
    require(i >= 0)
  }

  override fun copy(children: List<Expression<*>>): Expression<BitVecSort> =
      RotateLeftDecl.constructDynamic(children, listOf(i.idx()))

  /** Express [this] in terms of standard smt fixed size bitvector theory. */
  fun expand() =
      if (i == 0 || sort.bits == 1 || sort.bits == i) {
        inner
      } else {
        val distance = i % sort.bits

        BVConcat(
            BVExtract(sort.bits - distance - 1, 0, inner),
            BVExtract(sort.bits - 1, sort.bits - distance, inner),
        )
      }

  override fun toString() = "((_ rotate_left $i) $inner)"
}

/**
 * Rotate bits of [inner] to the right [i] times.
 * - `((_ rotate_right i) (_ BitVec m) (_ BitVec m))` -`((_ rotate_right [i]) [inner])`
 *
 * @throws [IllegalArgumentException] if [i] < 0
 */
class RotateRight(val i: Int, override val inner: Expression<BitVecSort>) :
    UnaryExpression<BitVecSort, BitVecSort>("rotate_right".toSymbol(), inner.sort) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET
  override val indices = listOf(i)

  init {
    require(i >= 0)
  }

  override fun copy(children: List<Expression<*>>): Expression<BitVecSort> =
      RotateRightDecl.constructDynamic(children, listOf(i.idx()))

  /** Express [this] in terms of standard smt fixed size bitvector theory. */
  fun expand(): Expression<BitVecSort> = TODO()

  override fun toString() = "((_ rotate_right $i) $inner)"
}

/**
 * Binary predicate for unsigned less than or equal.
 * - `(bvule (_ BitVec m) (_ BitVec m) Bool)`
 * - `(bvule [lhs] [rhs])`
 *
 * @throws [IllegalArgumentException] if [lhs] and [rhs] do not have the same number of bits
 */
class BVULe(override val lhs: Expression<BitVecSort>, override val rhs: Expression<BitVecSort>) :
    BinaryExpression<BoolSort, BitVecSort, BitVecSort>("bvule".toSymbol(), SMTBool) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  init {
    require(lhs.sort.bits == rhs.sort.bits)
  }

  override fun copy(children: List<Expression<*>>) =
      BVULeDecl.constructDynamic(children, emptyList())

  /** Express [this] in terms of standard smt fixed size bitvector theory. */
  fun expand() = Or(BVUlt(lhs, rhs), Equals(lhs, rhs))
}

/**
 * Binary predicate for unsigned greater than.
 * - `(bvugt (_ BitVec m) (_ BitVec m) Bool)`
 * - `(bvugt [lhs] [rhs])`
 *
 * @throws [IllegalArgumentException] if [lhs] and [rhs] do not have the same number of bits
 */
class BVUGt(override val lhs: Expression<BitVecSort>, override val rhs: Expression<BitVecSort>) :
    BinaryExpression<BoolSort, BitVecSort, BitVecSort>("bvugt".toSymbol(), SMTBool) {
  companion object {
    private val theoriesSet = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
  }

  override val theories: Set<Theories>
    get() = theoriesSet

  init {
    require(lhs.sort.bits == rhs.sort.bits)
  }

  override fun copy(children: List<Expression<*>>) =
      BVUGtDecl.constructDynamic(children, emptyList())

  /** Express [this] in terms of standard smt fixed size bitvector theory. */
  fun expand() = BVUlt(rhs, lhs)
}

/**
 * Binary predicate for unsigned greater than or equal.
 * - `(bvuge (_ BitVec m) (_ BitVec m) Bool)`
 * - `(bvuge [lhs] [rhs])`
 *
 * @throws [IllegalArgumentException] if [lhs] and [rhs] do not have the same number of bits
 */
class BVUGe(override val lhs: Expression<BitVecSort>, override val rhs: Expression<BitVecSort>) :
    BinaryExpression<BoolSort, BitVecSort, BitVecSort>("bvuge".toSymbol(), SMTBool) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  init {
    require(lhs.sort.bits == rhs.sort.bits)
  }

  override fun copy(children: List<Expression<*>>) =
      BVUGeDecl.constructDynamic(children, emptyList())

  /** Express [this] in terms of standard smt fixed size bitvector theory. */
  fun expand() = Or(BVUlt(rhs, lhs), Equals(lhs, rhs))
}

/**
 * Binary predicate for signed less than.
 * - `(bvslt (_ BitVec m) (_ BitVec m) Bool)`
 * - `(bvslt [lhs] [rhs])`
 *
 * @throws [IllegalArgumentException] if [lhs] and [rhs] do not have the same number of bits
 */
class BVSLt(override val lhs: Expression<BitVecSort>, override val rhs: Expression<BitVecSort>) :
    BinaryExpression<BoolSort, BitVecSort, BitVecSort>("bvslt".toSymbol(), SMTBool) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  init {
    require(lhs.sort.bits == rhs.sort.bits)
  }

  override fun copy(children: List<Expression<*>>) =
      BVSLtDecl.constructDynamic(children, emptyList())

  /** Express [this] in terms of standard smt fixed size bitvector theory. */
  fun expand() =
      Or(
          And(
              Equals(BVExtract(lhs.sort.bits - 1, lhs.sort.bits - 1, lhs), BVLiteral("#b1")),
              Equals(BVExtract(rhs.sort.bits - 1, rhs.sort.bits - 1, rhs), BVLiteral("#b0")),
          ),
          And(
              Equals(
                  BVExtract(lhs.sort.bits - 1, lhs.sort.bits - 1, lhs),
                  BVExtract(rhs.sort.bits - 1, rhs.sort.bits - 1, rhs),
              ),
              BVUlt(lhs, rhs),
          ),
      )
}

/**
 * Binary predicate for signed less than or equal.
 * - `(bvsle (_ BitVec m) (_ BitVec m) Bool)`
 * - `(bvsle [lhs] [rhs])`
 *
 * @throws [IllegalArgumentException] if [lhs] and [rhs] do not have the same number of bits
 */
class BVSLe(override val lhs: Expression<BitVecSort>, override val rhs: Expression<BitVecSort>) :
    BinaryExpression<BoolSort, BitVecSort, BitVecSort>("bvsle".toSymbol(), SMTBool) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  init {
    require(lhs.sort.bits == rhs.sort.bits)
  }

  override fun copy(children: List<Expression<*>>) =
      BVSLeDecl.constructDynamic(children, emptyList())

  /** Express [this] in terms of standard smt fixed size bitvector theory. */
  fun expand() =
      Or(
          And(
              Equals(BVExtract(lhs.sort.bits - 1, lhs.sort.bits - 1, lhs), BVLiteral("#b1")),
              Equals(BVExtract(rhs.sort.bits - 1, rhs.sort.bits - 1, rhs), BVLiteral("#b0")),
          ),
          And(
              Equals(
                  BVExtract(lhs.sort.bits - 1, lhs.sort.bits - 1, lhs),
                  BVExtract(rhs.sort.bits - 1, rhs.sort.bits - 1, rhs),
              ),
              BVULe(lhs, rhs).expand(),
          ),
      )
}

/**
 * Binary predicate for signed greater than
 * - `(bvsgt (_ BitVec m) (_ BitVec m) Bool)`
 * - `(bvsgt [lhs] [rhs])`
 *
 * @throws [IllegalArgumentException] if [lhs] and [rhs] do not have the same number of bits
 */
class BVSGt(override val lhs: Expression<BitVecSort>, override val rhs: Expression<BitVecSort>) :
    BinaryExpression<BoolSort, BitVecSort, BitVecSort>("bvsgt".toSymbol(), SMTBool) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  init {
    require(lhs.sort.bits == rhs.sort.bits)
  }

  override fun copy(children: List<Expression<*>>) =
      BVSGtDecl.constructDynamic(children, emptyList())

  /** Express [this] in terms of standard smt fixed size bitvector theory. */
  fun expand() = BVSLt(rhs, lhs).expand()
}

/**
 * Binary predicate for signed greater than or equal
 * - `(bvsge (_ BitVec m) (_ BitVec m) Bool)`
 * - `(bvsge [lhs] [rhs])`.
 *
 * @throws [IllegalArgumentException] if [lhs] and [rhs] do not have the same number of bits
 */
class BVSGe(override val lhs: Expression<BitVecSort>, override val rhs: Expression<BitVecSort>) :
    BinaryExpression<BoolSort, BitVecSort, BitVecSort>("bvsge".toSymbol(), SMTBool) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  init {
    require(lhs.sort.bits == rhs.sort.bits)
  }

  override fun copy(children: List<Expression<*>>) =
      BVSGeDecl.constructDynamic(children, emptyList())

  /** Express [this] in terms of standard smt fixed size bitvector theory. */
  fun expand() = BVSLe(rhs, lhs).expand()
}

/** Convert [this] into SMT bitvector literal. */
fun String.bitvec() = BVLiteral(this)

/** Convert [this] into SMT bitvector literal of sort (_ BitVec [bits]). */
fun String.bitvec(bits: Int) = BVLiteral(this, bits)

/** Returns true iff [this] is of form #bX, where X is any valid binary number. */
fun String.isSMTBinary() = this.startsWith("#b") && this.substring(2).all { ch -> ch in "01" }

/** Returns true iff [this] is of form #xX, where X is any valid hexadecimal number. */
fun String.isSMTHex() =
    this.startsWith("#x") && this.substring(2).all { ch -> ch in "0123456789abcdefABCDEF" }

/**
 * Returns true iff [this] is of form (_ bv numeral) where numeral is any decimal number not
 * starting with 0.
 */
fun String.isSMTBitvecShorthand(): Boolean {
  if (!this.startsWith("(_ bv")) return false
  val token = this.split(' ')

  return token[1].substring(2).all { ch -> ch.isDigit() } &&
      token[2].all { ch -> ch.isDigit() } &&
      token[2][0] != '0'
}

/** Returns true iff [this] is either #bX or #xX. */
fun String.isBitvecLiteral() = this.isSMTBinary() || this.isSMTHex()

class BVNegO(override val inner: Expression<BitVecSort>) :
    UnaryExpression<BoolSort, BitVecSort>("bvnego".toSymbol(), SMTBool) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      BVNegODecl.constructDynamic(children, emptyList())

  fun expand(): Expression<BoolSort> = TODO()
}

class BVUAddO(override val lhs: Expression<BitVecSort>, override val rhs: Expression<BitVecSort>) :
    BinaryExpression<BoolSort, BitVecSort, BitVecSort>("bvuaddo".toSymbol(), SMTBool) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      BVUAddODecl.constructDynamic(children, emptyList())

  fun expand(): Expression<BoolSort> = TODO()
}

class BVSAddO(override val lhs: Expression<BitVecSort>, override val rhs: Expression<BitVecSort>) :
    BinaryExpression<BoolSort, BitVecSort, BitVecSort>("bvsaddo".toSymbol(), SMTBool) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      BVSAddODecl.constructDynamic(children, emptyList())

  fun expand(): Expression<BoolSort> = TODO()
}

class BVUSubO(override val lhs: Expression<BitVecSort>, override val rhs: Expression<BitVecSort>) :
    BinaryExpression<BoolSort, BitVecSort, BitVecSort>("bvusubo".toSymbol(), SMTBool) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      BVUSubODecl.constructDynamic(children, emptyList())

  fun expand(): Expression<BoolSort> = TODO()
}

class BVSSubO(override val lhs: Expression<BitVecSort>, override val rhs: Expression<BitVecSort>) :
    BinaryExpression<BoolSort, BitVecSort, BitVecSort>("bvssubo".toSymbol(), SMTBool) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      BVSSubODecl.constructDynamic(children, emptyList())

  fun expand(): Expression<BoolSort> = TODO()
}

class BVUMulO(override val lhs: Expression<BitVecSort>, override val rhs: Expression<BitVecSort>) :
    BinaryExpression<BoolSort, BitVecSort, BitVecSort>("bvumulo".toSymbol(), SMTBool) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      BVUMulODecl.constructDynamic(children, emptyList())

  fun expand(): Expression<BoolSort> = TODO()
}

class BVSMulO(override val lhs: Expression<BitVecSort>, override val rhs: Expression<BitVecSort>) :
    BinaryExpression<BoolSort, BitVecSort, BitVecSort>("bvsmulo".toSymbol(), SMTBool) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      BVSMulODecl.constructDynamic(children, emptyList())

  fun expand(): Expression<BoolSort> = TODO()
}

class BVSDivO(override val lhs: Expression<BitVecSort>, override val rhs: Expression<BitVecSort>) :
    BinaryExpression<BoolSort, BitVecSort, BitVecSort>("bvsdivo".toSymbol(), SMTBool) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      BVSDivODecl.constructDynamic(children, emptyList())

  fun expand(): Expression<BoolSort> = TODO()
}

class UBVToInt(override val inner: Expression<BitVecSort>) :
    UnaryExpression<IntSort, BitVecSort>("ubv_to_int".toSymbol(), SMTInt) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      UBVToIntDecl.constructDynamic(children, emptyList())
}

class SBVToInt(override val inner: Expression<BitVecSort>) :
    UnaryExpression<IntSort, BitVecSort>("sbv_to_int".toSymbol(), SMTInt) {
  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      SBVToIntDecl.constructDynamic(children, emptyList())
}

class IntToBV(val m: Int, override val inner: Expression<IntSort>) :
    UnaryExpression<BitVecSort, IntSort>("int_to_bv".toSymbol(), BitVecSort(m)) {
  override val indices = listOf(m)

  override val theories = FIXED_SIZE_BIT_VECTORS_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<BitVecSort> =
      IntToBVDecl.constructDynamic(children, emptyList())
}

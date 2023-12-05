/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2023 The Konstraints Authors
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

package tools.aqua.konstraints

import tools.aqua.konstraints.parser.*

internal object BitVectorExpressionContext : TheoryContext {
  override val functions: HashSet<FunctionDecl<*>> =
      hashSetOf(
          BVUltDecl,
          BVConcatDecl,
          BVAndDecl,
          BVNegDecl,
          BVNotDecl,
          BVOrDecl,
          BVAddDecl,
          BVMulDecl,
          BVUDivDecl,
          BVURemDecl,
          BVShlDecl,
          BVLShrDecl)
  override val sorts = mapOf(Pair("BitVec", BVSortDecl))
}

internal object BVSortDecl : SortDecl<BVSort>("BitVec") {
  override fun getSort(sort: ProtoSort): BVSort {
    require(sort.identifier is IndexedIdentifier)
    require(sort.identifier.indices.size == 1)

    return BVSort((sort.identifier.indices[0] as NumeralParseIndex).numeral)
  }
}

/*
 * This file implements the SMT theory of fixed size bitvectors
 * http://smtlib.cs.uiowa.edu/theories-FixedSizeBitVectors.shtml
 */

data class BVLiteral(override val symbol: String) : Expression<BVSort>() {
  val bits: Int
  val isBinary: Boolean

  init {
    if (symbol[1] == 'b') {
      bits = symbol.length - 2
      isBinary = true
    } else if (symbol[1] == 'x') {
      bits = (symbol.length - 2) * 4
      isBinary = false
    } else {
      throw IllegalArgumentException("$symbol is not a valid bitvector literal.")
    }
  }

  override val sort = BVSort(bits)

  override fun toString() = symbol
}

/**
 * Concatenation of two [Expression]s of [BVSort]
 *
 * @param [lhs] left [Expression]
 * @param [rhs] right [Expression]
 */
class BVConcat(val lhs: Expression<BVSort>, val rhs: Expression<BVSort>) : Expression<BVSort>() {
  override val sort: BVSort = BVSort(lhs.sort.bits + rhs.sort.bits)
  override val symbol: String by lazy { "(concat $lhs $rhs)" }
}

object BVConcatDecl :
    FunctionDecl2<BVSort, BVSort, BVSort>(
        "concat",
        emptySet(),
        BVSort.fromSymbol("a"),
        BVSort.fromSymbol("b"),
        setOf(SymbolIndex("a"), SymbolIndex("b")),
        BVSort.fromSymbol("c")) {
  override fun buildExpression(
      param1: Expression<BVSort>,
      param2: Expression<BVSort>,
      bindings: Bindings
  ): Expression<BVSort> {
    return BVConcat(param1, param2)
  }
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
class BVExtract(val i: Int, val j: Int, val inner: Expression<BVSort>) : Expression<BVSort>() {
  override val sort: BVSort = BVSort(i - j + 1)
  override val symbol: String by lazy { "((_ extract $i $j) $inner)" }

  init {
    require(j >= 0) { "j needs to be greater or equal to 0, but was $j" }
    require(i >= j) { "i needs to be greater or equal to j, but was $i" }
    require(inner.sort.bits > i) {
      "i can not be greater than the number of bits in inner, but was $i"
    }
  }
}

/**
 * Bitwise not operation on bitvectors
 *
 * @param [inner] [Expression] to be inverted
 */
class BVNot(val inner: Expression<BVSort>) : Expression<BVSort>() {
  override val sort: BVSort = inner.sort
  override val symbol: String by lazy { "(bvnot $inner)" }

  override fun toString(): String = symbol
}

object BVNotDecl :
    FunctionDecl1<BVSort, BVSort>(
        "bvnot",
        emptySet(),
        BVSort.fromSymbol("A"),
        setOf(SymbolIndex("A")),
        BVSort.fromSymbol("A")) {
  override fun buildExpression(param: Expression<BVSort>, bindings: Bindings): Expression<BVSort> =
      BVNot(param)
}

/**
 * Negation operation on bitvectors
 *
 * @param [inner] [Expression] to be negated
 */
class BVNeg(val inner: Expression<BVSort>) : Expression<BVSort>() {
  override val sort: BVSort = inner.sort
  override val symbol: String by lazy { "(bvneg $inner)" }

  override fun toString(): String = symbol
}

object BVNegDecl :
    FunctionDecl1<BVSort, BVSort>(
        "bvneg",
        emptySet(),
        BVSort.fromSymbol("A"),
        setOf(SymbolIndex("A")),
        BVSort.fromSymbol("A")) {
  override fun buildExpression(param: Expression<BVSort>, bindings: Bindings): Expression<BVSort> =
      BVNeg(param)
}

/**
 * Bitwise and operation on bitvectors
 *
 * @param [conjuncts] List of [Expression]s to be combined by and
 * @throws [IllegalArgumentException] if two [conjuncts] do not have the same number of bits
 */
class BVAnd(val conjuncts: List<Expression<BVSort>>) : Expression<BVSort>() {
  /**
   * Bitwise and operation on bitvectors
   *
   * @param [conjuncts] any number of [Expression]s to be combined by and
   * @throws [IllegalArgumentException] if two [conjuncts] do not have the same number of bits
   */
  constructor(vararg conjuncts: Expression<BVSort>) : this(conjuncts.toList())

  override val sort: BVSort = conjuncts.first().sort
  override val symbol: String by lazy { "(bvand ${conjuncts.joinToString(" ")})" }

  init {
    require(conjuncts.all { it.sort.bits == sort.bits }) {
      "All bitvectors must have the same number of bits"
    }
  }

  override fun toString(): String = symbol
}

object BVAndDecl :
    FunctionDeclLeftAssociative<BVSort, BVSort, BVSort>(
        "bvand",
        emptySet(),
        BVSort.fromSymbol("A"),
        BVSort.fromSymbol("A"),
        setOf(SymbolIndex("A")),
        BVSort.fromSymbol("A")) {
  override fun buildExpression(
      param1: Expression<BVSort>,
      param2: Expression<BVSort>,
      varargs: List<Expression<BVSort>>,
      bindings: Bindings
  ): Expression<BVSort> = BVAnd(listOf(param1, param2))
}

/**
 * Bitwise or operation on bitvectors
 *
 * @param [disjuncts] List of [Expression]s to be combined by or
 * @throws [IllegalArgumentException] if two [disjuncts] do not have the same number of bits
 */
class BVOr(val disjuncts: List<Expression<BVSort>>) : Expression<BVSort>() {

  /**
   * Bitwise or operation on bitvectors
   *
   * @param [disjuncts] any number of [Expression]s to be combined by or
   * @throws [IllegalArgumentException] if two [disjuncts] do not have the same number of bits
   */
  constructor(vararg disjuncts: Expression<BVSort>) : this(disjuncts.toList())

  override val sort: BVSort = disjuncts.first().sort
  override val symbol: String by lazy { "(bvor ${disjuncts.joinToString(" ")})" }

  init {
    require(disjuncts.all { it.sort.bits == sort.bits }) {
      "All bitvectors must have the same number of bits"
    }
  }

  override fun toString(): String = symbol
}

object BVOrDecl :
    FunctionDeclLeftAssociative<BVSort, BVSort, BVSort>(
        "bvor",
        emptySet(),
        BVSort.fromSymbol("A"),
        BVSort.fromSymbol("A"),
        setOf(SymbolIndex("A")),
        BVSort.fromSymbol("A")) {
  override fun buildExpression(
      param1: Expression<BVSort>,
      param2: Expression<BVSort>,
      varargs: List<Expression<BVSort>>,
      bindings: Bindings
  ): Expression<BVSort> = BVOr(listOf(param1, param2))
}

/**
 * Addition operation on bitvectors
 *
 * @param [summands] List of [Expression]s to be added up
 * @throws [IllegalArgumentException] if two [summands] do not have the same number of bits
 */
class BVAdd(val summands: List<Expression<BVSort>>) : Expression<BVSort>() {
  /**
   * Addition operation on bitvectors
   *
   * @param [summands] any number of [Expression]s to be added up
   * @throws [IllegalArgumentException] if two [summands] do not have the same number of bits
   */
  constructor(vararg summands: Expression<BVSort>) : this(summands.toList())

  override val sort: BVSort = summands.first().sort
  override val symbol: String by lazy { "(bvadd ${summands.joinToString(" ")})" }

  init {
    require(summands.all { it.sort.bits == sort.bits }) {
      "All bitvectors must have the same number of bits"
    }
  }

  override fun toString(): String = symbol
}

object BVAddDecl :
    FunctionDeclLeftAssociative<BVSort, BVSort, BVSort>(
        "bvadd",
        emptySet(),
        BVSort.fromSymbol("A"),
        BVSort.fromSymbol("A"),
        setOf(SymbolIndex("A")),
        BVSort.fromSymbol("A")) {
  override fun buildExpression(
      param1: Expression<BVSort>,
      param2: Expression<BVSort>,
      varargs: List<Expression<BVSort>>,
      bindings: Bindings
  ): Expression<BVSort> = BVAdd(listOf(param1, param2))
}

/**
 * Multiplication operation on bitvectors
 *
 * @param [factors] List of [Expression]s to be multiplied
 * @throws [IllegalArgumentException] if two [factors] do not have the same number of bits
 */
class BVMul(val factors: List<Expression<BVSort>>) : Expression<BVSort>() {
  /**
   * Multiplication operation on bitvectors
   *
   * @param [factors] any number of [Expression]s to be multiplied
   * @throws [IllegalArgumentException] if two [factors] do not have the same number of bits
   */
  constructor(vararg factors: Expression<BVSort>) : this(factors.toList())

  override val sort: BVSort = factors.first().sort
  override val symbol: String by lazy { "(bvmul ${factors.joinToString(" ")})" }

  init {
    require(factors.all { it.sort.bits == sort.bits }) {
      "All bitvectors must have the same number of bits"
    }
  }

  override fun toString(): String = symbol
}

object BVMulDecl :
    FunctionDeclLeftAssociative<BVSort, BVSort, BVSort>(
        "bvmul",
        emptySet(),
        BVSort.fromSymbol("A"),
        BVSort.fromSymbol("A"),
        setOf(SymbolIndex("A")),
        BVSort.fromSymbol("A")) {
  override fun buildExpression(
      param1: Expression<BVSort>,
      param2: Expression<BVSort>,
      varargs: List<Expression<BVSort>>,
      bindings: Bindings
  ): Expression<BVSort> = BVMul(listOf(param1, param2))
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
    Expression<BVSort>() {

  override val sort: BVSort = numerator.sort
  override val symbol: String by lazy { "(bvudiv $numerator $denominator)" }

  init {
    require(numerator.sort.bits == denominator.sort.bits) {
      "Numerator and denominator must have the same number of bits, but were ${numerator.sort.bits} and ${denominator.sort.bits}"
    }
  }

  override fun toString(): String = symbol
}

object BVUDivDecl :
    FunctionDecl2<BVSort, BVSort, BVSort>(
        "bvudiv",
        emptySet(),
        BVSort.fromSymbol("A"),
        BVSort.fromSymbol("A"),
        setOf(SymbolIndex("A")),
        BVSort.fromSymbol("A")) {
  override fun buildExpression(
      param1: Expression<BVSort>,
      param2: Expression<BVSort>,
      bindings: Bindings
  ) = BVUDiv(param1, param2)
}

/**
 * Unsigned remainder operation on bitvectors
 *
 * @throws [IllegalArgumentException] if [numerator] and [denominator] do not have the same number
 *   of bits
 */
class BVURem(val numerator: Expression<BVSort>, val denominator: Expression<BVSort>) :
    Expression<BVSort>() {

  override val sort: BVSort = numerator.sort
  override val symbol: String by lazy { "(bvurem $numerator $denominator)" }

  init {
    require(numerator.sort.bits == denominator.sort.bits)
  }

  override fun toString(): String = symbol
}

object BVURemDecl :
    FunctionDecl2<BVSort, BVSort, BVSort>(
        "bvurem",
        emptySet(),
        BVSort.fromSymbol("A"),
        BVSort.fromSymbol("A"),
        setOf(SymbolIndex("A")),
        BVSort.fromSymbol("A")) {
  override fun buildExpression(
      param1: Expression<BVSort>,
      param2: Expression<BVSort>,
      bindings: Bindings
  ) = BVURem(param1, param2)
}

/**
 * Left shift operation on bitvectors
 *
 * @param [value] to be shifted
 * @param [distance] number of bits [value] is shifted by
 * @throws [IllegalArgumentException] if [value] and [distance] do not have the same number of bits
 */
class BVShl(val value: Expression<BVSort>, val distance: Expression<BVSort>) :
    Expression<BVSort>() {
  override val sort: BVSort = value.sort
  override val symbol: String by lazy { "(bvshl $value $distance)" }

  init {
    require(value.sort.bits == distance.sort.bits) {
      "value and distance must have the same number of bits, but were ${value.sort.bits} and ${value.sort.bits}"
    }
  }

  override fun toString(): String = symbol
}

object BVShlDecl :
    FunctionDecl2<BVSort, BVSort, BVSort>(
        "bvshl",
        emptySet(),
        BVSort.fromSymbol("A"),
        BVSort.fromSymbol("A"),
        setOf(SymbolIndex("A")),
        BVSort.fromSymbol("A")) {
  override fun buildExpression(
      param1: Expression<BVSort>,
      param2: Expression<BVSort>,
      bindings: Bindings
  ) = BVShl(param1, param2)
}

/**
 * Logical right shift operation on bitvectors
 *
 * @param [value] to be shifted
 * @param [distance] number of shifts
 * @throws [IllegalArgumentException] if [value] and [distance] do not have the same number of bits
 */
class BVLShr(val value: Expression<BVSort>, val distance: Expression<BVSort>) :
    Expression<BVSort>() {
  override val sort: BVSort = value.sort
  override val symbol: String by lazy { "(bvlshr $value $distance)" }

  init {
    require(value.sort.bits == distance.sort.bits) {
      "value and distance must have the same number of bits, but were ${value.sort.bits} and ${value.sort.bits}"
    }
  }

  override fun toString(): String = symbol
}

object BVLShrDecl :
    FunctionDecl2<BVSort, BVSort, BVSort>(
        "bvlshr",
        emptySet(),
        BVSort.fromSymbol("A"),
        BVSort.fromSymbol("A"),
        setOf(SymbolIndex("A")),
        BVSort.fromSymbol("A")) {
  override fun buildExpression(
      param1: Expression<BVSort>,
      param2: Expression<BVSort>,
      bindings: Bindings
  ) = BVLShr(param1, param2)
}

/**
 * Unsigned less-than operation on bitvectors
 *
 * @param [lhs] left value
 * @param [rhs] right value
 * @throws [IllegalArgumentException] if [lhs] and [rhs] do not have the same number of bits
 */
class BVUlt(val lhs: Expression<BVSort>, val rhs: Expression<BVSort>) : Expression<BoolSort>() {

  override val sort: BoolSort = BoolSort
  override val symbol: String by lazy { "(bvult $lhs $rhs)" }

  init {
    require(lhs.sort.bits == rhs.sort.bits) {
      "lhs and rhs must have the same number of bits, but were ${lhs.sort.bits} and ${rhs.sort.bits}"
    }
  }

  override fun toString(): String = symbol
}

object BVUltDecl :
    FunctionDecl2<BVSort, BVSort, BoolSort>(
        "bvult",
        emptySet(),
        BVSort.fromSymbol("a"),
        BVSort.fromSymbol("a"),
        setOf(SymbolIndex("a")),
        BoolSort) {
  override fun buildExpression(
      param1: Expression<BVSort>,
      param2: Expression<BVSort>,
      bindings: Bindings
  ): Expression<BoolSort> = BVUlt(param1, param2)
}

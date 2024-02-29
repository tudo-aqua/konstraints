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

package tools.aqua.konstraints.theories

import tools.aqua.konstraints.parser.*
import tools.aqua.konstraints.smt.*

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
          BVLShrDecl,
          ExtractDecl)
  override val sorts = mapOf(Pair("BitVec", BVSortDecl))
}

internal object BVSortDecl : SortDecl<BVSort>("BitVec") {
  override fun getSort(sort: ProtoSort): BVSort {
    require(sort.identifier is IndexedIdentifier)
    require(sort.identifier.indices.size == 1)

    return BVSort((sort.identifier.indices[0] as NumeralIndex).numeral)
  }
}

/*
 * This file implements the SMT theory of fixed size bitvectors
 * http://smtlib.cs.uiowa.edu/theories-FixedSizeBitVectors.shtml
 */

class BVLiteral(vector: String) : Expression<BVSort>() {
  val value: Int
  val bits: Int
  val isBinary: Boolean

  init {
    if (vector[1] == 'b') {
      bits = vector.length - 2
      isBinary = true
      value = Integer.parseInt(vector.substring(2), 2)
    } else if (vector[1] == 'x') {
      bits = (vector.length - 2) * 4
      isBinary = false
      value = Integer.parseInt(vector.substring(2), 16)
    } else {
      throw IllegalArgumentException("$vector is not a valid bitvector literal.")
    }
  }

  override val sort = BVSort(bits)
  override val symbol: Symbol = "|$vector|".symbol()

  override fun toString() = symbol.toString()
}

/**
 * Concatenation of two [Expression]s of [BVSort]
 *
 * @param [lhs] left [Expression]
 * @param [rhs] right [Expression]
 */
class BVConcat(val lhs: Expression<BVSort>, val rhs: Expression<BVSort>) : Expression<BVSort>() {
  override val sort: BVSort = BVSort(lhs.sort.bits + rhs.sort.bits)
  override val symbol: Symbol = "concat".symbol()

  override fun toString(): String = "(concat $lhs $rhs)"
}

object BVConcatDecl :
    FunctionDecl2<BVSort, BVSort, BVSort>(
        "concat".symbol(),
        emptySet(),
        BVSort.fromSymbol("i"),
        BVSort.fromSymbol("j"),
        emptySet(),
        setOf(SymbolIndex("i"), SymbolIndex("j")),
        BVSort.fromSymbol("m")) {
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
  override val symbol: Symbol = "extract".symbol()

  init {
    require(j >= 0) { "j needs to be greater or equal to 0, but was $j" }
    require(i >= j) { "i needs to be greater or equal to j, but was $i" }
    require(inner.sort.bits > i) {
      "i can not be greater than the number of bits in inner, but was $i"
    }
  }

  override fun toString(): String = "((_ extract $i $j) $inner)"
}

object ExtractDecl :
    FunctionDecl1<BVSort, BVSort>(
        "extract".symbol(),
        emptySet(),
        BVSort.fromSymbol("m"),
        setOf(SymbolIndex("i"), SymbolIndex("j")),
        setOf(SymbolIndex("m")),
        BVSort.fromSymbol("n")) {

  override fun buildExpression(
      args: List<Expression<*>>,
      functionIndices: Set<NumeralIndex>
  ): Expression<BVSort> {
    require(args.size == 1)
    val bindings = bindParametersToExpressions(args, functionIndices)

    return buildExpression(args.single() as Expression<BVSort>, bindings)
  }

  override fun buildExpression(param: Expression<BVSort>, bindings: Bindings): Expression<BVSort> {
    return BVExtract(bindings["i"].numeral, bindings["j"].numeral, param)
  }
}

/**
 * Bitwise not operation on bitvectors
 *
 * @param [inner] [Expression] to be inverted
 */
class BVNot(val inner: Expression<BVSort>) : Expression<BVSort>() {
  override val sort: BVSort = inner.sort
  override val symbol: Symbol = "bvnot".symbol()

  override fun toString(): String = "(bvnot $inner)"
}

object BVNotDecl :
    FunctionDecl1<BVSort, BVSort>(
        "bvnot".symbol(),
        emptySet(),
        BVSort.fromSymbol("m"),
        emptySet(),
        setOf(SymbolIndex("m")),
        BVSort.fromSymbol("m")) {
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
  override val symbol: Symbol = "bvneg".symbol()

  override fun toString(): String = "(bvneg $inner)"
}

object BVNegDecl :
    FunctionDecl1<BVSort, BVSort>(
        "bvneg".symbol(),
        emptySet(),
        BVSort.fromSymbol("m"),
        emptySet(),
        setOf(SymbolIndex("m")),
        BVSort.fromSymbol("m")) {
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
  override val symbol: Symbol = "bvand".symbol()

  init {
    require(conjuncts.all { it.sort.bits == sort.bits }) {
      "All bitvectors must have the same number of bits"
    }
  }

  override fun toString(): String = "(bvand ${conjuncts.joinToString(" ")})"
}

object BVAndDecl :
    FunctionDeclLeftAssociative<BVSort, BVSort, BVSort>(
        "bvand".symbol(),
        emptySet(),
        BVSort.fromSymbol("m"),
        BVSort.fromSymbol("m"),
        emptySet(),
        setOf(SymbolIndex("m")),
        BVSort.fromSymbol("m")) {
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
  override val symbol: Symbol = "bvor".symbol()

  init {
    require(disjuncts.all { it.sort.bits == sort.bits }) {
      "All bitvectors must have the same number of bits"
    }
  }

  override fun toString(): String = "(bvor ${disjuncts.joinToString(" ")})"
}

object BVOrDecl :
    FunctionDeclLeftAssociative<BVSort, BVSort, BVSort>(
        "bvor".symbol(),
        emptySet(),
        BVSort.fromSymbol("m"),
        BVSort.fromSymbol("m"),
        emptySet(),
        setOf(SymbolIndex("m")),
        BVSort.fromSymbol("m")) {
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
  override val symbol: Symbol = "bvadd".symbol()

  init {
    require(summands.all { it.sort.bits == sort.bits }) {
      "All bitvectors must have the same number of bits"
    }
  }

  override fun toString(): String = "(bvadd ${summands.joinToString(" ")})"
}

object BVAddDecl :
    FunctionDeclLeftAssociative<BVSort, BVSort, BVSort>(
        "bvadd".symbol(),
        emptySet(),
        BVSort.fromSymbol("m"),
        BVSort.fromSymbol("m"),
        emptySet(),
        setOf(SymbolIndex("m")),
        BVSort.fromSymbol("m")) {
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
  override val symbol: Symbol = "bvmul".symbol()

  init {
    require(factors.all { it.sort.bits == sort.bits }) {
      "All bitvectors must have the same number of bits"
    }
  }

  override fun toString(): String = "(bvmul ${factors.joinToString(" ")})"
}

object BVMulDecl :
    FunctionDeclLeftAssociative<BVSort, BVSort, BVSort>(
        "bvmul".symbol(),
        emptySet(),
        BVSort.fromSymbol("m"),
        BVSort.fromSymbol("m"),
        emptySet(),
        setOf(SymbolIndex("m")),
        BVSort.fromSymbol("m")) {
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
  override val symbol: Symbol = "bvudiv".symbol()

  init {
    require(numerator.sort.bits == denominator.sort.bits) {
      "Numerator and denominator must have the same number of bits, but were ${numerator.sort.bits} and ${denominator.sort.bits}"
    }
  }

  override fun toString(): String = "(bvudiv $numerator $denominator)"
}

object BVUDivDecl :
    FunctionDecl2<BVSort, BVSort, BVSort>(
        "bvudiv".symbol(),
        emptySet(),
        BVSort.fromSymbol("m"),
        BVSort.fromSymbol("m"),
        emptySet(),
        setOf(SymbolIndex("m")),
        BVSort.fromSymbol("m")) {
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
  override val symbol: Symbol = "bvurem".symbol()

  init {
    require(numerator.sort.bits == denominator.sort.bits)
  }

  override fun toString(): String = "(bvurem $numerator $denominator)"
}

object BVURemDecl :
    FunctionDecl2<BVSort, BVSort, BVSort>(
        "bvurem".symbol(),
        emptySet(),
        BVSort.fromSymbol("m"),
        BVSort.fromSymbol("m"),
        emptySet(),
        setOf(SymbolIndex("m")),
        BVSort.fromSymbol("m")) {
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
  override val symbol: Symbol = "bvshl".symbol()

  init {
    require(value.sort.bits == distance.sort.bits) {
      "value and distance must have the same number of bits, but were ${value.sort.bits} and ${value.sort.bits}"
    }
  }

  override fun toString(): String = "(bvshl $value $distance)"
}

object BVShlDecl :
    FunctionDecl2<BVSort, BVSort, BVSort>(
        "bvshl".symbol(),
        emptySet(),
        BVSort.fromSymbol("m"),
        BVSort.fromSymbol("m"),
        emptySet(),
        setOf(SymbolIndex("m")),
        BVSort.fromSymbol("m")) {
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
  override val symbol: Symbol = "bvlshr".symbol()

  init {
    require(value.sort.bits == distance.sort.bits) {
      "value and distance must have the same number of bits, but were ${value.sort.bits} and ${value.sort.bits}"
    }
  }

  override fun toString(): String = "(bvlshr $value $distance)"
}

object BVLShrDecl :
    FunctionDecl2<BVSort, BVSort, BVSort>(
        "bvlshr".symbol(),
        emptySet(),
        BVSort.fromSymbol("m"),
        BVSort.fromSymbol("m"),
        emptySet(),
        setOf(SymbolIndex("m")),
        BVSort.fromSymbol("m")) {
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
  override val symbol: Symbol = "bvult".symbol()

  init {
    require(lhs.sort.bits == rhs.sort.bits) {
      "lhs and rhs must have the same number of bits, but were ${lhs.sort.bits} and ${rhs.sort.bits}"
    }
  }

  override fun toString(): String = "(bvult $lhs $rhs)"
}

object BVUltDecl :
    FunctionDecl2<BVSort, BVSort, BoolSort>(
        "bvult".symbol(),
        emptySet(),
        BVSort.fromSymbol("m"),
        BVSort.fromSymbol("m"),
        emptySet(),
        setOf(SymbolIndex("m")),
        BoolSort) {
  override fun buildExpression(
      param1: Expression<BVSort>,
      param2: Expression<BVSort>,
      bindings: Bindings
  ): Expression<BoolSort> = BVUlt(param1, param2)
}
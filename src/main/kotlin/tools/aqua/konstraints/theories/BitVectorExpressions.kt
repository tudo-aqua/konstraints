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

import java.math.BigInteger
import tools.aqua.konstraints.parser.*
import tools.aqua.konstraints.smt.*

/** FixedSizeBitVectors theory object */
object BitVectorExpressionTheory : Theory {
  override val functions =
      listOf(
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
          .associateBy { it.name.toString() }
  override val sorts = mapOf(Pair("BitVec", BVSortDecl))
}

/**
 * BitVec sort declaration
 *
 * (_ BitVec m)
 */
object BVSortDecl : SortDecl<BVSort>("BitVec".symbol(), emptySet(), setOf("m".idx())) {
  override fun getSort(bindings: Bindings): BVSort = BVSort(bindings["m"].numeral)
}

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
  }

  override val sort = BVSort(bits)

  override fun toString() = name.toString()

  override fun copy(children: List<Expression<*>>): Expression<BVSort> = this
}

/**
 * Concatenation of two [Expression]s of [BVSort]
 *
 * @param [lhs] left [Expression]
 * @param [rhs] right [Expression]
 */
class BVConcat(override val lhs: Expression<BVSort>, override val rhs: Expression<BVSort>) :
    BinaryExpression<BVSort, BVSort, BVSort>("concat".symbol(), BVSort(1)) {
  override val sort: BVSort = BVSort(lhs.sort.bits + rhs.sort.bits)

  override val name: Symbol = "concat".symbol()

  init {
    require(!lhs.sort.isSymbolic())
    require(!rhs.sort.isSymbolic())
  }

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      BVConcatDecl.buildExpression(children, emptySet())
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
class BVExtract(val i: Int, val j: Int, override val inner: Expression<BVSort>) :
    UnaryExpression<BVSort, BVSort>("extract".symbol(), BVSort(1)) {
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
      ExtractDecl.buildExpression(children, setOf(i.idx(), j.idx()))
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
class BVNot(override val inner: Expression<BVSort>) :
    UnaryExpression<BVSort, BVSort>("bvnot".symbol(), inner.sort) {

  init {
    require(!inner.sort.isSymbolic())
  }

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      BVNotDecl.buildExpression(children, emptySet())
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
class BVNeg(override val inner: Expression<BVSort>) :
    UnaryExpression<BVSort, BVSort>("bvneg".symbol(), inner.sort) {

  init {
    require(!inner.sort.isSymbolic())
  }

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      BVNegDecl.buildExpression(children, emptySet())
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
class BVAnd(val conjuncts: List<Expression<BVSort>>) :
    HomogenousExpression<BVSort, BVSort>("bvand".symbol(), conjuncts.first().sort) {
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
      BVAndDecl.buildExpression(children, emptySet())
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
class BVOr(val disjuncts: List<Expression<BVSort>>) :
    HomogenousExpression<BVSort, BVSort>("bvor".symbol(), disjuncts.first().sort) {

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
      BVOrDecl.buildExpression(children, emptySet())
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
class BVAdd(val summands: List<Expression<BVSort>>) :
    HomogenousExpression<BVSort, BVSort>("bvadd".symbol(), summands.first().sort) {
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
      BVAddDecl.buildExpression(children, emptySet())
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
class BVMul(val factors: List<Expression<BVSort>>) :
    HomogenousExpression<BVSort, BVSort>("bvmul".symbol(), factors.first().sort) {
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
      BVMulDecl.buildExpression(children, emptySet())
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
    BinaryExpression<BVSort, BVSort, BVSort>("bvudiv".symbol(), numerator.sort) {

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
      BVUDivDecl.buildExpression(children, emptySet())
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
    BinaryExpression<BVSort, BVSort, BVSort>("bvurem".symbol(), numerator.sort) {

  init {
    require(numerator.sort.bits == denominator.sort.bits)
    require(!numerator.sort.isSymbolic())
    require(!denominator.sort.isSymbolic())
  }

  override val lhs: Expression<BVSort> = numerator

  override val rhs: Expression<BVSort> = denominator

  override fun copy(children: List<Expression<*>>): Expression<BVSort> =
      BVURemDecl.buildExpression(children, emptySet())
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
    BinaryExpression<BVSort, BVSort, BVSort>("bvshl".symbol(), value.sort) {

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
      BVShlDecl.buildExpression(children, emptySet())
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
    BinaryExpression<BVSort, BVSort, BVSort>("bvlshr".symbol(), value.sort) {

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
      BVLShrDecl.buildExpression(children, emptySet())
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
class BVUlt(override val lhs: Expression<BVSort>, override val rhs: Expression<BVSort>) :
    BinaryExpression<BoolSort, BVSort, BVSort>("bvult".symbol(), BoolSort) {

  init {
    require(lhs.sort.bits == rhs.sort.bits) {
      "lhs and rhs must have the same number of bits, but were ${lhs.sort.bits} and ${rhs.sort.bits}"
    }
    require(!lhs.sort.isSymbolic())
    require(!rhs.sort.isSymbolic())
  }

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      BVUltDecl.buildExpression(children, emptySet())
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

fun BVNAnd(lhs: Expression<BVSort>, rhs: Expression<BVSort>): Expression<BVSort> =
    BVNot(BVAnd(lhs, rhs))

object BVNAndDecl :
    FunctionDecl2<BVSort, BVSort, BVSort>(
        "bvnand".symbol(),
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
  ): Expression<BVSort> = BVNAnd(param1, param2)
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

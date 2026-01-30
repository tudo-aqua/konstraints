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

package tools.aqua.konstraints.parser

import tools.aqua.konstraints.smt.*

/** Enum for all associativity types. */
enum class Associativity {
  LEFT_ASSOC,
  RIGHT_ASSOC,
  PAIRWISE,
  CHAINABLE,
  NONE,
}

/** Base class for all smt functions defined by a theory. */
abstract class SMTTheoryFunction<T : Sort>(
    override val symbol: Symbol,
    override val parameters: List<Sort>,
    override val sort: T,
    val associativity: Associativity,
) : SMTFunction<T>()

/** Base class for all smt theories. */
interface Theory {
  val functions: Map<Symbol, SMTFunction<*>>
  val sorts: Map<Symbol, SortFactory>
}

/** Core theory internal object. */
internal object CoreTheory : Theory {
  override val functions =
      listOf(
              FalseDecl,
              TrueDecl,
              NotDecl,
              AndDecl,
              OrDecl,
              XOrDecl,
              EqualsDecl,
              DistinctDecl,
              IteDecl,
              ImpliesDecl,
          )
          .associateBy { it.symbol }
  override val sorts = mapOf(SMTBool.symbol to BoolFactory)
}

internal object TrueDecl :
    SMTTheoryFunction<BoolSort>(
        "true".toSymbol(),
        emptyList(),
        SMTBool,
        Associativity.NONE,
    ) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }

    return True
  }
}

internal object FalseDecl :
    SMTTheoryFunction<BoolSort>(
        "false".toSymbol(),
        emptyList(),
        SMTBool,
        Associativity.NONE,
    ) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }

    return False
  }
}

/** Not declaration internal object. */
internal object NotDecl :
    SMTTheoryFunction<BoolSort>(
        "not".toSymbol(),
        listOf(SMTBool),
        SMTBool,
        Associativity.NONE,
    ) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }

    return Not(args.single().cast())
  }
}

/** Implies declaration internal object. */
internal object ImpliesDecl :
    SMTTheoryFunction<BoolSort>(
        "=>".toSymbol(),
        listOf(SMTBool, SMTBool),
        SMTBool,
        Associativity.CHAINABLE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }

    return try {
      Implies(args.map { it.cast() })
    } catch (e: ExpressionCastException) {
      throw IllegalArgumentException(
          "Expected all args of $symbol to be of sort Bool but was: ${args.map { expr -> expr.sort }.joinToString(", ")}"
      )
    }
  }
}

/** And declaration internal object. */
internal object AndDecl :
    SMTTheoryFunction<BoolSort>(
        "and".toSymbol(),
        listOf(SMTBool, SMTBool),
        SMTBool,
        Associativity.LEFT_ASSOC,
    ) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }

    return try {
      And(args.map { it.cast() })
    } catch (e: ExpressionCastException) {
      throw IllegalArgumentException(
          "Expected all args of $symbol to be of sort Bool but was: ${args.map { expr -> expr.sort }.joinToString(", ")}"
      )
    }
  }
}

/** Or declaration internal object. */
internal object OrDecl :
    SMTTheoryFunction<BoolSort>(
        "or".toSymbol(),
        listOf(SMTBool, SMTBool),
        SMTBool,
        Associativity.LEFT_ASSOC,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }

    return try {
      Or(args.map { it.cast() })
    } catch (e: ExpressionCastException) {
      throw IllegalArgumentException(
          "Expected all args of $symbol to be of sort Bool but was: ${args.map { expr -> expr.sort }.joinToString(", ")}"
      )
    }
  }
}

/** Xor declaration internal object. */
internal object XOrDecl :
    SMTTheoryFunction<BoolSort>(
        "xor".toSymbol(),
        listOf(SMTBool, SMTBool),
        SMTBool,
        Associativity.LEFT_ASSOC,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }

    return try {
      XOr(args.map { it.cast() })
    } catch (e: ExpressionCastException) {
      throw IllegalArgumentException(
          "Expected all args of $symbol to be of sort Bool but was: ${args.map { expr -> expr.sort }.joinToString(", ")}"
      )
    }
  }
}

/** Equals declaration internal object. */
internal object EqualsDecl :
    SMTTheoryFunction<Sort>(
        "=".toSymbol(),
        listOf(SortParameter("A"), SortParameter("A")),
        SortParameter("A"),
        Associativity.CHAINABLE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort == args[0].sort }) {
      "Expected all args of $symbol to be of the same sort but was: ${args.map { expr -> expr.sort }.joinToString(", ")}"
    }

    return Equals(args)
  }
}

/** Distinct declaration internal object. */
internal object DistinctDecl :
    SMTTheoryFunction<Sort>(
        "distinct".toSymbol(),
        listOf(SortParameter("A"), SortParameter("A")),
        SortParameter("A"),
        Associativity.PAIRWISE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort == args[0].sort }) {
      "Expected all args of $symbol to be of the same sort but was: ${args.map { expr -> expr.sort }.joinToString(", ")}"
    }

    return Distinct(args)
  }
}

/** Ite declaration internal object. */
internal object IteDecl :
    SMTTheoryFunction<Sort>(
        "ite".toSymbol(),
        listOf(SMTBool, SortParameter("A"), SortParameter("A")),
        SMTBool,
        Associativity.NONE,
    ) {

  override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Ite<*> {
    require(args.size == 3) {
      "Three arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }

    return Ite(args[0].cast(), args[1], args[2])
  }
}

/** FixedSizeBitVectors theory internal object. */
internal object BitVectorExpressionTheory : Theory {
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
              ExtractDecl,
              BVNAndDecl,
              BVNOrDecl,
              BVXOrDecl,
              BVXNOrDecl,
              BVCompDecl,
              BVSubDecl,
              BVSDivDecl,
              BVSRemDecl,
              BVSModDecl,
              BVAShrDecl,
              RepeatDecl,
              ZeroExtendDecl,
              SignExtendDecl,
              RotateLeftDecl,
              RotateRightDecl,
              BVULeDecl,
              BVUGtDecl,
              BVUGeDecl,
              BVSLtDecl,
              BVSLeDecl,
              BVSGtDecl,
              BVSGeDecl,
              UBVToIntDecl,
              SBVToIntDecl,
              IntToBVDecl,
              BVNegODecl,
              BVUAddODecl,
              BVSAddODecl,
              BVUMulODecl,
              BVSMulODecl,
          )
          .associateBy { it.symbol }
  override val sorts = mapOf("BitVec".toSymbol() to BitVecFactory)
}

internal object BVConcatDecl :
    SMTTheoryFunction<BitVecSort>(
        "concat".toSymbol(),
        listOf(BitVecSort.fromSymbol("i"), BitVecSort.fromSymbol("j")),
        BitVecSort.fromSymbol("m"),
        Associativity.NONE,
    ) {
  @Suppress("UNCHECKED_CAST")
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BitVecSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    return BVConcat(args[0] as Expression<BitVecSort>, args[1] as Expression<BitVecSort>)
  }
}

internal object ExtractDecl :
    SMTTheoryFunction<BitVecSort>(
        "extract".toSymbol(),
        listOf(BitVecSort.fromSymbol("m")),
        BitVecSort.fromSymbol("n"),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 2) {
      "Two indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is BitVecSort) {
      "Expected arg of $symbol to be BitVec but was ${args.single().sort}"
    }
    require(indices.all { index -> index is NumeralIndex }) {
      "Expected all indices of $symbol to be numeral"
    }

    @Suppress("UNCHECKED_CAST")
    return BVExtract(
        (indices[0] as NumeralIndex).numeral,
        (indices[1] as NumeralIndex).numeral,
        args.single() as Expression<BitVecSort>,
    )
  }
}

internal object BVNotDecl :
    SMTTheoryFunction<BitVecSort>(
        "bvnot".toSymbol(),
        listOf(BitVecSort.fromSymbol("m")),
        BitVecSort.fromSymbol("m"),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is BitVecSort) {
      "Expected arg of $symbol to be BitVec but was ${args.single().sort}"
    }

    @Suppress("UNCHECKED_CAST")
    return BVNot(args.single() as Expression<BitVecSort>)
  }
}

internal object BVNegDecl :
    SMTTheoryFunction<BitVecSort>(
        "bvneg".toSymbol(),
        listOf(BitVecSort.fromSymbol("m")),
        BitVecSort.fromSymbol("m"),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is BitVecSort) {
      "Expected arg of $symbol to be BitVec but was ${args.single().sort}"
    }

    @Suppress("UNCHECKED_CAST")
    return BVNeg(args.single() as Expression<BitVecSort>)
  }
}

internal object BVAndDecl :
    SMTTheoryFunction<BitVecSort>(
        "bvand".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        BitVecSort.fromSymbol("m"),
        Associativity.LEFT_ASSOC,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BitVecSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVAnd(args.map { expression -> expression as Expression<BitVecSort> })
  }
}

internal object BVOrDecl :
    SMTTheoryFunction<BitVecSort>(
        "bvor".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        BitVecSort.fromSymbol("m"),
        Associativity.LEFT_ASSOC,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BitVecSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVOr(args.map { expression -> expression as Expression<BitVecSort> })
  }
}

internal object BVAddDecl :
    SMTTheoryFunction<BitVecSort>(
        "bvadd".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        BitVecSort.fromSymbol("m"),
        Associativity.LEFT_ASSOC,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BitVecSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVAdd(args.map { expression -> expression as Expression<BitVecSort> })
  }
}

internal object BVMulDecl :
    SMTTheoryFunction<BitVecSort>(
        "bvmul".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        BitVecSort.fromSymbol("m"),
        Associativity.LEFT_ASSOC,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BitVecSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVMul(args.map { expression -> expression as Expression<BitVecSort> })
  }
}

internal object BVUDivDecl :
    SMTTheoryFunction<BitVecSort>(
        "bvudiv".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        BitVecSort.fromSymbol("m"),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BitVecSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVUDiv(args[0] as Expression<BitVecSort>, args[1] as Expression<BitVecSort>)
  }
}

internal object BVURemDecl :
    SMTTheoryFunction<BitVecSort>(
        "bvurem".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        BitVecSort.fromSymbol("m"),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BitVecSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVURem(args[0] as Expression<BitVecSort>, args[1] as Expression<BitVecSort>)
  }
}

internal object BVShlDecl :
    SMTTheoryFunction<BitVecSort>(
        "bvshl".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        BitVecSort.fromSymbol("m"),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BitVecSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVShl(args[0] as Expression<BitVecSort>, args[1] as Expression<BitVecSort>)
  }
}

internal object BVLShrDecl :
    SMTTheoryFunction<BitVecSort>(
        "bvlshr".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        BitVecSort.fromSymbol("m"),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BitVecSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVLShr(args[0] as Expression<BitVecSort>, args[1] as Expression<BitVecSort>)
  }
}

internal object BVUltDecl :
    SMTTheoryFunction<BoolSort>(
        "bvult".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        SMTBool,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BitVecSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVUlt(args[0] as Expression<BitVecSort>, args[1] as Expression<BitVecSort>)
  }
}

internal object BVNAndDecl :
    SMTTheoryFunction<BitVecSort>(
        "bvnand".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        BitVecSort.fromSymbol("m"),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BitVecSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVNAnd(args[0] as Expression<BitVecSort>, args[1] as Expression<BitVecSort>)
  }
}

internal object BVNOrDecl :
    SMTTheoryFunction<BitVecSort>(
        "bvnor".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        BitVecSort.fromSymbol("m"),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BitVecSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVNOr(args[0] as Expression<BitVecSort>, args[1] as Expression<BitVecSort>)
  }
}

internal object BVXOrDecl :
    SMTTheoryFunction<BitVecSort>(
        "bvxor".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        BitVecSort.fromSymbol("m"),
        Associativity.LEFT_ASSOC,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BitVecSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    return BVXOr(args.map { expression -> expression.cast() })
  }
}

internal object BVXNOrDecl :
    SMTTheoryFunction<BitVecSort>(
        "bvxnor".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        BitVecSort.fromSymbol("m"),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BitVecSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVXNOr(args[0] as Expression<BitVecSort>, args[1] as Expression<BitVecSort>)
  }
}

internal object BVCompDecl :
    SMTTheoryFunction<BitVecSort>(
        "bvcomp".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        BitVecSort.fromSymbol("m"),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BitVecSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVComp(args[0] as Expression<BitVecSort>, args[1] as Expression<BitVecSort>)
  }
}

internal object BVSubDecl :
    SMTTheoryFunction<BitVecSort>(
        "bvsub".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        BitVecSort.fromSymbol("m"),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BitVecSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVSub(args[0] as Expression<BitVecSort>, args[1] as Expression<BitVecSort>)
  }
}

internal object BVSDivDecl :
    SMTTheoryFunction<BitVecSort>(
        "bvsdiv".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        BitVecSort.fromSymbol("m"),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BitVecSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVSDiv(args[0] as Expression<BitVecSort>, args[1] as Expression<BitVecSort>)
  }
}

internal object BVSRemDecl :
    SMTTheoryFunction<BitVecSort>(
        "bvsrem".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        BitVecSort.fromSymbol("m"),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BitVecSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVSRem(args[0] as Expression<BitVecSort>, args[1] as Expression<BitVecSort>)
  }
}

internal object BVSModDecl :
    SMTTheoryFunction<BitVecSort>(
        "bvsmod".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        BitVecSort.fromSymbol("m"),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BitVecSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVSMod(args[0] as Expression<BitVecSort>, args[1] as Expression<BitVecSort>)
  }
}

internal object BVULeDecl :
    SMTTheoryFunction<BoolSort>(
        "bvule".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        SMTBool,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BitVecSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVULe(args[0] as Expression<BitVecSort>, args[1] as Expression<BitVecSort>)
  }
}

internal object BVUGtDecl :
    SMTTheoryFunction<BoolSort>(
        "bvugt".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        SMTBool,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BitVecSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVUGt(args[0] as Expression<BitVecSort>, args[1] as Expression<BitVecSort>)
  }
}

internal object BVUGeDecl :
    SMTTheoryFunction<BoolSort>(
        "bvuge".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        SMTBool,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BitVecSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVUGe(args[0] as Expression<BitVecSort>, args[1] as Expression<BitVecSort>)
  }
}

internal object BVSLtDecl :
    SMTTheoryFunction<BoolSort>(
        "bvslt".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        SMTBool,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BitVecSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVSLt(args[0] as Expression<BitVecSort>, args[1] as Expression<BitVecSort>)
  }
}

internal object BVSLeDecl :
    SMTTheoryFunction<BoolSort>(
        "bvsle".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        SMTBool,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BitVecSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVSLe(args[0] as Expression<BitVecSort>, args[1] as Expression<BitVecSort>)
  }
}

internal object BVSGtDecl :
    SMTTheoryFunction<BoolSort>(
        "bvsgt".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        SMTBool,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BitVecSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVSGt(args[0] as Expression<BitVecSort>, args[1] as Expression<BitVecSort>)
  }
}

internal object BVSGeDecl :
    SMTTheoryFunction<BoolSort>(
        "bvsge".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        SMTBool,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BitVecSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVSGe(args[0] as Expression<BitVecSort>, args[1] as Expression<BitVecSort>)
  }
}

internal object BVAShrDecl :
    SMTTheoryFunction<BitVecSort>(
        "bvashr".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        BitVecSort.fromSymbol("m"),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BitVecSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVAShr(args[0] as Expression<BitVecSort>, args[1] as Expression<BitVecSort>)
  }
}

internal object RepeatDecl :
    SMTTheoryFunction<BitVecSort>(
        "repeat".toSymbol(),
        listOf(BitVecSort.fromSymbol("m")),
        BitVecSort.fromSymbol("n"),
        Associativity.NONE,
    ) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 1) {
      "One index expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is BitVecSort) {
      "Expected arg of $symbol to be BitVec but was ${args.single().sort}"
    }
    require(indices.single() is NumeralIndex) {
      "Expected index of $symbol to be numeral but was ${indices.single()}"
    }

    @Suppress("UNCHECKED_CAST")
    return Repeat(
        (indices.single() as NumeralIndex).numeral,
        args.single() as Expression<BitVecSort>,
    )
  }
}

internal object ZeroExtendDecl :
    SMTTheoryFunction<BitVecSort>(
        "zero_extend".toSymbol(),
        listOf(BitVecSort.fromSymbol("m")),
        BitVecSort.fromSymbol("n"),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 1) {
      "One index expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is BitVecSort) {
      "Expected arg of $symbol to be BitVec but was ${args.single().sort}"
    }
    require(indices.single() is NumeralIndex) {
      "Expected index of $symbol to be numeral but was ${indices.single()}"
    }

    @Suppress("UNCHECKED_CAST")
    return ZeroExtend(
        (indices.single() as NumeralIndex).numeral,
        args.single() as Expression<BitVecSort>,
    )
  }
}

internal object SignExtendDecl :
    SMTTheoryFunction<BitVecSort>(
        "sign_extend".toSymbol(),
        listOf(BitVecSort.fromSymbol("m")),
        BitVecSort.fromSymbol("n"),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 1) {
      "One index expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is BitVecSort) {
      "Expected arg of $symbol to be BitVec but was ${args.single().sort}"
    }
    require(indices.single() is NumeralIndex) {
      "Expected index of $symbol to be numeral but was ${indices.single()}"
    }

    @Suppress("UNCHECKED_CAST")
    return SignExtend(
        (indices.single() as NumeralIndex).numeral,
        args.single() as Expression<BitVecSort>,
    )
  }
}

internal object RotateLeftDecl :
    SMTTheoryFunction<BitVecSort>(
        "rotate_left".toSymbol(),
        listOf(BitVecSort.fromSymbol("m")),
        BitVecSort.fromSymbol("n"),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 1) {
      "One index expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is BitVecSort) {
      "Expected arg of $symbol to be BitVec but was ${args.single().sort}"
    }
    require(indices.single() is NumeralIndex) {
      "Expected index of $symbol to be numeral but was ${indices.single()}"
    }

    @Suppress("UNCHECKED_CAST")
    return RotateLeft(
        (indices.single() as NumeralIndex).numeral,
        args.single() as Expression<BitVecSort>,
    )
  }
}

internal object RotateRightDecl :
    SMTTheoryFunction<BitVecSort>(
        "rotate_right".toSymbol(),
        listOf(BitVecSort.fromSymbol("m")),
        BitVecSort.fromSymbol("n"),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 1) {
      "One index expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is BitVecSort) {
      "Expected arg of $symbol to be BitVec but was ${args.single().sort}"
    }
    require(indices.single() is NumeralIndex) {
      "Expected index of $symbol to be numeral but was ${indices.single()}"
    }

    @Suppress("UNCHECKED_CAST")
    return RotateRight(
        (indices.single() as NumeralIndex).numeral,
        args.single() as Expression<BitVecSort>,
    )
  }
}

internal object BVNegODecl :
    SMTTheoryFunction<BoolSort>(
        "bvnego".toSymbol(),
        listOf(BitVecSort.fromSymbol("m")),
        SMTBool,
        Associativity.NONE,
    ) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(args.single().sort is BitVecSort) {
      "Expected arg of $symbol to be BitVec but was ${args.single().sort}"
    }

    @Suppress("UNCHECKED_CAST")
    return BVNegO(args[0] as Expression<BitVecSort>)
  }
}

internal object BVUAddODecl :
    SMTTheoryFunction<BoolSort>(
        "bvuaddo".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        SMTBool,
        Associativity.NONE,
    ) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(args.single().sort is BitVecSort) {
      "Expected arg of $symbol to be BitVec but was ${args.single().sort}"
    }

    @Suppress("UNCHECKED_CAST")
    return BVUAddO(args[0] as Expression<BitVecSort>, args[1] as Expression<BitVecSort>)
  }
}

internal object BVSAddODecl :
    SMTTheoryFunction<BoolSort>(
        "bvsaddo".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        SMTBool,
        Associativity.NONE,
    ) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(args.single().sort is BitVecSort) {
      "Expected arg of $symbol to be BitVec but was ${args.single().sort}"
    }

    @Suppress("UNCHECKED_CAST")
    return BVSAddO(args[0] as Expression<BitVecSort>, args[1] as Expression<BitVecSort>)
  }
}

internal object BVUSubODecl :
    SMTTheoryFunction<BoolSort>(
        "bvusubo".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        SMTBool,
        Associativity.NONE,
    ) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(args.single().sort is BitVecSort) {
      "Expected arg of $symbol to be BitVec but was ${args.single().sort}"
    }

    @Suppress("UNCHECKED_CAST")
    return BVUSubO(args[0] as Expression<BitVecSort>, args[1] as Expression<BitVecSort>)
  }
}

internal object BVSSubODecl :
    SMTTheoryFunction<BoolSort>(
        "bvsaddo".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        SMTBool,
        Associativity.NONE,
    ) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(args.single().sort is BitVecSort) {
      "Expected arg of $symbol to be BitVec but was ${args.single().sort}"
    }

    @Suppress("UNCHECKED_CAST")
    return BVSSubO(args[0] as Expression<BitVecSort>, args[1] as Expression<BitVecSort>)
  }
}

internal object BVUMulODecl :
    SMTTheoryFunction<BoolSort>(
        "bvumulo".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        SMTBool,
        Associativity.NONE,
    ) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(args.single().sort is BitVecSort) {
      "Expected arg of $symbol to be BitVec but was ${args.single().sort}"
    }

    @Suppress("UNCHECKED_CAST")
    return BVUMulO(args[0] as Expression<BitVecSort>, args[1] as Expression<BitVecSort>)
  }
}

internal object BVSMulODecl :
    SMTTheoryFunction<BoolSort>(
        "bvsmulo".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        SMTBool,
        Associativity.NONE,
    ) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(args.single().sort is BitVecSort) {
      "Expected arg of $symbol to be BitVec but was ${args.single().sort}"
    }

    @Suppress("UNCHECKED_CAST")
    return BVSMulO(args[0] as Expression<BitVecSort>, args[1] as Expression<BitVecSort>)
  }
}

internal object BVSDivODecl :
    SMTTheoryFunction<BoolSort>(
        "bvsdivo".toSymbol(),
        listOf(BitVecSort.fromSymbol("m"), BitVecSort.fromSymbol("m")),
        SMTBool,
        Associativity.NONE,
    ) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(args.single().sort is BitVecSort) {
      "Expected arg of $symbol to be BitVec but was ${args.single().sort}"
    }

    @Suppress("UNCHECKED_CAST")
    return BVSDivO(args[0] as Expression<BitVecSort>, args[1] as Expression<BitVecSort>)
  }
}

internal object UBVToIntDecl :
    SMTTheoryFunction<IntSort>(
        "ubv_to_int".toSymbol(),
        listOf(BitVecSort.fromSymbol("m")),
        SMTInt,
        Associativity.NONE,
    ) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<IntSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(args.single().sort is BitVecSort) {
      "Expected arg of $symbol to be BitVec but was ${args.single().sort}"
    }

    @Suppress("UNCHECKED_CAST")
    return UBVToInt(args[0] as Expression<BitVecSort>)
  }
}

internal object SBVToIntDecl :
    SMTTheoryFunction<IntSort>(
        "sbv_to_int".toSymbol(),
        listOf(BitVecSort.fromSymbol("m")),
        SMTInt,
        Associativity.NONE,
    ) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<IntSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(args.single().sort is BitVecSort) {
      "Expected arg of $symbol to be BitVec but was ${args.single().sort}"
    }

    @Suppress("UNCHECKED_CAST")
    return SBVToInt(args[0] as Expression<BitVecSort>)
  }
}

internal object IntToBVDecl :
    SMTTheoryFunction<BitVecSort>(
        "int_to_bv".toSymbol(),
        listOf(SMTInt),
        BitVecSort.fromSymbol("m"),
        Associativity.NONE,
    ) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 1) {
      "One index expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is IntSort) {
      "Expected arg of $symbol to be BitVec but was ${args.single().sort}"
    }
    require(indices.single() is NumeralIndex) {
      "Expected index of $symbol to be numeral but was ${indices.single()}"
    }

    @Suppress("UNCHECKED_CAST")
    return IntToBV((indices.single() as NumeralIndex).numeral, args[0] as Expression<IntSort>)
  }
}

/** Ints theory internal object */
internal object IntsTheory : Theory {
  override val functions =
      listOf(
              IntNegSubDecl,
              IntAddDecl,
              IntMulDecl,
              IntDivDecl,
              ModDecl,
              AbsDecl,
              IntLessEqDecl,
              IntLessDecl,
              IntGreaterEqDecl,
              IntGreaterDecl,
              DivisibleDecl,
          )
          .associateBy { it.symbol }

  override val sorts = mapOf(SMTInt.symbol to IntFactory)
}

internal object IntNegDecl :
    SMTTheoryFunction<IntSort>(
        "-".toSymbol(),
        listOf(SMTInt),
        SMTInt,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<IntSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return IntNeg(args.single().cast())
  }
}

internal object IntSubDecl :
    SMTTheoryFunction<IntSort>(
        "-".toSymbol(),
        listOf(SMTInt, SMTInt),
        SMTInt,
        Associativity.LEFT_ASSOC,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<IntSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return IntSub(args.map { expr -> expr.cast() })
  }
}

/** Combined function declaration for overloaded '-' operator */
internal object IntNegSubDecl :
    SMTTheoryFunction<IntSort>(
        "-".toSymbol(),
        listOf(SMTInt),
        SMTInt,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<IntSort> =
      if (args.size == 1) {
        IntNegDecl.constructDynamic(args, indices)
      } else if (args.size > 1) {
        IntSubDecl.constructDynamic(args, indices)
      } else {
        throw IllegalArgumentException()
      }
}

internal object IntAddDecl :
    SMTTheoryFunction<IntSort>(
        "+".toSymbol(),
        listOf(SMTInt, SMTInt),
        SMTInt,
        Associativity.LEFT_ASSOC,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<IntSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return IntAdd(args.map { expr -> expr.cast() })
  }
}

internal object IntMulDecl :
    SMTTheoryFunction<IntSort>(
        "*".toSymbol(),
        listOf(SMTInt, SMTInt),
        SMTInt,
        Associativity.LEFT_ASSOC,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<IntSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return IntMul(args.map { expr -> expr.cast() })
  }
}

internal object IntDivDecl :
    SMTTheoryFunction<IntSort>(
        "div".toSymbol(),
        listOf(SMTInt, SMTInt),
        SMTInt,
        Associativity.LEFT_ASSOC,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<IntSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return IntDiv(args.map { expr -> expr.cast() })
  }
}

internal object ModDecl :
    SMTTheoryFunction<IntSort>(
        "mod".toSymbol(),
        listOf(SMTInt, SMTInt),
        SMTInt,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<IntSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return Mod(args[0].cast(), args[1].cast())
  }
}

internal object AbsDecl :
    SMTTheoryFunction<IntSort>(
        "abs".toSymbol(),
        listOf(SMTInt),
        SMTInt,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<IntSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return IntNeg(args.single().cast())
  }
}

internal object IntLessEqDecl :
    SMTTheoryFunction<BoolSort>(
        "<=".toSymbol(),
        listOf(SMTInt, SMTInt),
        SMTBool,
        Associativity.CHAINABLE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return IntLessEq(args.map { expr -> expr.cast() })
  }
}

internal object IntLessDecl :
    SMTTheoryFunction<BoolSort>(
        "<".toSymbol(),
        listOf(SMTInt, SMTInt),
        SMTBool,
        Associativity.CHAINABLE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return IntLess(args.map { expr -> expr.cast() })
  }
}

internal object IntGreaterEqDecl :
    SMTTheoryFunction<BoolSort>(
        ">=".toSymbol(),
        listOf(SMTInt, SMTInt),
        SMTBool,
        Associativity.CHAINABLE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return IntGreaterEq(args.map { expr -> expr.cast() })
  }
}

internal object IntGreaterDecl :
    SMTTheoryFunction<BoolSort>(
        ">".toSymbol(),
        listOf(SMTInt, SMTInt),
        SMTBool,
        Associativity.CHAINABLE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return IntGreater(args.map { expr -> expr.cast() })
  }
}

internal object DivisibleDecl :
    SMTTheoryFunction<BoolSort>(
        "divisible".toSymbol(),
        listOf(SMTInt),
        SMTBool,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 1) {
      "One index expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is IntSort) {
      "Expected arg of $symbol to be Int but was ${args.single().sort}"
    }
    require(indices.single() is NumeralIndex) {
      "Expected index of $symbol to be numeral but was ${indices.single()}"
    }

    @Suppress("UNCHECKED_CAST")
    return Divisible(
        (indices.single() as NumeralIndex).numeral,
        args.single() as Expression<IntSort>,
    )
  }
}

/** Reals theory internal object */
internal object RealsTheory : Theory {
  override val functions =
      listOf(
              RealNegSubDecl,
              RealAddDecl,
              RealMulDecl,
              RealDivDecl,
              RealLessEqDecl,
              RealLessDecl,
              RealGreaterEqDecl,
              RealGreaterDecl,
          )
          .associateBy { it.symbol }

  override val sorts = mapOf(SMTReal.symbol to RealFactory)
}

internal object RealNegDecl :
    SMTTheoryFunction<RealSort>("-".toSymbol(), listOf(SMTReal), SMTReal, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RealSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RealNeg(args.single().cast())
  }
}

internal object RealSubDecl :
    SMTTheoryFunction<RealSort>(
        "-".toSymbol(),
        listOf(SMTReal),
        SMTReal,
        Associativity.LEFT_ASSOC,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RealSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RealSub(args.map { expr -> expr.cast() })
  }
}

/** Combined function declaration for overloaded '-' operator */
internal object RealNegSubDecl :
    SMTTheoryFunction<RealSort>("-".toSymbol(), listOf(SMTReal), SMTReal, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RealSort> =
      if (args.size == 1) {
        RealNegDecl.constructDynamic(args, indices)
      } else if (args.size > 1) {
        RealSubDecl.constructDynamic(args, indices)
      } else {
        throw IllegalArgumentException()
      }
}

internal object RealAddDecl :
    SMTTheoryFunction<RealSort>(
        "+".toSymbol(),
        listOf(SMTReal, SMTReal),
        SMTReal,
        Associativity.LEFT_ASSOC,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RealSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RealAdd(args.map { expr -> expr.cast() })
  }
}

internal object RealMulDecl :
    SMTTheoryFunction<RealSort>(
        "*".toSymbol(),
        listOf(SMTReal, SMTReal),
        SMTReal,
        Associativity.LEFT_ASSOC,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RealSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RealMul(args.map { expr -> expr.cast() })
  }
}

internal object RealDivDecl :
    SMTTheoryFunction<RealSort>(
        "/".toSymbol(),
        listOf(SMTReal, SMTReal),
        SMTReal,
        Associativity.LEFT_ASSOC,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RealSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RealDiv(args.map { expr -> expr.cast() })
  }
}

internal object RealLessEqDecl :
    SMTTheoryFunction<BoolSort>(
        "<=".toSymbol(),
        listOf(SMTReal, SMTReal),
        SMTBool,
        Associativity.CHAINABLE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RealLessEq(args.map { expr -> expr.cast() })
  }
}

internal object RealLessDecl :
    SMTTheoryFunction<BoolSort>(
        "<".toSymbol(),
        listOf(SMTReal, SMTReal),
        SMTBool,
        Associativity.CHAINABLE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RealLess(args.map { expr -> expr.cast() })
  }
}

internal object RealGreaterEqDecl :
    SMTTheoryFunction<BoolSort>(
        ">=".toSymbol(),
        listOf(SMTReal, SMTReal),
        SMTBool,
        Associativity.CHAINABLE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RealGreaterEq(args.map { expr -> expr.cast() })
  }
}

internal object RealGreaterDecl :
    SMTTheoryFunction<BoolSort>(
        ">".toSymbol(),
        listOf(SMTReal, SMTReal),
        SMTBool,
        Associativity.CHAINABLE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RealGreater(args.map { expr -> expr.cast() })
  }
}

/** Reals Ints theory context */
internal object RealsIntsTheory : Theory {
  override val functions =
      listOf(
              IntRealNegSubDecl,
              ModDecl,
              AbsDecl,
              DivisibleDecl,
              IntRealAddDecl,
              IntRealMulDecl,
              IntDivDecl,
              RealDivDecl,
              ToRealDecl,
              ToIntDecl,
              IsIntDecl,
              IntRealLessDecl,
              IntRealLessEqDecl,
              IntRealGreaterDecl,
              IntRealGreaterEqDecl,
          )
          .associateBy { it.symbol }

  override val sorts = mapOf(SMTInt.symbol to IntFactory, SMTReal.symbol to RealFactory)
}

internal object IntRealNegSubDecl :
    SMTTheoryFunction<Sort>(
        "-".toSymbol(),
        listOf(NumeralSortInstance),
        NumeralSortInstance,
        Associativity.NONE,
    ) {

  override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<Sort> {
    require(args[0].sort is IntSort || args[0].sort is RealSort) {
      "Expected args to be Int or Real, but got ${args[0].sort}"
    }

    if (args.size == 2)
        require(args[0].sort == args[1].sort) {
          "Expected args to be (Int Int) or (Real Real), but got (${args[0].sort} ${args[1].sort})"
        }

    return if (args[0].sort is IntSort) {
      IntNegSubDecl.constructDynamic(args, indices)
    } else {
      RealNegSubDecl.constructDynamic(args, indices)
    }
  }
}

internal object IntRealAddDecl :
    SMTTheoryFunction<Sort>(
        "+".toSymbol(),
        listOf(NumeralSortInstance, NumeralSortInstance),
        NumeralSortInstance,
        Associativity.LEFT_ASSOC,
    ) {

  override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<Sort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }

    require(args[0].sort == args[1].sort && (args[0].sort is IntSort || args[0].sort is RealSort)) {
      "Expected args to be (Int Int) or (Real Real), but got (${args[0].sort} ${args[1].sort})"
    }

    return if (args[0].sort is IntSort) {
      IntAdd(args.map { expr -> expr.cast() })
    } else {
      RealAdd(args.map { expr -> expr.cast() })
    }
  }
}

internal object IntRealMulDecl :
    SMTTheoryFunction<Sort>(
        "*".toSymbol(),
        listOf(NumeralSortInstance, NumeralSortInstance),
        NumeralSortInstance,
        Associativity.LEFT_ASSOC,
    ) {

  override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<Sort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }

    require(args[0].sort == args[1].sort && (args[0].sort is IntSort || args[0].sort is RealSort)) {
      "Expected args to be (Int Int) or (Real Real), but got (${args[0].sort} ${args[1].sort})"
    }

    return if (args[0].sort is IntSort) {
      IntMul(args.map { expr -> expr.cast() })
    } else {
      RealMul(args.map { expr -> expr.cast() })
    }
  }
}

internal object ToRealDecl :
    SMTTheoryFunction<RealSort>(
        "to_real".toSymbol(),
        listOf(SMTInt),
        SMTReal,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RealSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return ToReal(args.single().cast())
  }
}

internal object ToIntDecl :
    SMTTheoryFunction<IntSort>(
        "to_int".toSymbol(),
        listOf(SMTReal),
        SMTInt,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<IntSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return ToInt(args.single().cast())
  }
}

internal object IsIntDecl :
    SMTTheoryFunction<BoolSort>(
        "is_int".toSymbol(),
        listOf(SMTReal),
        SMTBool,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return IsInt(args.single().cast())
  }
}

internal object IntRealLessDecl :
    SMTTheoryFunction<BoolSort>(
        "<".toSymbol(),
        listOf(SMTReal, SMTReal),
        SMTBool,
        Associativity.CHAINABLE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }

    return if (args[0].sort is IntSort && args[1].sort is IntSort)
        IntLessDecl.constructDynamic(args, indices)
    else if (args[0].sort is RealSort && args[1].sort is RealSort)
        RealLessDecl.constructDynamic(args, indices)
    else
        throw IllegalArgumentException(
            "Expected (Int Int) or (Real Real) for $symbol, but was (${args.map {expr -> expr.sort }.joinToString(" ")})"
        )
  }
}

internal object IntRealLessEqDecl :
    SMTTheoryFunction<BoolSort>(
        "<=".toSymbol(),
        listOf(SMTReal, SMTReal),
        SMTBool,
        Associativity.CHAINABLE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }

    return if (args[0].sort is IntSort && args[1].sort is IntSort)
        IntLessEqDecl.constructDynamic(args, indices)
    else if (args[0].sort is RealSort && args[1].sort is RealSort)
        RealLessEqDecl.constructDynamic(args, indices)
    else
        throw IllegalArgumentException(
            "Expected (Int Int) or (Real Real) for $symbol, but was (${args.map {expr -> expr.sort }.joinToString(" ")}), (<= ${args[0]} ${args[1].name})"
        )
  }
}

internal object IntRealGreaterEqDecl :
    SMTTheoryFunction<BoolSort>(
        ">=".toSymbol(),
        listOf(SMTReal, SMTReal),
        SMTBool,
        Associativity.CHAINABLE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }

    return if (args[0].sort is IntSort && args[1].sort is IntSort)
        IntGreaterEqDecl.constructDynamic(args, indices)
    else if (args[0].sort is RealSort && args[1].sort is RealSort)
        RealGreaterEqDecl.constructDynamic(args, indices)
    else
        throw IllegalArgumentException(
            "Expected (Int Int) or (Real Real) for $symbol, but was (${args.map {expr -> expr.sort }.joinToString(" ")})"
        )
  }
}

internal object IntRealGreaterDecl :
    SMTTheoryFunction<BoolSort>(
        ">".toSymbol(),
        listOf(SMTReal, SMTReal),
        SMTBool,
        Associativity.CHAINABLE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }

    return if (args[0].sort is IntSort && args[1].sort is IntSort)
        IntGreaterDecl.constructDynamic(args, indices)
    else if (args[0].sort is RealSort && args[1].sort is RealSort)
        RealGreaterDecl.constructDynamic(args, indices)
    else
        throw IllegalArgumentException(
            "Expected (Int Int) or (Real Real) for $symbol, but was (${args.map {expr -> expr.sort }.joinToString(" ")})"
        )
  }
}

/** FloatingPoint theory internal object */
internal object FloatingPointTheory : Theory {
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
              ToFPDecl,
              UBitVecToFPDecl,
              FPToUBitVecDecl,
              FPToSBitVecDecl,
              FPToRealDecl,
          )
          .associateBy { it.symbol }

  override val sorts =
      mapOf(
          SMTRoundingMode.symbol to RoundingModeFactory,
          SMTReal.symbol to RealFactory,
          "BitVec".toSymbol() to BitVecFactory,
          "FloatingPoint".toSymbol() to FloatingPointFactory,
          "Float16".toSymbol() to Float16Factory,
          "Float32".toSymbol() to Float32Factory,
          "Float64".toSymbol() to Float64Factory,
          "Float128".toSymbol() to Float128Factory,
      )
}

internal object RoundNearestTiesToEvenDecl :
    SMTTheoryFunction<RoundingModeSort>(
        "roundNearestTiesToEven".toSymbol(),
        emptyList(),
        SMTRoundingMode,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RoundingModeSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RoundNearestTiesToEven
  }
}

internal object RNEDecl :
    SMTTheoryFunction<RoundingModeSort>(
        "RNE".toSymbol(),
        emptyList(),
        SMTRoundingMode,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RoundingModeSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RNE
  }
}

internal object RoundNearestTiesToAwayDecl :
    SMTTheoryFunction<RoundingModeSort>(
        "roundNearestTiesToAway".toSymbol(),
        emptyList(),
        SMTRoundingMode,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RoundingModeSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RoundNearestTiesToAway
  }
}

internal object RNADecl :
    SMTTheoryFunction<RoundingModeSort>(
        "RNA".toSymbol(),
        emptyList(),
        SMTRoundingMode,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RoundingModeSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RNA
  }
}

internal object RoundTowardPositiveDecl :
    SMTTheoryFunction<RoundingModeSort>(
        "roundTowardPositive".toSymbol(),
        emptyList(),
        SMTRoundingMode,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RoundingModeSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RoundTowardPositive
  }
}

internal object RTPDecl :
    SMTTheoryFunction<RoundingModeSort>(
        "RTP".toSymbol(),
        emptyList(),
        SMTRoundingMode,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RoundingModeSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RTP
  }
}

internal object RoundTowardNegativeDecl :
    SMTTheoryFunction<RoundingModeSort>(
        "roundTowardNegative".toSymbol(),
        emptyList(),
        SMTRoundingMode,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RoundingModeSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RoundTowardNegative
  }
}

internal object RTNDecl :
    SMTTheoryFunction<RoundingModeSort>(
        "RTN".toSymbol(),
        emptyList(),
        SMTRoundingMode,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RoundingModeSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RTN
  }
}

internal object RoundTowardZeroDecl :
    SMTTheoryFunction<RoundingModeSort>(
        "roundTowardZero".toSymbol(),
        emptyList(),
        SMTRoundingMode,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RoundingModeSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RoundTowardZero
  }
}

internal object RTZDecl :
    SMTTheoryFunction<RoundingModeSort>(
        "RTZ".toSymbol(),
        emptyList(),
        SMTRoundingMode,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RoundingModeSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RTZ
  }
}

internal object FPLiteralDecl :
    SMTTheoryFunction<FPSort>(
        "fp".toSymbol(),
        listOf(BitVecSort(1), BitVecSort.fromSymbol("eb"), BitVecSort.fromSymbol("i")),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE,
    ) {

  @Suppress("UNCHECKED_CAST")
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<FPSort> {
    require(args.size == 3) {
      "Three arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is BitVecSort })
    return FPLiteral(
        args[0] as Expression<BitVecSort>,
        args[1] as Expression<BitVecSort>,
        args[2] as Expression<BitVecSort>,
    )
  }
}

/** Plus infinity declaration internal object */
internal object FPInfinityDecl :
    SMTTheoryFunction<FPSort>(
        "+oo".toSymbol(),
        emptyList(),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE,
    ) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<FPSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 2) {
      "Two indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(indices.all { index -> index is NumeralIndex }) {
      "Expected all indices of $symbol to be numeral"
    }

    return FPInfinity((indices[0] as NumeralIndex).numeral, (indices[1] as NumeralIndex).numeral)
  }
}

/** Minus infinity declaration internal object */
internal object FPMinusInfinityDecl :
    SMTTheoryFunction<FPSort>(
        "-oo".toSymbol(),
        emptyList(),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<FPSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 2) {
      "Two indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(indices.all { index -> index is NumeralIndex }) {
      "Expected all indices of $symbol to be numeral"
    }

    return FPMinusInfinity(
        (indices[0] as NumeralIndex).numeral,
        (indices[1] as NumeralIndex).numeral,
    )
  }
}

/** Plus zero declaration internal object */
internal object FPZeroDecl :
    SMTTheoryFunction<FPSort>(
        "+zero".toSymbol(),
        emptyList(),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<FPSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 2) {
      "Two indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(indices.all { index -> index is NumeralIndex }) {
      "Expected all indices of $symbol to be numeral"
    }

    return FPZero((indices[0] as NumeralIndex).numeral, (indices[1] as NumeralIndex).numeral)
  }
}

/** Minus zero declaration internal object */
internal object FPMinusZeroDecl :
    SMTTheoryFunction<FPSort>(
        "-zero".toSymbol(),
        emptyList(),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<FPSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 2) {
      "Two indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(indices.all { index -> index is NumeralIndex }) {
      "Expected all indices of $symbol to be numeral"
    }

    return FPMinusZero((indices[0] as NumeralIndex).numeral, (indices[1] as NumeralIndex).numeral)
  }
}

/** NaN declaration internal object */
internal object FPNaNDecl :
    SMTTheoryFunction<FPSort>(
        "NaN".toSymbol(),
        emptyList(),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<FPSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 2) {
      "Two indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(indices.all { index -> index is NumeralIndex }) {
      "Expected all indices of $symbol to be numeral"
    }

    return FPNaN((indices[0] as NumeralIndex).numeral, (indices[1] as NumeralIndex).numeral)
  }
}

/** Absolute value declaration internal object */
internal object FPAbsDecl :
    SMTTheoryFunction<FPSort>(
        "fp.abs".toSymbol(),
        listOf(FPSort("eb".idx(), "sb".idx())),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<FPSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is FPSort) {
      "Expected arg of $symbol to be FloatingPoint but was ${args.single().sort}"
    }

    @Suppress("UNCHECKED_CAST")
    return FPAbs(args.single().cast())
  }
}

/** Negation declaration internal object */
internal object FPNegDecl :
    SMTTheoryFunction<FPSort>(
        "fp.neg".toSymbol(),
        listOf(FPSort("eb".idx(), "sb".idx())),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<FPSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is FPSort) {
      "Expected arg of $symbol to be FloatingPoint but was ${args.single().sort}"
    }

    @Suppress("UNCHECKED_CAST")
    return FPNeg(args.single().cast())
  }
}

/** Addition declaration internal object */
internal object FPAddDecl :
    SMTTheoryFunction<FPSort>(
        "fp.add".toSymbol(),
        listOf(SMTRoundingMode, FPSort("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<FPSort> {
    require(args.size == 3) {
      "Three arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args[0].sort is RoundingModeSort)
    require(args[1].sort is FPSort)
    require(args[2].sort is FPSort)

    @Suppress("UNCHECKED_CAST")
    return FPAdd(args[0].cast(), args[1].cast(), args[2].cast())
  }
}

/** Subtraction declaration internal object */
internal object FPSubDecl :
    SMTTheoryFunction<FPSort>(
        "fp.sub".toSymbol(),
        listOf(SMTRoundingMode, FPSort("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<FPSort> {
    require(args.size == 3) {
      "Three arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args[0].sort is RoundingModeSort)
    require(args[1].sort is FPSort)
    require(args[2].sort is FPSort)

    @Suppress("UNCHECKED_CAST")
    return FPSub(args[0].cast(), args[1].cast(), args[2].cast())
  }
}

internal object FPMulDecl :
    SMTTheoryFunction<FPSort>(
        "fp.mul".toSymbol(),
        listOf(SMTRoundingMode, FPSort("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<FPSort> {
    require(args.size == 3) {
      "Three arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args[0].sort is RoundingModeSort)
    require(args[1].sort is FPSort)
    require(args[2].sort is FPSort)

    @Suppress("UNCHECKED_CAST")
    return FPMul(args[0].cast(), args[1].cast(), args[2].cast())
  }
}

internal object FPDivDecl :
    SMTTheoryFunction<FPSort>(
        "fp.div".toSymbol(),
        listOf(SMTRoundingMode, FPSort("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<FPSort> {
    require(args.size == 3) {
      "Three arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args[0].sort is RoundingModeSort)
    require(args[1].sort is FPSort)
    require(args[2].sort is FPSort)

    @Suppress("UNCHECKED_CAST")
    return FPDiv(args[0].cast(), args[1].cast(), args[2].cast())
  }
}

internal object FPFmaDecl :
    SMTTheoryFunction<FPSort>(
        "fp.fma".toSymbol(),
        listOf(
            SMTRoundingMode,
            FPSort("eb".idx(), "sb".idx()),
            FPSort("eb".idx(), "sb".idx()),
            FPSort("eb".idx(), "sb".idx()),
        ),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<FPSort> {
    require(args.size == 4) {
      "Four arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args[0].sort is RoundingModeSort)
    require(args[1].sort is FPSort)
    require(args[2].sort is FPSort)
    require(args[3].sort is FPSort)

    @Suppress("UNCHECKED_CAST")
    return FPFma(args[0].cast(), args[1].cast(), args[2].cast(), args[3].cast())
  }
}

internal object FPSqrtDecl :
    SMTTheoryFunction<FPSort>(
        "fp.sqrt".toSymbol(),
        listOf(SMTRoundingMode, FPSort("eb".idx(), "sb".idx())),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<FPSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args[0].sort is RoundingModeSort)
    require(args[1].sort is FPSort)

    @Suppress("UNCHECKED_CAST")
    return FPSqrt(args[0].cast(), args[1].cast())
  }
}

internal object FPRemDecl :
    SMTTheoryFunction<FPSort>(
        "fp.rem".toSymbol(),
        listOf(FPSort("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<FPSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is FPSort })

    @Suppress("UNCHECKED_CAST")
    return FPRem(args[0].cast(), args[1].cast())
  }
}

internal object FPRoundToIntegralDecl :
    SMTTheoryFunction<FPSort>(
        "fp.roundToIntegral".toSymbol(),
        listOf(SMTRoundingMode, FPSort("eb".idx(), "sb".idx())),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<FPSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args[0].sort is RoundingModeSort)
    require(args[1].sort is FPSort)

    @Suppress("UNCHECKED_CAST")
    return FPRoundToIntegral(args[0].cast(), args[1].cast())
  }
}

internal object FPMinDecl :
    SMTTheoryFunction<FPSort>(
        "fp.min".toSymbol(),
        listOf(FPSort("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<FPSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is FPSort })

    @Suppress("UNCHECKED_CAST")
    return FPMin(args[0].cast(), args[1].cast())
  }
}

internal object FPMaxDecl :
    SMTTheoryFunction<FPSort>(
        "fp.max".toSymbol(),
        listOf(FPSort("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<FPSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is FPSort })

    @Suppress("UNCHECKED_CAST")
    return FPMax(args[0].cast(), args[1].cast())
  }
}

internal object FPLeqDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.leq".toSymbol(),
        listOf(FPSort("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())),
        SMTBool,
        Associativity.CHAINABLE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is FPSort })

    @Suppress("UNCHECKED_CAST")
    return FPLeq(args as List<Expression<FPSort>>)
  }
}

internal object FPLtDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.lt".toSymbol(),
        listOf(FPSort("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())),
        SMTBool,
        Associativity.CHAINABLE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is FPSort })

    @Suppress("UNCHECKED_CAST")
    return FPLt(args as List<Expression<FPSort>>)
  }
}

internal object FPGeqDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.geq".toSymbol(),
        listOf(FPSort("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())),
        SMTBool,
        Associativity.CHAINABLE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is FPSort })

    @Suppress("UNCHECKED_CAST")
    return FPGeq(args as List<Expression<FPSort>>)
  }
}

internal object FPGtDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.gt".toSymbol(),
        listOf(FPSort("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())),
        SMTBool,
        Associativity.CHAINABLE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is FPSort })

    @Suppress("UNCHECKED_CAST")
    return FPGt(args as List<Expression<FPSort>>)
  }
}

internal object FPEqDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.eq".toSymbol(),
        listOf(FPSort("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())),
        SMTBool,
        Associativity.CHAINABLE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is FPSort })

    @Suppress("UNCHECKED_CAST")
    return FPEq(args as List<Expression<FPSort>>)
  }
}

internal object FPIsNormalDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.isNormal".toSymbol(),
        listOf(FPSort("eb".idx(), "sb".idx())),
        SMTBool,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is FPSort) {
      "Expected arg of $symbol to be FloatingPoint but was ${args.single().sort}"
    }

    @Suppress("UNCHECKED_CAST")
    return FPIsNormal(args.single().cast())
  }
}

internal object FPIsSubormalDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.isSubnormal".toSymbol(),
        listOf(FPSort("eb".idx(), "sb".idx())),
        SMTBool,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is FPSort) {
      "Expected arg of $symbol to be FloatingPoint but was ${args.single().sort}"
    }

    @Suppress("UNCHECKED_CAST")
    return FPIsSubnormal(args.single().cast())
  }
}

internal object FPIsZeroDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.isZero".toSymbol(),
        listOf(FPSort("eb".idx(), "sb".idx())),
        SMTBool,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is FPSort) {
      "Expected arg of $symbol to be FloatingPoint but was ${args.single().sort}"
    }

    @Suppress("UNCHECKED_CAST")
    return FPIsZero(args.single().cast())
  }
}

internal object FPIsInfiniteDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.isInfinite".toSymbol(),
        listOf(FPSort("eb".idx(), "sb".idx())),
        SMTBool,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is FPSort) {
      "Expected arg of $symbol to be FloatingPoint but was ${args.single().sort}"
    }

    @Suppress("UNCHECKED_CAST")
    return FPIsInfinite(args.single().cast())
  }
}

internal object FPIsNaNDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.isNaN".toSymbol(),
        listOf(FPSort("eb".idx(), "sb".idx())),
        SMTBool,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is FPSort) {
      "Expected arg of $symbol to be FloatingPoint but was ${args.single().sort}"
    }

    @Suppress("UNCHECKED_CAST")
    return FPIsNaN(args.single().cast())
  }
}

internal object FPIsNegativeDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.isNegative".toSymbol(),
        listOf(FPSort("eb".idx(), "sb".idx())),
        SMTBool,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is FPSort) {
      "Expected arg of $symbol to be FloatingPoint but was ${args.single().sort}"
    }

    @Suppress("UNCHECKED_CAST")
    return FPIsNegative(args.single().cast())
  }
}

internal object FPIsPositiveDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.isPositive".toSymbol(),
        listOf(FPSort("eb".idx(), "sb".idx())),
        SMTBool,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is FPSort) {
      "Expected arg of $symbol to be FloatingPoint but was ${args.single().sort}"
    }

    @Suppress("UNCHECKED_CAST")
    return FPIsPositive(args.single().cast())
  }
}

// "Super" SMT Function to emulate shadowing
internal object ToFPDecl :
    SMTTheoryFunction<FPSort>(
        "to_fp".toSymbol(),
        emptyList(),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE,
    ) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<FPSort> {
    require(indices.size == 2) {
      "Two indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }

    // can only be bitvec version
    return if (args.size == 1) {
      BitVecToFPDecl.constructDynamic(args, indices)
    } else if (args.size == 2) {
      require(args[0].sort is RoundingModeSort)

      when (args[1].sort) {
        is FPSort -> FPToFPDecl.constructDynamic(args, indices)
        is RealSort -> RealToFPDecl.constructDynamic(args, indices)
        is BitVecSort -> SBitVecToFPDecl.constructDynamic(args, indices)
        else -> throw IllegalArgumentException()
      }
    } else {
      throw IllegalArgumentException()
    }
  }
}

internal object BitVecToFPDecl :
    SMTTheoryFunction<FPSort>(
        "to_fp".toSymbol(),
        listOf(BitVecSort.fromSymbol("m")),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<FPSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 2) {
      "Two indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is BitVecSort) {
      "Expected arg of $symbol to be BitVec but was ${args.single().sort}"
    }
    require(indices.all { index -> index is NumeralIndex }) {
      "Expected all indices of $symbol to be numeral"
    }

    @Suppress("UNCHECKED_CAST")
    return BitVecToFP(
        args.single() as Expression<BitVecSort>,
        (indices[0] as NumeralIndex).numeral,
        (indices[1] as NumeralIndex).numeral,
    )
  }
}

internal object FPToFPDecl :
    SMTTheoryFunction<FPSort>(
        "to_fp".toSymbol(),
        listOf(SMTRoundingMode, FPSort("mb".idx(), "nb".idx())),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<FPSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 2) {
      "Two indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args[0].sort is RoundingModeSort)
    require(args[1].sort is FPSort)
    require(indices.all { index -> index is NumeralIndex }) {
      "Expected all indices of $symbol to be numeral"
    }

    @Suppress("UNCHECKED_CAST")
    return FPToFP(
        args[0].cast(),
        args[1].cast(),
        (indices[0] as NumeralIndex).numeral,
        (indices[1] as NumeralIndex).numeral,
    )
  }
}

internal object RealToFPDecl :
    SMTTheoryFunction<FPSort>(
        "to_fp".toSymbol(),
        listOf(SMTRoundingMode, SMTReal),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<FPSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 2) {
      "Two indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args[0].sort is RoundingModeSort)
    require(args[1].sort is RealSort)
    require(indices.all { index -> index is NumeralIndex }) {
      "Expected all indices of $symbol to be numeral"
    }

    @Suppress("UNCHECKED_CAST")
    return RealToFP(
        args[0].cast(),
        args[1] as Expression<RealSort>,
        (indices[0] as NumeralIndex).numeral,
        (indices[1] as NumeralIndex).numeral,
    )
  }
}

internal object SBitVecToFPDecl :
    SMTTheoryFunction<FPSort>(
        "to_fp".toSymbol(),
        listOf(SMTRoundingMode, BitVecSort.fromSymbol("m")),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<FPSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 2) {
      "Two indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args[0].sort is RoundingModeSort)
    require(args[1].sort is BitVecSort)
    require(indices.all { index -> index is NumeralIndex }) {
      "Expected all indices of $symbol to be numeral"
    }

    @Suppress("UNCHECKED_CAST")
    return SBitVecToFP(
        args[0].cast(),
        args[1] as Expression<BitVecSort>,
        (indices[0] as NumeralIndex).numeral,
        (indices[1] as NumeralIndex).numeral,
    )
  }
}

internal object UBitVecToFPDecl :
    SMTTheoryFunction<FPSort>(
        "to_fp_unsigned".toSymbol(),
        listOf(
            SMTRoundingMode,
            BitVecSort.fromSymbol("m"),
        ),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<FPSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 2) {
      "Two indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args[0].sort is RoundingModeSort)
    require(args[1].sort is BitVecSort)
    require(indices.all { index -> index is NumeralIndex }) {
      "Expected all indices of $symbol to be numeral"
    }

    @Suppress("UNCHECKED_CAST")
    return UBitVecToFP(
        args[0].cast(),
        args[1] as Expression<BitVecSort>,
        (indices[0] as NumeralIndex).numeral,
        (indices[1] as NumeralIndex).numeral,
    )
  }
}

internal object FPToUBitVecDecl :
    SMTTheoryFunction<BitVecSort>(
        "fp.to_ubv".toSymbol(),
        listOf(SMTRoundingMode, FPSort("eb".idx(), "sb".idx())),
        BitVecSort.fromSymbol("m"),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 1) {
      "One index expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args[0].sort is RoundingModeSort)
    require(args[1].sort is FPSort)
    require(indices.single() is NumeralIndex) {
      "Expected index of $symbol to be numeral but was ${indices.single()}"
    }

    @Suppress("UNCHECKED_CAST")
    return FPToUBitVec(args[0].cast(), args[1].cast(), (indices.single() as NumeralIndex).numeral)
  }
}

internal object FPToSBitVecDecl :
    SMTTheoryFunction<BitVecSort>(
        "fp.to_sbv".toSymbol(),
        listOf(SMTRoundingMode, FPSort("eb".idx(), "sb".idx())),
        BitVecSort.fromSymbol("m"),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BitVecSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 1) {
      "One index expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args[0].sort is RoundingModeSort)
    require(args[1].sort is FPSort)
    require(indices.single() is NumeralIndex) {
      "Expected index of $symbol to be numeral but was ${indices.single()}"
    }

    @Suppress("UNCHECKED_CAST")
    return FPToSBitVec(args[0].cast(), args[1].cast(), (indices.single() as NumeralIndex).numeral)
  }
}

internal object FPToRealDecl :
    SMTTheoryFunction<RealSort>(
        "fp.to_real".toSymbol(),
        listOf(
            FPSort("eb".idx(), "sb".idx()),
        ),
        SMTReal,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RealSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is FPSort) {
      "Expected arg of $symbol to be FloatingPoint but was ${args.single().sort}"
    }

    @Suppress("UNCHECKED_CAST")
    return FPToReal(args.single().cast())
  }
}

/** Array extension theory internal object. */
internal object ArrayExTheory : Theory {
  override val functions = listOf(ArraySelectDecl, ArrayStoreDecl).associateBy { it.symbol }

  override val sorts = mapOf("Array".toSymbol() to ArraySortFactory)
}

/** Array selection declaration internal object. */
internal object ArraySelectDecl :
    SMTTheoryFunction<Sort>(
        "select".toSymbol(),
        listOf(SMTArray(SortParameter("X"), SortParameter("Y"))),
        SortParameter("Y"),
        Associativity.NONE,
    ) {

  // TODO can this be improved (maybe make this generic)?
  override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<Sort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args[0].sort is ArraySort<*, *>)
    require(args[1].sort == (args[0].sort as ArraySort<*, *>).x)

    @Suppress("UNCHECKED_CAST")
    return ArraySelect(args[0].cast(), args[1].cast())
  }
}

/** Array store declaration internal object. */
internal object ArrayStoreDecl :
    SMTTheoryFunction<ArraySort<Sort, Sort>>(
        "store".toSymbol(),
        listOf(SMTArray(SortParameter("X"), SortParameter("Y"))),
        SMTArray(SortParameter("X"), SortParameter("Y")),
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<ArraySort<Sort, Sort>> {
    require(args.size == 3) {
      "Three arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args[0].sort is ArraySort<*, *>)

    // TODO these can probably be removed (castTo) checks the same requirement
    require(args[1].sort == (args[0].sort as ArraySort<*, *>).x)
    require(args[2].sort == (args[0].sort as ArraySort<*, *>).y)

    @Suppress("UNCHECKED_CAST")
    return ArrayStore(args[0].cast(), args[1].cast(), args[2].cast())
  }
}

/** Strings theory internal object. */
internal object StringsTheory : Theory {
  override val functions =
      listOf(
              CharDecl,
              StrConcatDecl,
              StrLengthDecl,
              StrLexOrderDecl,
              StrRefLexOrderDecl,
              StrAtDecl,
              StrSubstringDecl,
              StrPrefixOfDecl,
              StrSuffixOfDecl,
              StrContainsDecl,
              StrIndexOfDecl,
              StrReplaceDecl,
              StrReplaceAllDecl,
              StrReplaceRegexDecl,
              StrReplaceAllRegexDecl,
              StrIsDigitDecl,
              StrToCodeDecl,
              StrToIntDecl,
              StrFromCodeDecl,
              StrFromIntDecl,
              RegexNoneDecl,
              RegexAllDecl,
              RegexAllCharDecl,
              RegexConcatDecl,
              RegexUnionDecl,
              RegexIntersecDecl,
              RegexStarDecl,
              RegexCompDecl,
              RegexDiffDecl,
              RegexPlusDecl,
              RegexOptionDecl,
              RegexRangeDecl,
              RegexPowerDecl,
              RegexLoopDecl,
              InRegexDecl,
              ToRegexDecl,
          )
          .associateBy { it.symbol }

  override val sorts =
      mapOf(
          SMTString.symbol to StringFactory,
          SMTRegLan.symbol to RegLanFactory,
          SMTInt.symbol to IntFactory,
      )
}

internal object CharDecl :
    SMTTheoryFunction<StringSort>(
        "char".toSymbol(),
        emptyList(),
        SMTString,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<StringSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 1) {
      "One index expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(indices.single() is NumeralIndex) {
      "Expected index of $symbol to be numeral but was ${indices.single()}"
    }

    return TODO("SMT-Lib char not implemented yet!")
  }
}

internal object StrConcatDecl :
    SMTTheoryFunction<StringSort>(
        "str.++".toSymbol(),
        listOf(SMTString, SMTString),
        SMTString,
        Associativity.LEFT_ASSOC,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<StringSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is StringSort })

    @Suppress("UNCHECKED_CAST")
    return StrConcat(args as List<Expression<StringSort>>)
  }
}

internal object StrLengthDecl :
    SMTTheoryFunction<IntSort>(
        "str.len".toSymbol(),
        listOf(SMTString),
        SMTInt,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<IntSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is StringSort)

    return StrLength(args.single().cast())
  }
}

internal object StrLexOrderDecl :
    SMTTheoryFunction<BoolSort>(
        "str.<".toSymbol(),
        listOf(SMTString, SMTString),
        SMTBool,
        Associativity.CHAINABLE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is StringSort })

    @Suppress("UNCHECKED_CAST")
    return StrLexOrder(args as List<Expression<StringSort>>)
  }
}

internal object ToRegexDecl :
    SMTTheoryFunction<RegLanSort>(
        "str.to_re".toSymbol(),
        listOf(SMTString),
        SMTRegLan,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RegLanSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is StringSort)

    return StrToRe(args.single().cast())
  }
}

internal object InRegexDecl :
    SMTTheoryFunction<BoolSort>(
        "str.in_re".toSymbol(),
        listOf(SMTString, SMTRegLan),
        SMTBool,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args[0].sort is StringSort)
    require(args[1].sort is RegLanSort)

    return StrInRe(args[0].cast(), args[1].cast())
  }
}

internal object RegexNoneDecl :
    SMTTheoryFunction<RegLanSort>(
        "re.none".toSymbol(),
        emptyList(),
        SMTRegLan,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RegLanSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }

    return RegexNone
  }
}

internal object RegexAllDecl :
    SMTTheoryFunction<RegLanSort>(
        "re.all".toSymbol(),
        emptyList(),
        SMTRegLan,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RegLanSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }

    return RegexAll
  }
}

internal object RegexAllCharDecl :
    SMTTheoryFunction<RegLanSort>(
        "re.allchar".toSymbol(),
        emptyList(),
        SMTRegLan,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RegLanSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }

    return RegexAllChar
  }
}

internal object RegexConcatDecl :
    SMTTheoryFunction<RegLanSort>(
        "re.++".toSymbol(),
        listOf(SMTRegLan, SMTRegLan),
        SMTRegLan,
        Associativity.LEFT_ASSOC,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RegLanSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is RegLanSort })

    @Suppress("UNCHECKED_CAST")
    return RegexConcat(args as List<Expression<RegLanSort>>)
  }
}

internal object RegexUnionDecl :
    SMTTheoryFunction<RegLanSort>(
        "re.union".toSymbol(),
        listOf(SMTRegLan, SMTRegLan),
        SMTRegLan,
        Associativity.LEFT_ASSOC,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RegLanSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is RegLanSort })

    @Suppress("UNCHECKED_CAST")
    return RegexUnion(args as List<Expression<RegLanSort>>)
  }
}

internal object RegexIntersecDecl :
    SMTTheoryFunction<RegLanSort>(
        "re.inter".toSymbol(),
        listOf(SMTRegLan, SMTRegLan),
        SMTRegLan,
        Associativity.LEFT_ASSOC,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RegLanSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is RegLanSort })

    @Suppress("UNCHECKED_CAST")
    return RegexIntersec(args as List<Expression<RegLanSort>>)
  }
}

internal object RegexStarDecl :
    SMTTheoryFunction<RegLanSort>(
        "re.*".toSymbol(),
        listOf(SMTRegLan),
        SMTRegLan,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RegLanSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is RegLanSort)

    @Suppress("UNCHECKED_CAST")
    return RegexStar(args.single().cast())
  }
}

internal object StrRefLexOrderDecl :
    SMTTheoryFunction<BoolSort>(
        "str.<=".toSymbol(),
        listOf(SMTString, SMTString),
        SMTBool,
        Associativity.CHAINABLE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is StringSort })

    @Suppress("UNCHECKED_CAST")
    return StrRefLexOrder(args as List<Expression<StringSort>>)
  }
}

internal object StrAtDecl :
    SMTTheoryFunction<StringSort>(
        "str.at".toSymbol(),
        listOf(SMTString, SMTInt),
        SMTString,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<StringSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args[0].sort is StringSort)
    require(args[1].sort is IntSort)

    return StrAt(args[0].cast(), args[1].cast())
  }
}

internal object StrSubstringDecl :
    SMTTheoryFunction<StringSort>(
        "str.substr".toSymbol(),
        listOf(SMTString, SMTInt, SMTInt),
        SMTString,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<StringSort> {
    require(args.size == 3) {
      "Three arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args[0].sort is StringSort)
    require(args[1].sort is IntSort)
    require(args[2].sort is IntSort)

    return StrSubstring(args[0].cast(), args[1].cast(), args[2].cast())
  }
}

internal object StrPrefixOfDecl :
    SMTTheoryFunction<BoolSort>(
        "str.prefixof".toSymbol(),
        listOf(SMTString, SMTString),
        SMTBool,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is StringSort })

    return StrPrefixOf(args[0].cast(), args[1].cast())
  }
}

internal object StrSuffixOfDecl :
    SMTTheoryFunction<BoolSort>(
        "str.suffixof".toSymbol(),
        listOf(SMTString, SMTString),
        SMTBool,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is StringSort })

    return StrSuffixOf(args[0].cast(), args[1].cast())
  }
}

internal object StrContainsDecl :
    SMTTheoryFunction<BoolSort>(
        "str.contains".toSymbol(),
        listOf(SMTString, SMTString),
        SMTBool,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is StringSort })

    return StrContains(args[0].cast(), args[1].cast())
  }
}

internal object StrIndexOfDecl :
    SMTTheoryFunction<IntSort>(
        "str.indexof".toSymbol(),
        listOf(SMTString, SMTString, SMTInt),
        SMTInt,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<IntSort> {
    require(args.size == 3) {
      "Three arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args[0].sort is StringSort)
    require(args[1].sort is StringSort)
    require(args[2].sort is IntSort)

    return StrIndexOf(args[0].cast(), args[1].cast(), args[2].cast())
  }
}

internal object StrReplaceDecl :
    SMTTheoryFunction<StringSort>(
        "str.replace".toSymbol(),
        listOf(SMTString, SMTString, SMTString),
        SMTString,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<StringSort> {
    require(args.size == 3) {
      "Three arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is StringSort })

    return StrReplace(args[0].cast(), args[1].cast(), args[2].cast())
  }
}

internal object StrReplaceAllDecl :
    SMTTheoryFunction<StringSort>(
        "str.replace_all".toSymbol(),
        listOf(SMTString, SMTString, SMTString),
        SMTString,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<StringSort> {
    require(args.size == 3) {
      "Three arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is StringSort })

    return StrReplaceAll(args[0].cast(), args[1].cast(), args[2].cast())
  }
}

internal object StrReplaceRegexDecl :
    SMTTheoryFunction<StringSort>(
        "str.replace_re".toSymbol(),
        listOf(SMTString, SMTRegLan, SMTString),
        SMTString,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<StringSort> {
    require(args.size == 3) {
      "Three arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args[0].sort is StringSort)
    require(args[1].sort is RegLanSort)
    require(args[2].sort is StringSort)

    return StrReplaceRegex(args[0].cast(), args[1].cast(), args[2].cast())
  }
}

internal object StrReplaceAllRegexDecl :
    SMTTheoryFunction<StringSort>(
        "str.replace_re_all".toSymbol(),
        listOf(SMTString, SMTRegLan, SMTString),
        SMTString,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<StringSort> {
    require(args.size == 3) {
      "Three arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args[0].sort is StringSort)
    require(args[1].sort is RegLanSort)
    require(args[2].sort is StringSort)

    return StrReplaceAllRegex(args[0].cast(), args[1].cast(), args[2].cast())
  }
}

internal object RegexCompDecl :
    SMTTheoryFunction<RegLanSort>(
        "re.comp".toSymbol(),
        listOf(SMTRegLan),
        SMTRegLan,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RegLanSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is RegLanSort)

    return RegexComp(args.single().cast())
  }
}

internal object RegexDiffDecl :
    SMTTheoryFunction<RegLanSort>(
        "re.diff".toSymbol(),
        listOf(SMTRegLan, SMTRegLan),
        SMTRegLan,
        Associativity.LEFT_ASSOC,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RegLanSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is RegLanSort })

    @Suppress("UNCHECKED_CAST")
    return RegexDiff(args as List<Expression<RegLanSort>>)
  }
}

internal object RegexPlusDecl :
    SMTTheoryFunction<RegLanSort>(
        "re.+".toSymbol(),
        listOf(SMTRegLan),
        SMTRegLan,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RegLanSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is RegLanSort)

    return RegexPlus(args.single().cast())
  }
}

internal object RegexOptionDecl :
    SMTTheoryFunction<RegLanSort>(
        "re.opt".toSymbol(),
        listOf(SMTRegLan),
        SMTRegLan,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RegLanSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is RegLanSort)

    return RegexOption(args.single().cast())
  }
}

internal object RegexRangeDecl :
    SMTTheoryFunction<RegLanSort>(
        "re.range".toSymbol(),
        listOf(SMTString, SMTString),
        SMTRegLan,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RegLanSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is StringSort })

    return RegexRange(args[0].cast(), args[1].cast())
  }
}

internal object RegexPowerDecl :
    SMTTheoryFunction<RegLanSort>(
        "re.^".toSymbol(),
        listOf(SMTRegLan),
        SMTRegLan,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RegLanSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 1) {
      "One index expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is RegLanSort)
    require(indices.single() is NumeralIndex) {
      "Expected index of $symbol to be numeral but was ${indices.single()}"
    }

    return RegexPower(args[0].cast(), (indices.single() as NumeralIndex).numeral)
  }
}

internal object RegexLoopDecl :
    SMTTheoryFunction<RegLanSort>(
        "re.loop".toSymbol(),
        listOf(SMTRegLan),
        SMTRegLan,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<RegLanSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 2) {
      "Two indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is RegLanSort)
    require(indices.all { index -> index is NumeralIndex }) {
      "Expected all indices of $symbol to be numeral"
    }

    return RegexLoop(
        args[0].cast(),
        (indices[0] as NumeralIndex).numeral,
        (indices[1] as NumeralIndex).numeral,
    )
  }
}

internal object StrIsDigitDecl :
    SMTTheoryFunction<BoolSort>(
        "str.is_digit".toSymbol(),
        listOf(SMTString),
        SMTBool,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is StringSort)

    return StrIsDigit(args.single().cast())
  }
}

internal object StrToCodeDecl :
    SMTTheoryFunction<IntSort>(
        "str.to_code".toSymbol(),
        listOf(SMTString),
        SMTInt,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<IntSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is StringSort)

    return StrToCode(args.single().cast())
  }
}

internal object StrFromCodeDecl :
    SMTTheoryFunction<StringSort>(
        "str.from_code".toSymbol(),
        listOf(SMTInt),
        SMTString,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<StringSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is IntSort) {
      "Expected arg of $symbol to be Int but was ${args.single().sort}"
    }

    return StrFromCode(args.single().cast())
  }
}

internal object StrToIntDecl :
    SMTTheoryFunction<IntSort>(
        "str.to_int".toSymbol(),
        listOf(SMTString),
        SMTInt,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<IntSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is StringSort)

    return StrToInt(args.single().cast())
  }
}

internal object StrFromIntDecl :
    SMTTheoryFunction<StringSort>(
        "str.from_int".toSymbol(),
        listOf(SMTInt),
        SMTString,
        Associativity.NONE,
    ) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<StringSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is IntSort) {
      "Expected arg of $symbol to be Int but was ${args.single().sort}"
    }

    return StrFromInt(args.single().cast())
  }
}

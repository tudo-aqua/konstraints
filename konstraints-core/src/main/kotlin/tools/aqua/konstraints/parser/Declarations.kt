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

package tools.aqua.konstraints.parser

import tools.aqua.konstraints.smt.*

enum class Associativity {
  LEFT_ASSOC,
  RIGHT_ASSOC,
  PAIRWISE,
  CHAINABLE,
  NONE
}

abstract class SMTTheoryFunction<T : Sort>(
    override val symbol: Symbol,
    override val parameters: List<Sort>,
    override val sort: T,
    val associativity: Associativity
) : SMTFunction<T>()

interface Theory {
  companion object {
    val logicLookup = mapOf(Theories.CORE to CoreTheory)
  }

  val functions: Map<Symbol, SMTFunction<*>>
  val sorts: Map<Symbol, SortFactory>
}

/** Core theory internal object */
/*internal*/ object CoreTheory : Theory {
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
              ImpliesDecl)
          .associateBy { it.symbol }
  override val sorts = mapOf(Bool.symbol to BoolFactory)
}

internal object TrueDecl :
    SMTTheoryFunction<BoolSort>(
        "true".toSymbolWithQuotes(), emptyList(), Bool, Associativity.NONE) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
        "false".toSymbolWithQuotes(), emptyList(), Bool, Associativity.NONE) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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

/** Not declaration internal object */
internal object NotDecl :
    SMTTheoryFunction<BoolSort>(
        "not".toSymbolWithQuotes(), listOf(Bool), Bool, Associativity.NONE) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }

    return Not(args.single().castTo<BoolSort>())
  }
}

/** Implies declaration internal object */
internal object ImpliesDecl :
    SMTTheoryFunction<BoolSort>(
        "=>".toSymbolWithQuotes(), listOf(Bool, Bool), Bool, Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }

    return Implies(args.map { it.castTo<BoolSort>() })
  }
}

/** And declaration internal object */
internal object AndDecl :
    SMTTheoryFunction<BoolSort>(
        "and".toSymbolWithQuotes(), listOf(Bool, Bool), Bool, Associativity.LEFT_ASSOC) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }

    return And(args.map { it.castTo<BoolSort>() })
  }
}

/** Or declaration internal object */
internal object OrDecl :
    SMTTheoryFunction<BoolSort>(
        "or".toSymbolWithQuotes(), listOf(Bool, Bool), Bool, Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }

    return Or(args.map { it.castTo<BoolSort>() })
  }
}

/** Xor declaration internal object */
internal object XOrDecl :
    SMTTheoryFunction<BoolSort>(
        "xor".toSymbolWithQuotes(), listOf(Bool, Bool), Bool, Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }

    return XOr(args.map { it.castTo<BoolSort>() })
  }
}

/** Equals declaration internal object */
internal object EqualsDecl :
    SMTTheoryFunction<Sort>(
        "=".toSymbolWithQuotes(),
        listOf(SortParameter("A"), SortParameter("A")),
        SortParameter("A"),
        Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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

/** Distinct declaration internal object */
internal object DistinctDecl :
    SMTTheoryFunction<Sort>(
        "distinct".toSymbolWithQuotes(),
        listOf(SortParameter("A"), SortParameter("A")),
        SortParameter("A"),
        Associativity.PAIRWISE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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

/** Ite declaration internal object */
internal object IteDecl :
    SMTTheoryFunction<Sort>(
        "ite".toSymbolWithQuotes(),
        listOf(Bool, SortParameter("A"), SortParameter("A")),
        Bool,
        Associativity.NONE) {

  override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Ite<*> {
    require(args.size == 3) {
      "Three arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }

    return Ite(args[0].castTo<BoolSort>(), args[1], args[2])
  }
}

/** FixedSizeBitVectors theory internal object */
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
              BVSGeDecl)
          .associateBy { it.symbol }
  override val sorts = mapOf("BitVec".toSymbolWithQuotes() to BitVecFactory)
}

internal object BVConcatDecl :
    SMTTheoryFunction<BVSort>(
        "concat".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("i"), BVSort.fromSymbol("j")),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {
  @Suppress("UNCHECKED_CAST")
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BVSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BVSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    return BVConcat(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object ExtractDecl :
    SMTTheoryFunction<BVSort>(
        "extract".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m")),
        BVSort.fromSymbol("n"),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BVSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 2) {
      "Two indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is BVSort) {
      "Expected arg of $symbol to be BitVec but was ${args.single().sort}"
    }
    require(indices.all { index -> index is NumeralIndex }) {
      "Expected all indices of $symbol to be numeral"
    }

    @Suppress("UNCHECKED_CAST")
    return BVExtract(
        (indices[0] as NumeralIndex).numeral,
        (indices[1] as NumeralIndex).numeral,
        args.single() as Expression<BVSort>)
  }
}

internal object BVNotDecl :
    SMTTheoryFunction<BVSort>(
        "bvnot".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BVSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is BVSort) {
      "Expected arg of $symbol to be BitVec but was ${args.single().sort}"
    }

    @Suppress("UNCHECKED_CAST")
    return BVNot(args.single() as Expression<BVSort>)
  }
}

internal object BVNegDecl :
    SMTTheoryFunction<BVSort>(
        "bvneg".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BVSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is BVSort) {
      "Expected arg of $symbol to be BitVec but was ${args.single().sort}"
    }

    @Suppress("UNCHECKED_CAST")
    return BVNeg(args.single() as Expression<BVSort>)
  }
}

internal object BVAndDecl :
    SMTTheoryFunction<BVSort>(
        "bvand".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BVSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BVSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVAnd(args.map { expression -> expression as Expression<BVSort> })
  }
}

internal object BVOrDecl :
    SMTTheoryFunction<BVSort>(
        "bvor".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BVSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BVSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVOr(args.map { expression -> expression as Expression<BVSort> })
  }
}

internal object BVAddDecl :
    SMTTheoryFunction<BVSort>(
        "bvadd".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BVSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BVSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVAdd(args.map { expression -> expression as Expression<BVSort> })
  }
}

internal object BVMulDecl :
    SMTTheoryFunction<BVSort>(
        "bvmul".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BVSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BVSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVMul(args.map { expression -> expression as Expression<BVSort> })
  }
}

internal object BVUDivDecl :
    SMTTheoryFunction<BVSort>(
        "bvudiv".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BVSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BVSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVUDiv(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object BVURemDecl :
    SMTTheoryFunction<BVSort>(
        "bvurem".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BVSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BVSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVURem(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object BVShlDecl :
    SMTTheoryFunction<BVSort>(
        "bvshl".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BVSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BVSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVShl(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object BVLShrDecl :
    SMTTheoryFunction<BVSort>(
        "bvlshr".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BVSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BVSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVLShr(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object BVUltDecl :
    SMTTheoryFunction<BoolSort>(
        "bvult".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        Bool,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BVSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVUlt(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object BVNAndDecl :
    SMTTheoryFunction<BVSort>(
        "bvnand".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BVSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BVSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVNAnd(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object BVNOrDecl :
    SMTTheoryFunction<BVSort>(
        "bvnor".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BVSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BVSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVNOr(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object BVXOrDecl :
    SMTTheoryFunction<BVSort>(
        "bvxor".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BVSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BVSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVXOr(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object BVXNOrDecl :
    SMTTheoryFunction<BVSort>(
        "bvxnor".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BVSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BVSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVXNOr(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object BVCompDecl :
    SMTTheoryFunction<BVSort>(
        "bvcomp".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BVSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BVSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVComp(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object BVSubDecl :
    SMTTheoryFunction<BVSort>(
        "bvsub".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BVSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BVSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVSub(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object BVSDivDecl :
    SMTTheoryFunction<BVSort>(
        "bvsdiv".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BVSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BVSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVSDiv(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object BVSRemDecl :
    SMTTheoryFunction<BVSort>(
        "bvsrem".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BVSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BVSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVSRem(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object BVSModDecl :
    SMTTheoryFunction<BVSort>(
        "bvsmod".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BVSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BVSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVSMod(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object BVULeDecl :
    SMTTheoryFunction<BoolSort>(
        "bvule".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        Bool,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BVSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVULe(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object BVUGtDecl :
    SMTTheoryFunction<BoolSort>(
        "bvugt".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        Bool,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BVSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVUGt(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object BVUGeDecl :
    SMTTheoryFunction<BoolSort>(
        "bvuge".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        Bool,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BVSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVUGe(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object BVSLtDecl :
    SMTTheoryFunction<BoolSort>(
        "bvslt".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        Bool,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BVSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVSLt(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object BVSLeDecl :
    SMTTheoryFunction<BoolSort>(
        "bvsle".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        Bool,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BVSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVSLe(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object BVSGtDecl :
    SMTTheoryFunction<BoolSort>(
        "bvsgt".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        Bool,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BVSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVSGt(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object BVSGeDecl :
    SMTTheoryFunction<BoolSort>(
        "bvsge".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        Bool,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BVSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVSGe(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object BVAShrDecl :
    SMTTheoryFunction<BVSort>(
        "bvashr".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BVSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expression -> expression.sort is BVSort }) {
      "Expected all args of $symbol to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
    }

    @Suppress("UNCHECKED_CAST")
    return BVAShr(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object RepeatDecl :
    SMTTheoryFunction<BVSort>(
        "repeat".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m")),
        BVSort.fromSymbol("n"),
        Associativity.NONE) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BVSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 1) {
      "One index expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is BVSort) {
      "Expected arg of $symbol to be BitVec but was ${args.single().sort}"
    }
    require(indices.single() is NumeralIndex) {
      "Expected index of $symbol to be numeral but was ${indices.single()}"
    }

    @Suppress("UNCHECKED_CAST")
    return Repeat((indices.single() as NumeralIndex).numeral, args.single() as Expression<BVSort>)
  }
}

internal object ZeroExtendDecl :
    SMTTheoryFunction<BVSort>(
        "zero_extend".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m")),
        BVSort.fromSymbol("n"),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BVSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 1) {
      "One index expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is BVSort) {
      "Expected arg of $symbol to be BitVec but was ${args.single().sort}"
    }
    require(indices.single() is NumeralIndex) {
      "Expected index of $symbol to be numeral but was ${indices.single()}"
    }

    @Suppress("UNCHECKED_CAST")
    return ZeroExtend(
        (indices.single() as NumeralIndex).numeral, args.single() as Expression<BVSort>)
  }
}

internal object SignExtendDecl :
    SMTTheoryFunction<BVSort>(
        "sign_extend".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m")),
        BVSort.fromSymbol("n"),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BVSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 1) {
      "One index expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is BVSort) {
      "Expected arg of $symbol to be BitVec but was ${args.single().sort}"
    }
    require(indices.single() is NumeralIndex) {
      "Expected index of $symbol to be numeral but was ${indices.single()}"
    }

    @Suppress("UNCHECKED_CAST")
    return SignExtend(
        (indices.single() as NumeralIndex).numeral, args.single() as Expression<BVSort>)
  }
}

internal object RotateLeftDecl :
    SMTTheoryFunction<BVSort>(
        "rotate_left".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m")),
        BVSort.fromSymbol("n"),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BVSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 1) {
      "One index expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is BVSort) {
      "Expected arg of $symbol to be BitVec but was ${args.single().sort}"
    }
    require(indices.single() is NumeralIndex) {
      "Expected index of $symbol to be numeral but was ${indices.single()}"
    }

    @Suppress("UNCHECKED_CAST")
    return RotateLeft(
        (indices.single() as NumeralIndex).numeral, args.single() as Expression<BVSort>)
  }
}

internal object RotateRightDecl :
    SMTTheoryFunction<BVSort>(
        "rotate_right".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m")),
        BVSort.fromSymbol("n"),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BVSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 1) {
      "One index expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is BVSort) {
      "Expected arg of $symbol to be BitVec but was ${args.single().sort}"
    }
    require(indices.single() is NumeralIndex) {
      "Expected index of $symbol to be numeral but was ${indices.single()}"
    }

    @Suppress("UNCHECKED_CAST")
    return RotateRight(
        (indices.single() as NumeralIndex).numeral, args.single() as Expression<BVSort>)
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
              DivisibleDecl)
          .associateBy { it.symbol }

  override val sorts = mapOf(SMTInt.symbol to IntFactory)
}

internal object IntNegDecl :
    SMTTheoryFunction<IntSort>(
        "-".toSymbolWithQuotes(), listOf(SMTInt), SMTInt, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<IntSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return IntNeg(args.single().castTo<IntSort>())
  }
}

internal object IntSubDecl :
    SMTTheoryFunction<IntSort>(
        "-".toSymbolWithQuotes(), listOf(SMTInt, SMTInt), SMTInt, Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<IntSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return IntSub(args.map { expr -> expr.castTo<IntSort>() })
  }
}

/** Combined function declaration for overloaded '-' operator */
internal object IntNegSubDecl :
    SMTTheoryFunction<IntSort>(
        "-".toSymbolWithQuotes(), listOf(SMTInt), SMTInt, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
        "+".toSymbolWithQuotes(), listOf(SMTInt, SMTInt), SMTInt, Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<IntSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return IntAdd(args.map { expr -> expr.castTo<IntSort>() })
  }
}

internal object IntMulDecl :
    SMTTheoryFunction<IntSort>(
        "*".toSymbolWithQuotes(), listOf(SMTInt, SMTInt), SMTInt, Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<IntSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return IntMul(args.map { expr -> expr.castTo<IntSort>() })
  }
}

internal object IntDivDecl :
    SMTTheoryFunction<IntSort>(
        "div".toSymbolWithQuotes(), listOf(SMTInt, SMTInt), SMTInt, Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<IntSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return IntDiv(args.map { expr -> expr.castTo<IntSort>() })
  }
}

internal object ModDecl :
    SMTTheoryFunction<IntSort>(
        "mod".toSymbolWithQuotes(), listOf(SMTInt, SMTInt), SMTInt, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<IntSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return Mod(args[0].castTo<IntSort>(), args[1].castTo<IntSort>())
  }
}

internal object AbsDecl :
    SMTTheoryFunction<IntSort>(
        "abs".toSymbolWithQuotes(), listOf(SMTInt), SMTInt, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<IntSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return IntNeg(args.single().castTo<IntSort>())
  }
}

internal object IntLessEqDecl :
    SMTTheoryFunction<BoolSort>(
        "<=".toSymbolWithQuotes(), listOf(SMTInt, SMTInt), Bool, Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return IntLessEq(args.map { expr -> expr.castTo<IntSort>() })
  }
}

internal object IntLessDecl :
    SMTTheoryFunction<BoolSort>(
        "<".toSymbolWithQuotes(), listOf(SMTInt, SMTInt), Bool, Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return IntLess(args.map { expr -> expr.castTo<IntSort>() })
  }
}

internal object IntGreaterEqDecl :
    SMTTheoryFunction<BoolSort>(
        ">=".toSymbolWithQuotes(), listOf(SMTInt, SMTInt), Bool, Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return IntGreaterEq(args.map { expr -> expr.castTo<IntSort>() })
  }
}

internal object IntGreaterDecl :
    SMTTheoryFunction<BoolSort>(
        ">".toSymbolWithQuotes(), listOf(SMTInt, SMTInt), Bool, Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return IntGreater(args.map { expr -> expr.castTo<IntSort>() })
  }
}

internal object DivisibleDecl :
    SMTTheoryFunction<BoolSort>(
        "divisible".toSymbolWithQuotes(), listOf(SMTInt), Bool, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
        (indices.single() as NumeralIndex).numeral, args.single() as Expression<IntSort>)
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
              RealGreaterDecl)
          .associateBy { it.symbol }

  override val sorts = mapOf(Real.symbol to RealFactory)
}

internal object RealNegDecl :
    SMTTheoryFunction<RealSort>("-".toSymbolWithQuotes(), listOf(Real), Real, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RealSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RealNeg(args.single().castTo<RealSort>())
  }
}

internal object RealSubDecl :
    SMTTheoryFunction<RealSort>(
        "-".toSymbolWithQuotes(), listOf(Real), Real, Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RealSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RealSub(args.map { expr -> expr.castTo<RealSort>() })
  }
}

/** Combined function declaration for overloaded '-' operator */
internal object RealNegSubDecl :
    SMTTheoryFunction<RealSort>("-".toSymbolWithQuotes(), listOf(Real), Real, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
        "+".toSymbolWithQuotes(), listOf(Real, Real), Real, Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RealSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RealAdd(args.map { expr -> expr.castTo<RealSort>() })
  }
}

internal object RealMulDecl :
    SMTTheoryFunction<RealSort>(
        "*".toSymbolWithQuotes(), listOf(Real, Real), Real, Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RealSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RealMul(args.map { expr -> expr.castTo<RealSort>() })
  }
}

internal object RealDivDecl :
    SMTTheoryFunction<RealSort>(
        "/".toSymbolWithQuotes(), listOf(Real, Real), Real, Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RealSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RealDiv(args.map { expr -> expr.castTo<RealSort>() })
  }
}

internal object RealLessEqDecl :
    SMTTheoryFunction<BoolSort>(
        "<=".toSymbolWithQuotes(), listOf(Real, Real), Bool, Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RealLessEq(args.map { expr -> expr.castTo<RealSort>() })
  }
}

internal object RealLessDecl :
    SMTTheoryFunction<BoolSort>(
        "<".toSymbolWithQuotes(), listOf(Real, Real), Bool, Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RealLess(args.map { expr -> expr.castTo<RealSort>() })
  }
}

internal object RealGreaterEqDecl :
    SMTTheoryFunction<BoolSort>(
        ">=".toSymbolWithQuotes(), listOf(Real, Real), Bool, Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RealGreaterEq(args.map { expr -> expr.castTo<RealSort>() })
  }
}

internal object RealGreaterDecl :
    SMTTheoryFunction<BoolSort>(
        ">".toSymbolWithQuotes(), listOf(Real, Real), Bool, Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2) {
      "Atleast two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RealGreater(args.map { expr -> expr.castTo<RealSort>() })
  }
}

/** Reals Ints theory context */
internal object RealsIntsTheory : Theory {
  override val functions =
      listOf(
              IntNegSubDecl,
              IntAddDecl,
              IntMulDecl,
              IntDivDecl,
              ModDecl,
              AbsDecl,
              DivisibleDecl,
              RealNegSubDecl,
              RealAddDecl,
              RealMulDecl,
              RealDivDecl,
              ToRealDecl,
              ToIntDecl,
              IsIntDecl,
              IntRealLessDecl,
              IntRealLessEqDecl,
              IntRealGreaterDecl,
              IntRealGreaterEqDecl)
          .associateBy { it.symbol }

  override val sorts = mapOf(SMTInt.symbol to IntFactory, Real.symbol to RealFactory)
}

internal object ToRealDecl :
    SMTTheoryFunction<RealSort>(
        "to_real".toSymbolWithQuotes(), listOf(SMTInt), Real, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RealSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return ToReal(args.single().castTo<IntSort>())
  }
}

internal object ToIntDecl :
    SMTTheoryFunction<IntSort>(
        "to_real".toSymbolWithQuotes(), listOf(Real), SMTInt, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<IntSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return ToInt(args.single().castTo<RealSort>())
  }
}

internal object IsIntDecl :
    SMTTheoryFunction<BoolSort>(
        "to_real".toSymbolWithQuotes(), listOf(Real), Bool, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return IsInt(args.single().castTo<RealSort>())
  }
}

internal object IntRealLessDecl :
    SMTTheoryFunction<BoolSort>(
        "<".toSymbolWithQuotes(), listOf(Real, Real), Bool, Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
            "Expected (Int Int) or (Real Real) for $symbol, but was (${args.map {expr -> expr.sort }.joinToString(" ")})")
  }
}

internal object IntRealLessEqDecl :
    SMTTheoryFunction<BoolSort>(
        "<=".toSymbolWithQuotes(), listOf(Real, Real), Bool, Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
            "Expected (Int Int) or (Real Real) for $symbol, but was (${args.map {expr -> expr.sort }.joinToString(" ")})")
  }
}

internal object IntRealGreaterEqDecl :
    SMTTheoryFunction<BoolSort>(
        ">=".toSymbolWithQuotes(), listOf(Real, Real), Bool, Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
            "Expected (Int Int) or (Real Real) for $symbol, but was (${args.map {expr -> expr.sort }.joinToString(" ")})")
  }
}

internal object IntRealGreaterDecl :
    SMTTheoryFunction<BoolSort>(
        ">".toSymbolWithQuotes(), listOf(Real, Real), Bool, Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
            "Expected (Int Int) or (Real Real) for $symbol, but was (${args.map {expr -> expr.sort }.joinToString(" ")})")
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
              FPToRealDecl)
          .associateBy { it.symbol }

  override val sorts =
      mapOf(
          RoundingMode.symbol to RoundingModeFactory,
          Real.symbol to RealFactory,
          "BitVec".toSymbolWithQuotes() to BitVecFactory,
          "FloatingPoint".toSymbolWithQuotes() to FloatingPointFactory,
          "Float16".toSymbolWithQuotes() to Float16Factory,
          "Float32".toSymbolWithQuotes() to Float32Factory,
          "Float64".toSymbolWithQuotes() to Float64Factory,
          "Float128".toSymbolWithQuotes() to Float128Factory)
}

internal object RoundNearestTiesToEvenDecl :
    SMTTheoryFunction<RoundingModeSort>(
        "roundNearestTiesToEven".toSymbolWithQuotes(),
        emptyList(),
        RoundingMode,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RoundingModeSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RoundNearestTiesToEven
  }
}

internal object RNEDecl :
    SMTTheoryFunction<RoundingModeSort>(
        "RNE".toSymbolWithQuotes(), emptyList(), RoundingMode, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RoundingModeSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RNE
  }
}

internal object RoundNearestTiesToAwayDecl :
    SMTTheoryFunction<RoundingModeSort>(
        "roundNearestTiesToAway".toSymbolWithQuotes(),
        emptyList(),
        RoundingMode,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RoundingModeSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RoundNearestTiesToAway
  }
}

internal object RNADecl :
    SMTTheoryFunction<RoundingModeSort>(
        "RNA".toSymbolWithQuotes(), emptyList(), RoundingMode, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RoundingModeSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RNA
  }
}

internal object RoundTowardPositiveDecl :
    SMTTheoryFunction<RoundingModeSort>(
        "roundTowardPositive".toSymbolWithQuotes(), emptyList(), RoundingMode, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RoundingModeSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RoundTowardPositive
  }
}

internal object RTPDecl :
    SMTTheoryFunction<RoundingModeSort>(
        "RTP".toSymbolWithQuotes(), emptyList(), RoundingMode, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RoundingModeSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RTP
  }
}

internal object RoundTowardNegativeDecl :
    SMTTheoryFunction<RoundingModeSort>(
        "roundTowardNegative".toSymbolWithQuotes(), emptyList(), RoundingMode, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RoundingModeSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RoundTowardNegative
  }
}

internal object RTNDecl :
    SMTTheoryFunction<RoundingModeSort>(
        "RTN".toSymbolWithQuotes(), emptyList(), RoundingMode, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RoundingModeSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RTN
  }
}

internal object RoundTowardZeroDecl :
    SMTTheoryFunction<RoundingModeSort>(
        "roundTowardZero".toSymbolWithQuotes(), emptyList(), RoundingMode, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RoundingModeSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RoundTowardZero
  }
}

internal object RTZDecl :
    SMTTheoryFunction<RoundingModeSort>(
        "RTZ".toSymbolWithQuotes(), emptyList(), RoundingMode, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RoundingModeSort> {
    require(args.isEmpty()) {
      "No arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    return RTZ
  }
}

internal object FPLiteralDecl :
    SMTTheoryFunction<FPSort>(
        "fp".toSymbolWithQuotes(),
        listOf(BVSort(1), BVSort.fromSymbol("eb"), BVSort.fromSymbol("i")),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE) {

  @Suppress("UNCHECKED_CAST")
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<FPSort> {
    require(args.size == 3) {
      "Three arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is BVSort })
    return FPLiteral(
        args[0] as Expression<BVSort>, args[1] as Expression<BVSort>, args[2] as Expression<BVSort>)
  }
}

/** Plus infinity declaration internal object */
internal object FPInfinityDecl :
    SMTTheoryFunction<FPSort>(
        "+oo".toSymbolWithQuotes(),
        emptyList(),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
        "-oo".toSymbolWithQuotes(),
        emptyList(),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
        (indices[0] as NumeralIndex).numeral, (indices[1] as NumeralIndex).numeral)
  }
}

/** Plus zero declaration internal object */
internal object FPZeroDecl :
    SMTTheoryFunction<FPSort>(
        "+zero".toSymbolWithQuotes(),
        emptyList(),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
        "-zero".toSymbolWithQuotes(),
        emptyList(),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
        "NaN".toSymbolWithQuotes(),
        emptyList(),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
        "fp.abs".toSymbolWithQuotes(),
        listOf(FPSort("eb".idx(), "sb".idx())),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
    return FPAbs(args.single().castTo<FPSort>())
  }
}

/** Negation declaration internal object */
internal object FPNegDecl :
    SMTTheoryFunction<FPSort>(
        "fp.neg".toSymbolWithQuotes(),
        listOf(FPSort("eb".idx(), "sb".idx())),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
    return FPNeg(args.single().castTo<FPSort>())
  }
}

/** Addition declaration internal object */
internal object FPAddDecl :
    SMTTheoryFunction<FPSort>(
        "fp.add".toSymbolWithQuotes(),
        listOf(RoundingMode, FPSort("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
    return FPAdd(
        args[0].castTo<RoundingModeSort>(), args[1].castTo<FPSort>(), args[2].castTo<FPSort>())
  }
}

/** Subtraction declaration internal object */
internal object FPSubDecl :
    SMTTheoryFunction<FPSort>(
        "fp.sub".toSymbolWithQuotes(),
        listOf(RoundingMode, FPSort("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
    return FPSub(
        args[0].castTo<RoundingModeSort>(), args[1].castTo<FPSort>(), args[2].castTo<FPSort>())
  }
}

internal object FPMulDecl :
    SMTTheoryFunction<FPSort>(
        "fp.mul".toSymbolWithQuotes(),
        listOf(RoundingMode, FPSort("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
    return FPMul(
        args[0].castTo<RoundingModeSort>(), args[1].castTo<FPSort>(), args[2].castTo<FPSort>())
  }
}

internal object FPDivDecl :
    SMTTheoryFunction<FPSort>(
        "fp.div".toSymbolWithQuotes(),
        listOf(RoundingMode, FPSort("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
    return FPDiv(
        args[0].castTo<RoundingModeSort>(), args[1].castTo<FPSort>(), args[2].castTo<FPSort>())
  }
}

internal object FPFmaDecl :
    SMTTheoryFunction<FPSort>(
        "fp.fma".toSymbolWithQuotes(),
        listOf(
            RoundingMode,
            FPSort("eb".idx(), "sb".idx()),
            FPSort("eb".idx(), "sb".idx()),
            FPSort("eb".idx(), "sb".idx())),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
    return FPFma(
        args[0].castTo<RoundingModeSort>(),
        args[1].castTo<FPSort>(),
        args[2].castTo<FPSort>(),
        args[3].castTo<FPSort>())
  }
}

internal object FPSqrtDecl :
    SMTTheoryFunction<FPSort>(
        "fp.sqrt".toSymbolWithQuotes(),
        listOf(RoundingMode, FPSort("eb".idx(), "sb".idx())),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
    return FPSqrt(args[0].castTo<RoundingModeSort>(), args[1].castTo<FPSort>())
  }
}

internal object FPRemDecl :
    SMTTheoryFunction<FPSort>(
        "fp.rem".toSymbolWithQuotes(),
        listOf(FPSort("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<FPSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is FPSort })

    @Suppress("UNCHECKED_CAST")
    return FPRem(args[0].castTo<FPSort>(), args[1].castTo<FPSort>())
  }
}

internal object FPRoundToIntegralDecl :
    SMTTheoryFunction<FPSort>(
        "fp.roundToIntegral".toSymbolWithQuotes(),
        listOf(RoundingMode, FPSort("eb".idx(), "sb".idx())),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
    return FPRoundToIntegral(args[0].castTo<RoundingModeSort>(), args[1].castTo<FPSort>())
  }
}

internal object FPMinDecl :
    SMTTheoryFunction<FPSort>(
        "fp.min".toSymbolWithQuotes(),
        listOf(FPSort("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<FPSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is FPSort })

    @Suppress("UNCHECKED_CAST")
    return FPMin(args[0].castTo<FPSort>(), args[1].castTo<FPSort>())
  }
}

internal object FPMaxDecl :
    SMTTheoryFunction<FPSort>(
        "fp.max".toSymbolWithQuotes(),
        listOf(FPSort("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<FPSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is FPSort })

    @Suppress("UNCHECKED_CAST")
    return FPMax(args[0].castTo<FPSort>(), args[1].castTo<FPSort>())
  }
}

internal object FPLeqDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.leq".toSymbolWithQuotes(),
        listOf(FPSort("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())),
        Bool,
        Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
        "fp.lt".toSymbolWithQuotes(),
        listOf(FPSort("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())),
        Bool,
        Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
        "fp.geq".toSymbolWithQuotes(),
        listOf(FPSort("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())),
        Bool,
        Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
        "fp.gt".toSymbolWithQuotes(),
        listOf(FPSort("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())),
        Bool,
        Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
        "fp.eq".toSymbolWithQuotes(),
        listOf(FPSort("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())),
        Bool,
        Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
        "fp.isNormal".toSymbolWithQuotes(),
        listOf(FPSort("eb".idx(), "sb".idx())),
        Bool,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
    return FPIsNormal(args.single().castTo<FPSort>())
  }
}

internal object FPIsSubormalDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.isSubnormal".toSymbolWithQuotes(),
        listOf(FPSort("eb".idx(), "sb".idx())),
        Bool,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
    return FPIsSubnormal(args.single().castTo<FPSort>())
  }
}

internal object FPIsZeroDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.isZero".toSymbolWithQuotes(),
        listOf(FPSort("eb".idx(), "sb".idx())),
        Bool,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
    return FPIsZero(args.single().castTo<FPSort>())
  }
}

internal object FPIsInfiniteDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.isInfinite".toSymbolWithQuotes(),
        listOf(FPSort("eb".idx(), "sb".idx())),
        Bool,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
    return FPIsInfinite(args.single().castTo<FPSort>())
  }
}

internal object FPIsNaNDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.isNaN".toSymbolWithQuotes(),
        listOf(FPSort("eb".idx(), "sb".idx())),
        Bool,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
    return FPIsNaN(args.single().castTo<FPSort>())
  }
}

internal object FPIsNegativeDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.isNegative".toSymbolWithQuotes(),
        listOf(FPSort("eb".idx(), "sb".idx())),
        Bool,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
    return FPIsNegative(args.single().castTo<FPSort>())
  }
}

internal object FPIsPositiveDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.isPositive".toSymbolWithQuotes(),
        listOf(FPSort("eb".idx(), "sb".idx())),
        Bool,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
    return FPIsPositive(args.single().castTo<FPSort>())
  }
}

// "Super" SMT Function to emulate shadowing
internal object ToFPDecl :
    SMTTheoryFunction<FPSort>(
        "to_fp".toSymbolWithQuotes(),
        emptyList(),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
        is BVSort -> SBitVecToFPDecl.constructDynamic(args, indices)
        else -> throw IllegalArgumentException()
      }
    } else {
      throw IllegalArgumentException()
    }
  }
}

internal object BitVecToFPDecl :
    SMTTheoryFunction<FPSort>(
        "to_fp".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m")),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<FPSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 2) {
      "Two indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is BVSort) {
      "Expected arg of $symbol to be BitVec but was ${args.single().sort}"
    }
    require(indices.all { index -> index is NumeralIndex }) {
      "Expected all indices of $symbol to be numeral"
    }

    @Suppress("UNCHECKED_CAST")
    return BitVecToFP(
        args.single() as Expression<BVSort>,
        (indices[0] as NumeralIndex).numeral,
        (indices[1] as NumeralIndex).numeral)
  }
}

internal object FPToFPDecl :
    SMTTheoryFunction<FPSort>(
        "to_fp".toSymbolWithQuotes(),
        listOf(RoundingMode, FPSort("mb".idx(), "nb".idx())),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
        args[0].castTo<RoundingModeSort>(),
        args[1].castTo<FPSort>(),
        (indices[0] as NumeralIndex).numeral,
        (indices[1] as NumeralIndex).numeral)
  }
}

internal object RealToFPDecl :
    SMTTheoryFunction<FPSort>(
        "to_fp".toSymbolWithQuotes(),
        listOf(RoundingMode, Real),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
        args[0].castTo<RoundingModeSort>(),
        args[1] as Expression<RealSort>,
        (indices[0] as NumeralIndex).numeral,
        (indices[1] as NumeralIndex).numeral)
  }
}

internal object SBitVecToFPDecl :
    SMTTheoryFunction<FPSort>(
        "to_fp".toSymbolWithQuotes(),
        listOf(RoundingMode, BVSort.fromSymbol("m")),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<FPSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 2) {
      "Two indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args[0].sort is RoundingModeSort)
    require(args[1].sort is BVSort)
    require(indices.all { index -> index is NumeralIndex }) {
      "Expected all indices of $symbol to be numeral"
    }

    @Suppress("UNCHECKED_CAST")
    return SBitVecToFP(
        args[0].castTo<RoundingModeSort>(),
        args[1] as Expression<BVSort>,
        (indices[0] as NumeralIndex).numeral,
        (indices[1] as NumeralIndex).numeral)
  }
}

internal object UBitVecToFPDecl :
    SMTTheoryFunction<FPSort>(
        "to_fp_unsigned".toSymbolWithQuotes(),
        listOf(
            RoundingMode,
            BVSort.fromSymbol("m"),
        ),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<FPSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.size == 2) {
      "Two indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args[0].sort is RoundingModeSort)
    require(args[1].sort is BVSort)
    require(indices.all { index -> index is NumeralIndex }) {
      "Expected all indices of $symbol to be numeral"
    }

    @Suppress("UNCHECKED_CAST")
    return UBitVecToFP(
        args[0].castTo<RoundingModeSort>(),
        args[1] as Expression<BVSort>,
        (indices[0] as NumeralIndex).numeral,
        (indices[1] as NumeralIndex).numeral)
  }
}

internal object FPToUBitVecDecl :
    SMTTheoryFunction<BVSort>(
        "fp.to_ubv".toSymbolWithQuotes(),
        listOf(RoundingMode, FPSort("eb".idx(), "sb".idx())),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BVSort> {
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
    return FPToUBitVec(
        args[0].castTo<RoundingModeSort>(),
        args[1].castTo<FPSort>(),
        (indices.single() as NumeralIndex).numeral)
  }
}

internal object FPToSBitVecDecl :
    SMTTheoryFunction<BVSort>(
        "fp.to_sbv".toSymbolWithQuotes(),
        listOf(RoundingMode, FPSort("eb".idx(), "sb".idx())),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BVSort> {
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
    return FPToSBitVec(
        args[0].castTo<RoundingModeSort>(),
        args[1].castTo<FPSort>(),
        (indices.single() as NumeralIndex).numeral)
  }
}

internal object FPToRealDecl :
    SMTTheoryFunction<RealSort>(
        "fp.to_real".toSymbolWithQuotes(),
        listOf(
            FPSort("eb".idx(), "sb".idx()),
        ),
        Real,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
    return FPToReal(args.single().castTo<FPSort>())
  }
}

/** Array extension theory internal object */
internal object ArrayExTheory : Theory {
  override val functions = listOf(ArraySelectDecl, ArrayStoreDecl).associateBy { it.symbol }

  override val sorts = mapOf("Array".toSymbolWithQuotes() to ArraySortFactory)
}

/** Array selection declaration internal object */
internal object ArraySelectDecl :
    SMTTheoryFunction<Sort>(
        "select".toSymbolWithQuotes(),
        listOf(SMTArray(SortParameter("X"), SortParameter("Y"))),
        SortParameter("Y"),
        Associativity.NONE) {

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
    return ArraySelect(
        args[0].castTo(),
        args[1].castTo())
  }
}

/** Array store declaration internal object */
internal object ArrayStoreDecl :
    SMTTheoryFunction<ArraySort<Sort, Sort>>(
        "store".toSymbolWithQuotes(),
        listOf(SMTArray(SortParameter("X"), SortParameter("Y"))),
        SMTArray(SortParameter("X"), SortParameter("Y")),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
    return ArrayStore(
        args[0].castTo(),
        args[1].castTo(),
        args[2].castTo())
  }
}

/** Strings theory internal object */
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
              RegexLoopDecl)
          .associateBy { it.symbol }

  override val sorts =
      mapOf(
          SMTString.symbol to StringFactory,
          RegLan.symbol to RegLanFactory,
          SMTInt.symbol to IntFactory)
}

internal object CharDecl :
    SMTTheoryFunction<StringSort>(
        "char".toSymbolWithQuotes(), emptyList(), SMTString, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
        "str.++".toSymbolWithQuotes(),
        listOf(SMTString, SMTString),
        SMTString,
        Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
        "str.len".toSymbolWithQuotes(), listOf(SMTString), SMTInt, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<IntSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is StringSort)

    return StrLength(args.single().castTo())
  }
}

internal object StrLexOrderDecl :
    SMTTheoryFunction<BoolSort>(
        "str.<".toSymbolWithQuotes(), listOf(SMTString, SMTString), Bool, Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
        "str.to_reg".toSymbolWithQuotes(), listOf(SMTString), RegLan, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RegLanSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is StringSort)

    return ToRegex(args.single().castTo())
  }
}

internal object InRegexDecl :
    SMTTheoryFunction<BoolSort>(
        "str.in_reg".toSymbolWithQuotes(), listOf(SMTString, RegLan), Bool, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args[0].sort is StringSort)
    require(args[1].sort is RegLanSort)

    return InRegex(args[0].castTo(), args[1].castTo())
  }
}

internal object RegexNoneDecl :
    SMTTheoryFunction<RegLanSort>(
        "re.none".toSymbolWithQuotes(), emptyList(), RegLan, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
        "re.all".toSymbolWithQuotes(), emptyList(), RegLan, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
        "re.allchar".toSymbolWithQuotes(), emptyList(), RegLan, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
        "re.++".toSymbolWithQuotes(), listOf(RegLan, RegLan), RegLan, Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
        "re.union".toSymbolWithQuotes(), listOf(RegLan, RegLan), RegLan, Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
        "re.inter".toSymbolWithQuotes(), listOf(RegLan, RegLan), RegLan, Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
        "re.*".toSymbolWithQuotes(), listOf(RegLan), RegLan, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RegLanSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is RegLanSort)

    @Suppress("UNCHECKED_CAST")
    return RegexStar(args.single().castTo())
  }
}

internal object StrRefLexOrderDecl :
    SMTTheoryFunction<BoolSort>(
        "str.<=".toSymbolWithQuotes(),
        listOf(SMTString, SMTString),
        Bool,
        Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
        "str.at".toSymbolWithQuotes(), listOf(SMTString, SMTInt), SMTString, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<StringSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args[0].sort is StringSort)
    require(args[1].sort is IntSort)

    return StrAt(args[0].castTo(), args[1].castTo<IntSort>())
  }
}

internal object StrSubstringDecl :
    SMTTheoryFunction<StringSort>(
        "str.substr".toSymbolWithQuotes(),
        listOf(SMTString, SMTInt, SMTInt),
        SMTString,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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

    return StrSubstring(args[0].castTo(), args[1].castTo<IntSort>(), args[2].castTo<IntSort>())
  }
}

internal object StrPrefixOfDecl :
    SMTTheoryFunction<BoolSort>(
        "str.prefixof".toSymbolWithQuotes(),
        listOf(SMTString, SMTString),
        Bool,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is StringSort })

    return StrPrefixOf(args[0].castTo(), args[1].castTo())
  }
}

internal object StrSuffixOfDecl :
    SMTTheoryFunction<BoolSort>(
        "str.suffixof".toSymbolWithQuotes(),
        listOf(SMTString, SMTString),
        Bool,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is StringSort })

    return StrSuffixOf(args[0].castTo(), args[1].castTo())
  }
}

internal object StrContainsDecl :
    SMTTheoryFunction<BoolSort>(
        "str.contains".toSymbolWithQuotes(),
        listOf(SMTString, SMTString),
        Bool,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is StringSort })

    return StrContains(args[0].castTo(), args[1].castTo())
  }
}

internal object StrIndexOfDecl :
    SMTTheoryFunction<IntSort>(
        "str.indexof".toSymbolWithQuotes(),
        listOf(SMTString, SMTString, SMTInt),
        SMTInt,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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

    return StrIndexOf(args[0].castTo(), args[1].castTo(), args[2].castTo<IntSort>())
  }
}

internal object StrReplaceDecl :
    SMTTheoryFunction<StringSort>(
        "str.replace".toSymbolWithQuotes(),
        listOf(SMTString, SMTString, SMTString),
        SMTString,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<StringSort> {
    require(args.size == 3) {
      "Three arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is StringSort })

    return StrReplace(args[0].castTo(), args[1].castTo(), args[2].castTo())
  }
}

internal object StrReplaceAllDecl :
    SMTTheoryFunction<StringSort>(
        "str.replace".toSymbolWithQuotes(),
        listOf(SMTString, SMTString, SMTString),
        SMTString,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<StringSort> {
    require(args.size == 3) {
      "Three arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is StringSort })

    return StrReplaceAll(
        args[0].castTo(), args[1].castTo(), args[2].castTo())
  }
}

internal object StrReplaceRegexDecl :
    SMTTheoryFunction<StringSort>(
        "str.replace_re".toSymbolWithQuotes(),
        listOf(SMTString, RegLan, SMTString),
        SMTString,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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

    return StrReplaceRegex(
        args[0].castTo(), args[1].castTo(), args[2].castTo())
  }
}

internal object StrReplaceAllRegexDecl :
    SMTTheoryFunction<StringSort>(
        "str.replace_re_all".toSymbolWithQuotes(),
        listOf(SMTString, RegLan, SMTString),
        SMTString,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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

    return StrReplaceAllRegex(
        args[0].castTo(), args[1].castTo(), args[2].castTo())
  }
}

internal object RegexCompDecl :
    SMTTheoryFunction<RegLanSort>(
        "re.comp".toSymbolWithQuotes(), listOf(RegLan), RegLan, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RegLanSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is RegLanSort)

    return RegexComp(args.single().castTo())
  }
}

internal object RegexDiffDecl :
    SMTTheoryFunction<RegLanSort>(
        "re.diff".toSymbolWithQuotes(), listOf(RegLan, RegLan), RegLan, Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
        "re.+".toSymbolWithQuotes(), listOf(RegLan), RegLan, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RegLanSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is RegLanSort)

    return RegexPlus(args.single().castTo())
  }
}

internal object RegexOptionDecl :
    SMTTheoryFunction<RegLanSort>(
        "re.opt".toSymbolWithQuotes(), listOf(RegLan), RegLan, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RegLanSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is RegLanSort)

    return RegexOption(args.single().castTo())
  }
}

internal object RegexRangeDecl :
    SMTTheoryFunction<RegLanSort>(
        "re.range".toSymbolWithQuotes(), listOf(SMTString, SMTString), RegLan, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RegLanSort> {
    require(args.size == 2) {
      "Two arguments expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.all { expr -> expr.sort is StringSort })

    return RegexRange(args[0].castTo(), args[1].castTo())
  }
}

internal object RegexPowerDecl :
    SMTTheoryFunction<RegLanSort>(
        "re.^".toSymbolWithQuotes(), listOf(RegLan), RegLan, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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

    return RegexPower(args[0].castTo(), (indices.single() as NumeralIndex).numeral)
  }
}

internal object RegexLoopDecl :
    SMTTheoryFunction<RegLanSort>(
        "re.loop".toSymbolWithQuotes(), listOf(RegLan), RegLan, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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
        args[0].castTo(),
        (indices[0] as NumeralIndex).numeral,
        (indices[1] as NumeralIndex).numeral)
  }
}

internal object StrIsDigitDecl :
    SMTTheoryFunction<BoolSort>(
        "str.is_digit".toSymbolWithQuotes(), listOf(SMTString), Bool, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is StringSort)

    return StrIsDigit(args.single().castTo())
  }
}

internal object StrToCodeDecl :
    SMTTheoryFunction<IntSort>(
        "str.to_code".toSymbolWithQuotes(), listOf(SMTString), SMTInt, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<IntSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is StringSort)

    return StrToCode(args.single().castTo())
  }
}

internal object StrFromCodeDecl :
    SMTTheoryFunction<StringSort>(
        "str.from_code".toSymbolWithQuotes(), listOf(SMTInt), SMTString, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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

    return StrFromCode(args.single().castTo<IntSort>())
  }
}

internal object StrToIntDecl :
    SMTTheoryFunction<IntSort>(
        "str.to_code".toSymbolWithQuotes(), listOf(SMTString), SMTInt, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<IntSort> {
    require(args.size == 1) {
      "One argument expected for ${this.symbol} but ${args.size} were given:\n${args.joinToString(separator="\n")}"
    }
    require(indices.isEmpty()) {
      "No indices expected for ${this.symbol} but ${indices.size} were given:\n${indices.joinToString(separator="\n")}"
    }
    require(args.single().sort is StringSort)

    return StrToInt(args.single().castTo())
  }
}

internal object StrFromIntDecl :
    SMTTheoryFunction<StringSort>(
        "str.from_code".toSymbolWithQuotes(), listOf(SMTInt), SMTString, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
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

    return StrFromInt(args.single().castTo<IntSort>())
  }
}

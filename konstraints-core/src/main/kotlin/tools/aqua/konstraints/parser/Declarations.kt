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
  override val sorts = mapOf(BoolSort.symbol to BoolFactory)
}

internal object TrueDecl :
    SMTTheoryFunction<BoolSort>(
        "true".toSymbolWithQuotes(), emptyList(), BoolSort, Associativity.NONE) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.isEmpty())
    require(indices.isEmpty())

    return True
  }
}

internal object FalseDecl :
    SMTTheoryFunction<BoolSort>(
        "false".toSymbolWithQuotes(), emptyList(), BoolSort, Associativity.NONE) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.isEmpty())
    require(indices.isEmpty())

    return False
  }
}

/** Not declaration internal object */
internal object NotDecl :
    SMTTheoryFunction<BoolSort>(
        "not".toSymbolWithQuotes(), listOf(BoolSort), BoolSort, Associativity.NONE) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 1)
    require(indices.isEmpty())

    return Not(args.single() castTo BoolSort)
  }
}

/** Implies declaration internal object */
internal object ImpliesDecl :
    SMTTheoryFunction<BoolSort>(
        "=>".toSymbolWithQuotes(), listOf(BoolSort, BoolSort), BoolSort, Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2)
    require(indices.isEmpty())

    return Implies(args.map { it castTo BoolSort })
  }
}

/** And declaration internal object */
internal object AndDecl :
    SMTTheoryFunction<BoolSort>(
        "and".toSymbolWithQuotes(),
        listOf(BoolSort, BoolSort),
        BoolSort,
        Associativity.LEFT_ASSOC) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2)
    require(indices.isEmpty())

    return And(args.map { it castTo BoolSort })
  }
}

/** Or declaration internal object */
internal object OrDecl :
    SMTTheoryFunction<BoolSort>(
        "or".toSymbolWithQuotes(), listOf(BoolSort, BoolSort), BoolSort, Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2)
    require(indices.isEmpty())

    return Or(args.map { it castTo BoolSort })
  }
}

/** Xor declaration internal object */
internal object XOrDecl :
    SMTTheoryFunction<BoolSort>(
        "xor".toSymbolWithQuotes(),
        listOf(BoolSort, BoolSort),
        BoolSort,
        Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2)
    require(indices.isEmpty())

    return XOr(args.map { it castTo BoolSort })
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
    require(args.size >= 2)
    require(indices.isEmpty())
    require(args.all { expr -> expr.sort == args[0].sort }) {
      "Expected all sorts in equals to be of the same sort but was: ${args.map { expr -> expr.sort }.joinToString(", ")}"
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
    require(args.size >= 2)
    require(indices.isEmpty())
    require(args.all { expr -> expr.sort == args[0].sort }) // TODO is this necessary?

    return Distinct(args)
  }
}

/** Ite declaration internal object */
internal object IteDecl :
    SMTTheoryFunction<Sort>(
        "ite".toSymbolWithQuotes(),
        listOf(BoolSort, SortParameter("A"), SortParameter("A")),
        BoolSort,
        Associativity.NONE) {

  override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Ite<*> {
    require(args.size == 3)
    require(indices.isEmpty())

    return Ite(args[0] castTo BoolSort, args[1], args[2])
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
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expression -> expression.sort is BVSort }) {
      "Expected all args to be of sort BitVec but was (${args.map { it.sort }.joinToString(" ")})"
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
    require(args.size == 1)
    require(indices.size == 2)
    require(args.single().sort is BVSort)
    require(indices.all { index -> index is NumeralIndex })

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
    require(args.size == 1)
    require(indices.isEmpty())
    require(args.single().sort is BVSort)

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
    require(args.size == 1)
    require(indices.isEmpty())
    require(args.single().sort is BVSort)

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
    require(args.size >= 2)
    require(indices.isEmpty())
    require(args.all { expression -> expression.sort is BVSort })

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
    require(args.size >= 2)
    require(indices.isEmpty())
    require(args.all { expression -> expression.sort is BVSort })

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
    require(args.size >= 2)
    require(indices.isEmpty())
    require(args.all { expression -> expression.sort is BVSort })

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
    require(args.size >= 2)
    require(indices.isEmpty())
    require(args.all { expression -> expression.sort is BVSort })

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
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expression -> expression.sort is BVSort })

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
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expression -> expression.sort is BVSort })

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
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expression -> expression.sort is BVSort })

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
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expression -> expression.sort is BVSort })

    @Suppress("UNCHECKED_CAST")
    return BVLShr(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object BVUltDecl :
    SMTTheoryFunction<BoolSort>(
        "bvult".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        BoolSort,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expression -> expression.sort is BVSort })

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
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expression -> expression.sort is BVSort })

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
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expression -> expression.sort is BVSort })

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
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expression -> expression.sort is BVSort })

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
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expression -> expression.sort is BVSort })

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
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expression -> expression.sort is BVSort })

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
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expression -> expression.sort is BVSort })

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
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expression -> expression.sort is BVSort })

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
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expression -> expression.sort is BVSort })

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
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expression -> expression.sort is BVSort })

    @Suppress("UNCHECKED_CAST")
    return BVSMod(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object BVULeDecl :
    SMTTheoryFunction<BoolSort>(
        "bvule".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        BoolSort,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expression -> expression.sort is BVSort })

    @Suppress("UNCHECKED_CAST")
    return BVULe(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object BVUGtDecl :
    SMTTheoryFunction<BoolSort>(
        "bvugt".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        BoolSort,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expression -> expression.sort is BVSort })

    @Suppress("UNCHECKED_CAST")
    return BVUGt(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object BVUGeDecl :
    SMTTheoryFunction<BoolSort>(
        "bvuge".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        BoolSort,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expression -> expression.sort is BVSort })

    @Suppress("UNCHECKED_CAST")
    return BVUGe(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object BVSLtDecl :
    SMTTheoryFunction<BoolSort>(
        "bvslt".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        BoolSort,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expression -> expression.sort is BVSort })

    @Suppress("UNCHECKED_CAST")
    return BVSLt(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object BVSLeDecl :
    SMTTheoryFunction<BoolSort>(
        "bvsle".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        BoolSort,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expression -> expression.sort is BVSort })

    @Suppress("UNCHECKED_CAST")
    return BVSLe(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object BVSGtDecl :
    SMTTheoryFunction<BoolSort>(
        "bvsgt".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        BoolSort,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expression -> expression.sort is BVSort })

    @Suppress("UNCHECKED_CAST")
    return BVSGt(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
  }
}

internal object BVSGeDecl :
    SMTTheoryFunction<BoolSort>(
        "bvsge".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m"), BVSort.fromSymbol("m")),
        BoolSort,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expression -> expression.sort is BVSort })

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
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expression -> expression.sort is BVSort })

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
    require(args.size == 1)
    require(indices.size == 1)
    require(args.single().sort is BVSort)
    require(indices.single() is NumeralIndex)

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
    require(args.size == 1)
    require(indices.size == 1)
    require(args.single().sort is BVSort)
    require(indices.single() is NumeralIndex)

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
    require(args.size == 1)
    require(indices.size == 1)
    require(args.single().sort is BVSort)
    require(indices.single() is NumeralIndex)

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
    require(args.size == 1)
    require(indices.size == 1)
    require(args.single().sort is BVSort)
    require(indices.single() is NumeralIndex)

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
    require(args.size == 1)
    require(indices.size == 1)
    require(args.single().sort is BVSort)
    require(indices.single() is NumeralIndex)

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

  override val sorts = mapOf(IntSort.symbol to IntFactory)
}

internal object IntNegDecl :
    SMTTheoryFunction<IntSort>(
        "-".toSymbolWithQuotes(), listOf(IntSort), IntSort, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<IntSort> {
    require(args.size == 1)
    return IntNeg(args.single() castTo IntSort)
  }
}

internal object IntSubDecl :
    SMTTheoryFunction<IntSort>(
        "-".toSymbolWithQuotes(), listOf(IntSort, IntSort), IntSort, Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<IntSort> {
    require(args.size >= 2)
    return IntSub(args.map { expr -> expr castTo IntSort })
  }
}

/** Combined function declaration for overloaded '-' operator */
internal object IntNegSubDecl :
    SMTTheoryFunction<IntSort>(
        "-".toSymbolWithQuotes(), listOf(IntSort), IntSort, Associativity.NONE) {

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
        "+".toSymbolWithQuotes(), listOf(IntSort, IntSort), IntSort, Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<IntSort> {
    require(args.size >= 2)
    return IntAdd(args.map { expr -> expr castTo IntSort })
  }
}

internal object IntMulDecl :
    SMTTheoryFunction<IntSort>(
        "*".toSymbolWithQuotes(), listOf(IntSort, IntSort), IntSort, Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<IntSort> {
    require(args.size >= 2)
    return IntMul(args.map { expr -> expr castTo IntSort })
  }
}

internal object IntDivDecl :
    SMTTheoryFunction<IntSort>(
        "div".toSymbolWithQuotes(), listOf(IntSort, IntSort), IntSort, Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<IntSort> {
    require(args.size >= 2)
    return IntDiv(args.map { expr -> expr castTo IntSort })
  }
}

internal object ModDecl :
    SMTTheoryFunction<IntSort>(
        "mod".toSymbolWithQuotes(), listOf(IntSort, IntSort), IntSort, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<IntSort> {
    require(args.size == 2)
    return Mod(args[0] castTo IntSort, args[1] castTo IntSort)
  }
}

internal object AbsDecl :
    SMTTheoryFunction<IntSort>(
        "abs".toSymbolWithQuotes(), listOf(IntSort), IntSort, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<IntSort> {
    require(args.size == 1)
    return IntNeg(args.single() castTo IntSort)
  }
}

internal object IntLessEqDecl :
    SMTTheoryFunction<BoolSort>(
        "<=".toSymbolWithQuotes(), listOf(IntSort, IntSort), BoolSort, Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2)
    return IntLessEq(args.map { expr -> expr castTo IntSort })
  }
}

internal object IntLessDecl :
    SMTTheoryFunction<BoolSort>(
        "<".toSymbolWithQuotes(), listOf(IntSort, IntSort), BoolSort, Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2)
    return IntLess(args.map { expr -> expr castTo IntSort })
  }
}

internal object IntGreaterEqDecl :
    SMTTheoryFunction<BoolSort>(
        ">=".toSymbolWithQuotes(), listOf(IntSort, IntSort), BoolSort, Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2)
    return IntGreaterEq(args.map { expr -> expr castTo IntSort })
  }
}

internal object IntGreaterDecl :
    SMTTheoryFunction<BoolSort>(
        ">".toSymbolWithQuotes(), listOf(IntSort, IntSort), BoolSort, Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2)
    return IntGreater(args.map { expr -> expr castTo IntSort })
  }
}

internal object DivisibleDecl :
    SMTTheoryFunction<BoolSort>(
        "divisible".toSymbolWithQuotes(), listOf(IntSort), BoolSort, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 1)
    require(indices.size == 1)
    require(args.single().sort is IntSort)
    require(indices.single() is NumeralIndex)

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

  override val sorts = mapOf(RealSort.symbol to RealFactory)
}

internal object RealNegDecl :
    SMTTheoryFunction<RealSort>(
        "-".toSymbolWithQuotes(), listOf(RealSort), RealSort, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RealSort> {
    require(args.size == 1)
    return RealNeg(args.single() castTo RealSort)
  }
}

internal object RealSubDecl :
    SMTTheoryFunction<RealSort>(
        "-".toSymbolWithQuotes(), listOf(RealSort), RealSort, Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RealSort> {
    require(args.size >= 2)
    return RealSub(args.map { expr -> expr castTo RealSort })
  }
}

/** Combined function declaration for overloaded '-' operator */
internal object RealNegSubDecl :
    SMTTheoryFunction<RealSort>(
        "-".toSymbolWithQuotes(), listOf(RealSort), RealSort, Associativity.NONE) {

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
        "+".toSymbolWithQuotes(), listOf(RealSort, RealSort), RealSort, Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RealSort> {
    require(args.size >= 2)
    return RealAdd(args.map { expr -> expr castTo RealSort })
  }
}

internal object RealMulDecl :
    SMTTheoryFunction<RealSort>(
        "*".toSymbolWithQuotes(), listOf(RealSort, RealSort), RealSort, Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RealSort> {
    require(args.size >= 2)
    return RealMul(args.map { expr -> expr castTo RealSort })
  }
}

internal object RealDivDecl :
    SMTTheoryFunction<RealSort>(
        "/".toSymbolWithQuotes(), listOf(RealSort, RealSort), RealSort, Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RealSort> {
    require(args.size >= 2)
    return RealDiv(args.map { expr -> expr castTo RealSort })
  }
}

internal object RealLessEqDecl :
    SMTTheoryFunction<BoolSort>(
        "<=".toSymbolWithQuotes(), listOf(RealSort, RealSort), BoolSort, Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2)
    return RealLessEq(args.map { expr -> expr castTo RealSort })
  }
}

internal object RealLessDecl :
    SMTTheoryFunction<BoolSort>(
        "<".toSymbolWithQuotes(), listOf(RealSort, RealSort), BoolSort, Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2)
    return RealLess(args.map { expr -> expr castTo RealSort })
  }
}

internal object RealGreaterEqDecl :
    SMTTheoryFunction<BoolSort>(
        ">=".toSymbolWithQuotes(), listOf(RealSort, RealSort), BoolSort, Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2)
    return RealGreaterEq(args.map { expr -> expr castTo RealSort })
  }
}

internal object RealGreaterDecl :
    SMTTheoryFunction<BoolSort>(
        ">".toSymbolWithQuotes(), listOf(RealSort, RealSort), BoolSort, Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2)
    return RealGreater(args.map { expr -> expr castTo RealSort })
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

  override val sorts = mapOf(IntSort.symbol to IntFactory, RealSort.symbol to RealFactory)
}

internal object ToRealDecl :
    SMTTheoryFunction<RealSort>(
        "to_real".toSymbolWithQuotes(), listOf(IntSort), RealSort, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RealSort> {
    require(args.size == 1)
    return ToReal(args.single() castTo IntSort)
  }
}

internal object ToIntDecl :
    SMTTheoryFunction<IntSort>(
        "to_real".toSymbolWithQuotes(), listOf(RealSort), IntSort, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<IntSort> {
    require(args.size == 1)
    return ToInt(args.single() castTo RealSort)
  }
}

internal object IsIntDecl :
    SMTTheoryFunction<BoolSort>(
        "to_real".toSymbolWithQuotes(), listOf(RealSort), BoolSort, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 1)
    return IsInt(args.single() castTo RealSort)
  }
}

internal object IntRealLessDecl :
    SMTTheoryFunction<BoolSort>(
        "<".toSymbolWithQuotes(), listOf(RealSort, RealSort), BoolSort, Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2)

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
        "<=".toSymbolWithQuotes(), listOf(RealSort, RealSort), BoolSort, Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2)

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
        ">=".toSymbolWithQuotes(), listOf(RealSort, RealSort), BoolSort, Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2)

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
        ">".toSymbolWithQuotes(), listOf(RealSort, RealSort), BoolSort, Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2)

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
          RealSort.symbol to RealFactory,
          // FP16.symbol,
          // FP32.symbol,
          // FP64.symbol,
          // FP128.symbol,
          "BitVec".toSymbolWithQuotes() to BitVecFactory,
          "FloatingPoint".toSymbolWithQuotes() to FloatingPointFactory,
          "Float16".toSymbolWithQuotes() to Float16Factory,
          "Float32".toSymbolWithQuotes() to Float32Factory,
          "Float64".toSymbolWithQuotes() to Float64Factory,
          "Float128".toSymbolWithQuotes() to Float128Factory)
}

internal object RoundNearestTiesToEvenDecl :
    SMTTheoryFunction<RoundingMode>(
        "roundNearestTiesToEven".toSymbolWithQuotes(),
        emptyList(),
        RoundingMode,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RoundingMode> {
    require(args.isEmpty())
    return RoundNearestTiesToEven
  }
}

internal object RNEDecl :
    SMTTheoryFunction<RoundingMode>(
        "RNE".toSymbolWithQuotes(), emptyList(), RoundingMode, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RoundingMode> {
    require(args.isEmpty())
    return RNE
  }
}

internal object RoundNearestTiesToAwayDecl :
    SMTTheoryFunction<RoundingMode>(
        "roundNearestTiesToAway".toSymbolWithQuotes(),
        emptyList(),
        RoundingMode,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RoundingMode> {
    require(args.isEmpty())
    return RoundNearestTiesToAway
  }
}

internal object RNADecl :
    SMTTheoryFunction<RoundingMode>(
        "RNA".toSymbolWithQuotes(), emptyList(), RoundingMode, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RoundingMode> {
    require(args.isEmpty())
    return RNA
  }
}

internal object RoundTowardPositiveDecl :
    SMTTheoryFunction<RoundingMode>(
        "roundTowardPositive".toSymbolWithQuotes(), emptyList(), RoundingMode, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RoundingMode> {
    require(args.isEmpty())
    return RoundTowardPositive
  }
}

internal object RTPDecl :
    SMTTheoryFunction<RoundingMode>(
        "RTP".toSymbolWithQuotes(), emptyList(), RoundingMode, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RoundingMode> {
    require(args.isEmpty())
    return RTP
  }
}

internal object RoundTowardNegativeDecl :
    SMTTheoryFunction<RoundingMode>(
        "roundTowardNegative".toSymbolWithQuotes(), emptyList(), RoundingMode, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RoundingMode> {
    require(args.isEmpty())
    return RoundTowardNegative
  }
}

internal object RTNDecl :
    SMTTheoryFunction<RoundingMode>(
        "RTN".toSymbolWithQuotes(), emptyList(), RoundingMode, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RoundingMode> {
    require(args.isEmpty())
    return RTN
  }
}

internal object RoundTowardZeroDecl :
    SMTTheoryFunction<RoundingMode>(
        "roundTowardZero".toSymbolWithQuotes(), emptyList(), RoundingMode, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RoundingMode> {
    require(args.isEmpty())
    return RoundTowardZero
  }
}

internal object RTZDecl :
    SMTTheoryFunction<RoundingMode>(
        "RTZ".toSymbolWithQuotes(), emptyList(), RoundingMode, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RoundingMode> {
    require(args.isEmpty())
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
    require(args.size == 3)
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
    require(args.isEmpty())
    require(indices.size == 2)
    require(indices.all { index -> index is NumeralIndex })

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
    require(args.isEmpty())
    require(indices.size == 2)
    require(indices.all { index -> index is NumeralIndex })

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
    require(args.isEmpty())
    require(indices.size == 2)
    require(indices.all { index -> index is NumeralIndex })

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
    require(args.isEmpty())
    require(indices.size == 2)
    require(indices.all { index -> index is NumeralIndex })

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
    require(args.isEmpty())
    require(indices.size == 2)
    require(indices.all { index -> index is NumeralIndex })

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
    require(args.size == 1)
    require(indices.isEmpty())
    require(args.single().sort is FPSort)

    @Suppress("UNCHECKED_CAST")
    return FPAbs(args.single() as Expression<FPSort>)
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
    require(args.size == 1)
    require(indices.isEmpty())
    require(args.single().sort is FPSort)

    @Suppress("UNCHECKED_CAST")
    return FPNeg(args.single() as Expression<FPSort>)
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
    require(args.size == 3)
    require(indices.isEmpty())
    require(args[0].sort is RoundingMode)
    require(args[1].sort is FPSort)
    require(args[2].sort is FPSort)

    @Suppress("UNCHECKED_CAST")
    return FPAdd(
        args[0] castTo RoundingMode, args[1] as Expression<FPSort>, args[2] as Expression<FPSort>)
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
    require(args.size == 3)
    require(indices.isEmpty())
    require(args[0].sort is RoundingMode)
    require(args[1].sort is FPSort)
    require(args[2].sort is FPSort)

    @Suppress("UNCHECKED_CAST")
    return FPSub(
        args[0] castTo RoundingMode, args[1] as Expression<FPSort>, args[2] as Expression<FPSort>)
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
    require(args.size == 3)
    require(indices.isEmpty())
    require(args[0].sort is RoundingMode)
    require(args[1].sort is FPSort)
    require(args[2].sort is FPSort)

    @Suppress("UNCHECKED_CAST")
    return FPMul(
        args[0] castTo RoundingMode, args[1] as Expression<FPSort>, args[2] as Expression<FPSort>)
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
    require(args.size == 3)
    require(indices.isEmpty())
    require(args[0].sort is RoundingMode)
    require(args[1].sort is FPSort)
    require(args[2].sort is FPSort)

    @Suppress("UNCHECKED_CAST")
    return FPDiv(
        args[0] castTo RoundingMode, args[1] as Expression<FPSort>, args[2] as Expression<FPSort>)
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
    require(args.size == 4)
    require(indices.isEmpty())
    require(args[0].sort is RoundingMode)
    require(args[1].sort is FPSort)
    require(args[2].sort is FPSort)
    require(args[3].sort is FPSort)

    @Suppress("UNCHECKED_CAST")
    return FPFma(
        args[0] castTo RoundingMode,
        args[1] as Expression<FPSort>,
        args[2] as Expression<FPSort>,
        args[3] as Expression<FPSort>)
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
    require(args.size == 2)
    require(indices.isEmpty())
    require(args[0].sort is RoundingMode)
    require(args[1].sort is FPSort)

    @Suppress("UNCHECKED_CAST")
    return FPSqrt(args[0] castTo RoundingMode, args[1] as Expression<FPSort>)
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
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expr -> expr.sort is FPSort })

    @Suppress("UNCHECKED_CAST")
    return FPRem(args[0] as Expression<FPSort>, args[1] as Expression<FPSort>)
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
    require(args.size == 2)
    require(indices.isEmpty())
    require(args[0].sort is RoundingMode)
    require(args[1].sort is FPSort)

    @Suppress("UNCHECKED_CAST")
    return FPRoundToIntegral(args[0] castTo RoundingMode, args[1] as Expression<FPSort>)
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
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expr -> expr.sort is FPSort })

    @Suppress("UNCHECKED_CAST")
    return FPMin(args[0] as Expression<FPSort>, args[1] as Expression<FPSort>)
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
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expr -> expr.sort is FPSort })

    @Suppress("UNCHECKED_CAST")
    return FPMax(args[0] as Expression<FPSort>, args[1] as Expression<FPSort>)
  }
}

internal object FPLeqDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.leq".toSymbolWithQuotes(),
        listOf(FPSort("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())),
        BoolSort,
        Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2)
    require(indices.isEmpty())
    require(args.all { expr -> expr.sort is FPSort })

    @Suppress("UNCHECKED_CAST")
    return FPLeq(args as List<Expression<FPSort>>)
  }
}

internal object FPLtDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.lt".toSymbolWithQuotes(),
        listOf(FPSort("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())),
        BoolSort,
        Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2)
    require(indices.isEmpty())
    require(args.all { expr -> expr.sort is FPSort })

    @Suppress("UNCHECKED_CAST")
    return FPLt(args as List<Expression<FPSort>>)
  }
}

internal object FPGeqDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.geq".toSymbolWithQuotes(),
        listOf(FPSort("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())),
        BoolSort,
        Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2)
    require(indices.isEmpty())
    require(args.all { expr -> expr.sort is FPSort })

    @Suppress("UNCHECKED_CAST")
    return FPGeq(args as List<Expression<FPSort>>)
  }
}

internal object FPGtDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.gt".toSymbolWithQuotes(),
        listOf(FPSort("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())),
        BoolSort,
        Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2)
    require(indices.isEmpty())
    require(args.all { expr -> expr.sort is FPSort })

    @Suppress("UNCHECKED_CAST")
    return FPGt(args as List<Expression<FPSort>>)
  }
}

internal object FPEqDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.eq".toSymbolWithQuotes(),
        listOf(FPSort("eb".idx(), "sb".idx()), FPSort("eb".idx(), "sb".idx())),
        BoolSort,
        Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2)
    require(indices.isEmpty())
    require(args.all { expr -> expr.sort is FPSort })

    @Suppress("UNCHECKED_CAST")
    return FPEq(args as List<Expression<FPSort>>)
  }
}

internal object FPIsNormalDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.isNormal".toSymbolWithQuotes(),
        listOf(FPSort("eb".idx(), "sb".idx())),
        BoolSort,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 1)
    require(indices.isEmpty())
    require(args.single().sort is FPSort)

    @Suppress("UNCHECKED_CAST")
    return FPIsNormal(args.single() as Expression<FPSort>)
  }
}

internal object FPIsSubormalDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.isSubnormal".toSymbolWithQuotes(),
        listOf(FPSort("eb".idx(), "sb".idx())),
        BoolSort,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 1)
    require(indices.isEmpty())
    require(args.single().sort is FPSort)

    @Suppress("UNCHECKED_CAST")
    return FPIsSubnormal(args.single() as Expression<FPSort>)
  }
}

internal object FPIsZeroDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.isZero".toSymbolWithQuotes(),
        listOf(FPSort("eb".idx(), "sb".idx())),
        BoolSort,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 1)
    require(indices.isEmpty())
    require(args.single().sort is FPSort)

    @Suppress("UNCHECKED_CAST")
    return FPIsZero(args.single() as Expression<FPSort>)
  }
}

internal object FPIsInfiniteDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.isInfinite".toSymbolWithQuotes(),
        listOf(FPSort("eb".idx(), "sb".idx())),
        BoolSort,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 1)
    require(indices.isEmpty())
    require(args.single().sort is FPSort)

    @Suppress("UNCHECKED_CAST")
    return FPIsInfinite(args.single() as Expression<FPSort>)
  }
}

internal object FPIsNaNDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.isNaN".toSymbolWithQuotes(),
        listOf(FPSort("eb".idx(), "sb".idx())),
        BoolSort,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 1)
    require(indices.isEmpty())
    require(args.single().sort is FPSort)

    @Suppress("UNCHECKED_CAST")
    return FPIsNaN(args.single() as Expression<FPSort>)
  }
}

internal object FPIsNegativeDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.isNegative".toSymbolWithQuotes(),
        listOf(FPSort("eb".idx(), "sb".idx())),
        BoolSort,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 1)
    require(indices.isEmpty())
    require(args.single().sort is FPSort)

    @Suppress("UNCHECKED_CAST")
    return FPIsNegative(args.single() as Expression<FPSort>)
  }
}

internal object FPIsPositiveDecl :
    SMTTheoryFunction<BoolSort>(
        "fp.isPositive".toSymbolWithQuotes(),
        listOf(FPSort("eb".idx(), "sb".idx())),
        BoolSort,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 1)
    require(indices.isEmpty())
    require(args.single().sort is FPSort)

    @Suppress("UNCHECKED_CAST")
    return FPIsPositive(args.single() as Expression<FPSort>)
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
    require(indices.size == 2)

    // can only be bitvec version
    return if (args.size == 1) {
      BitVecToFPDecl.constructDynamic(args, indices)
    } else if (args.size == 2) {
      require(args[0].sort is RoundingMode)

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
    require(args.size == 1)
    require(indices.size == 2)
    require(args.single().sort is BVSort)
    require(indices.all { index -> index is NumeralIndex })

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
    require(args.size == 2)
    require(indices.size == 2)
    require(args[0].sort is RoundingMode)
    require(args[1].sort is FPSort)
    require(indices.all { index -> index is NumeralIndex })

    @Suppress("UNCHECKED_CAST")
    return FPToFP(
        args[0] castTo RoundingMode,
        args[1] as Expression<FPSort>,
        (indices[0] as NumeralIndex).numeral,
        (indices[1] as NumeralIndex).numeral)
  }
}

internal object RealToFPDecl :
    SMTTheoryFunction<FPSort>(
        "to_fp".toSymbolWithQuotes(),
        listOf(RoundingMode, RealSort),
        FPSort("eb".idx(), "sb".idx()),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<FPSort> {
    require(args.size == 2)
    require(indices.size == 2)
    require(args[0].sort is RoundingMode)
    require(args[1].sort is RealSort)
    require(indices.all { index -> index is NumeralIndex })

    @Suppress("UNCHECKED_CAST")
    return RealToFP(
        args[0] castTo RoundingMode,
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
    require(args.size == 2)
    require(indices.size == 2)
    require(args[0].sort is RoundingMode)
    require(args[1].sort is BVSort)
    require(indices.all { index -> index is NumeralIndex })

    @Suppress("UNCHECKED_CAST")
    return SBitVecToFP(
        args[0] castTo RoundingMode,
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
    require(args.size == 2)
    require(indices.size == 2)
    require(args[0].sort is RoundingMode)
    require(args[1].sort is BVSort)
    require(indices.all { index -> index is NumeralIndex })

    @Suppress("UNCHECKED_CAST")
    return UBitVecToFP(
        args[0] castTo RoundingMode,
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
    require(args.size == 2)
    require(indices.size == 1)
    require(args[0].sort is RoundingMode)
    require(args[1].sort is FPSort)
    require(indices.single() is NumeralIndex)

    @Suppress("UNCHECKED_CAST")
    return FPToUBitVec(
        args[0] castTo RoundingMode,
        args[1] as Expression<FPSort>,
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
    require(args.size == 2)
    require(indices.size == 1)
    require(args[0].sort is RoundingMode)
    require(args[1].sort is FPSort)
    require(indices.single() is NumeralIndex)

    @Suppress("UNCHECKED_CAST")
    return FPToSBitVec(
        args[0] castTo RoundingMode,
        args[1] as Expression<FPSort>,
        (indices.single() as NumeralIndex).numeral)
  }
}

internal object FPToRealDecl :
    SMTTheoryFunction<RealSort>(
        "fp.to_real".toSymbolWithQuotes(),
        listOf(
            FPSort("eb".idx(), "sb".idx()),
        ),
        RealSort,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RealSort> {
    require(args.size == 1)
    require(indices.isEmpty())
    require(args.single().sort is FPSort)

    @Suppress("UNCHECKED_CAST")
    return FPToReal(args.single() as Expression<FPSort>)
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
        listOf(ArraySort(SortParameter("X"), SortParameter("Y"))),
        SortParameter("Y"),
        Associativity.NONE) {

  // TODO can this be improved (maybe make this generic)?
  override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<Sort> {
    require(args.size == 2)
    require(indices.isEmpty())
    require(args[0].sort is ArraySort<*, *>)
    require(args[1].sort == (args[0].sort as ArraySort<*, *>).x)

    @Suppress("UNCHECKED_CAST")
    return ArraySelect(
        args[0] as Expression<ArraySort<Sort, Sort>>,
        args[1] castTo (args[0].sort as ArraySort<*, *>).x)
  }
}

/** Array store declaration internal object */
internal object ArrayStoreDecl :
    SMTTheoryFunction<ArraySort<Sort, Sort>>(
        "store".toSymbolWithQuotes(),
        listOf(ArraySort(SortParameter("X"), SortParameter("Y"))),
        ArraySort(SortParameter("X"), SortParameter("Y")),
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<ArraySort<Sort, Sort>> {
    require(args.size == 3)
    require(indices.isEmpty())
    require(args[0].sort is ArraySort<*, *>)

    // TODO these can probably be removed (castTo) checks the same requirement
    require(args[1].sort == (args[0].sort as ArraySort<*, *>).x)
    require(args[2].sort == (args[0].sort as ArraySort<*, *>).y)

    @Suppress("UNCHECKED_CAST")
    return ArrayStore(
        args[0] as Expression<ArraySort<Sort, Sort>>,
        args[1] castTo (args[0].sort as ArraySort<*, *>).x,
        args[2] castTo (args[0].sort as ArraySort<*, *>).y)
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
          StringSort.symbol to StringFactory,
          RegLan.symbol to RegLanFactory,
          IntSort.symbol to IntFactory)
}

internal object CharDecl :
    SMTTheoryFunction<StringSort>(
        "char".toSymbolWithQuotes(), emptyList(), StringSort, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<StringSort> {
    require(args.isEmpty())
    require(indices.size == 1)
    require(indices.single() is NumeralIndex)

    return TODO("SMT-Lib char not implemented yet!")
  }
}

internal object StrConcatDecl :
    SMTTheoryFunction<StringSort>(
        "str.++".toSymbolWithQuotes(),
        listOf(StringSort, StringSort),
        StringSort,
        Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<StringSort> {
    require(args.size >= 2)
    require(indices.isEmpty())
    require(args.all { expr -> expr.sort is StringSort })

    @Suppress("UNCHECKED_CAST")
    return StrConcat(args as List<Expression<StringSort>>)
  }
}

internal object StrLengthDecl :
    SMTTheoryFunction<IntSort>(
        "str.len".toSymbolWithQuotes(), listOf(StringSort), IntSort, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<IntSort> {
    require(args.size == 1)
    require(indices.isEmpty())
    require(args.single().sort is StringSort)

    return StrLength(args.single() castTo StringSort)
  }
}

internal object StrLexOrderDecl :
    SMTTheoryFunction<BoolSort>(
        "str.<".toSymbolWithQuotes(),
        listOf(StringSort, StringSort),
        BoolSort,
        Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2)
    require(indices.isEmpty())
    require(args.all { expr -> expr.sort is StringSort })

    @Suppress("UNCHECKED_CAST")
    return StrLexOrder(args as List<Expression<StringSort>>)
  }
}

internal object ToRegexDecl :
    SMTTheoryFunction<RegLan>(
        "str.to_reg".toSymbolWithQuotes(), listOf(StringSort), RegLan, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RegLan> {
    require(args.size == 1)
    require(indices.isEmpty())
    require(args.single().sort is StringSort)

    return ToRegex(args.single() castTo StringSort)
  }
}

internal object InRegexDecl :
    SMTTheoryFunction<BoolSort>(
        "str.in_reg".toSymbolWithQuotes(),
        listOf(StringSort, RegLan),
        BoolSort,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 2)
    require(indices.isEmpty())
    require(args[0].sort is StringSort)
    require(args[1].sort is RegLan)

    return InRegex(args[0] castTo StringSort, args[1] castTo RegLan)
  }
}

internal object RegexNoneDecl :
    SMTTheoryFunction<RegLan>(
        "re.none".toSymbolWithQuotes(), emptyList(), RegLan, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RegLan> {
    require(args.isEmpty())
    require(indices.isEmpty())

    return RegexNone
  }
}

internal object RegexAllDecl :
    SMTTheoryFunction<RegLan>(
        "re.all".toSymbolWithQuotes(), emptyList(), RegLan, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RegLan> {
    require(args.isEmpty())
    require(indices.isEmpty())

    return RegexAll
  }
}

internal object RegexAllCharDecl :
    SMTTheoryFunction<RegLan>(
        "re.allchar".toSymbolWithQuotes(), emptyList(), RegLan, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RegLan> {
    require(args.isEmpty())
    require(indices.isEmpty())

    return RegexAllChar
  }
}

internal object RegexConcatDecl :
    SMTTheoryFunction<RegLan>(
        "re.++".toSymbolWithQuotes(), listOf(RegLan, RegLan), RegLan, Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RegLan> {
    require(args.size >= 2)
    require(indices.isEmpty())
    require(args.all { expr -> expr.sort is RegLan })

    @Suppress("UNCHECKED_CAST")
    return RegexConcat(args as List<Expression<RegLan>>)
  }
}

internal object RegexUnionDecl :
    SMTTheoryFunction<RegLan>(
        "re.union".toSymbolWithQuotes(), listOf(RegLan, RegLan), RegLan, Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RegLan> {
    require(args.size >= 2)
    require(indices.isEmpty())
    require(args.all { expr -> expr.sort is RegLan })

    @Suppress("UNCHECKED_CAST")
    return RegexUnion(args as List<Expression<RegLan>>)
  }
}

internal object RegexIntersecDecl :
    SMTTheoryFunction<RegLan>(
        "re.inter".toSymbolWithQuotes(), listOf(RegLan, RegLan), RegLan, Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RegLan> {
    require(args.size >= 2)
    require(indices.isEmpty())
    require(args.all { expr -> expr.sort is RegLan })

    @Suppress("UNCHECKED_CAST")
    return RegexIntersec(args as List<Expression<RegLan>>)
  }
}

internal object RegexStarDecl :
    SMTTheoryFunction<RegLan>(
        "re.*".toSymbolWithQuotes(), listOf(RegLan), RegLan, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RegLan> {
    require(args.size == 1)
    require(indices.isEmpty())
    require(args.single().sort is RegLan)

    @Suppress("UNCHECKED_CAST")
    return RegexStar(args.single() castTo RegLan)
  }
}

internal object StrRefLexOrderDecl :
    SMTTheoryFunction<BoolSort>(
        "str.<=".toSymbolWithQuotes(),
        listOf(StringSort, StringSort),
        BoolSort,
        Associativity.CHAINABLE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size >= 2)
    require(indices.isEmpty())
    require(args.all { expr -> expr.sort is StringSort })

    @Suppress("UNCHECKED_CAST")
    return StrRefLexOrder(args as List<Expression<StringSort>>)
  }
}

internal object StrAtDecl :
    SMTTheoryFunction<StringSort>(
        "str.at".toSymbolWithQuotes(),
        listOf(StringSort, IntSort),
        StringSort,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<StringSort> {
    require(args.size == 2)
    require(indices.isEmpty())
    require(args[0].sort is StringSort)
    require(args[1].sort is IntSort)

    return StrAt(args[0] castTo StringSort, args[1] castTo IntSort)
  }
}

internal object StrSubstringDecl :
    SMTTheoryFunction<StringSort>(
        "str.substr".toSymbolWithQuotes(),
        listOf(StringSort, IntSort, IntSort),
        StringSort,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<StringSort> {
    require(args.size == 3)
    require(indices.isEmpty())
    require(args[0].sort is StringSort)
    require(args[1].sort is IntSort)
    require(args[2].sort is IntSort)

    return StrSubstring(args[0] castTo StringSort, args[1] castTo IntSort, args[2] castTo IntSort)
  }
}

internal object StrPrefixOfDecl :
    SMTTheoryFunction<BoolSort>(
        "str.prefixof".toSymbolWithQuotes(),
        listOf(StringSort, StringSort),
        BoolSort,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expr -> expr.sort is StringSort })

    return StrPrefixOf(args[0] castTo StringSort, args[1] castTo StringSort)
  }
}

internal object StrSuffixOfDecl :
    SMTTheoryFunction<BoolSort>(
        "str.suffixof".toSymbolWithQuotes(),
        listOf(StringSort, StringSort),
        BoolSort,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expr -> expr.sort is StringSort })

    return StrSuffixOf(args[0] castTo StringSort, args[1] castTo StringSort)
  }
}

internal object StrContainsDecl :
    SMTTheoryFunction<BoolSort>(
        "str.contains".toSymbolWithQuotes(),
        listOf(StringSort, StringSort),
        BoolSort,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expr -> expr.sort is StringSort })

    return StrContains(args[0] castTo StringSort, args[1] castTo StringSort)
  }
}

internal object StrIndexOfDecl :
    SMTTheoryFunction<IntSort>(
        "str.indexof".toSymbolWithQuotes(),
        listOf(StringSort, StringSort, IntSort),
        IntSort,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<IntSort> {
    require(args.size == 3)
    require(indices.isEmpty())
    require(args[0].sort is StringSort)
    require(args[1].sort is StringSort)
    require(args[2].sort is IntSort)

    return StrIndexOf(args[0] castTo StringSort, args[1] castTo StringSort, args[2] castTo IntSort)
  }
}

internal object StrReplaceDecl :
    SMTTheoryFunction<StringSort>(
        "str.replace".toSymbolWithQuotes(),
        listOf(StringSort, StringSort, StringSort),
        StringSort,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<StringSort> {
    require(args.size == 3)
    require(indices.isEmpty())
    require(args.all { expr -> expr.sort is StringSort })

    return StrReplace(
        args[0] castTo StringSort, args[1] castTo StringSort, args[2] castTo StringSort)
  }
}

internal object StrReplaceAllDecl :
    SMTTheoryFunction<StringSort>(
        "str.replace".toSymbolWithQuotes(),
        listOf(StringSort, StringSort, StringSort),
        StringSort,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<StringSort> {
    require(args.size == 3)
    require(indices.isEmpty())
    require(args.all { expr -> expr.sort is StringSort })

    return StrReplaceAll(
        args[0] castTo StringSort, args[1] castTo StringSort, args[2] castTo StringSort)
  }
}

internal object StrReplaceRegexDecl :
    SMTTheoryFunction<StringSort>(
        "str.replace_re".toSymbolWithQuotes(),
        listOf(StringSort, RegLan, StringSort),
        StringSort,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<StringSort> {
    require(args.size == 3)
    require(indices.isEmpty())
    require(args[0].sort is StringSort)
    require(args[1].sort is RegLan)
    require(args[2].sort is StringSort)

    return StrReplaceRegex(
        args[0] castTo StringSort, args[1] castTo RegLan, args[2] castTo StringSort)
  }
}

internal object StrReplaceAllRegexDecl :
    SMTTheoryFunction<StringSort>(
        "str.replace_re_all".toSymbolWithQuotes(),
        listOf(StringSort, RegLan, StringSort),
        StringSort,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<StringSort> {
    require(args.size == 3)
    require(indices.isEmpty())
    require(args[0].sort is StringSort)
    require(args[1].sort is RegLan)
    require(args[2].sort is StringSort)

    return StrReplaceAllRegex(
        args[0] castTo StringSort, args[1] castTo RegLan, args[2] castTo StringSort)
  }
}

internal object RegexCompDecl :
    SMTTheoryFunction<RegLan>(
        "re.comp".toSymbolWithQuotes(), listOf(RegLan), RegLan, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RegLan> {
    require(args.size == 1)
    require(indices.isEmpty())
    require(args.single().sort is RegLan)

    return RegexComp(args.single() castTo RegLan)
  }
}

internal object RegexDiffDecl :
    SMTTheoryFunction<RegLan>(
        "re.diff".toSymbolWithQuotes(), listOf(RegLan, RegLan), RegLan, Associativity.LEFT_ASSOC) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RegLan> {
    require(args.size >= 2)
    require(indices.isEmpty())
    require(args.all { expr -> expr.sort is RegLan })

    @Suppress("UNCHECKED_CAST")
    return RegexDiff(args as List<Expression<RegLan>>)
  }
}

internal object RegexPlusDecl :
    SMTTheoryFunction<RegLan>(
        "re.+".toSymbolWithQuotes(), listOf(RegLan), RegLan, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RegLan> {
    require(args.size == 1)
    require(indices.isEmpty())
    require(args.single().sort is RegLan)

    return RegexPlus(args.single() castTo RegLan)
  }
}

internal object RegexOptionDecl :
    SMTTheoryFunction<RegLan>(
        "re.opt".toSymbolWithQuotes(), listOf(RegLan), RegLan, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RegLan> {
    require(args.size == 1)
    require(indices.isEmpty())
    require(args.single().sort is RegLan)

    return RegexOption(args.single() castTo RegLan)
  }
}

internal object RegexRangeDecl :
    SMTTheoryFunction<RegLan>(
        "re.range".toSymbolWithQuotes(),
        listOf(StringSort, StringSort),
        RegLan,
        Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RegLan> {
    require(args.size == 2)
    require(indices.isEmpty())
    require(args.all { expr -> expr.sort is StringSort })

    return RegexRange(args[0] castTo StringSort, args[1] castTo StringSort)
  }
}

internal object RegexPowerDecl :
    SMTTheoryFunction<RegLan>(
        "re.^".toSymbolWithQuotes(), listOf(RegLan), RegLan, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RegLan> {
    require(args.size == 1)
    require(indices.size == 1)
    require(args.single().sort is RegLan)
    require(indices.single() is NumeralIndex)

    return RegexPower(args[0] castTo RegLan, (indices.single() as NumeralIndex).numeral)
  }
}

internal object RegexLoopDecl :
    SMTTheoryFunction<RegLan>(
        "re.loop".toSymbolWithQuotes(), listOf(RegLan), RegLan, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<RegLan> {
    require(args.size == 1)
    require(indices.size == 2)
    require(args.single().sort is RegLan)
    require(indices.all { index -> index is NumeralIndex })

    return RegexLoop(
        args[0] castTo RegLan,
        (indices[0] as NumeralIndex).numeral,
        (indices[1] as NumeralIndex).numeral)
  }
}

internal object StrIsDigitDecl :
    SMTTheoryFunction<BoolSort>(
        "str.is_digit".toSymbolWithQuotes(), listOf(StringSort), BoolSort, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<BoolSort> {
    require(args.size == 1)
    require(indices.isEmpty())
    require(args.single().sort is StringSort)

    return StrIsDigit(args.single() castTo StringSort)
  }
}

internal object StrToCodeDecl :
    SMTTheoryFunction<IntSort>(
        "str.to_code".toSymbolWithQuotes(), listOf(StringSort), IntSort, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<IntSort> {
    require(args.size == 1)
    require(indices.isEmpty())
    require(args.single().sort is StringSort)

    return StrToCode(args.single() castTo StringSort)
  }
}

internal object StrFromCodeDecl :
    SMTTheoryFunction<StringSort>(
        "str.from_code".toSymbolWithQuotes(), listOf(IntSort), StringSort, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<StringSort> {
    require(args.size == 1)
    require(indices.isEmpty())
    require(args.single().sort is IntSort)

    return StrFromCode(args.single() castTo IntSort)
  }
}

internal object StrToIntDecl :
    SMTTheoryFunction<IntSort>(
        "str.to_code".toSymbolWithQuotes(), listOf(StringSort), IntSort, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<IntSort> {
    require(args.size == 1)
    require(indices.isEmpty())
    require(args.single().sort is StringSort)

    return StrToInt(args.single() castTo StringSort)
  }
}

internal object StrFromIntDecl :
    SMTTheoryFunction<StringSort>(
        "str.from_code".toSymbolWithQuotes(), listOf(IntSort), StringSort, Associativity.NONE) {

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>
  ): Expression<StringSort> {
    require(args.size == 1)
    require(indices.isEmpty())
    require(args.single().sort is IntSort)

    return StrFromInt(args.single() castTo IntSort)
  }
}

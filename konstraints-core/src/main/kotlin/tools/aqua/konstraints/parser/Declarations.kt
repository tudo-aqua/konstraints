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
import tools.aqua.konstraints.theories.*

enum class Associativity {
    LEFT_ASSOC,
    RIGHT_ASSOC,
    PAIRWISE,
    CHAINABLE,
    NONE
}

abstract class SMTTheoryFunction<T : Sort>(override val symbol : Symbol, override val parameters: List<Sort>, override val sort : T, val associativity: Associativity) : SMTFunction<T>()

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
          .associateBy { it.symbol.toString() }
  override val sorts = mapOf(Pair("Bool", BoolSortDecl))
}

/** Declaration internal object for Bool sort */
/*internal*/ object BoolSortDecl :
    SortDecl<BoolSort>("Bool".toSymbolWithQuotes(), emptySet(), emptySet()) {
  override fun getSort(bindings: Bindings): BoolSort = BoolSort
}

internal object TrueDecl :
    SMTTheoryFunction<BoolSort>("true".toSymbolWithQuotes(), emptyList(), BoolSort, Associativity.NONE) {
    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.isEmpty())
        require(indices.isEmpty())

        return True
    }
}

internal object FalseDecl :
    SMTTheoryFunction<BoolSort>("false".toSymbolWithQuotes(), emptyList(), BoolSort, Associativity.NONE) {
    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.isEmpty())
        require(indices.isEmpty())

        return False
    }
}

/** Not declaration internal object */
internal object NotDecl :
    SMTTheoryFunction<BoolSort>(
        "not".toSymbolWithQuotes(), listOf(BoolSort), BoolSort, Associativity.NONE) {
    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size == 1)
        require(indices.isEmpty())

        return Not(args.single() castTo BoolSort)
    }
}

/** Implies declaration internal object */
internal object ImpliesDecl :
    SMTTheoryFunction<BoolSort>(
        "=>".toSymbolWithQuotes(),
        listOf(BoolSort, BoolSort),
        BoolSort, Associativity.CHAINABLE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
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
        BoolSort, Associativity.LEFT_ASSOC) {
    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size >= 2)
        require(indices.isEmpty())

        return And(args.map { it castTo BoolSort })
    }
}

/** Or declaration internal object */
internal object OrDecl :
    SMTTheoryFunction<BoolSort>(
        "or".toSymbolWithQuotes(),
        listOf(BoolSort, BoolSort),
        BoolSort, Associativity.LEFT_ASSOC) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
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
        BoolSort, Associativity.LEFT_ASSOC) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
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
        SortParameter("A"), Associativity.CHAINABLE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size >= 2)
        require(indices.isEmpty())
        require(args.all { expr -> expr.sort == args[0].sort })

        return Equals(args)
    }
}

/** Distinct declaration internal object */
internal object DistinctDecl :
    SMTTheoryFunction<Sort>(
        "distinct".toSymbolWithQuotes(),
        listOf(SortParameter("A"), SortParameter("A")),
        SortParameter("A"), Associativity.PAIRWISE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
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
        BoolSort, Associativity.NONE) {

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
          .associateBy { it.symbol.toString() }
  override val sorts = mapOf(Pair("BitVec", BVSortDecl))
}

/**
 * BitVec sort declaration
 *
 * (_ BitVec m)
 */
internal object BVSortDecl :
    SortDecl<BVSort>("BitVec".toSymbolWithQuotes(), emptySet(), setOf("m".idx())) {
  override fun getSort(bindings: Bindings): BVSort = BVSort(bindings["m"].numeral)
}

internal object BVConcatDecl :
    SMTTheoryFunction<BVSort>(
        "concat".toSymbolWithQuotes(),
        listOf(
        BVSort.fromSymbol("i"),
        BVSort.fromSymbol("j")),
        BVSort.fromSymbol("m"), Associativity.NONE
    ) {
    @Suppress("UNCHECKED_CAST")
    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expression -> expression.sort is BVSort })

        return BVConcat(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
    }
}

internal object ExtractDecl :
    SMTTheoryFunction<BVSort>(
        "extract".toSymbolWithQuotes(),
        listOf(
        BVSort.fromSymbol("m")),
        BVSort.fromSymbol("n"), Associativity.NONE
    ) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
        require(args.size == 1)
        require(indices.size == 2)
        require(args.single().sort is BVSort)
        require(indices.all { index -> index is NumeralIndex })

        @Suppress("UNCHECKED_CAST")
        return BVExtract((indices[0] as NumeralIndex).numeral, (indices[1] as NumeralIndex).numeral, args.single() as Expression<BVSort>)
    }
}

internal object BVNotDecl :
    SMTTheoryFunction<BVSort>(
        "bvnot".toSymbolWithQuotes(),
        listOf(BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"), Associativity.NONE
    ) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
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
        listOf(
        BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.NONE
    ) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
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
        listOf(
        BVSort.fromSymbol("m"),
        BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.LEFT_ASSOC
    ) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
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
        listOf(
            BVSort.fromSymbol("m"),
            BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.LEFT_ASSOC) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
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
        listOf(
            BVSort.fromSymbol("m"),
            BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.LEFT_ASSOC) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
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
        listOf(
            BVSort.fromSymbol("m"),
            BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.LEFT_ASSOC) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
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
        listOf(
            BVSort.fromSymbol("m"),
            BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
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
        listOf(
            BVSort.fromSymbol("m"),
            BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
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
        listOf(
            BVSort.fromSymbol("m"),
            BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
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
        listOf(
            BVSort.fromSymbol("m"),
            BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
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
        listOf(
            BVSort.fromSymbol("m"),
            BVSort.fromSymbol("m")),
        BoolSort,
        Associativity.NONE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
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
        listOf(
            BVSort.fromSymbol("m"),
            BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
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
        listOf(
            BVSort.fromSymbol("m"),
            BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
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
        listOf(
            BVSort.fromSymbol("m"),
            BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.LEFT_ASSOC) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
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
        listOf(
            BVSort.fromSymbol("m"),
            BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
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
        listOf(
            BVSort.fromSymbol("m"),
            BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
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
        listOf(
            BVSort.fromSymbol("m"),
            BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
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
        listOf(
            BVSort.fromSymbol("m"),
            BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
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
        listOf(
            BVSort.fromSymbol("m"),
            BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
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
        listOf(
            BVSort.fromSymbol("m"),
            BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
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
        listOf(
            BVSort.fromSymbol("m"),
            BVSort.fromSymbol("m")),
        BoolSort,
        Associativity.NONE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
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
        listOf(
            BVSort.fromSymbol("m"),
            BVSort.fromSymbol("m")),
        BoolSort,
        Associativity.NONE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
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
        listOf(
            BVSort.fromSymbol("m"),
            BVSort.fromSymbol("m")),
        BoolSort,
        Associativity.NONE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
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
        listOf(
            BVSort.fromSymbol("m"),
            BVSort.fromSymbol("m")),
        BoolSort,
        Associativity.NONE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
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
        listOf(
            BVSort.fromSymbol("m"),
            BVSort.fromSymbol("m")),
        BoolSort,
        Associativity.NONE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
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
        listOf(
            BVSort.fromSymbol("m"),
            BVSort.fromSymbol("m")),
        BoolSort,
        Associativity.NONE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
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
        listOf(
            BVSort.fromSymbol("m"),
            BVSort.fromSymbol("m")),
        BoolSort,
        Associativity.NONE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
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
        listOf(
            BVSort.fromSymbol("m"),
            BVSort.fromSymbol("m")),
        BVSort.fromSymbol("m"),
        Associativity.NONE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
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
        listOf(
        BVSort.fromSymbol("m")),
        BVSort.fromSymbol("n"),
        Associativity.NONE
    ) {
    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
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
        listOf(
        BVSort.fromSymbol("m")),
        BVSort.fromSymbol("n"),
        Associativity.NONE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
        require(args.size == 1)
        require(indices.size == 1)
        require(args.single().sort is BVSort)
        require(indices.single() is NumeralIndex)

        @Suppress("UNCHECKED_CAST")
        return ZeroExtend((indices.single() as NumeralIndex).numeral, args.single() as Expression<BVSort>)
    }
}

internal object SignExtendDecl :
    SMTTheoryFunction<BVSort>(
        "sign_extend".toSymbolWithQuotes(),
        listOf(
        BVSort.fromSymbol("m")),
        BVSort.fromSymbol("n"),
        Associativity.NONE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
        require(args.size == 1)
        require(indices.size == 1)
        require(args.single().sort is BVSort)
        require(indices.single() is NumeralIndex)

        @Suppress("UNCHECKED_CAST")
        return SignExtend((indices.single() as NumeralIndex).numeral, args.single() as Expression<BVSort>)
    }
}

internal object RotateLeftDecl :
    SMTTheoryFunction<BVSort>(
        "rotate_left".toSymbolWithQuotes(),
        listOf(
        BVSort.fromSymbol("m")),
        BVSort.fromSymbol("n"),
        Associativity.NONE
    ) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
        require(args.size == 1)
        require(indices.size == 1)
        require(args.single().sort is BVSort)
        require(indices.single() is NumeralIndex)

        @Suppress("UNCHECKED_CAST")
        return RotateLeft((indices.single() as NumeralIndex).numeral, args.single() as Expression<BVSort>)
    }
}

internal object RotateRightDecl :
    SMTTheoryFunction<BVSort>(
        "rotate_right".toSymbolWithQuotes(),
        listOf(
            BVSort.fromSymbol("m")),
        BVSort.fromSymbol("n"),
        Associativity.NONE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
        require(args.size == 1)
        require(indices.size == 1)
        require(args.single().sort is BVSort)
        require(indices.single() is NumeralIndex)

        @Suppress("UNCHECKED_CAST")
        return RotateRight((indices.single() as NumeralIndex).numeral, args.single() as Expression<BVSort>)
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
          .associateBy { it.symbol.toString() }

  override val sorts: Map<String, SortDecl<*>> = mapOf(Pair("Int", IntSortDecl))
}

internal object IntSortDecl :
    SortDecl<IntSort>("Int".toSymbolWithQuotes(), emptySet(), emptySet()) {
  override fun getSort(bindings: Bindings): IntSort = IntSort
}

internal object IntNegDecl :
    SMTTheoryFunction<IntSort>(
        "-".toSymbolWithQuotes(), listOf(IntSort), IntSort, Associativity.NONE
    ) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<IntSort> {
        require(args.size == 1)
        return IntNeg(args.single() castTo IntSort)
    }
}

internal object IntSubDecl :
    SMTTheoryFunction<IntSort>(
        "-".toSymbolWithQuotes(), listOf( IntSort, IntSort), IntSort, Associativity.LEFT_ASSOC) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<IntSort> {
        require(args.size >= 2)
        return IntSub(args.map { expr -> expr castTo IntSort })
    }
}

/** Combined function declaration for overloaded '-' operator */
internal object IntNegSubDecl :
    SMTTheoryFunction<IntSort>(
        "-".toSymbolWithQuotes(),
        listOf(IntSort),
        IntSort,
        Associativity.NONE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<IntSort> = if(args.size == 1) {
        IntNegDecl.constructDynamic(args, indices)
    } else if(args.size > 1) {
        IntSubDecl.constructDynamic(args, indices)
    } else {
        throw IllegalArgumentException()
    }
}

internal object IntAddDecl :
    SMTTheoryFunction<IntSort>(
        "+".toSymbolWithQuotes(), listOf(IntSort, IntSort), IntSort, Associativity.LEFT_ASSOC
    ) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<IntSort> {
        require(args.size >= 2)
        return IntAdd(args.map { expr -> expr castTo IntSort })
    }
}

internal object IntMulDecl :
    SMTTheoryFunction<IntSort>(
        "*".toSymbolWithQuotes(), listOf(IntSort, IntSort), IntSort, Associativity.LEFT_ASSOC
    ) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<IntSort> {
        require(args.size >= 2)
        return IntMul(args.map { expr -> expr castTo IntSort })
    }
}

internal object IntDivDecl :
    SMTTheoryFunction<IntSort>(
        "div".toSymbolWithQuotes(), listOf(IntSort, IntSort), IntSort, Associativity.LEFT_ASSOC
    ) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<IntSort> {
        require(args.size >= 2)
        return IntDiv(args.map { expr -> expr castTo IntSort })
    }
}

internal object ModDecl :
    SMTTheoryFunction<IntSort>(
        "mod".toSymbolWithQuotes(), listOf(IntSort, IntSort), IntSort, Associativity.NONE
    ) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<IntSort> {
        require(args.size == 2)
        return Mod(args[0] castTo IntSort, args[1] castTo IntSort)
    }
}

internal object AbsDecl :
    SMTTheoryFunction<IntSort>(
        "abs".toSymbolWithQuotes(), listOf(IntSort), IntSort, Associativity.NONE
    ) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<IntSort> {
        require(args.size == 1)
        return IntNeg(args.single() castTo IntSort)
    }
}

internal object IntLessEqDecl :
    SMTTheoryFunction<BoolSort>(
        "<=".toSymbolWithQuotes(), listOf(IntSort, IntSort), BoolSort, Associativity.CHAINABLE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size >= 2)
        return IntLessEq(args.map { expr -> expr castTo IntSort })
    }
}

internal object IntLessDecl :
    SMTTheoryFunction<BoolSort>(
        "<".toSymbolWithQuotes(), listOf(IntSort, IntSort), BoolSort, Associativity.CHAINABLE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size >= 2)
        return IntLess(args.map { expr -> expr castTo IntSort })
    }
}

internal object IntGreaterEqDecl :
    SMTTheoryFunction<BoolSort>(
        ">=".toSymbolWithQuotes(), listOf(IntSort, IntSort), BoolSort, Associativity.CHAINABLE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size >= 2)
        return IntGreaterEq(args.map { expr -> expr castTo IntSort })
    }
}

internal object IntGreaterDecl :
    SMTTheoryFunction<BoolSort>(
        ">".toSymbolWithQuotes(), listOf(IntSort, IntSort), BoolSort, Associativity.CHAINABLE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size >= 2)
        return IntGreater(args.map { expr -> expr castTo IntSort })
    }
}

internal object DivisibleDecl :
    SMTTheoryFunction<BoolSort>(
        "divisible".toSymbolWithQuotes(),
        listOf(
        IntSort),
        BoolSort, Associativity.NONE
    ) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size == 1)
        require(indices.size == 1)
        require(args.single().sort is IntSort)
        require(indices.single() is NumeralIndex)

        @Suppress("UNCHECKED_CAST")
        return Divisible((indices.single() as NumeralIndex).numeral, args.single() as Expression<IntSort>)
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
          .associateBy { it.symbol.toString() }

  override val sorts: Map<String, SortDecl<*>> = mapOf(Pair("Real", RealSortDecl))
}

internal object RealSortDecl :
    SortDecl<RealSort>("Real".toSymbolWithQuotes(), emptySet(), emptySet()) {
  override fun getSort(bindings: Bindings): RealSort = RealSort
}

internal object RealNegDecl :
    SMTTheoryFunction<RealSort>(
        "-".toSymbolWithQuotes(), listOf(RealSort), RealSort, Associativity.NONE
    ) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RealSort> {
        require(args.size == 1)
        return RealNeg(args.single() castTo RealSort)
    }
}

internal object RealSubDecl :
    SMTTheoryFunction<RealSort>(
        "-".toSymbolWithQuotes(),
        listOf(
        RealSort),
        RealSort, Associativity.LEFT_ASSOC
    ) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RealSort> {
        require(args.size >= 2)
        return RealSub(args.map { expr -> expr castTo RealSort })
    }
}

/** Combined function declaration for overloaded '-' operator */
internal object RealNegSubDecl :
    SMTTheoryFunction<RealSort>(
        "-".toSymbolWithQuotes(),
        listOf(RealSort),
        RealSort,
        Associativity.NONE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RealSort> = if(args.size == 1) {
        RealNegDecl.constructDynamic(args, indices)
    } else if(args.size > 1) {
        RealSubDecl.constructDynamic(args, indices)
    } else {
        throw IllegalArgumentException()
    }
}

internal object RealAddDecl :
    SMTTheoryFunction<RealSort>(
        "+".toSymbolWithQuotes(),
        listOf(
        RealSort,
        RealSort),
        RealSort,
        Associativity.LEFT_ASSOC
    ) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RealSort> {
        require(args.size >= 2)
        return RealAdd(args.map { expr -> expr castTo RealSort })
    }
}

internal object RealMulDecl :
    SMTTheoryFunction<RealSort>(
        "*".toSymbolWithQuotes(),
        listOf(
            RealSort,
            RealSort),
        RealSort,
        Associativity.LEFT_ASSOC) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RealSort> {
        require(args.size >= 2)
        return RealMul(args.map { expr -> expr castTo RealSort })
    }
}

internal object RealDivDecl :
    SMTTheoryFunction<RealSort>(
        "/".toSymbolWithQuotes(),
        listOf(
            RealSort,
            RealSort),
        RealSort,
        Associativity.LEFT_ASSOC) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RealSort> {
        require(args.size >= 2)
        return RealDiv(args.map { expr -> expr castTo RealSort })
    }
}

internal object RealLessEqDecl :
    SMTTheoryFunction<BoolSort>(
        "<=".toSymbolWithQuotes(), listOf( RealSort, RealSort), BoolSort, Associativity.CHAINABLE
    ) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size >= 2)
        return RealLessEq(args.map { expr -> expr castTo RealSort })
    }
}

internal object RealLessDecl :
    SMTTheoryFunction<BoolSort>(
        "<".toSymbolWithQuotes(), listOf( RealSort, RealSort), BoolSort, Associativity.CHAINABLE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size >= 2)
        return RealLess(args.map { expr -> expr castTo RealSort })
    }
}

internal object RealGreaterEqDecl :
    SMTTheoryFunction<BoolSort>(
        ">=".toSymbolWithQuotes(),listOf( RealSort, RealSort), BoolSort, Associativity.CHAINABLE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size >= 2)
        return RealGreaterEq(args.map { expr -> expr castTo RealSort })
    }
}

internal object RealGreaterDecl :
    SMTTheoryFunction<BoolSort>(
        ">".toSymbolWithQuotes(),listOf( RealSort, RealSort), BoolSort, Associativity.CHAINABLE) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
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
              IntLessEqDecl,
              IntLessDecl,
              IntGreaterEqDecl,
              IntGreaterDecl,
              DivisibleDecl,
              RealNegSubDecl,
              RealAddDecl,
              RealMulDecl,
              RealDivDecl,
              RealLessEqDecl,
              RealLessDecl,
              RealGreaterEqDecl,
              RealGreaterDecl,
              ToRealDecl,
              ToIntDecl,
              IsIntDecl)
          .associateBy { it.symbol.toString() }

  override val sorts: Map<String, SortDecl<*>> =
      mapOf(Pair("Int", IntSortDecl), Pair("Real", RealSortDecl))
}

internal object ToRealDecl :
    SMTTheoryFunction<RealSort>(
        "to_real".toSymbolWithQuotes(), listOf(IntSort), RealSort, Associativity.NONE
    ) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RealSort> {
        require(args.size == 1)
        return ToReal(args.single() castTo IntSort)
    }
}

internal object ToIntDecl :
    SMTTheoryFunction<IntSort>(
        "to_real".toSymbolWithQuotes(), listOf(RealSort), IntSort, Associativity.NONE
    ) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<IntSort> {
        require(args.size == 1)
        return ToInt(args.single() castTo RealSort)
    }
}

internal object IsIntDecl :
    SMTTheoryFunction<BoolSort>(
        "to_real".toSymbolWithQuotes(), listOf(RealSort), BoolSort, Associativity.NONE
    ) {

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size == 1)
        return IsInt(args.single() castTo RealSort)
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
              BitVecToFPDecl,
              FPToFPDecl,
              RealToFPDecl,
              SBitVecToFPDecl,
              UBitVecToFPDecl,
              FPToUBitVecDecl,
              FPToSBitVecDecl,
              FPToRealDecl)
          .associateBy { it.symbol.toString() }

  override val sorts: Map<String, SortDecl<*>> =
      mapOf(
          Pair("RoundingMode", RoundingModeDecl),
          Pair("Real", RealSortDecl),
          Pair("Float16", FP16Decl),
          Pair("Float32", FP32Decl),
          Pair("Float64", FP64Decl),
          Pair("Float128", FP128Decl),
          Pair("BitVec", BVSortDecl),
          Pair("FloatingPoint", FPSortDecl))
}

/** RoundíngMode sort declaration internal object */
internal object RoundingModeDecl :
    SortDecl<RoundingMode>("RoundingMode".toSymbolWithQuotes(), emptySet(), emptySet()) {
  override fun getSort(bindings: Bindings): RoundingMode = RoundingMode
}

/** FloatingPoint sort declaration internal object */
internal object FPSortDecl :
    SortDecl<FPSort>(
        "FloatingPoint".toSymbolWithQuotes(), emptySet(), setOf("eb".idx(), "sb".idx())) {
  override fun getSort(bindings: Bindings): FPSort =
      FPSort(bindings["eb"].numeral, bindings["sb"].numeral)
}

/** 16-bit FloatingPoint declaration internal object */
internal object FP16Decl :
    SortDecl<FPSort>("Float16".toSymbolWithQuotes(), emptySet(), emptySet()) {
  override fun getSort(bindings: Bindings): FPSort = FPSort(5, 11)
}

/** 32-bit FloatingPoint declaration internal object */
internal object FP32Decl :
    SortDecl<FPSort>("Float32".toSymbolWithQuotes(), emptySet(), emptySet()) {
  override fun getSort(bindings: Bindings): FPSort = FPSort(8, 24)
}

/** 64-bit FloatingPoint declaration internal object */
internal object FP64Decl :
    SortDecl<FPSort>("Float64".toSymbolWithQuotes(), emptySet(), emptySet()) {
  override fun getSort(bindings: Bindings): FPSort = FPSort(11, 53)
}

/** 128-bit FloatingPoint declaration internal object */
internal object FP128Decl :
    SortDecl<FPSort>("Float128".toSymbolWithQuotes(), emptySet(), emptySet()) {
  override fun getSort(bindings: Bindings): FPSort = FPSort(15, 113)
}

internal object RoundNearestTiesToEvenDecl :
    SMTTheoryFunction<RoundingMode>(
        "roundNearestTiesToEven".toSymbolWithQuotes(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> =
      RoundNearestTiesToEven

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RoundingMode> {
        require(args.isEmpty())
        return RoundNearestTiesToEven
    }
}

internal object RNEDecl :
    SMTTheoryFunction<RoundingMode>("RNE".toSymbolWithQuotes(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RNE

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RoundingMode> {
        require(args.isEmpty())
        return RNE
    }
}

internal object RoundNearestTiesToAwayDecl :
    SMTTheoryFunction<RoundingMode>(
        "roundNearestTiesToAway".toSymbolWithQuotes(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> =
      RoundNearestTiesToAway

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RoundingMode> {
        require(args.isEmpty())
        return RoundNearestTiesToAway
    }
}

internal object RNADecl :
    SMTTheoryFunction<RoundingMode>("RNA".toSymbolWithQuotes(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RNA

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RoundingMode> {
        require(args.isEmpty())
        return RNA
    }
}

internal object RoundTowardPositiveDecl :
    SMTTheoryFunction<RoundingMode>(
        "roundTowardPositive".toSymbolWithQuotes(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RoundTowardPositive

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RoundingMode> {
        require(args.isEmpty())
        return RoundTowardPositive
    }
}

internal object RTPDecl :
    SMTTheoryFunction<RoundingMode>("RTP".toSymbolWithQuotes(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RTP

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RoundingMode> {
        require(args.isEmpty())
        return RTP
    }
}

internal object RoundTowardNegativeDecl :
    SMTTheoryFunction<RoundingMode>(
        "RoundTowardNegative".toSymbolWithQuotes(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RoundTowardNegative

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RoundingMode> {
        require(args.isEmpty())
        return RoundTowardNegative
    }
}

internal object RTNDecl :
    SMTTheoryFunction<RoundingMode>("RTN".toSymbolWithQuotes(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RTN

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RoundingMode> {
        require(args.isEmpty())
        return RTN
    }
}

internal object RoundTowardZeroDecl :
    SMTTheoryFunction<RoundingMode>(
        "RoundTowardZero".toSymbolWithQuotes(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RoundTowardZero

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RoundingMode> {
        require(args.isEmpty())
        return RoundTowardZero
    }
}

internal object RTZDecl :
    SMTTheoryFunction<RoundingMode>("RTZ".toSymbolWithQuotes(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RTZ

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RoundingMode> {
        require(args.isEmpty())
        return RTZ
    }
}

internal object FPLiteralDecl :
    SMTTheoryFunction<BVSort, BVSort, BVSort, FPSort>(
        "fp".toSymbolWithQuotes(),
        emptySet(),
        BVSort(1),
        BVSort.fromSymbol("eb"),
        BVSort.fromSymbol("i"),
        emptySet(),
        setOf("eb".idx(), "i".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<BVSort>,
      param2: Expression<BVSort>,
      param3: Expression<BVSort>,
      bindings: Bindings
  ): Expression<FPSort> {
    return FPLiteral(param1 as BVLiteral, param2 as BVLiteral, param3 as BVLiteral)
  }

    @Suppress("UNCHECKED_CAST")
    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<FPSort> {
        require(args.size == 3)
        require(args.all { expr -> expr.sort is BVSort })
        return FPLiteral(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>, args[2] as Expression<BVSort>)
    }
}

/** Plus infinity declaration internal object */
internal object FPInfinityDecl :
    SMTTheoryFunction<FPSort>(
        "+oo".toSymbolWithQuotes(),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(bindings: Bindings): Expression<FPSort> =
      FPInfinity(bindings["eb"].numeral, bindings["sb"].numeral)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<FPSort> {
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
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(bindings: Bindings): Expression<FPSort> =
      FPMinusInfinity(bindings["eb"].numeral, bindings["sb"].numeral)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<FPSort> {
        require(args.isEmpty())
        require(indices.size == 2)
        require(indices.all { index -> index is NumeralIndex })

        return FPMinusInfinity((indices[0] as NumeralIndex).numeral, (indices[1] as NumeralIndex).numeral)
    }
}

/** Plus zero declaration internal object */
internal object FPZeroDecl :
    SMTTheoryFunction<FPSort>(
        "+zero".toSymbolWithQuotes(),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(bindings: Bindings): Expression<FPSort> =
      FPZero(bindings["eb"].numeral, bindings["sb"].numeral)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<FPSort> {
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
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(bindings: Bindings): Expression<FPSort> =
      FPMinusZero(bindings["eb"].numeral, bindings["sb"].numeral)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<FPSort> {
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
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(bindings: Bindings): Expression<FPSort> =
      FPNaN(bindings["eb"].numeral, bindings["sb"].numeral)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<FPSort> {
        require(args.isEmpty())
        require(indices.size == 2)
        require(indices.all { index -> index is NumeralIndex })

        return FPNaN((indices[0] as NumeralIndex).numeral, (indices[1] as NumeralIndex).numeral)
    }
}

/** Absolute value declaration internal object */
internal object FPAbsDecl :
    SMTTheoryFunction<FPSort, FPSort>(
        "fp.abs".toSymbolWithQuotes(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(param: Expression<FPSort>, bindings: Bindings): Expression<FPSort> =
      FPAbs(param)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<FPSort> {
        require(args.size == 1)
        require(indices.isEmpty())
        require(args.single().sort is FPSort)

        @Suppress("UNCHECKED_CAST")
        return FPAbs(args.single() as Expression<FPSort>)
    }
}

/** Negation declaration internal object */
internal object FPNegDecl :
    SMTTheoryFunction<FPSort, FPSort>(
        "fp.neg".toSymbolWithQuotes(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(param: Expression<FPSort>, bindings: Bindings): Expression<FPSort> =
      FPNeg(param)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<FPSort> {
        require(args.size == 1)
        require(indices.isEmpty())
        require(args.single().sort is FPSort)

        @Suppress("UNCHECKED_CAST")
        return FPNeg(args.single() as Expression<FPSort>)
    }
}

/** Addition declaration internal object */
internal object FPAddDecl :
    SMTTheoryFunction<RoundingMode, FPSort, FPSort, FPSort>(
        "fp.add".toSymbolWithQuotes(),
        emptySet(),
        RoundingMode,
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<RoundingMode>,
      param2: Expression<FPSort>,
      param3: Expression<FPSort>,
      bindings: Bindings
  ): Expression<FPSort> = FPAdd(param1, param2, param3)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<FPSort> {
        require(args.size == 3)
        require(indices.isEmpty())
        require(args[0].sort is RoundingMode)
        require(args[1].sort is FPSort)
        require(args[2].sort is FPSort)

        @Suppress("UNCHECKED_CAST")
        return FPAdd(args[0] castTo RoundingMode, args[1] as Expression<FPSort>, args[2] as Expression<FPSort>)
    }
}

/** Subtraction declaration internal object */
internal object FPSubDecl :
    SMTTheoryFunction<RoundingMode, FPSort, FPSort, FPSort>(
        "fp.sub".toSymbolWithQuotes(),
        emptySet(),
        RoundingMode,
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<RoundingMode>,
      param2: Expression<FPSort>,
      param3: Expression<FPSort>,
      bindings: Bindings
  ): Expression<FPSort> = FPSub(param1, param2, param3)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<FPSort> {
        require(args.size == 3)
        require(indices.isEmpty())
        require(args[0].sort is RoundingMode)
        require(args[1].sort is FPSort)
        require(args[2].sort is FPSort)

        @Suppress("UNCHECKED_CAST")
        return FPSub(args[0] castTo RoundingMode, args[1] as Expression<FPSort>, args[2] as Expression<FPSort>)
    }
}

internal object FPMulDecl :
    SMTTheoryFunction<RoundingMode, FPSort, FPSort, FPSort>(
        "fp.mul".toSymbolWithQuotes(),
        emptySet(),
        RoundingMode,
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<RoundingMode>,
      param2: Expression<FPSort>,
      param3: Expression<FPSort>,
      bindings: Bindings
  ): Expression<FPSort> = FPMul(param1, param2, param3)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<FPSort> {
        require(args.size == 3)
        require(indices.isEmpty())
        require(args[0].sort is RoundingMode)
        require(args[1].sort is FPSort)
        require(args[2].sort is FPSort)

        @Suppress("UNCHECKED_CAST")
        return FPMul(args[0] castTo RoundingMode, args[1] as Expression<FPSort>, args[2] as Expression<FPSort>)
    }
}

internal object FPDivDecl :
    SMTTheoryFunction<RoundingMode, FPSort, FPSort, FPSort>(
        "fp.div".toSymbolWithQuotes(),
        emptySet(),
        RoundingMode,
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<RoundingMode>,
      param2: Expression<FPSort>,
      param3: Expression<FPSort>,
      bindings: Bindings
  ): Expression<FPSort> = FPDiv(param1, param2, param3)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<FPSort> {
        require(args.size == 3)
        require(indices.isEmpty())
        require(args[0].sort is RoundingMode)
        require(args[1].sort is FPSort)
        require(args[2].sort is FPSort)

        @Suppress("UNCHECKED_CAST")
        return FPDiv(args[0] castTo RoundingMode, args[1] as Expression<FPSort>, args[2] as Expression<FPSort>)
    }
}

internal object FPFmaDecl :
    SMTTheoryFunction<RoundingMode, FPSort, FPSort, FPSort, FPSort>(
        "fp.fma".toSymbolWithQuotes(),
        emptySet(),
        RoundingMode,
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<RoundingMode>,
      param2: Expression<FPSort>,
      param3: Expression<FPSort>,
      param4: Expression<FPSort>,
      bindings: Bindings
  ): Expression<FPSort> = FPFma(param1, param2, param3, param4)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<FPSort> {
        require(args.size == 4)
        require(indices.isEmpty())
        require(args[0].sort is RoundingMode)
        require(args[1].sort is FPSort)
        require(args[2].sort is FPSort)
        require(args[3].sort is FPSort)

        @Suppress("UNCHECKED_CAST")
        return FPFma(args[0] castTo RoundingMode, args[1] as Expression<FPSort>, args[2] as Expression<FPSort>, args[3] as Expression<FPSort>)
    }
}

internal object FPSqrtDecl :
    SMTTheoryFunction<RoundingMode, FPSort, FPSort>(
        "fp.sqrt".toSymbolWithQuotes(),
        emptySet(),
        RoundingMode,
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<RoundingMode>,
      param2: Expression<FPSort>,
      bindings: Bindings
  ): Expression<FPSort> = FPSqrt(param1, param2)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<FPSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args[0].sort is RoundingMode)
        require(args[1].sort is FPSort)

        @Suppress("UNCHECKED_CAST")
        return FPSqrt(args[0] castTo RoundingMode, args[1] as Expression<FPSort>)
    }
}

internal object FPRemDecl :
    SMTTheoryFunction<FPSort, FPSort, FPSort>(
        "fp.rem".toSymbolWithQuotes(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<FPSort>,
      param2: Expression<FPSort>,
      bindings: Bindings
  ): Expression<FPSort> = FPRem(param1, param2)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<FPSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expr -> expr.sort is FPSort })

        @Suppress("UNCHECKED_CAST")
        return FPRem(args[0] as Expression<FPSort>, args[1] as Expression<FPSort>)
    }
}

internal object FPRoundToIntegralDecl :
    SMTTheoryFunction<RoundingMode, FPSort, FPSort>(
        "fp.roundToIntegral".toSymbolWithQuotes(),
        emptySet(),
        RoundingMode,
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<RoundingMode>,
      param2: Expression<FPSort>,
      bindings: Bindings
  ): Expression<FPSort> = FPRoundToIntegral(param1, param2)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<FPSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args[0].sort is RoundingMode)
        require(args[1].sort is FPSort)

        @Suppress("UNCHECKED_CAST")
        return FPRoundToIntegral(args[0] castTo RoundingMode, args[1] as Expression<FPSort>)
    }
}

internal object FPMinDecl :
    SMTTheoryFunction<FPSort, FPSort, FPSort>(
        "fp.min".toSymbolWithQuotes(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<FPSort>,
      param2: Expression<FPSort>,
      bindings: Bindings
  ): Expression<FPSort> = FPMin(param1, param2)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<FPSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expr -> expr.sort is FPSort })

        @Suppress("UNCHECKED_CAST")
        return FPMin(args[0] as Expression<FPSort>, args[1] as Expression<FPSort>)
    }
}

internal object FPMaxDecl :
    SMTTheoryFunction<FPSort, FPSort, FPSort>(
        "fp.max".toSymbolWithQuotes(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<FPSort>,
      param2: Expression<FPSort>,
      bindings: Bindings
  ): Expression<FPSort> = FPMin(param1, param2)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<FPSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expr -> expr.sort is FPSort })

        @Suppress("UNCHECKED_CAST")
        return FPMax(args[0] as Expression<FPSort>, args[1] as Expression<FPSort>)
    }
}

internal object FPLeqDecl :
    SMTTheoryFunction<FPSort>(
        "fp.leq".toSymbolWithQuotes(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      varargs: List<Expression<FPSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = FPLeq(varargs)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size >= 2)
        require(indices.isEmpty())
        require(args.all { expr -> expr.sort is FPSort })

        @Suppress("UNCHECKED_CAST")
        return FPLeq(args as List<Expression<FPSort>>)
    }
}

internal object FPLtDecl :
    SMTTheoryFunction<FPSort>(
        "fp.lt".toSymbolWithQuotes(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      varargs: List<Expression<FPSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = FPLt(varargs)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size >= 2)
        require(indices.isEmpty())
        require(args.all { expr -> expr.sort is FPSort })

        @Suppress("UNCHECKED_CAST")
        return FPLt(args as List<Expression<FPSort>>)
    }
}

internal object FPGeqDecl :
    SMTTheoryFunction<FPSort>(
        "fp.geq".toSymbolWithQuotes(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      varargs: List<Expression<FPSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = FPGeq(varargs)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size >= 2)
        require(indices.isEmpty())
        require(args.all { expr -> expr.sort is FPSort })

        @Suppress("UNCHECKED_CAST")
        return FPGeq(args as List<Expression<FPSort>>)
    }
}

internal object FPGtDecl :
    SMTTheoryFunction<FPSort>(
        "fp.gt".toSymbolWithQuotes(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      varargs: List<Expression<FPSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = FPGt(varargs)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size >= 2)
        require(indices.isEmpty())
        require(args.all { expr -> expr.sort is FPSort })

        @Suppress("UNCHECKED_CAST")
        return FPGt(args as List<Expression<FPSort>>)
    }
}

internal object FPEqDecl :
    SMTTheoryFunction<FPSort>(
        "fp.eq".toSymbolWithQuotes(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      varargs: List<Expression<FPSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = FPEq(varargs)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size >= 2)
        require(indices.isEmpty())
        require(args.all { expr -> expr.sort is FPSort })

        @Suppress("UNCHECKED_CAST")
        return FPEq(args as List<Expression<FPSort>>)
    }
}

internal object FPIsNormalDecl :
    SMTTheoryFunction<FPSort, BoolSort>(
        "fp.isNormal".toSymbolWithQuotes(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        BoolSort) {
  override fun buildExpression(
      param: Expression<FPSort>,
      bindings: Bindings
  ): Expression<BoolSort> = FPIsNormal(param)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size == 1)
        require(indices.isEmpty())
        require(args.single().sort is FPSort)

        @Suppress("UNCHECKED_CAST")
        return FPIsNormal(args.single() as Expression<FPSort>)
    }
}

internal object FPIsSubormalDecl :
    SMTTheoryFunction<FPSort, BoolSort>(
        "fp.isSubormal".toSymbolWithQuotes(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        BoolSort) {
  override fun buildExpression(
      param: Expression<FPSort>,
      bindings: Bindings
  ): Expression<BoolSort> = FPIsSubnormal(param)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size == 1)
        require(indices.isEmpty())
        require(args.single().sort is FPSort)

        @Suppress("UNCHECKED_CAST")
        return FPIsSubnormal(args.single() as Expression<FPSort>)
    }
}

internal object FPIsZeroDecl :
    SMTTheoryFunction<FPSort, BoolSort>(
        "fp.isZero".toSymbolWithQuotes(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        BoolSort) {
  override fun buildExpression(
      param: Expression<FPSort>,
      bindings: Bindings
  ): Expression<BoolSort> = FPIsZero(param)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size == 1)
        require(indices.isEmpty())
        require(args.single().sort is FPSort)

        @Suppress("UNCHECKED_CAST")
        return FPIsZero(args.single() as Expression<FPSort>)
    }
}

internal object FPIsInfiniteDecl :
    SMTTheoryFunction<FPSort, BoolSort>(
        "fp.isInfinite".toSymbolWithQuotes(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        BoolSort) {
  override fun buildExpression(
      param: Expression<FPSort>,
      bindings: Bindings
  ): Expression<BoolSort> = FPIsInfinite(param)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size == 1)
        require(indices.isEmpty())
        require(args.single().sort is FPSort)

        @Suppress("UNCHECKED_CAST")
        return FPIsInfinite(args.single() as Expression<FPSort>)
    }
}

internal object FPIsNaNDecl :
    SMTTheoryFunction<FPSort, BoolSort>(
        "fp.isNan".toSymbolWithQuotes(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        BoolSort) {
  override fun buildExpression(
      param: Expression<FPSort>,
      bindings: Bindings
  ): Expression<BoolSort> = FPIsNaN(param)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size == 1)
        require(indices.isEmpty())
        require(args.single().sort is FPSort)

        @Suppress("UNCHECKED_CAST")
        return FPIsNaN(args.single() as Expression<FPSort>)
    }
}

internal object FPIsNegativeDecl :
    SMTTheoryFunction<FPSort, BoolSort>(
        "fp.isNegative".toSymbolWithQuotes(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        BoolSort) {
  override fun buildExpression(
      param: Expression<FPSort>,
      bindings: Bindings
  ): Expression<BoolSort> = FPIsNegative(param)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size == 1)
        require(indices.isEmpty())
        require(args.single().sort is FPSort)

        @Suppress("UNCHECKED_CAST")
        return FPIsNegative(args.single() as Expression<FPSort>)
    }
}

internal object FPIsPositiveDecl :
    SMTTheoryFunction<FPSort, BoolSort>(
        "fp.isPositive".toSymbolWithQuotes(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        BoolSort) {
  override fun buildExpression(
      param: Expression<FPSort>,
      bindings: Bindings
  ): Expression<BoolSort> = FPIsPositive(param)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size == 1)
        require(indices.isEmpty())
        require(args.single().sort is FPSort)

        @Suppress("UNCHECKED_CAST")
        return FPIsPositive(args.single() as Expression<FPSort>)
    }
}

internal object BitVecToFPDecl :
    SMTTheoryFunction<BVSort, FPSort>(
        "to_fp".toSymbolWithQuotes(),
        emptySet(),
        BVSort.fromSymbol("m"),
        setOf("eb".idx(), "sb".idx()),
        setOf("m".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(param: Expression<BVSort>, bindings: Bindings): Expression<FPSort> =
      BitVecToFP(param, bindings["eb"].numeral, bindings["sb"].numeral)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<FPSort> {
        require(args.size == 1)
        require(indices.size == 2)
        require(args.single().sort is BVSort)
        require(indices.all { index -> index is NumeralIndex})

        @Suppress("UNCHECKED_CAST")
        return BitVecToFP(args.single() as Expression<BVSort>, (indices[0] as NumeralIndex).numeral, (indices[1] as NumeralIndex).numeral)
    }
}

internal object FPToFPDecl :
    SMTTheoryFunction<RoundingMode, FPSort, FPSort>(
        "to_fp".toSymbolWithQuotes(),
        emptySet(),
        RoundingMode,
        FPSort("mb".idx(), "nb".idx()),
        setOf("eb".idx(), "sb".idx()),
        setOf("mb".idx(), "nb".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<RoundingMode>,
      param2: Expression<FPSort>,
      bindings: Bindings
  ): Expression<FPSort> = FPToFP(param1, param2, bindings["eb"].numeral, bindings["sb"].numeral)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<FPSort> {
        require(args.size == 2)
        require(indices.size == 2)
        require(args[0].sort is RoundingMode)
        require(args[1].sort is FPSort)
        require(indices.all { index -> index is NumeralIndex})

        @Suppress("UNCHECKED_CAST")
        return FPToFP(args[0] castTo RoundingMode, args[1] as Expression<FPSort>, (indices[0] as NumeralIndex).numeral, (indices[1] as NumeralIndex).numeral)
    }
}

internal object RealToFPDecl :
    SMTTheoryFunction<RoundingMode, RealSort, FPSort>(
        "to_fp".toSymbolWithQuotes(),
        emptySet(),
        RoundingMode,
        RealSort,
        setOf("eb".idx(), "sb".idx()),
        emptySet(),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<RoundingMode>,
      param2: Expression<RealSort>,
      bindings: Bindings
  ): Expression<FPSort> = RealToFP(param1, param2, bindings["eb"].numeral, bindings["sb"].numeral)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<FPSort> {
        require(args.size == 2)
        require(indices.size == 2)
        require(args[0].sort is RoundingMode)
        require(args[1].sort is RealSort)
        require(indices.all { index -> index is NumeralIndex})

        @Suppress("UNCHECKED_CAST")
        return RealToFP(args[0] castTo RoundingMode, args[1] as Expression<RealSort>, (indices[0] as NumeralIndex).numeral, (indices[1] as NumeralIndex).numeral)
    }
}

internal object SBitVecToFPDecl :
    SMTTheoryFunction<RoundingMode, BVSort, FPSort>(
        "to_fp".toSymbolWithQuotes(),
        emptySet(),
        RoundingMode,
        BVSort.fromSymbol("m"),
        setOf("eb".idx(), "sb".idx()),
        setOf("m".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<RoundingMode>,
      param2: Expression<BVSort>,
      bindings: Bindings
  ): Expression<FPSort> =
      SBitVecToFP(param1, param2, bindings["eb"].numeral, bindings["sb"].numeral)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<FPSort> {
        require(args.size == 2)
        require(indices.size == 2)
        require(args[0].sort is RoundingMode)
        require(args[1].sort is BVSort)
        require(indices.all { index -> index is NumeralIndex})

        @Suppress("UNCHECKED_CAST")
        return SBitVecToFP(args[0] castTo RoundingMode, args[1] as Expression<BVSort>, (indices[0] as NumeralIndex).numeral, (indices[1] as NumeralIndex).numeral)
    }
}

internal object UBitVecToFPDecl :
    SMTTheoryFunction<RoundingMode, BVSort, FPSort>(
        "to_fp_unsigned".toSymbolWithQuotes(),
        emptySet(),
        RoundingMode,
        BVSort.fromSymbol("m"),
        setOf("eb".idx(), "sb".idx()),
        setOf("m".idx()),
        FPSort("eb".idx(), "sb".idx())) {
  override fun buildExpression(
      param1: Expression<RoundingMode>,
      param2: Expression<BVSort>,
      bindings: Bindings
  ): Expression<FPSort> =
      UBitVecToFP(param1, param2, bindings["eb"].numeral, bindings["sb"].numeral)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<FPSort> {
        require(args.size == 2)
        require(indices.size == 2)
        require(args[0].sort is RoundingMode)
        require(args[1].sort is BVSort)
        require(indices.all { index -> index is NumeralIndex})

        @Suppress("UNCHECKED_CAST")
        return UBitVecToFP(args[0] castTo RoundingMode, args[1] as Expression<BVSort>, (indices[0] as NumeralIndex).numeral, (indices[1] as NumeralIndex).numeral)
    }
}

internal object FPToUBitVecDecl :
    SMTTheoryFunction<RoundingMode, FPSort, BVSort>(
        "fp.to_ubv".toSymbolWithQuotes(),
        emptySet(),
        RoundingMode,
        FPSort("eb".idx(), "sb".idx()),
        setOf("m".idx()),
        setOf("eb".idx(), "sb".idx()),
        BVSort.fromSymbol("m")) {
  override fun buildExpression(
      param1: Expression<RoundingMode>,
      param2: Expression<FPSort>,
      bindings: Bindings
  ): Expression<BVSort> = FPToUBitVec(param1, param2, bindings["m"].numeral)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
        require(args.size == 2)
        require(indices.size == 1)
        require(args[0].sort is RoundingMode)
        require(args[1].sort is FPSort)
        require(indices.single() is NumeralIndex)

        @Suppress("UNCHECKED_CAST")
        return FPToUBitVec(args[0] castTo RoundingMode, args[1] as Expression<FPSort>, (indices.single() as NumeralIndex).numeral)
    }
}

internal object FPToSBitVecDecl :
    SMTTheoryFunction<RoundingMode, FPSort, BVSort>(
        "fp.to_ubv".toSymbolWithQuotes(),
        emptySet(),
        RoundingMode,
        FPSort("eb".idx(), "sb".idx()),
        setOf("m".idx()),
        setOf("eb".idx(), "sb".idx()),
        BVSort.fromSymbol("m")) {
  override fun buildExpression(
      param1: Expression<RoundingMode>,
      param2: Expression<FPSort>,
      bindings: Bindings
  ): Expression<BVSort> = FPToSBitVec(param1, param2, bindings["m"].numeral)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
        require(args.size == 2)
        require(indices.size == 1)
        require(args[0].sort is RoundingMode)
        require(args[1].sort is FPSort)
        require(indices.single() is NumeralIndex)

        @Suppress("UNCHECKED_CAST")
        return FPToSBitVec(args[0] castTo RoundingMode, args[1] as Expression<FPSort>, (indices.single() as NumeralIndex).numeral)
    }
}

internal object FPToRealDecl :
    SMTTheoryFunction<FPSort, RealSort>(
        "fp.to_real".toSymbolWithQuotes(),
        emptySet(),
        FPSort("eb".idx(), "sb".idx()),
        emptySet(),
        setOf("eb".idx(), "sb".idx()),
        RealSort) {
  override fun buildExpression(
      param: Expression<FPSort>,
      bindings: Bindings
  ): Expression<RealSort> = FPToReal(param)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RealSort> {
        require(args.size == 1)
        require(indices.isEmpty())
        require(args.single().sort is FPSort)

        @Suppress("UNCHECKED_CAST")
        return FPToReal(args.single() as Expression<FPSort>)
    }
}

/** Array extension theory internal object */
internal object ArrayExTheory : Theory {
  override val functions: Map<String, FunctionDecl<*>> =
      listOf(ArraySelectDecl, ArrayStoreDecl).associateBy { it.symbol.toString() }

  override val sorts: MutableMap<String, SortDecl<*>> = mutableMapOf(Pair("Array", ArraySortDecl))
}

/** Sort declaration internal object for array sort */
internal object ArraySortDecl :
    SortDecl<ArraySort<Sort, Sort>>(
        "Array".toSymbolWithQuotes(), setOf(SortParameter("X"), SortParameter("Y")), emptySet()) {
  override fun getSort(bindings: Bindings): ArraySort<Sort, Sort> =
      ArraySort(bindings[SortParameter("X")], bindings[SortParameter("Y")])
}

/** Array selection declaration internal object */
internal object ArraySelectDecl :
    SMTTheoryFunction<ArraySort<Sort, Sort>, Sort, Sort>(
        "select".toSymbolWithQuotes(),
        setOf(SortParameter("X"), SortParameter("Y")),
        ArraySort(SortParameter("X"), SortParameter("Y")),
        SortParameter("X"),
        emptySet(),
        emptySet(),
        SortParameter("Y")) {
  override fun buildExpression(
      param1: Expression<ArraySort<Sort, Sort>>,
      param2: Expression<Sort>,
      bindings: Bindings
  ): Expression<Sort> = ArraySelect(param1, param2)

    // TODO can this be improved (maybe make this generic)?
    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<Sort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args[0].sort is ArraySort<*, *>)
        require(args[1].sort == (args[0].sort as ArraySort<*, *>).x)

        @Suppress("UNCHECKED_CAST")
        return ArraySelect(args[0] as Expression<ArraySort<Sort, Sort>>, args[1] castTo (args[0].sort as ArraySort<*, *>).x)
    }
}

/** Array store declaration internal object */
internal object ArrayStoreDecl :
    SMTTheoryFunction<ArraySort<Sort, Sort>, Sort, Sort, ArraySort<Sort, Sort>>(
        "store".toSymbolWithQuotes(),
        setOf(SortParameter("X"), SortParameter("Y")),
        ArraySort(SortParameter("X"), SortParameter("Y")),
        SortParameter("X"),
        SortParameter("Y"),
        emptySet(),
        emptySet(),
        ArraySort(SortParameter("X"), SortParameter("Y"))) {
  override fun buildExpression(
      param1: Expression<ArraySort<Sort, Sort>>,
      param2: Expression<Sort>,
      param3: Expression<Sort>,
      bindings: Bindings
  ): Expression<ArraySort<Sort, Sort>> = ArrayStore(param1, param2, param3)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<ArraySort<Sort, Sort>> {
        require(args.size == 3)
        require(indices.isEmpty())
        require(args[0].sort is ArraySort<*, *>)

        // TODO these can probably be removed (castTo) checks the same requirement
        require(args[1].sort == (args[0].sort as ArraySort<*, *>).x)
        require(args[2].sort == (args[0].sort as ArraySort<*, *>).y)

        @Suppress("UNCHECKED_CAST")
        return ArrayStore(args[0] as Expression<ArraySort<Sort, Sort>>, args[1] castTo (args[0].sort as ArraySort<*, *>).x, args[2] castTo (args[0].sort as ArraySort<*, *>).y)
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
          .associateBy { it.symbol.toString() }

  override val sorts: Map<String, SortDecl<*>> =
      mapOf(Pair("String", StringSortDecl), Pair("RegLan", RegLanDecl), Pair("Int", IntSortDecl))
}

internal object StringSortDecl :
    SortDecl<StringSort>("String".toSymbolWithQuotes(), emptySet(), emptySet()) {
  override fun getSort(bindings: Bindings): StringSort = StringSort
}

internal object RegLanDecl :
    SortDecl<RegLan>("RegLan".toSymbolWithQuotes(), emptySet(), emptySet()) {
  override fun getSort(bindings: Bindings): RegLan = RegLan
}

internal object CharDecl :
    SMTTheoryFunction<StringSort>(
        "char".toSymbolWithQuotes(), emptySet(), setOf("H".idx()), StringSort) {
  override fun buildExpression(bindings: Bindings): Expression<StringSort> = TODO()

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<StringSort> {
        require(args.isEmpty())
        require(indices.size == 1)
        require(indices.single() is NumeralIndex)

        return TODO("SMT-Lib char not implemented yet!")
    }
}

internal object StrConcatDecl :
    SMTTheoryFunction<StringSort, StringSort, StringSort>(
        "str.++".toSymbolWithQuotes(),
        emptySet(),
        StringSort,
        StringSort,
        emptySet(),
        emptySet(),
        StringSort) {
  override fun buildExpression(
      param1: Expression<StringSort>,
      param2: Expression<StringSort>,
      varargs: List<Expression<StringSort>>,
      bindings: Bindings
  ): Expression<StringSort> = StrConcat(param1, param2, *varargs.toTypedArray())

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<StringSort> {
        require(args.size >= 2)
        require(indices.isEmpty())
        require(args.all { expr -> expr.sort is StringSort })

        @Suppress("UNCHECKED_CAST")
        return StrConcat(args as List<Expression<StringSort>>)
    }
}

internal object StrLengthDecl :
    SMTTheoryFunction<StringSort, IntSort>(
        "str.len".toSymbolWithQuotes(), emptySet(), StringSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param: Expression<StringSort>,
      bindings: Bindings
  ): Expression<IntSort> = StrLength(param)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<IntSort> {
        require(args.size == 1)
        require(indices.isEmpty())
        require(args.single().sort is StringSort)

        return StrLength(args.single() castTo StringSort)
    }
}

internal object StrLexOrderDecl :
    SMTTheoryFunction<StringSort>(
        "str.<".toSymbolWithQuotes(), emptySet(), StringSort, StringSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<StringSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = StrLexOrder(varargs)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size >= 2)
        require(indices.isEmpty())
        require(args.all { expr -> expr.sort is StringSort })

        @Suppress("UNCHECKED_CAST")
        return StrLexOrder(args as List<Expression<StringSort>>)
    }
}

internal object ToRegexDecl :
    SMTTheoryFunction<StringSort, RegLan>(
        "str.to_reg".toSymbolWithQuotes(), emptySet(), StringSort, emptySet(), emptySet(), RegLan) {
  override fun buildExpression(
      param: Expression<StringSort>,
      bindings: Bindings
  ): Expression<RegLan> = ToRegex(param)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RegLan> {
        require(args.size == 1)
        require(indices.isEmpty())
        require(args.single().sort is StringSort)

        return ToRegex(args.single() castTo StringSort)
    }
}

internal object InRegexDecl :
    SMTTheoryFunction<StringSort, RegLan, BoolSort>(
        "str.in_reg".toSymbolWithQuotes(),
        emptySet(),
        StringSort,
        RegLan,
        emptySet(),
        emptySet(),
        BoolSort) {
  override fun buildExpression(
      param1: Expression<StringSort>,
      param2: Expression<RegLan>,
      bindings: Bindings
  ): Expression<BoolSort> = InRegex(param1, param2)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args[0].sort is StringSort)
        require(args[1].sort is RegLan)

        return InRegex(args[0] castTo StringSort, args[1] castTo RegLan)
    }
}

internal object RegexNoneDecl :
    SMTTheoryFunction<RegLan>("re.none".toSymbolWithQuotes(), emptySet(), emptySet(), RegLan) {
  override fun buildExpression(bindings: Bindings): Expression<RegLan> = RegexNone

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RegLan> {
        require(args.isEmpty())
        require(indices.isEmpty())

        return RegexNone
    }
}

internal object RegexAllDecl :
    SMTTheoryFunction<RegLan>("re.all".toSymbolWithQuotes(), emptySet(), emptySet(), RegLan) {
  override fun buildExpression(bindings: Bindings): Expression<RegLan> = RegexAll
    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RegLan> {
        require(args.isEmpty())
        require(indices.isEmpty())

        return RegexAll
    }

}

internal object RegexAllCharDecl :
    SMTTheoryFunction<RegLan>("re.allchar".toSymbolWithQuotes(), emptySet(), emptySet(), RegLan) {
  override fun buildExpression(bindings: Bindings): Expression<RegLan> = RegexAllChar

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RegLan> {
        require(args.isEmpty())
        require(indices.isEmpty())

        return RegexAllChar
    }
}

internal object RegexConcatDecl :
    SMTTheoryFunction<RegLan, RegLan, RegLan>(
        "re.++".toSymbolWithQuotes(), emptySet(), RegLan, RegLan, emptySet(), emptySet(), RegLan) {
  override fun buildExpression(
      param1: Expression<RegLan>,
      param2: Expression<RegLan>,
      varargs: List<Expression<RegLan>>,
      bindings: Bindings
  ): Expression<RegLan> = RegexConcat(param1, param2, *varargs.toTypedArray())

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RegLan> {
        require(args.size >= 2)
        require(indices.isEmpty())
        require(args.all { expr -> expr.sort is RegLan })

        @Suppress("UNCHECKED_CAST")
        return RegexConcat(args as List<Expression<RegLan>>)
    }
}

internal object RegexUnionDecl :
    SMTTheoryFunction<RegLan, RegLan, RegLan>(
        "re.union".toSymbolWithQuotes(),
        emptySet(),
        RegLan,
        RegLan,
        emptySet(),
        emptySet(),
        RegLan) {
  override fun buildExpression(
      param1: Expression<RegLan>,
      param2: Expression<RegLan>,
      varargs: List<Expression<RegLan>>,
      bindings: Bindings
  ): Expression<RegLan> = RegexUnion(param1, param2, *varargs.toTypedArray())

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RegLan> {
        require(args.size >= 2)
        require(indices.isEmpty())
        require(args.all { expr -> expr.sort is RegLan })

        @Suppress("UNCHECKED_CAST")
        return RegexUnion(args as List<Expression<RegLan>>)
    }
}

internal object RegexIntersecDecl :
    SMTTheoryFunction<RegLan, RegLan, RegLan>(
        "re.inter".toSymbolWithQuotes(),
        emptySet(),
        RegLan,
        RegLan,
        emptySet(),
        emptySet(),
        RegLan) {
  override fun buildExpression(
      param1: Expression<RegLan>,
      param2: Expression<RegLan>,
      varargs: List<Expression<RegLan>>,
      bindings: Bindings
  ): Expression<RegLan> = RegexIntersec(param1, param2, *varargs.toTypedArray())

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RegLan> {
        require(args.size >= 2)
        require(indices.isEmpty())
        require(args.all { expr -> expr.sort is RegLan })

        @Suppress("UNCHECKED_CAST")
        return RegexIntersec(args as List<Expression<RegLan>>)
    }
}

internal object RegexStarDecl :
    SMTTheoryFunction<RegLan, RegLan>(
        "re.*".toSymbolWithQuotes(), emptySet(), RegLan, emptySet(), emptySet(), RegLan) {
  override fun buildExpression(param: Expression<RegLan>, bindings: Bindings): Expression<RegLan> =
      RegexStar(param)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RegLan> {
        require(args.size == 1)
        require(indices.isEmpty())
        require(args.single().sort is RegLan)

        @Suppress("UNCHECKED_CAST")
        return RegexStar(args.single() castTo RegLan)
    }
}

internal object StrRefLexOrderDecl :
    SMTTheoryFunction<StringSort>(
        "str.<=".toSymbolWithQuotes(), emptySet(), StringSort, StringSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<StringSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = StrRefLexOrder(varargs)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size >= 2)
        require(indices.isEmpty())
        require(args.all { expr -> expr.sort is StringSort })

        @Suppress("UNCHECKED_CAST")
        return StrRefLexOrder(args as List<Expression<StringSort>>)
    }
}

internal object StrAtDecl :
    SMTTheoryFunction<StringSort, IntSort, StringSort>(
        "str.at".toSymbolWithQuotes(),
        emptySet(),
        StringSort,
        IntSort,
        emptySet(),
        emptySet(),
        StringSort) {
  override fun buildExpression(
      param1: Expression<StringSort>,
      param2: Expression<IntSort>,
      bindings: Bindings
  ): Expression<StringSort> = StrAt(param1, param2)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<StringSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args[0].sort is StringSort)
        require(args[1].sort is IntSort)

        return StrAt(args[0] castTo StringSort, args[1] castTo IntSort)
    }
}

internal object StrSubstringDecl :
    SMTTheoryFunction<StringSort, IntSort, IntSort, StringSort>(
        "str.substr".toSymbolWithQuotes(),
        emptySet(),
        StringSort,
        IntSort,
        IntSort,
        emptySet(),
        emptySet(),
        StringSort) {
  override fun buildExpression(
      param1: Expression<StringSort>,
      param2: Expression<IntSort>,
      param3: Expression<IntSort>,
      bindings: Bindings
  ): Expression<StringSort> = StrSubstring(param1, param2, param3)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<StringSort> {
        require(args.size == 3)
        require(indices.isEmpty())
        require(args[0].sort is StringSort)
        require(args[1].sort is IntSort)
        require(args[2].sort is IntSort)

        return StrSubstring(args[0] castTo StringSort, args[1] castTo IntSort, args[2] castTo IntSort)
    }
}

internal object StrPrefixOfDecl :
    SMTTheoryFunction<StringSort, StringSort, BoolSort>(
        "str.prefixof".toSymbolWithQuotes(),
        emptySet(),
        StringSort,
        StringSort,
        emptySet(),
        emptySet(),
        BoolSort) {
  override fun buildExpression(
      param1: Expression<StringSort>,
      param2: Expression<StringSort>,
      bindings: Bindings
  ): Expression<BoolSort> = StrPrefixOf(param1, param2)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expr -> expr.sort is StringSort })

        return StrPrefixOf(args[0] castTo StringSort, args[1] castTo StringSort)
    }
}

internal object StrSuffixOfDecl :
    SMTTheoryFunction<StringSort, StringSort, BoolSort>(
        "str.suffixof".toSymbolWithQuotes(),
        emptySet(),
        StringSort,
        StringSort,
        emptySet(),
        emptySet(),
        BoolSort) {
  override fun buildExpression(
      param1: Expression<StringSort>,
      param2: Expression<StringSort>,
      bindings: Bindings
  ): Expression<BoolSort> = StrSuffixOf(param1, param2)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expr -> expr.sort is StringSort })

        return StrSuffixOf(args[0] castTo StringSort, args[1] castTo StringSort)
    }
}

internal object StrContainsDecl :
    SMTTheoryFunction<StringSort, StringSort, BoolSort>(
        "str.contains".toSymbolWithQuotes(),
        emptySet(),
        StringSort,
        StringSort,
        emptySet(),
        emptySet(),
        BoolSort) {
  override fun buildExpression(
      param1: Expression<StringSort>,
      param2: Expression<StringSort>,
      bindings: Bindings
  ): Expression<BoolSort> = StrContains(param1, param2)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expr -> expr.sort is StringSort })

        return StrContains(args[0] castTo StringSort, args[1] castTo StringSort)
    }
}

internal object StrIndexOfDecl :
    SMTTheoryFunction<StringSort, StringSort, IntSort, IntSort>(
        "str.indexof".toSymbolWithQuotes(),
        emptySet(),
        StringSort,
        StringSort,
        IntSort,
        emptySet(),
        emptySet(),
        IntSort) {
  override fun buildExpression(
      param1: Expression<StringSort>,
      param2: Expression<StringSort>,
      param3: Expression<IntSort>,
      bindings: Bindings
  ): Expression<IntSort> = StrIndexOf(param1, param2, param3)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<IntSort> {
        require(args.size == 3)
        require(indices.isEmpty())
        require(args[0].sort is StringSort)
        require(args[1].sort is StringSort)
        require(args[2].sort is IntSort)

        return StrIndexOf(args[0] castTo StringSort, args[1] castTo StringSort, args[2] castTo IntSort)
    }
}

internal object StrReplaceDecl :
    SMTTheoryFunction<StringSort, StringSort, StringSort, StringSort>(
        "str.replace".toSymbolWithQuotes(),
        emptySet(),
        StringSort,
        StringSort,
        StringSort,
        emptySet(),
        emptySet(),
        StringSort) {
  override fun buildExpression(
      param1: Expression<StringSort>,
      param2: Expression<StringSort>,
      param3: Expression<StringSort>,
      bindings: Bindings
  ): Expression<StringSort> = StrReplace(param1, param2, param3)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<StringSort> {
        require(args.size == 3)
        require(indices.isEmpty())
        require(args.all { expr -> expr.sort is StringSort })

        return StrReplace(args[0] castTo StringSort, args[1] castTo StringSort, args[2] castTo StringSort)
    }
}

internal object StrReplaceAllDecl :
    SMTTheoryFunction<StringSort, StringSort, StringSort, StringSort>(
        "str.replace".toSymbolWithQuotes(),
        emptySet(),
        StringSort,
        StringSort,
        StringSort,
        emptySet(),
        emptySet(),
        StringSort) {
  override fun buildExpression(
      param1: Expression<StringSort>,
      param2: Expression<StringSort>,
      param3: Expression<StringSort>,
      bindings: Bindings
  ): Expression<StringSort> = StrReplaceAll(param1, param2, param3)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<StringSort> {
        require(args.size == 3)
        require(indices.isEmpty())
        require(args.all { expr -> expr.sort is StringSort })

        return StrReplaceAll(args[0] castTo StringSort, args[1] castTo StringSort, args[2] castTo StringSort)
    }
}

internal object StrReplaceRegexDecl :
    SMTTheoryFunction<StringSort, RegLan, StringSort, StringSort>(
        "str.replace_re".toSymbolWithQuotes(),
        emptySet(),
        StringSort,
        RegLan,
        StringSort,
        emptySet(),
        emptySet(),
        StringSort) {
  override fun buildExpression(
      param1: Expression<StringSort>,
      param2: Expression<RegLan>,
      param3: Expression<StringSort>,
      bindings: Bindings
  ): Expression<StringSort> = StrReplaceRegex(param1, param2, param3)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<StringSort> {
        require(args.size == 3)
        require(indices.isEmpty())
        require(args[0].sort is StringSort)
        require(args[1].sort is RegLan)
        require(args[2].sort is StringSort)

        return StrReplaceRegex(args[0] castTo StringSort, args[1] castTo RegLan, args[2] castTo StringSort)
    }
}

internal object StrReplaceAllRegexDecl :
    SMTTheoryFunction<StringSort, RegLan, StringSort, StringSort>(
        "str.replace_re_all".toSymbolWithQuotes(),
        emptySet(),
        StringSort,
        RegLan,
        StringSort,
        emptySet(),
        emptySet(),
        StringSort) {
  override fun buildExpression(
      param1: Expression<StringSort>,
      param2: Expression<RegLan>,
      param3: Expression<StringSort>,
      bindings: Bindings
  ): Expression<StringSort> = StrReplaceRegex(param1, param2, param3)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<StringSort> {
        require(args.size == 3)
        require(indices.isEmpty())
        require(args[0].sort is StringSort)
        require(args[1].sort is RegLan)
        require(args[2].sort is StringSort)

        return StrReplaceAllRegex(args[0] castTo StringSort, args[1] castTo RegLan, args[2] castTo StringSort)
    }
}

internal object RegexCompDecl :
    SMTTheoryFunction<RegLan, RegLan>(
        "re.comp".toSymbolWithQuotes(), emptySet(), RegLan, emptySet(), emptySet(), RegLan) {
  override fun buildExpression(param: Expression<RegLan>, bindings: Bindings): Expression<RegLan> =
      RegexComp(param)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RegLan> {
        require(args.size == 1)
        require(indices.isEmpty())
        require(args.single().sort is RegLan)

        return RegexComp(args.single() castTo RegLan)
    }
}

internal object RegexDiffDecl :
    SMTTheoryFunction<RegLan, RegLan, RegLan>(
        "re.diff".toSymbolWithQuotes(),
        emptySet(),
        RegLan,
        RegLan,
        emptySet(),
        emptySet(),
        RegLan) {
  override fun buildExpression(
      param1: Expression<RegLan>,
      param2: Expression<RegLan>,
      varargs: List<Expression<RegLan>>,
      bindings: Bindings
  ): Expression<RegLan> = RegexDiff(param1, param2, *varargs.toTypedArray())

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RegLan> {
        require(args.size >= 2)
        require(indices.isEmpty())
        require(args.all { expr -> expr.sort is RegLan })

        @Suppress("UNCHECKED_CAST")
        return RegexDiff(args as List<Expression<RegLan>>)
    }
}

internal object RegexPlusDecl :
    SMTTheoryFunction<RegLan, RegLan>(
        "re.+".toSymbolWithQuotes(), emptySet(), RegLan, emptySet(), emptySet(), RegLan) {
  override fun buildExpression(param: Expression<RegLan>, bindings: Bindings): Expression<RegLan> =
      RegexPlus(param)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RegLan> {
        require(args.size == 1)
        require(indices.isEmpty())
        require(args.single().sort is RegLan)

        return RegexPlus(args.single() castTo RegLan)
    }
}

internal object RegexOptionDecl :
    SMTTheoryFunction<RegLan, RegLan>(
        "re.opt".toSymbolWithQuotes(), emptySet(), RegLan, emptySet(), emptySet(), RegLan) {
  override fun buildExpression(param: Expression<RegLan>, bindings: Bindings): Expression<RegLan> =
      RegexOption(param)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RegLan> {
        require(args.size == 1)
        require(indices.isEmpty())
        require(args.single().sort is RegLan)

        return RegexOption(args.single() castTo RegLan)
    }
}

internal object RegexRangeDecl :
    SMTTheoryFunction<StringSort, StringSort, RegLan>(
        "re.range".toSymbolWithQuotes(),
        emptySet(),
        StringSort,
        StringSort,
        emptySet(),
        emptySet(),
        RegLan) {
  override fun buildExpression(
      param1: Expression<StringSort>,
      param2: Expression<StringSort>,
      bindings: Bindings
  ): Expression<RegLan> = RegexRange(param1, param2)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RegLan> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expr -> expr.sort is StringSort })

        return RegexRange(args[0] castTo StringSort, args[1] castTo StringSort)
    }
}

internal object RegexPowerDecl :
    SMTTheoryFunction<RegLan, RegLan>(
        "re.^".toSymbolWithQuotes(), emptySet(), RegLan, setOf("n".idx()), emptySet(), RegLan) {
  override fun buildExpression(param: Expression<RegLan>, bindings: Bindings): Expression<RegLan> =
      RegexPower(param, bindings["n"].numeral)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RegLan> {
        require(args.size == 1)
        require(indices.size == 1)
        require(args.single().sort is RegLan)
        require(indices.single() is NumeralIndex)

        return RegexPower(args[0] castTo RegLan, (indices.single() as NumeralIndex).numeral)
    }
}

internal object RegexLoopDecl :
    SMTTheoryFunction<RegLan, RegLan>(
        "re.loop".toSymbolWithQuotes(),
        emptySet(),
        RegLan,
        setOf("n1".idx(), "n2".idx()),
        emptySet(),
        RegLan) {
  override fun buildExpression(param: Expression<RegLan>, bindings: Bindings): Expression<RegLan> =
      RegexLoop(param, bindings["n1"].numeral, bindings["n2"].numeral)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RegLan> {
        require(args.size == 1)
        require(indices.size == 2)
        require(args.single().sort is RegLan)
        require(indices.all { index -> index is NumeralIndex })

        return RegexLoop(args[0] castTo RegLan, (indices[0] as NumeralIndex).numeral, (indices[1] as NumeralIndex).numeral)
    }
}

internal object StrIsDigitDecl :
    SMTTheoryFunction<StringSort, BoolSort>(
        "str.is_digit".toSymbolWithQuotes(),
        emptySet(),
        StringSort,
        emptySet(),
        emptySet(),
        BoolSort) {
  override fun buildExpression(
      param: Expression<StringSort>,
      bindings: Bindings
  ): Expression<BoolSort> = StrIsDigit(param)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size == 1)
        require(indices.isEmpty())
        require(args.single().sort is StringSort)

        return StrIsDigit(args.single() castTo StringSort)
    }
}

internal object StrToCodeDecl :
    SMTTheoryFunction<StringSort, IntSort>(
        "str.to_code".toSymbolWithQuotes(),
        emptySet(),
        StringSort,
        emptySet(),
        emptySet(),
        IntSort) {
  override fun buildExpression(
      param: Expression<StringSort>,
      bindings: Bindings
  ): Expression<IntSort> = StrToCode(param)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<IntSort> {
        require(args.size == 1)
        require(indices.isEmpty())
        require(args.single().sort is StringSort)

        return StrToCode(args.single() castTo StringSort)
    }
}

internal object StrFromCodeDecl :
    SMTTheoryFunction<IntSort, StringSort>(
        "str.from_code".toSymbolWithQuotes(),
        emptySet(),
        IntSort,
        emptySet(),
        emptySet(),
        StringSort) {
  override fun buildExpression(
      param: Expression<IntSort>,
      bindings: Bindings
  ): Expression<StringSort> = StrFromCode(param)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<StringSort> {
        require(args.size == 1)
        require(indices.isEmpty())
        require(args.single().sort is IntSort)

        return StrFromCode(args.single() castTo IntSort)
    }
}

internal object StrToIntDecl :
    SMTTheoryFunction<StringSort, IntSort>(
        "str.to_code".toSymbolWithQuotes(),
        emptySet(),
        StringSort,
        emptySet(),
        emptySet(),
        IntSort) {
  override fun buildExpression(
      param: Expression<StringSort>,
      bindings: Bindings
  ): Expression<IntSort> = StrToInt(param)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<IntSort> {
        require(args.size == 1)
        require(indices.isEmpty())
        require(args.single().sort is StringSort)

        return StrToInt(args.single() castTo StringSort)
    }
}

internal object StrFromIntDecl :
    SMTTheoryFunction<IntSort, StringSort>(
        "str.from_code".toSymbolWithQuotes(),
        emptySet(),
        IntSort,
        emptySet(),
        emptySet(),
        StringSort) {
  override fun buildExpression(
      param: Expression<IntSort>,
      bindings: Bindings
  ): Expression<StringSort> = StrFromInt(param)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<StringSort> {
        require(args.size == 1)
        require(indices.isEmpty())
        require(args.single().sort is IntSort)

        return StrFromInt(args.single() castTo IntSort)
    }
}

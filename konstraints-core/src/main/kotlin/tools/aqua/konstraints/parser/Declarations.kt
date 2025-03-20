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
    FunctionDecl0<BoolSort>("true".toSymbolWithQuotes(), emptySet(), emptySet(), BoolSort) {
  override fun buildExpression(bindings: Bindings): Expression<BoolSort> = True
    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.isEmpty())
        require(indices.isEmpty())

        return True
    }
}

internal object FalseDecl :
    FunctionDecl0<BoolSort>("false".toSymbolWithQuotes(), emptySet(), emptySet(), BoolSort) {
  override fun buildExpression(bindings: Bindings): Expression<BoolSort> = False

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.isEmpty())
        require(indices.isEmpty())

        return False
    }
}

/** Not declaration internal object */
internal object NotDecl :
    FunctionDecl1<BoolSort, BoolSort>(
        "not".toSymbolWithQuotes(), emptySet(), BoolSort, emptySet(), emptySet(), BoolSort) {
  override fun buildExpression(
      param: Expression<BoolSort>,
      bindings: Bindings
  ): Expression<BoolSort> = Not(param)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size == 1)
        require(indices.isEmpty())

        return Not(args.single() castTo BoolSort)
    }
}

/** Implies declaration internal object */
internal object ImpliesDecl :
    FunctionDeclRightAssociative<BoolSort, BoolSort, BoolSort>(
        "=>".toSymbolWithQuotes(),
        emptySet(),
        BoolSort,
        BoolSort,
        emptySet(),
        emptySet(),
        BoolSort) {
  override fun buildExpression(
      param1: Expression<BoolSort>,
      param2: Expression<BoolSort>,
      varargs: List<Expression<BoolSort>>,
      bindings: Bindings
  ) = Implies(listOf(param1, param2).plus(varargs))

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size >= 2)
        require(indices.isEmpty())

        return Implies(args.map { it castTo BoolSort })
    }
}

/** And declaration internal object */
internal object AndDecl :
    FunctionDeclLeftAssociative<BoolSort, BoolSort, BoolSort>(
        "and".toSymbolWithQuotes(),
        emptySet(),
        BoolSort,
        BoolSort,
        emptySet(),
        emptySet(),
        BoolSort) {
  override fun buildExpression(
      param1: Expression<BoolSort>,
      param2: Expression<BoolSort>,
      varargs: List<Expression<BoolSort>>,
      bindings: Bindings
  ) = And(listOf(param1, param2).plus(varargs))

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size >= 2)
        require(indices.isEmpty())

        return And(args.map { it castTo BoolSort })
    }
}

/** Or declaration internal object */
internal object OrDecl :
    FunctionDeclLeftAssociative<BoolSort, BoolSort, BoolSort>(
        "or".toSymbolWithQuotes(),
        emptySet(),
        BoolSort,
        BoolSort,
        emptySet(),
        emptySet(),
        BoolSort) {
  override fun buildExpression(
      param1: Expression<BoolSort>,
      param2: Expression<BoolSort>,
      varargs: List<Expression<BoolSort>>,
      bindings: Bindings
  ) = Or(listOf(param1, param2).plus(varargs))

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size >= 2)
        require(indices.isEmpty())

        return Or(args.map { it castTo BoolSort })
    }
}

/** Xor declaration internal object */
internal object XOrDecl :
    FunctionDeclLeftAssociative<BoolSort, BoolSort, BoolSort>(
        "xor".toSymbolWithQuotes(),
        emptySet(),
        BoolSort,
        BoolSort,
        emptySet(),
        emptySet(),
        BoolSort) {
  override fun buildExpression(
      param1: Expression<BoolSort>,
      param2: Expression<BoolSort>,
      varargs: List<Expression<BoolSort>>,
      bindings: Bindings
  ) = XOr(listOf(param1, param2).plus(varargs))

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size >= 2)
        require(indices.isEmpty())

        return XOr(args.map { it castTo BoolSort })
    }
}

/** Equals declaration internal object */
internal object EqualsDecl :
    FunctionDeclChainable<Sort>(
        "=".toSymbolWithQuotes(),
        setOf(SortParameter("A")),
        SortParameter("A"),
        SortParameter("A"),
        emptySet(),
        emptySet()) {

  override fun buildExpression(
      varargs: List<Expression<Sort>>,
      bindings: Bindings
  ): Expression<BoolSort> = Equals(varargs)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size >= 2)
        require(indices.isEmpty())
        require(args.all { expr -> expr.sort == args[0].sort })

        return Equals(args)
    }
}

/** Distinct declaration internal object */
internal object DistinctDecl :
    FunctionDeclPairwise<Sort>(
        "distinct".toSymbolWithQuotes(),
        setOf(SortParameter("A")),
        SortParameter("A"),
        SortParameter("A"),
        emptySet(),
        emptySet()) {

  override fun buildExpression(
      args: List<Expression<*>>,
      functionIndices: List<NumeralIndex>
  ): Expression<BoolSort> {
    val bindings = signature.bindParameters(args.map { it.sort }.slice(0..1), functionIndices)

    return buildExpression(args as List<Expression<Sort>>, bindings)
  }

  override fun buildExpression(
      varargs: List<Expression<Sort>>,
      bindings: Bindings
  ): Expression<BoolSort> = Distinct(varargs)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size >= 2)
        require(indices.isEmpty())
        require(args.all { expr -> expr.sort == args[0].sort }) // TODO is this necessary?

        return Distinct(args)
    }
}

/** Ite declaration internal object */
internal object IteDecl :
    FunctionDecl3<BoolSort, Sort, Sort, Sort>(
        "ite".toSymbolWithQuotes(),
        setOf(SortParameter("A")),
        BoolSort,
        SortParameter("A"),
        SortParameter("A"),
        emptySet(),
        emptySet(),
        SortParameter("A")) {
  override fun buildExpression(
      param1: Expression<BoolSort>,
      param2: Expression<Sort>,
      param3: Expression<Sort>,
      bindings: Bindings
  ): Expression<Sort> = Ite(param1, param2, param3)

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
    FunctionDecl2<BVSort, BVSort, BVSort>(
        "concat".toSymbolWithQuotes(),
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

    @Suppress("UNCHECKED_CAST")
    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expression -> expression.sort is BVSort })

        return BVConcat(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
    }
}

internal object ExtractDecl :
    FunctionDecl1<BVSort, BVSort>(
        "extract".toSymbolWithQuotes(),
        emptySet(),
        BVSort.fromSymbol("m"),
        setOf(SymbolIndex("i"), SymbolIndex("j")),
        setOf(SymbolIndex("m")),
        BVSort.fromSymbol("n")) {

  override fun buildExpression(
      args: List<Expression<*>>,
      functionIndices: List<NumeralIndex>
  ): Expression<BVSort> {
    require(args.size == 1)
    val bindings = bindParametersToExpressions(args, functionIndices)

    return buildExpression(args.single() as Expression<BVSort>, bindings)
  }

  override fun buildExpression(param: Expression<BVSort>, bindings: Bindings): Expression<BVSort> {
    return BVExtract(bindings["i"].numeral, bindings["j"].numeral, param)
  }

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
    FunctionDecl1<BVSort, BVSort>(
        "bvnot".toSymbolWithQuotes(),
        emptySet(),
        BVSort.fromSymbol("m"),
        emptySet(),
        setOf(SymbolIndex("m")),
        BVSort.fromSymbol("m")) {
  override fun buildExpression(param: Expression<BVSort>, bindings: Bindings): Expression<BVSort> =
      BVNot(param)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
        require(args.size == 1)
        require(indices.isEmpty())
        require(args.single().sort is BVSort)

        @Suppress("UNCHECKED_CAST")
        return BVNot(args.single() as Expression<BVSort>)
    }
}

internal object BVNegDecl :
    FunctionDecl1<BVSort, BVSort>(
        "bvneg".toSymbolWithQuotes(),
        emptySet(),
        BVSort.fromSymbol("m"),
        emptySet(),
        setOf(SymbolIndex("m")),
        BVSort.fromSymbol("m")) {
  override fun buildExpression(param: Expression<BVSort>, bindings: Bindings): Expression<BVSort> =
      BVNeg(param)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
        require(args.size == 1)
        require(indices.isEmpty())
        require(args.single().sort is BVSort)

        @Suppress("UNCHECKED_CAST")
        return BVNeg(args.single() as Expression<BVSort>)
    }
}

internal object BVAndDecl :
    FunctionDeclLeftAssociative<BVSort, BVSort, BVSort>(
        "bvand".toSymbolWithQuotes(),
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

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
        require(args.size >= 2)
        require(indices.isEmpty())
        require(args.all { expression -> expression.sort is BVSort })

        @Suppress("UNCHECKED_CAST")
        return BVAnd(args.map { expression -> expression as Expression<BVSort> })
    }
}

internal object BVOrDecl :
    FunctionDeclLeftAssociative<BVSort, BVSort, BVSort>(
        "bvor".toSymbolWithQuotes(),
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

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
        require(args.size >= 2)
        require(indices.isEmpty())
        require(args.all { expression -> expression.sort is BVSort })

        @Suppress("UNCHECKED_CAST")
        return BVOr(args.map { expression -> expression as Expression<BVSort> })
    }
}

internal object BVAddDecl :
    FunctionDeclLeftAssociative<BVSort, BVSort, BVSort>(
        "bvadd".toSymbolWithQuotes(),
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

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
        require(args.size >= 2)
        require(indices.isEmpty())
        require(args.all { expression -> expression.sort is BVSort })

        @Suppress("UNCHECKED_CAST")
        return BVAdd(args.map { expression -> expression as Expression<BVSort> })
    }
}

internal object BVMulDecl :
    FunctionDeclLeftAssociative<BVSort, BVSort, BVSort>(
        "bvmul".toSymbolWithQuotes(),
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

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
        require(args.size >= 2)
        require(indices.isEmpty())
        require(args.all { expression -> expression.sort is BVSort })

        @Suppress("UNCHECKED_CAST")
        return BVMul(args.map { expression -> expression as Expression<BVSort> })
    }
}

internal object BVUDivDecl :
    FunctionDecl2<BVSort, BVSort, BVSort>(
        "bvudiv".toSymbolWithQuotes(),
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

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expression -> expression.sort is BVSort })

        @Suppress("UNCHECKED_CAST")
        return BVUDiv(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
    }
}

internal object BVURemDecl :
    FunctionDecl2<BVSort, BVSort, BVSort>(
        "bvurem".toSymbolWithQuotes(),
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

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expression -> expression.sort is BVSort })

        @Suppress("UNCHECKED_CAST")
        return BVURem(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
    }
}

internal object BVShlDecl :
    FunctionDecl2<BVSort, BVSort, BVSort>(
        "bvshl".toSymbolWithQuotes(),
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

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expression -> expression.sort is BVSort })

        @Suppress("UNCHECKED_CAST")
        return BVShl(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
    }
}

internal object BVLShrDecl :
    FunctionDecl2<BVSort, BVSort, BVSort>(
        "bvlshr".toSymbolWithQuotes(),
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

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expression -> expression.sort is BVSort })

        @Suppress("UNCHECKED_CAST")
        return BVLShr(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
    }
}

internal object BVUltDecl :
    FunctionDecl2<BVSort, BVSort, BoolSort>(
        "bvult".toSymbolWithQuotes(),
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

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expression -> expression.sort is BVSort })

        @Suppress("UNCHECKED_CAST")
        return BVUlt(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
    }
}

internal object BVNAndDecl :
    FunctionDecl2<BVSort, BVSort, BVSort>(
        "bvnand".toSymbolWithQuotes(),
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

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expression -> expression.sort is BVSort })

        @Suppress("UNCHECKED_CAST")
        return BVNAnd(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
    }
}

internal object BVNOrDecl :
    FunctionDecl2<BVSort, BVSort, BVSort>(
        "bvnor".toSymbolWithQuotes(),
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
  ): Expression<BVSort> = BVNOr(param1, param2)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expression -> expression.sort is BVSort })

        @Suppress("UNCHECKED_CAST")
        return BVNOr(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
    }
}

internal object BVXOrDecl :
    FunctionDeclLeftAssociative<BVSort, BVSort, BVSort>(
        "bvxor".toSymbolWithQuotes(),
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
  ): Expression<BVSort> = BVXOr(param1, param2, *varargs.toTypedArray())

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expression -> expression.sort is BVSort })

        @Suppress("UNCHECKED_CAST")
        return BVXOr(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
    }
}

internal object BVXNOrDecl :
    FunctionDecl2<BVSort, BVSort, BVSort>(
        "bvxnor".toSymbolWithQuotes(),
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
  ): Expression<BVSort> = BVXNOr(param1, param2)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expression -> expression.sort is BVSort })

        @Suppress("UNCHECKED_CAST")
        return BVXNOr(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
    }
}

internal object BVCompDecl :
    FunctionDecl2<BVSort, BVSort, BVSort>(
        "bvcomp".toSymbolWithQuotes(),
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
  ): Expression<BVSort> = BVComp(param1, param2)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expression -> expression.sort is BVSort })

        @Suppress("UNCHECKED_CAST")
        return BVComp(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
    }
}

internal object BVSubDecl :
    FunctionDecl2<BVSort, BVSort, BVSort>(
        "bvsub".toSymbolWithQuotes(),
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
  ): Expression<BVSort> = BVSub(param1, param2)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expression -> expression.sort is BVSort })

        @Suppress("UNCHECKED_CAST")
        return BVSub(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
    }
}

internal object BVSDivDecl :
    FunctionDecl2<BVSort, BVSort, BVSort>(
        "bvsdiv".toSymbolWithQuotes(),
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
  ): Expression<BVSort> = BVSDiv(param1, param2)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expression -> expression.sort is BVSort })

        @Suppress("UNCHECKED_CAST")
        return BVSDiv(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
    }
}

internal object BVSRemDecl :
    FunctionDecl2<BVSort, BVSort, BVSort>(
        "bvsrem".toSymbolWithQuotes(),
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
  ): Expression<BVSort> = BVSRem(param1, param2)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expression -> expression.sort is BVSort })

        @Suppress("UNCHECKED_CAST")
        return BVSRem(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
    }
}

internal object BVSModDecl :
    FunctionDecl2<BVSort, BVSort, BVSort>(
        "bvsmod".toSymbolWithQuotes(),
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
  ): Expression<BVSort> = BVSMod(param1, param2)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expression -> expression.sort is BVSort })

        @Suppress("UNCHECKED_CAST")
        return BVSMod(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
    }
}

internal object BVULeDecl :
    FunctionDecl2<BVSort, BVSort, BoolSort>(
        "bvule".toSymbolWithQuotes(),
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
  ): Expression<BoolSort> = BVULe(param1, param2)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expression -> expression.sort is BVSort })

        @Suppress("UNCHECKED_CAST")
        return BVULe(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
    }
}

internal object BVUGtDecl :
    FunctionDecl2<BVSort, BVSort, BoolSort>(
        "bvugt".toSymbolWithQuotes(),
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
  ): Expression<BoolSort> = BVUGt(param1, param2)


    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expression -> expression.sort is BVSort })

        @Suppress("UNCHECKED_CAST")
        return BVUGt(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
    }
}

internal object BVUGeDecl :
    FunctionDecl2<BVSort, BVSort, BoolSort>(
        "bvuge".toSymbolWithQuotes(),
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
  ): Expression<BoolSort> = BVUGe(param1, param2)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expression -> expression.sort is BVSort })

        @Suppress("UNCHECKED_CAST")
        return BVUGe(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
    }
}

internal object BVSLtDecl :
    FunctionDecl2<BVSort, BVSort, BoolSort>(
        "bvslt".toSymbolWithQuotes(),
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
  ): Expression<BoolSort> = BVSLt(param1, param2)


    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expression -> expression.sort is BVSort })

        @Suppress("UNCHECKED_CAST")
        return BVSLt(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
    }
}

internal object BVSLeDecl :
    FunctionDecl2<BVSort, BVSort, BoolSort>(
        "bvsle".toSymbolWithQuotes(),
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
  ): Expression<BoolSort> = BVSLe(param1, param2)


    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expression -> expression.sort is BVSort })

        @Suppress("UNCHECKED_CAST")
        return BVSLe(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
    }
}

internal object BVSGtDecl :
    FunctionDecl2<BVSort, BVSort, BoolSort>(
        "bvsgt".toSymbolWithQuotes(),
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
  ): Expression<BoolSort> = BVSGt(param1, param2)


    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expression -> expression.sort is BVSort })

        @Suppress("UNCHECKED_CAST")
        return BVSGt(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
    }
}

internal object BVSGeDecl :
    FunctionDecl2<BVSort, BVSort, BoolSort>(
        "bvsge".toSymbolWithQuotes(),
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
  ): Expression<BoolSort> = BVSGe(param1, param2)


    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expression -> expression.sort is BVSort })

        @Suppress("UNCHECKED_CAST")
        return BVSGe(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
    }
}

internal object BVAShrDecl :
    FunctionDecl2<BVSort, BVSort, BVSort>(
        "bvashr".toSymbolWithQuotes(),
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
  ): Expression<BVSort> = BVAShr(param1, param2)


    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BVSort> {
        require(args.size == 2)
        require(indices.isEmpty())
        require(args.all { expression -> expression.sort is BVSort })

        @Suppress("UNCHECKED_CAST")
        return BVAShr(args[0] as Expression<BVSort>, args[1] as Expression<BVSort>)
    }
}

internal object RepeatDecl :
    FunctionDecl1<BVSort, BVSort>(
        "repeat".toSymbolWithQuotes(),
        emptySet(),
        BVSort.fromSymbol("m"),
        setOf(SymbolIndex("j")),
        emptySet(),
        BVSort.fromSymbol("n")) {
  override fun buildExpression(param: Expression<BVSort>, bindings: Bindings): Expression<BVSort> =
      Repeat(bindings["j"].numeral, param)

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
    FunctionDecl1<BVSort, BVSort>(
        "zero_extend".toSymbolWithQuotes(),
        emptySet(),
        BVSort.fromSymbol("m"),
        setOf(SymbolIndex("i")),
        emptySet(),
        BVSort.fromSymbol("n")) {
  override fun buildExpression(param: Expression<BVSort>, bindings: Bindings): Expression<BVSort> =
      ZeroExtend(bindings["i"].numeral, param)

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
    FunctionDecl1<BVSort, BVSort>(
        "sign_extend".toSymbolWithQuotes(),
        emptySet(),
        BVSort.fromSymbol("m"),
        setOf(SymbolIndex("i")),
        emptySet(),
        BVSort.fromSymbol("n")) {
  override fun buildExpression(param: Expression<BVSort>, bindings: Bindings): Expression<BVSort> =
      ZeroExtend(bindings["i"].numeral, param)

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
    FunctionDecl1<BVSort, BVSort>(
        "rotate_left".toSymbolWithQuotes(),
        emptySet(),
        BVSort.fromSymbol("m"),
        setOf(SymbolIndex("i")),
        emptySet(),
        BVSort.fromSymbol("n")) {
  override fun buildExpression(param: Expression<BVSort>, bindings: Bindings): Expression<BVSort> =
      RotateLeft(bindings["i"].numeral, param)

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
    FunctionDecl1<BVSort, BVSort>(
        "rotate_right".toSymbolWithQuotes(),
        emptySet(),
        BVSort.fromSymbol("m"),
        setOf(SymbolIndex("i")),
        emptySet(),
        BVSort.fromSymbol("n")) {
  override fun buildExpression(param: Expression<BVSort>, bindings: Bindings): Expression<BVSort> =
      RotateRight(bindings["i"].numeral, param)

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
    FunctionDecl1<IntSort, IntSort>(
        "-".toSymbolWithQuotes(), emptySet(), IntSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param: Expression<IntSort>,
      bindings: Bindings
  ): Expression<IntSort> = IntNeg(param)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<IntSort> {
        require(args.size == 1)
        return IntNeg(args.single() castTo IntSort)
    }
}

internal object IntSubDecl :
    FunctionDeclLeftAssociative<IntSort, IntSort, IntSort>(
        "-".toSymbolWithQuotes(), emptySet(), IntSort, IntSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param1: Expression<IntSort>,
      param2: Expression<IntSort>,
      varargs: List<Expression<IntSort>>,
      bindings: Bindings
  ): Expression<IntSort> = IntSub(listOf(param1, param2) + varargs)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<IntSort> {
        require(args.size >= 2)
        return IntSub(args.map { expr -> expr castTo IntSort })
    }
}

/** Combined function declaration for overloaded '-' operator */
internal object IntNegSubDecl :
    FunctionDecl<IntSort>(
        "-".toSymbolWithQuotes(),
        emptySet(),
        listOf(IntSort),
        emptySet(),
        emptySet(),
        IntSort,
        Associativity.NONE,
        null) {
  override fun buildExpression(
      args: List<Expression<*>>,
      functionIndices: List<NumeralIndex>
  ): Expression<IntSort> {
    require(args.isNotEmpty())

    return if (args.size == 1) {
      IntNegDecl.buildExpression(args, functionIndices)
    } else {
      IntSubDecl.buildExpression(args, functionIndices)
    }
  }

  override fun bindParametersTo(args: List<Sort>, indices: List<NumeralIndex>) =
      if (args.size == 1) {
        IntNegDecl.bindParametersTo(args, indices)
      } else {
        IntSubDecl.bindParametersTo(args, indices)
      }

  override fun accepts(args: List<Sort>, indices: List<NumeralIndex>) =
      if (args.size == 1) {
        IntNegDecl.accepts(args, indices)
      } else {
        IntSubDecl.accepts(args, indices)
      }

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<IntSort> = if(args.size == 1) {
        IntNegDecl.constructDynamic(args, indices)
    } else if(args.size > 1) {
        IntSubDecl.constructDynamic(args, indices)
    } else {
        throw IllegalArgumentException()
    }
}

internal object IntAddDecl :
    FunctionDeclLeftAssociative<IntSort, IntSort, IntSort>(
        "+".toSymbolWithQuotes(), emptySet(), IntSort, IntSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param1: Expression<IntSort>,
      param2: Expression<IntSort>,
      varargs: List<Expression<IntSort>>,
      bindings: Bindings
  ): Expression<IntSort> = IntAdd(listOf(param1, param2) + varargs)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<IntSort> {
        require(args.size >= 2)
        return IntAdd(args.map { expr -> expr castTo IntSort })
    }
}

internal object IntMulDecl :
    FunctionDeclLeftAssociative<IntSort, IntSort, IntSort>(
        "*".toSymbolWithQuotes(), emptySet(), IntSort, IntSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param1: Expression<IntSort>,
      param2: Expression<IntSort>,
      varargs: List<Expression<IntSort>>,
      bindings: Bindings
  ): Expression<IntSort> = IntMul(listOf(param1, param2) + varargs)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<IntSort> {
        require(args.size >= 2)
        return IntMul(args.map { expr -> expr castTo IntSort })
    }
}

internal object IntDivDecl :
    FunctionDeclLeftAssociative<IntSort, IntSort, IntSort>(
        "div".toSymbolWithQuotes(), emptySet(), IntSort, IntSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param1: Expression<IntSort>,
      param2: Expression<IntSort>,
      varargs: List<Expression<IntSort>>,
      bindings: Bindings
  ): Expression<IntSort> = IntDiv(listOf(param1, param2) + varargs)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<IntSort> {
        require(args.size >= 2)
        return IntDiv(args.map { expr -> expr castTo IntSort })
    }
}

internal object ModDecl :
    FunctionDecl2<IntSort, IntSort, IntSort>(
        "mod".toSymbolWithQuotes(), emptySet(), IntSort, IntSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param1: Expression<IntSort>,
      param2: Expression<IntSort>,
      bindings: Bindings
  ): Expression<IntSort> = Mod(param1, param2)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<IntSort> {
        require(args.size == 2)
        return Mod(args[0] castTo IntSort, args[1] castTo IntSort)
    }
}

internal object AbsDecl :
    FunctionDecl1<IntSort, IntSort>(
        "abs".toSymbolWithQuotes(), emptySet(), IntSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param: Expression<IntSort>,
      bindings: Bindings
  ): Expression<IntSort> = Abs(param)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<IntSort> {
        require(args.size == 1)
        return IntNeg(args.single() castTo IntSort)
    }
}

internal object IntLessEqDecl :
    FunctionDeclChainable<IntSort>(
        "<=".toSymbolWithQuotes(), emptySet(), IntSort, IntSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<IntSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = IntLessEq(varargs)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size >= 2)
        return IntLessEq(args.map { expr -> expr castTo IntSort })
    }
}

internal object IntLessDecl :
    FunctionDeclChainable<IntSort>(
        "<".toSymbolWithQuotes(), emptySet(), IntSort, IntSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<IntSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = IntLess(varargs)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size >= 2)
        return IntLess(args.map { expr -> expr castTo IntSort })
    }
}

internal object IntGreaterEqDecl :
    FunctionDeclChainable<IntSort>(
        ">=".toSymbolWithQuotes(), emptySet(), IntSort, IntSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<IntSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = IntGreaterEq(varargs)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size >= 2)
        return IntGreaterEq(args.map { expr -> expr castTo IntSort })
    }
}

internal object IntGreaterDecl :
    FunctionDeclChainable<IntSort>(
        ">".toSymbolWithQuotes(), emptySet(), IntSort, IntSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<IntSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = IntGreater(varargs)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size >= 2)
        return IntGreater(args.map { expr -> expr castTo IntSort })
    }
}

internal object DivisibleDecl :
    FunctionDecl1<IntSort, BoolSort>(
        "divisible".toSymbolWithQuotes(),
        emptySet(),
        IntSort,
        setOf(SymbolIndex("n")),
        emptySet(),
        BoolSort) {
  override fun buildExpression(
      param: Expression<IntSort>,
      bindings: Bindings
  ): Expression<BoolSort> = Divisible(bindings["n"].numeral, param)

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
    FunctionDecl1<RealSort, RealSort>(
        "-".toSymbolWithQuotes(), emptySet(), RealSort, emptySet(), emptySet(), RealSort) {
  override fun buildExpression(
      param: Expression<RealSort>,
      bindings: Bindings
  ): Expression<RealSort> = RealNeg(param)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RealSort> {
        require(args.size == 1)
        return RealNeg(args.single() castTo RealSort)
    }
}

internal object RealSubDecl :
    FunctionDeclLeftAssociative<RealSort, RealSort, RealSort>(
        "-".toSymbolWithQuotes(),
        emptySet(),
        RealSort,
        RealSort,
        emptySet(),
        emptySet(),
        RealSort) {
  override fun buildExpression(
      param1: Expression<RealSort>,
      param2: Expression<RealSort>,
      varargs: List<Expression<RealSort>>,
      bindings: Bindings
  ): Expression<RealSort> = RealSub(listOf(param1, param2) + varargs)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RealSort> {
        require(args.size >= 2)
        return RealSub(args.map { expr -> expr castTo RealSort })
    }
}

/** Combined function declaration for overloaded '-' operator */
internal object RealNegSubDecl :
    FunctionDecl<RealSort>(
        "-".toSymbolWithQuotes(),
        emptySet(),
        listOf(RealSort),
        emptySet(),
        emptySet(),
        RealSort,
        Associativity.NONE,
        null) {
  override fun buildExpression(
      args: List<Expression<*>>,
      functionIndices: List<NumeralIndex>
  ): Expression<RealSort> {
    require(args.isNotEmpty())

    return if (args.size == 1) {
      RealNegDecl.buildExpression(args, functionIndices)
    } else {
      RealSubDecl.buildExpression(args, functionIndices)
    }
  }

  override fun bindParametersTo(args: List<Sort>, indices: List<NumeralIndex>) =
      if (args.size == 1) {
        RealNegDecl.bindParametersTo(args, indices)
      } else {
        RealSubDecl.bindParametersTo(args, indices)
      }

  override fun accepts(args: List<Sort>, indices: List<NumeralIndex>) =
      if (args.size == 1) {
        RealNegDecl.accepts(args, indices)
      } else {
        RealSubDecl.accepts(args, indices)
      }

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RealSort> = if(args.size == 1) {
        RealNegDecl.constructDynamic(args, indices)
    } else if(args.size > 1) {
        RealSubDecl.constructDynamic(args, indices)
    } else {
        throw IllegalArgumentException()
    }
}

internal object RealAddDecl :
    FunctionDeclLeftAssociative<RealSort, RealSort, RealSort>(
        "+".toSymbolWithQuotes(),
        emptySet(),
        RealSort,
        RealSort,
        emptySet(),
        emptySet(),
        RealSort) {
  override fun buildExpression(
      param1: Expression<RealSort>,
      param2: Expression<RealSort>,
      varargs: List<Expression<RealSort>>,
      bindings: Bindings
  ): Expression<RealSort> = RealAdd(listOf(param1, param2) + varargs)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RealSort> {
        require(args.size >= 2)
        return RealAdd(args.map { expr -> expr castTo RealSort })
    }
}

internal object RealMulDecl :
    FunctionDeclLeftAssociative<RealSort, RealSort, RealSort>(
        "*".toSymbolWithQuotes(),
        emptySet(),
        RealSort,
        RealSort,
        emptySet(),
        emptySet(),
        RealSort) {
  override fun buildExpression(
      param1: Expression<RealSort>,
      param2: Expression<RealSort>,
      varargs: List<Expression<RealSort>>,
      bindings: Bindings
  ): Expression<RealSort> = RealMul(listOf(param1, param2) + varargs)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RealSort> {
        require(args.size >= 2)
        return RealMul(args.map { expr -> expr castTo RealSort })
    }
}

internal object RealDivDecl :
    FunctionDeclLeftAssociative<RealSort, RealSort, RealSort>(
        "/".toSymbolWithQuotes(),
        emptySet(),
        RealSort,
        RealSort,
        emptySet(),
        emptySet(),
        RealSort) {
  override fun buildExpression(
      param1: Expression<RealSort>,
      param2: Expression<RealSort>,
      varargs: List<Expression<RealSort>>,
      bindings: Bindings
  ): Expression<RealSort> = RealDiv(listOf(param1, param2) + varargs)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RealSort> {
        require(args.size >= 2)
        return RealDiv(args.map { expr -> expr castTo RealSort })
    }
}

internal object RealLessEqDecl :
    FunctionDeclChainable<RealSort>(
        "<=".toSymbolWithQuotes(), emptySet(), RealSort, RealSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<RealSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = RealLessEq(varargs)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size >= 2)
        return RealLessEq(args.map { expr -> expr castTo RealSort })
    }
}

internal object RealLessDecl :
    FunctionDeclChainable<RealSort>(
        "<".toSymbolWithQuotes(), emptySet(), RealSort, RealSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<RealSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = RealLess(varargs)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size >= 2)
        return RealLess(args.map { expr -> expr castTo RealSort })
    }
}

internal object RealGreaterEqDecl :
    FunctionDeclChainable<RealSort>(
        ">=".toSymbolWithQuotes(), emptySet(), RealSort, RealSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<RealSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = RealGreaterEq(varargs)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<BoolSort> {
        require(args.size >= 2)
        return RealGreaterEq(args.map { expr -> expr castTo RealSort })
    }
}

internal object RealGreaterDecl :
    FunctionDeclChainable<RealSort>(
        ">".toSymbolWithQuotes(), emptySet(), RealSort, RealSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<RealSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = RealGreater(varargs)

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
    FunctionDecl1<IntSort, RealSort>(
        "to_real".toSymbolWithQuotes(), emptySet(), IntSort, emptySet(), emptySet(), RealSort) {
  override fun buildExpression(
      param: Expression<IntSort>,
      bindings: Bindings
  ): Expression<RealSort> = ToReal(param)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RealSort> {
        require(args.size == 1)
        return ToReal(args.single() castTo IntSort)
    }
}

internal object ToIntDecl :
    FunctionDecl1<RealSort, IntSort>(
        "to_real".toSymbolWithQuotes(), emptySet(), RealSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param: Expression<RealSort>,
      bindings: Bindings
  ): Expression<IntSort> = ToInt(param)

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<IntSort> {
        require(args.size == 1)
        return ToInt(args.single() castTo RealSort)
    }
}

internal object IsIntDecl :
    FunctionDecl1<RealSort, BoolSort>(
        "to_real".toSymbolWithQuotes(), emptySet(), RealSort, emptySet(), emptySet(), BoolSort) {
  override fun buildExpression(
      param: Expression<RealSort>,
      bindings: Bindings
  ): Expression<BoolSort> = IsInt(param)

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
    FunctionDecl0<RoundingMode>(
        "roundNearestTiesToEven".toSymbolWithQuotes(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> =
      RoundNearestTiesToEven

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RoundingMode> {
        require(args.isEmpty())
        return RoundNearestTiesToEven
    }
}

internal object RNEDecl :
    FunctionDecl0<RoundingMode>("RNE".toSymbolWithQuotes(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RNE

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RoundingMode> {
        require(args.isEmpty())
        return RNE
    }
}

internal object RoundNearestTiesToAwayDecl :
    FunctionDecl0<RoundingMode>(
        "roundNearestTiesToAway".toSymbolWithQuotes(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> =
      RoundNearestTiesToAway

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RoundingMode> {
        require(args.isEmpty())
        return RoundNearestTiesToAway
    }
}

internal object RNADecl :
    FunctionDecl0<RoundingMode>("RNA".toSymbolWithQuotes(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RNA

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RoundingMode> {
        require(args.isEmpty())
        return RNA
    }
}

internal object RoundTowardPositiveDecl :
    FunctionDecl0<RoundingMode>(
        "roundTowardPositive".toSymbolWithQuotes(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RoundTowardPositive

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RoundingMode> {
        require(args.isEmpty())
        return RoundTowardPositive
    }
}

internal object RTPDecl :
    FunctionDecl0<RoundingMode>("RTP".toSymbolWithQuotes(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RTP

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RoundingMode> {
        require(args.isEmpty())
        return RTP
    }
}

internal object RoundTowardNegativeDecl :
    FunctionDecl0<RoundingMode>(
        "RoundTowardNegative".toSymbolWithQuotes(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RoundTowardNegative

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RoundingMode> {
        require(args.isEmpty())
        return RoundTowardNegative
    }
}

internal object RTNDecl :
    FunctionDecl0<RoundingMode>("RTN".toSymbolWithQuotes(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RTN

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RoundingMode> {
        require(args.isEmpty())
        return RTN
    }
}

internal object RoundTowardZeroDecl :
    FunctionDecl0<RoundingMode>(
        "RoundTowardZero".toSymbolWithQuotes(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RoundTowardZero

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RoundingMode> {
        require(args.isEmpty())
        return RoundTowardZero
    }
}

internal object RTZDecl :
    FunctionDecl0<RoundingMode>("RTZ".toSymbolWithQuotes(), emptySet(), emptySet(), RoundingMode) {
  override fun buildExpression(bindings: Bindings): Expression<RoundingMode> = RTZ

    override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<RoundingMode> {
        require(args.isEmpty())
        return RTZ
    }
}

internal object FPLiteralDecl :
    FunctionDecl3<BVSort, BVSort, BVSort, FPSort>(
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
    FunctionDecl0<FPSort>(
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
    FunctionDecl0<FPSort>(
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
    FunctionDecl0<FPSort>(
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
    FunctionDecl0<FPSort>(
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
    FunctionDecl0<FPSort>(
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
    FunctionDecl1<FPSort, FPSort>(
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
    FunctionDecl1<FPSort, FPSort>(
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
    FunctionDecl3<RoundingMode, FPSort, FPSort, FPSort>(
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
    FunctionDecl3<RoundingMode, FPSort, FPSort, FPSort>(
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
    FunctionDecl3<RoundingMode, FPSort, FPSort, FPSort>(
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
    FunctionDecl3<RoundingMode, FPSort, FPSort, FPSort>(
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
    FunctionDecl4<RoundingMode, FPSort, FPSort, FPSort, FPSort>(
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
    FunctionDecl2<RoundingMode, FPSort, FPSort>(
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
    FunctionDecl2<FPSort, FPSort, FPSort>(
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
    FunctionDecl2<RoundingMode, FPSort, FPSort>(
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
    FunctionDecl2<FPSort, FPSort, FPSort>(
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
    FunctionDecl2<FPSort, FPSort, FPSort>(
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
    FunctionDeclChainable<FPSort>(
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
    FunctionDeclChainable<FPSort>(
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
    FunctionDeclChainable<FPSort>(
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
    FunctionDeclChainable<FPSort>(
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
    FunctionDeclChainable<FPSort>(
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
    FunctionDecl1<FPSort, BoolSort>(
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
    FunctionDecl1<FPSort, BoolSort>(
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
    FunctionDecl1<FPSort, BoolSort>(
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
    FunctionDecl1<FPSort, BoolSort>(
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
    FunctionDecl1<FPSort, BoolSort>(
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
    FunctionDecl1<FPSort, BoolSort>(
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
    FunctionDecl1<FPSort, BoolSort>(
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
    FunctionDecl1<BVSort, FPSort>(
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
    FunctionDecl2<RoundingMode, FPSort, FPSort>(
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
    FunctionDecl2<RoundingMode, RealSort, FPSort>(
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
    FunctionDecl2<RoundingMode, BVSort, FPSort>(
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
    FunctionDecl2<RoundingMode, BVSort, FPSort>(
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
    FunctionDecl2<RoundingMode, FPSort, BVSort>(
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
    FunctionDecl2<RoundingMode, FPSort, BVSort>(
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
    FunctionDecl1<FPSort, RealSort>(
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
    FunctionDecl2<ArraySort<Sort, Sort>, Sort, Sort>(
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
    FunctionDecl3<ArraySort<Sort, Sort>, Sort, Sort, ArraySort<Sort, Sort>>(
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
    FunctionDecl0<StringSort>(
        "char".toSymbolWithQuotes(), emptySet(), setOf("H".idx()), StringSort) {
  override fun buildExpression(bindings: Bindings): Expression<StringSort> = TODO()
}

internal object StrConcatDecl :
    FunctionDeclLeftAssociative<StringSort, StringSort, StringSort>(
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
}

internal object StrLengthDecl :
    FunctionDecl1<StringSort, IntSort>(
        "str.len".toSymbolWithQuotes(), emptySet(), StringSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param: Expression<StringSort>,
      bindings: Bindings
  ): Expression<IntSort> = StrLength(param)
}

internal object StrLexOrderDecl :
    FunctionDeclChainable<StringSort>(
        "str.<".toSymbolWithQuotes(), emptySet(), StringSort, StringSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<StringSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = StrLexOrder(varargs)
}

internal object ToRegexDecl :
    FunctionDecl1<StringSort, RegLan>(
        "str.to_reg".toSymbolWithQuotes(), emptySet(), StringSort, emptySet(), emptySet(), RegLan) {
  override fun buildExpression(
      param: Expression<StringSort>,
      bindings: Bindings
  ): Expression<RegLan> = ToRegex(param)
}

internal object InRegexDecl :
    FunctionDecl2<StringSort, RegLan, BoolSort>(
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
}

internal object RegexNoneDecl :
    FunctionDecl0<RegLan>("re.none".toSymbolWithQuotes(), emptySet(), emptySet(), RegLan) {
  override fun buildExpression(bindings: Bindings): Expression<RegLan> = RegexNone
}

internal object RegexAllDecl :
    FunctionDecl0<RegLan>("re.all".toSymbolWithQuotes(), emptySet(), emptySet(), RegLan) {
  override fun buildExpression(bindings: Bindings): Expression<RegLan> = RegexAll
}

internal object RegexAllCharDecl :
    FunctionDecl0<RegLan>("re.allchar".toSymbolWithQuotes(), emptySet(), emptySet(), RegLan) {
  override fun buildExpression(bindings: Bindings): Expression<RegLan> = RegexAllChar
}

internal object RegexConcatDecl :
    FunctionDeclLeftAssociative<RegLan, RegLan, RegLan>(
        "re.++".toSymbolWithQuotes(), emptySet(), RegLan, RegLan, emptySet(), emptySet(), RegLan) {
  override fun buildExpression(
      param1: Expression<RegLan>,
      param2: Expression<RegLan>,
      varargs: List<Expression<RegLan>>,
      bindings: Bindings
  ): Expression<RegLan> = RegexConcat(param1, param2, *varargs.toTypedArray())
}

internal object RegexUnionDecl :
    FunctionDeclLeftAssociative<RegLan, RegLan, RegLan>(
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
}

internal object RegexIntersecDecl :
    FunctionDeclLeftAssociative<RegLan, RegLan, RegLan>(
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
}

internal object RegexStarDecl :
    FunctionDecl1<RegLan, RegLan>(
        "re.*".toSymbolWithQuotes(), emptySet(), RegLan, emptySet(), emptySet(), RegLan) {
  override fun buildExpression(param: Expression<RegLan>, bindings: Bindings): Expression<RegLan> =
      RegexStar(param)
}

internal object StrRefLexOrderDecl :
    FunctionDeclChainable<StringSort>(
        "str.<=".toSymbolWithQuotes(), emptySet(), StringSort, StringSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<StringSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = StrRefLexOrder(varargs)
}

internal object StrAtDecl :
    FunctionDecl2<StringSort, IntSort, StringSort>(
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
}

internal object StrSubstringDecl :
    FunctionDecl3<StringSort, IntSort, IntSort, StringSort>(
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
}

internal object StrPrefixOfDecl :
    FunctionDecl2<StringSort, StringSort, BoolSort>(
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
}

internal object StrSuffixOfDecl :
    FunctionDecl2<StringSort, StringSort, BoolSort>(
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
}

internal object StrContainsDecl :
    FunctionDecl2<StringSort, StringSort, BoolSort>(
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
}

internal object StrIndexOfDecl :
    FunctionDecl3<StringSort, StringSort, IntSort, IntSort>(
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
}

internal object StrReplaceDecl :
    FunctionDecl3<StringSort, StringSort, StringSort, StringSort>(
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
}

internal object StrReplaceAllDecl :
    FunctionDecl3<StringSort, StringSort, StringSort, StringSort>(
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
}

internal object StrReplaceRegexDecl :
    FunctionDecl3<StringSort, RegLan, StringSort, StringSort>(
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
}

internal object StrReplaceAllRegexDecl :
    FunctionDecl3<StringSort, RegLan, StringSort, StringSort>(
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
}

internal object RegexCompDecl :
    FunctionDecl1<RegLan, RegLan>(
        "re.comp".toSymbolWithQuotes(), emptySet(), RegLan, emptySet(), emptySet(), RegLan) {
  override fun buildExpression(param: Expression<RegLan>, bindings: Bindings): Expression<RegLan> =
      RegexComp(param)
}

internal object RegexDiffDecl :
    FunctionDeclLeftAssociative<RegLan, RegLan, RegLan>(
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
}

internal object RegexPlusDecl :
    FunctionDecl1<RegLan, RegLan>(
        "re.+".toSymbolWithQuotes(), emptySet(), RegLan, emptySet(), emptySet(), RegLan) {
  override fun buildExpression(param: Expression<RegLan>, bindings: Bindings): Expression<RegLan> =
      RegexPlus(param)
}

internal object RegexOptionDecl :
    FunctionDecl1<RegLan, RegLan>(
        "re.opt".toSymbolWithQuotes(), emptySet(), RegLan, emptySet(), emptySet(), RegLan) {
  override fun buildExpression(param: Expression<RegLan>, bindings: Bindings): Expression<RegLan> =
      RegexOption(param)
}

internal object RegexRangeDecl :
    FunctionDecl2<StringSort, StringSort, RegLan>(
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
}

internal object RegexPowerDecl :
    FunctionDecl1<RegLan, RegLan>(
        "re.^".toSymbolWithQuotes(), emptySet(), RegLan, setOf("n".idx()), emptySet(), RegLan) {
  override fun buildExpression(param: Expression<RegLan>, bindings: Bindings): Expression<RegLan> =
      RegexPower(param, bindings["n"].numeral)
}

internal object RegexLoopDecl :
    FunctionDecl1<RegLan, RegLan>(
        "re.loop".toSymbolWithQuotes(),
        emptySet(),
        RegLan,
        setOf("n1".idx(), "n2".idx()),
        emptySet(),
        RegLan) {
  override fun buildExpression(param: Expression<RegLan>, bindings: Bindings): Expression<RegLan> =
      RegexLoop(param, bindings["n1"].numeral, bindings["n2"].numeral)
}

internal object StrIsDigitDecl :
    FunctionDecl1<StringSort, BoolSort>(
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
}

internal object StrToCodeDecl :
    FunctionDecl1<StringSort, IntSort>(
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
}

internal object StrFromCodeDecl :
    FunctionDecl1<IntSort, StringSort>(
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
}

internal object StrToIntDecl :
    FunctionDecl1<StringSort, IntSort>(
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
}

internal object StrFromIntDecl :
    FunctionDecl1<IntSort, StringSort>(
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
}

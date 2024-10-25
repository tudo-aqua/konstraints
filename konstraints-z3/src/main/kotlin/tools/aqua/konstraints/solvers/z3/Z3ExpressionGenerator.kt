/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2024 The Konstraints Authors
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

package tools.aqua.konstraints.solvers.z3

import com.microsoft.z3.*
import com.microsoft.z3.ArraySort as Z3ArraySort
import com.microsoft.z3.BoolSort as Z3BoolSort
import com.microsoft.z3.CharSort
import com.microsoft.z3.FPRMSort
import com.microsoft.z3.FPSort as Z3FPSort
import com.microsoft.z3.IntSort as Z3IntSort
import com.microsoft.z3.ReSort
import com.microsoft.z3.RealSort as Z3RealSort
import com.microsoft.z3.SeqSort
import com.microsoft.z3.Sort as Z3Sort
import com.microsoft.z3.UninterpretedSort
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.theories.*

fun makeLeftAssoc(
    expressions: List<Expression<*>>,
    context: Z3Context,
    operation: (Expr<*>, Expr<*>) -> Expr<*>
): Expr<*> {
  return if (expressions.size == 2) {
    operation(expressions[0].z3ify(context), expressions[1].z3ify(context))
  } else {
    operation(
        makeLeftAssoc(expressions.dropLast(1), context, operation),
        expressions.last().z3ify(context))
  }
}

/**
 * Build a right associative expression using [operation] (e.g. =>) S1 and S2 are Z3 target sorts, R
 * is a konstraints sort of the original expression
 */
fun makeRightAssoc(
    expressions: List<Expression<*>>,
    context: Z3Context,
    operation: (Expr<*>, Expr<*>) -> Expr<*>
): Expr<*> {
  return if (expressions.size == 2) {
    operation(expressions[0].z3ify(context), expressions[1].z3ify(context))
  } else {
    operation(
        expressions.first().z3ify(context), makeRightAssoc(expressions.drop(1), context, operation))
  }
}

@JvmName("z3ifyAny")
fun Expression<*>.z3ify(context: Z3Context): Expr<*> {
  // Z3 ignores annotations
  if (this is AnnotatedExpression) {
    return this.term.z3ify(context)
  }

  return when (this.sort) {
    is BoolSort -> (this castTo BoolSort).z3ify(context)
    is BVSort -> (this as Expression<BVSort>).z3ify(context)
    is IntSort -> (this castTo IntSort).z3ify(context)
    is RealSort -> (this castTo RealSort).z3ify(context)
    is RoundingMode -> (this castTo RoundingMode).z3ify(context)
    is FPSort -> (this as Expression<FPSort>).z3ify(context)
    is FP16 -> (this as Expression<FPSort>).z3ify(context)
    is FP32 -> (this as Expression<FPSort>).z3ify(context)
    is FP64 -> (this as Expression<FPSort>).z3ify(context)
    is FP128 -> (this as Expression<FPSort>).z3ify(context)
    is StringSort -> (this castTo StringSort).z3ify(context)
    is RegLan -> (this castTo RegLan).z3ify(context)
    is UserDefinedSort -> (this as Expression<UserDefinedSort>).z3ify(context)
    is ArraySort<*, *> -> (this as Expression<ArraySort<*, *>>).z3ify(context)
    else -> throw RuntimeException("Unknown sort ${this.sort}")
  }
}

@JvmName("z3ifyIteBool")
fun Ite<BoolSort>.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkITE(
        this.statement.z3ify(context),
        this.then.z3ify(context) as Expr<Z3BoolSort>,
        this.otherwise.z3ify(context) as Expr<Z3BoolSort>)

@JvmName("z3ifyIteBitVec")
fun Ite<BVSort>.z3ify(context: Z3Context): Expr<BitVecSort> =
    context.context.mkITE(
        this.statement.z3ify(context),
        this.then.z3ify(context) as Expr<BitVecSort>,
        this.otherwise.z3ify(context) as Expr<BitVecSort>)

@JvmName("z3ifyIteInt")
fun Ite<IntSort>.z3ify(context: Z3Context): Expr<Z3IntSort> =
    context.context.mkITE(
        this.statement.z3ify(context),
        this.then.z3ify(context) as Expr<Z3IntSort>,
        this.otherwise.z3ify(context) as Expr<Z3IntSort>)

@JvmName("z3ifyIteReal")
fun Ite<RealSort>.z3ify(context: Z3Context): Expr<Z3RealSort> =
    context.context.mkITE(
        this.statement.z3ify(context),
        this.then.z3ify(context) as Expr<Z3RealSort>,
        this.otherwise.z3ify(context) as Expr<Z3RealSort>)

@JvmName("z3ifyIteFP")
fun Ite<FPSort>.z3ify(context: Z3Context): Expr<Z3FPSort> =
    context.context.mkITE(
        this.statement.z3ify(context),
        this.then.z3ify(context) as Expr<Z3FPSort>,
        this.otherwise.z3ify(context) as Expr<Z3FPSort>)

@JvmName("z3ifyIteRM")
fun Ite<RoundingMode>.z3ify(context: Z3Context): Expr<FPRMSort> =
    context.context.mkITE(
        this.statement.z3ify(context),
        this.then.z3ify(context) as Expr<FPRMSort>,
        this.otherwise.z3ify(context) as Expr<FPRMSort>)

@JvmName("z3ifyIteString")
fun Ite<StringSort>.z3ify(context: Z3Context): Expr<SeqSort<CharSort>> =
    context.context.mkITE(
        this.statement.z3ify(context),
        this.then.z3ify(context) as Expr<SeqSort<CharSort>>,
        this.otherwise.z3ify(context) as Expr<SeqSort<CharSort>>)

@JvmName("z3ifyIteFreeSort")
fun Ite<UserDefinedSort>.z3ify(context: Z3Context): Expr<UninterpretedSort> =
    context.context.mkITE(
        this.statement.z3ify(context),
        this.then.z3ify(context) as Expr<UninterpretedSort>,
        this.otherwise.z3ify(context) as Expr<UninterpretedSort>)

@JvmName("z3ifyArraySelectBool")
fun ArraySelect<*, BoolSort>.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkSelect(
        this.array.z3ify(context) as Expr<Z3ArraySort<Z3Sort, Z3BoolSort>>,
        this.index.z3ify(context) as Expr<Z3Sort>)

@JvmName("z3ifyArraySelectBitVec")
fun ArraySelect<*, BVSort>.z3ify(context: Z3Context): Expr<BitVecSort> =
    context.context.mkSelect(
        this.array.z3ify(context) as Expr<Z3ArraySort<Z3Sort, BitVecSort>>,
        this.index.z3ify(context) as Expr<Z3Sort>)

@JvmName("z3ifyArraySelectInt")
fun ArraySelect<*, IntSort>.z3ify(context: Z3Context): Expr<Z3IntSort> =
    context.context.mkSelect(
        this.array.z3ify(context) as Expr<Z3ArraySort<Z3Sort, Z3IntSort>>,
        this.index.z3ify(context) as Expr<Z3Sort>)

@JvmName("z3ifyArraySelectReal")
fun ArraySelect<*, RealSort>.z3ify(context: Z3Context): Expr<Z3RealSort> =
    context.context.mkSelect(
        this.array.z3ify(context) as Expr<Z3ArraySort<Z3Sort, Z3RealSort>>,
        this.index.z3ify(context) as Expr<Z3Sort>)

@JvmName("z3ifyArraySelectFP")
fun ArraySelect<*, FPSort>.z3ify(context: Z3Context): Expr<Z3FPSort> =
    context.context.mkSelect(
        this.array.z3ify(context) as Expr<Z3ArraySort<Z3Sort, Z3FPSort>>,
        this.index.z3ify(context) as Expr<Z3Sort>)

@JvmName("z3ifyArraySelectRM")
fun ArraySelect<*, RoundingMode>.z3ify(context: Z3Context): Expr<FPRMSort> =
    context.context.mkSelect(
        this.array.z3ify(context) as Expr<Z3ArraySort<Z3Sort, FPRMSort>>,
        this.index.z3ify(context) as Expr<Z3Sort>)

@JvmName("z3ifyArraySelectString")
fun ArraySelect<*, StringSort>.z3ify(context: Z3Context): Expr<SeqSort<CharSort>> =
    context.context.mkSelect(
        this.array.z3ify(context) as Expr<Z3ArraySort<Z3Sort, SeqSort<CharSort>>>,
        this.index.z3ify(context) as Expr<Z3Sort>)

@JvmName("z3ifyArraySelectFreeSort")
fun ArraySelect<*, UserDefinedSort>.z3ify(context: Z3Context): Expr<UninterpretedSort> =
    context.context.mkSelect(
        this.array.z3ify(context) as Expr<Z3ArraySort<Z3Sort, UninterpretedSort>>,
        this.index.z3ify(context) as Expr<Z3Sort>)

@JvmName("z3ifyBool")
fun Expression<BoolSort>.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    when (this) {
      is LocalExpression -> context.localVariable(this.name, this.sort.z3ify(context))
      is LetExpression -> context.let(this.bindings) { this.inner.z3ify(context) }
      is ForallExpression ->
          context.bind(this.vars) { boundVars ->
            context.context.mkForall(
                boundVars.toTypedArray(), /* bound variables */
                this.term.z3ify(context), /* inner term */
                0, /* weight (z3 doc says to pass 0 by default) */
                emptyArray(), /* patterns */
                emptyArray(), /* anti-patterns */
                context.context.mkSymbol("exists"), /* quantifier id */
                context.context.mkSymbol("skolemID"), /* skolem id */
            )
          }
      is ExistsExpression ->
          context.bind(this.vars) { boundVars ->
            context.context.mkExists(
                boundVars.toTypedArray(), /* bound variables */
                this.term.z3ify(context), /* inner term */
                0, /* weight (z3 doc says to pass 0 by default) */
                emptyArray(), /* patterns */
                emptyArray(), /* anti-patterns */
                context.context.mkSymbol("exists"), /* quantifier id */
                context.context.mkSymbol("skolemID"), /* skolem id */
            )
          }
      is BoundVariable -> context.boundVariable(this.name, this.sort.z3ify(context))
      // annotations are usually handled by the most generic z3ify function
      // this is only needed in case the first term in an assert is annotated
      is AnnotatedExpression -> this.term.z3ify(context)
      is Ite -> this.z3ify(context)
      is True -> this.z3ify(context)
      is False -> this.z3ify(context)
      is Not -> this.z3ify(context)
      is Implies -> this.z3ify(context)
      is And -> this.z3ify(context)
      is Or -> this.z3ify(context)
      is XOr -> this.z3ify(context)
      is Equals<*> -> this.z3ify(context)
      is Distinct -> this.z3ify(context)
      is BVUlt -> this.z3ify(context)
      is BVULe -> this.z3ify(context)
      is BVUGt -> this.z3ify(context)
      is BVUGe -> this.z3ify(context)
      is BVSLt -> this.z3ify(context)
      is BVSLe -> this.z3ify(context)
      is BVSGt -> this.z3ify(context)
      is BVSGe -> this.z3ify(context)
      is IntLessEq -> this.z3ify(context)
      is IntLess -> this.z3ify(context)
      is IntGreaterEq -> this.z3ify(context)
      is IntGreater -> this.z3ify(context)
      is Divisible -> this.z3ify(context)
      is RealLessEq -> this.z3ify(context)
      is RealLess -> this.z3ify(context)
      is RealGreaterEq -> this.z3ify(context)
      is RealGreater -> this.z3ify(context)
      is IsInt -> this.z3ify(context)
      is FPLeq -> this.z3ify(context)
      is FPLt -> this.z3ify(context)
      is FPGeq -> this.z3ify(context)
      is FPGt -> this.z3ify(context)
      is FPEq -> this.z3ify(context)
      is FPIsNormal -> this.z3ify(context)
      is FPIsSubnormal -> this.z3ify(context)
      is FPIsZero -> this.z3ify(context)
      is FPIsInfinite -> this.z3ify(context)
      is FPIsNaN -> this.z3ify(context)
      is FPIsNegative -> this.z3ify(context)
      is FPIsPositive -> this.z3ify(context)
      is StrLexOrder -> this.z3ify(context)
      is StrRefLexOrder -> this.z3ify(context)
      is StrPrefixOf -> this.z3ify(context)
      is StrSuffixOf -> this.z3ify(context)
      is StrContains -> this.z3ify(context)
      is StrIsDigit -> this.z3ify(context)
      is ArraySelect<*, BoolSort> -> this.z3ify(context)
      /* free constant and function symbols */
      is UserDeclaredExpression ->
          if (this.children.isEmpty()) {
            context.getConstant(this.name, this.sort.z3ify(context))
          } else {
            context.getFunction(
                this.name, this.children.map { it.z3ify(context) }, this.sort.z3ify(context))
          }
      is UserDefinedExpression -> this.expand().z3ify(context) as Expr<Z3BoolSort>
      else -> throw IllegalArgumentException("Z3 can not visit expression $this.expression!")
    }

fun True.z3ify(context: Z3Context): Expr<Z3BoolSort> = context.context.mkTrue()

fun False.z3ify(context: Z3Context): Expr<Z3BoolSort> = context.context.mkFalse()

fun Not.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkNot(this.inner.z3ify(context))

fun Implies.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    makeRightAssoc(this.statements, context) { lhs, rhs ->
      context.context.mkImplies(lhs as Expr<Z3BoolSort>, rhs as Expr<Z3BoolSort>)
    }
        as Expr<Z3BoolSort>

fun And.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkAnd(*this.conjuncts.map { it.z3ify(context) }.toTypedArray())

fun Or.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkOr(*this.disjuncts.map { it.z3ify(context) }.toTypedArray())

fun XOr.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    makeLeftAssoc(this.disjuncts, context) { lhs, rhs ->
      context.context.mkXor(lhs as Expr<Z3BoolSort>, rhs as Expr<Z3BoolSort>)
    }
        as Expr<Z3BoolSort>

fun Equals<*>.z3ify(context: Z3Context): Expr<Z3BoolSort> {
  val inner =
      this.statements.zipWithNext { a, b ->
        context.context.mkEq(a.z3ify(context), b.z3ify(context))
      }
  return if (inner.size == 1) inner.single() else context.context.mkAnd(*inner.toTypedArray())
}

fun Distinct.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkDistinct(*this.statements.map { it.z3ify(context) }.toTypedArray())

fun BVUlt.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkBVULT(lhs.z3ify(context), rhs.z3ify(context))

fun BVULe.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkBVULE(lhs.z3ify(context), rhs.z3ify(context))

fun BVUGt.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkBVUGT(lhs.z3ify(context), rhs.z3ify(context))

fun BVUGe.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkBVUGE(lhs.z3ify(context), rhs.z3ify(context))

fun BVSLt.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkBVSLT(lhs.z3ify(context), rhs.z3ify(context))

fun BVSLe.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkBVSLE(lhs.z3ify(context), rhs.z3ify(context))

fun BVSGt.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkBVSGT(lhs.z3ify(context), rhs.z3ify(context))

fun BVSGe.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkBVSGE(lhs.z3ify(context), rhs.z3ify(context))

fun IntLessEq.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    makeLeftAssoc(this.terms, context) { lhs, rhs ->
      context.context.mkLe(lhs as Expr<out ArithSort>, rhs as Expr<out ArithSort>)
    }
        as Expr<Z3BoolSort>

fun IntLess.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    makeLeftAssoc(this.terms, context) { lhs, rhs ->
      context.context.mkLt(lhs as Expr<out ArithSort>, rhs as Expr<out ArithSort>)
    }
        as Expr<Z3BoolSort>

fun IntGreaterEq.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    makeLeftAssoc(this.terms, context) { lhs, rhs ->
      context.context.mkGe(lhs as Expr<out ArithSort>, rhs as Expr<out ArithSort>)
    }
        as Expr<Z3BoolSort>

fun IntGreater.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    makeLeftAssoc(this.terms, context) { lhs, rhs ->
      context.context.mkGt(lhs as Expr<out ArithSort>, rhs as Expr<out ArithSort>)
    }
        as Expr<Z3BoolSort>

fun RealLessEq.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    makeLeftAssoc(this.terms, context) { lhs, rhs ->
      context.context.mkLe(lhs as Expr<out ArithSort>, rhs as Expr<out ArithSort>)
    }
        as Expr<Z3BoolSort>

fun RealLess.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    makeLeftAssoc(this.terms, context) { lhs, rhs ->
      context.context.mkLt(lhs as Expr<out ArithSort>, rhs as Expr<out ArithSort>)
    }
        as Expr<Z3BoolSort>

fun RealGreaterEq.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    makeLeftAssoc(this.terms, context) { lhs, rhs ->
      context.context.mkGe(lhs as Expr<out ArithSort>, rhs as Expr<out ArithSort>)
    }
        as Expr<Z3BoolSort>

fun RealGreater.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    makeLeftAssoc(this.terms, context) { lhs, rhs ->
      context.context.mkGt(lhs as Expr<out ArithSort>, rhs as Expr<out ArithSort>)
    }
        as Expr<Z3BoolSort>

fun Divisible.z3ify(context: Z3Context): Expr<Z3BoolSort> = TODO() // C-API mk_divides missing

fun IsInt.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkIsInteger(this.inner.z3ify(context))

fun FPLeq.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkAnd(
        *this.terms
            .zipWithNext()
            .map { (lhs, rhs) -> context.context.mkFPLEq(lhs.z3ify(context), rhs.z3ify(context)) }
            .toTypedArray())

fun FPLt.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkAnd(
        *this.terms
            .zipWithNext()
            .map { (lhs, rhs) -> context.context.mkFPLt(lhs.z3ify(context), rhs.z3ify(context)) }
            .toTypedArray())

fun FPGeq.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkAnd(
        *this.terms
            .zipWithNext()
            .map { (lhs, rhs) -> context.context.mkFPGEq(lhs.z3ify(context), rhs.z3ify(context)) }
            .toTypedArray())

fun FPGt.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkAnd(
        *this.terms
            .zipWithNext()
            .map { (lhs, rhs) -> context.context.mkFPGt(lhs.z3ify(context), rhs.z3ify(context)) }
            .toTypedArray())

fun FPEq.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkAnd(
        *this.terms
            .zipWithNext()
            .map { (lhs, rhs) -> context.context.mkFPEq(lhs.z3ify(context), rhs.z3ify(context)) }
            .toTypedArray())

fun FPIsNormal.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkFPIsNormal(this.inner.z3ify(context))

fun FPIsSubnormal.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkFPIsSubnormal(this.inner.z3ify(context))

fun FPIsZero.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkFPIsZero(this.inner.z3ify(context))

fun FPIsInfinite.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkFPIsInfinite(this.inner.z3ify(context))

fun FPIsNaN.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkFPIsNaN(this.inner.z3ify(context))

fun FPIsNegative.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkFPIsNegative(this.inner.z3ify(context))

fun FPIsPositive.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkFPIsPositive(this.inner.z3ify(context))

fun StrLexOrder.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkAnd(
        *this.strings
            .zipWithNext()
            .map { (lhs, rhs) ->
              context.context.MkStringLt(lhs.z3ify(context), rhs.z3ify(context))
            }
            .toTypedArray())

fun StrRefLexOrder.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkAnd(
        *this.strings
            .zipWithNext()
            .map { (lhs, rhs) ->
              context.context.MkStringLe(lhs.z3ify(context), rhs.z3ify(context))
            }
            .toTypedArray())

fun StrPrefixOf.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkPrefixOf(inner.z3ify(context), prefix.z3ify(context))

fun StrSuffixOf.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkSuffixOf(inner.z3ify(context), suffix.z3ify(context))

fun StrContains.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    context.context.mkContains(string.z3ify(context), substring.z3ify(context))

fun StrIsDigit.z3ify(context: Z3Context): Expr<Z3BoolSort> = TODO()

@JvmName("z3ifyBitVec")
fun Expression<BVSort>.z3ify(context: Z3Context): Expr<BitVecSort> =
    when (this) {
      is LocalExpression -> context.localVariable(this.name, this.sort.z3ify(context))
      is LetExpression -> context.let(this.bindings) { this.inner.z3ify(context) }
      is BoundVariable -> context.boundVariable(this.name, this.sort.z3ify(context))
      is Ite -> this.z3ify(context)
      is BVLiteral -> this.z3ify(context)
      is BVConcat -> this.z3ify(context)
      is BVExtract -> this.z3ify(context)
      is BVNot -> this.z3ify(context)
      is BVNeg -> this.z3ify(context)
      is BVAnd -> this.z3ify(context)
      is BVOr -> this.z3ify(context)
      is BVAdd -> this.z3ify(context)
      is BVMul -> this.z3ify(context)
      is BVUDiv -> this.z3ify(context)
      is BVURem -> this.z3ify(context)
      is BVShl -> this.z3ify(context)
      is BVLShr -> this.z3ify(context)
      is FPToUBitVec -> this.z3ify(context)
      is FPToSBitVec -> this.z3ify(context)
      is BVNAnd -> this.z3ify(context)
      is BVNOr -> this.z3ify(context)
      is BVXOr -> this.z3ify(context)
      is BVXNOr -> this.z3ify(context)
      is BVComp -> this.z3ify(context)
      is BVSub -> this.z3ify(context)
      is BVSDiv -> this.z3ify(context)
      is BVSRem -> this.z3ify(context)
      is BVSMod -> this.z3ify(context)
      is BVAShr -> this.z3ify(context)
      is Repeat -> this.z3ify(context)
      is ZeroExtend -> this.z3ify(context)
      is SignExtend -> this.z3ify(context)
      is RotateRight -> this.z3ify(context)
      is RotateLeft -> this.z3ify(context)
      is ArraySelect<*, BVSort> -> this.z3ify(context)
      /* free constant and function symbols */
      is UserDeclaredExpression ->
          if (this.children.isEmpty()) {
            context.getConstant(this.name, this.sort.z3ify(context))
          } else {
            context.getFunction(
                this.name, this.children.map { it.z3ify(context) }, this.sort.z3ify(context))
          }
      is UserDefinedExpression -> this.expand().z3ify(context) as Expr<BitVecSort>
      else -> throw IllegalArgumentException("Z3 can not visit expression $this!")
    }

fun BVLiteral.z3ify(context: Z3Context): Expr<BitVecSort> =
    context.context.mkBV(this.value.toString(), this.bits)

fun BVConcat.z3ify(context: Z3Context): Expr<BitVecSort> =
    context.context.mkConcat(this.lhs.z3ify(context), this.rhs.z3ify(context))

fun BVExtract.z3ify(context: Z3Context): Expr<BitVecSort> =
    context.context.mkExtract(this.i, this.j, this.inner.z3ify(context))

fun BVNot.z3ify(context: Z3Context): Expr<BitVecSort> =
    context.context.mkBVNot(this.inner.z3ify(context))

fun BVNeg.z3ify(context: Z3Context): Expr<BitVecSort> =
    context.context.mkBVNeg(this.inner.z3ify(context))

fun BVAnd.z3ify(context: Z3Context): Expr<BitVecSort> =
    makeLeftAssoc(this.conjuncts, context) { lhs, rhs ->
      context.context.mkBVAND(lhs as Expr<BitVecSort>, rhs as Expr<BitVecSort>)
    }
        as Expr<BitVecSort>

fun BVOr.z3ify(context: Z3Context): Expr<BitVecSort> =
    makeLeftAssoc(this.disjuncts, context) { lhs, rhs ->
      context.context.mkBVOR(lhs as Expr<BitVecSort>, rhs as Expr<BitVecSort>)
    }
        as Expr<BitVecSort>

fun BVAdd.z3ify(context: Z3Context): Expr<BitVecSort> =
    makeLeftAssoc(this.summands, context) { lhs, rhs ->
      context.context.mkBVAdd(lhs as Expr<BitVecSort>, rhs as Expr<BitVecSort>)
    }
        as Expr<BitVecSort>

fun BVMul.z3ify(context: Z3Context): Expr<BitVecSort> =
    makeLeftAssoc(this.factors, context) { lhs, rhs ->
      context.context.mkBVMul(lhs as Expr<BitVecSort>, rhs as Expr<BitVecSort>)
    }
        as Expr<BitVecSort>

fun BVUDiv.z3ify(context: Z3Context): Expr<BitVecSort> =
    context.context.mkBVUDiv(this.numerator.z3ify(context), this.denominator.z3ify(context))

fun BVURem.z3ify(context: Z3Context): Expr<BitVecSort> =
    context.context.mkBVURem(this.numerator.z3ify(context), this.denominator.z3ify(context))

fun BVShl.z3ify(context: Z3Context): Expr<BitVecSort> =
    context.context.mkBVSHL(this.value.z3ify(context), this.distance.z3ify(context))

fun BVLShr.z3ify(context: Z3Context): Expr<BitVecSort> =
    context.context.mkBVLSHR(this.value.z3ify(context), this.distance.z3ify(context))

fun FPToUBitVec.z3ify(context: Z3Context): Expr<BitVecSort> =
    context.context.mkFPToBV(
        this.roundingMode.z3ify(context), this.inner.z3ify(context), this.m, false)

fun FPToSBitVec.z3ify(context: Z3Context): Expr<BitVecSort> =
    context.context.mkFPToBV(
        this.roundingMode.z3ify(context), this.inner.z3ify(context), this.m, true)

fun BVNAnd.z3ify(context: Z3Context): Expr<BitVecSort> =
    context.context.mkBVNAND(lhs.z3ify(context), rhs.z3ify(context))

fun BVNOr.z3ify(context: Z3Context): Expr<BitVecSort> =
    context.context.mkBVNOR(lhs.z3ify(context), rhs.z3ify(context))

fun BVXOr.z3ify(context: Z3Context): Expr<BitVecSort> =
    disjuncts.slice(2 ..< disjuncts.size).fold(
        context.context.mkBVXOR(disjuncts[0].z3ify(context), disjuncts[1].z3ify(context))) {
            xor,
            expr ->
          context.context.mkBVXOR(xor, expr.z3ify(context))
        }

fun BVXNOr.z3ify(context: Z3Context): Expr<BitVecSort> =
    context.context.mkBVXNOR(lhs.z3ify(context), rhs.z3ify(context))

fun BVComp.z3ify(context: Z3Context): Expr<BitVecSort> = this.expand().z3ify(context)

fun BVSub.z3ify(context: Z3Context): Expr<BitVecSort> =
    context.context.mkBVSub(lhs.z3ify(context), rhs.z3ify(context))

fun BVSDiv.z3ify(context: Z3Context): Expr<BitVecSort> =
    context.context.mkBVSDiv(lhs.z3ify(context), rhs.z3ify(context))

fun BVSRem.z3ify(context: Z3Context): Expr<BitVecSort> =
    context.context.mkBVSRem(lhs.z3ify(context), rhs.z3ify(context))

fun BVSMod.z3ify(context: Z3Context): Expr<BitVecSort> =
    context.context.mkBVSMod(lhs.z3ify(context), rhs.z3ify(context))

fun BVAShr.z3ify(context: Z3Context): Expr<BitVecSort> =
    context.context.mkBVASHR(lhs.z3ify(context), rhs.z3ify(context))

fun Repeat.z3ify(context: Z3Context): Expr<BitVecSort> =
    context.context.mkRepeat(j, inner.z3ify(context))

fun ZeroExtend.z3ify(context: Z3Context): Expr<BitVecSort> =
    context.context.mkZeroExt(i, inner.z3ify(context))

fun SignExtend.z3ify(context: Z3Context): Expr<BitVecSort> =
    context.context.mkSignExt(i, inner.z3ify(context))

fun RotateLeft.z3ify(context: Z3Context): Expr<BitVecSort> =
    context.context.mkBVRotateLeft(i, inner.z3ify(context))

fun RotateRight.z3ify(context: Z3Context): Expr<BitVecSort> =
    context.context.mkBVRotateRight(i, inner.z3ify(context))

@JvmName("z3ifyInts")
fun Expression<IntSort>.z3ify(context: Z3Context): Expr<Z3IntSort> =
    when (this) {
      is LocalExpression -> context.localVariable(this.name, this.sort.z3ify(context))
      is LetExpression -> context.let(this.bindings) { this.inner.z3ify(context) }
      is BoundVariable -> context.boundVariable(this.name, this.sort.z3ify(context))
      is Ite -> this.z3ify(context)
      is IntLiteral -> this.z3ify(context)
      is IntNeg -> this.z3ify(context)
      is IntSub -> this.z3ify(context)
      is IntAdd -> this.z3ify(context)
      is IntMul -> this.z3ify(context)
      is IntDiv -> this.z3ify(context)
      is Mod -> this.z3ify(context)
      is Abs -> this.z3ify(context)
      is ToInt -> this.z3ify(context)
      is StrLength -> this.z3ify(context)
      is StrIndexOf -> this.z3ify(context)
      is StrToCode -> this.z3ify(context)
      is StrToInt -> this.z3ify(context)
      is ArraySelect<*, IntSort> -> this.z3ify(context)
      /* free constant and function symbols */
      is UserDeclaredExpression ->
          if (this.children.isEmpty()) {
            context.getConstant(this.name, this.sort.z3ify(context))
          } else {
            context.getFunction(
                this.name, this.children.map { it.z3ify(context) }, this.sort.z3ify(context))
          }
      is UserDefinedExpression -> this.expand().z3ify(context) as Expr<Z3IntSort>
      else -> throw IllegalArgumentException("Z3 can not visit expression $this!")
    }

fun IntLiteral.z3ify(context: Z3Context): Expr<Z3IntSort> =
    context.context.mkInt(this.value.toString())

fun IntNeg.z3ify(context: Z3Context): Expr<Z3IntSort> =
    context.context.mkUnaryMinus(this.inner.z3ify(context))

fun IntSub.z3ify(context: Z3Context): Expr<Z3IntSort> =
    context.context.mkSub(*this.terms.map { it.z3ify(context) }.toTypedArray())

fun IntAdd.z3ify(context: Z3Context): Expr<Z3IntSort> =
    context.context.mkAdd(*this.terms.map { it.z3ify(context) }.toTypedArray())

fun IntMul.z3ify(context: Z3Context): Expr<Z3IntSort> =
    context.context.mkMul(*this.factors.map { it.z3ify(context) }.toTypedArray())

fun IntDiv.z3ify(context: Z3Context): Expr<Z3IntSort> =
    makeLeftAssoc(this.terms, context) { lhs, rhs ->
      context.context.mkDiv(lhs as Expr<ArithSort>, rhs as Expr<ArithSort>)
    }
        as Expr<Z3IntSort>

fun Mod.z3ify(context: Z3Context): Expr<Z3IntSort> =
    context.context.mkMod(this.dividend.z3ify(context), this.divisor.z3ify(context))

/*
 * Abs has no native function in z3 and is implemented using ite in the c++ api
 */
fun Abs.z3ify(context: Z3Context): Expr<Z3IntSort> =
    context.context.mkITE(
        context.context.mkGe(this.inner.z3ify(context), context.context.mkInt(0)),
        this.inner.z3ify(context),
        context.context.mkUnaryMinus(this.inner.z3ify(context)))

fun ToInt.z3ify(context: Z3Context): Expr<Z3IntSort> =
    context.context.mkReal2Int(this.inner.z3ify(context))

fun StrLength.z3ify(context: Z3Context): Expr<Z3IntSort> =
    context.context.mkLength(this.inner.z3ify(context))

fun StrIndexOf.z3ify(context: Z3Context): Expr<Z3IntSort> =
    context.context.mkIndexOf(
        this.string.z3ify(context), this.substring.z3ify(context), this.start.z3ify(context))

fun StrToCode.z3ify(context: Z3Context): Expr<Z3IntSort> =
    context.context.stringToInt(this.inner.z3ify(context))

@JvmName("z3ifyReals")
fun Expression<RealSort>.z3ify(context: Z3Context): Expr<Z3RealSort> =
    when (this) {
      is LocalExpression -> context.localVariable(this.name, context.context.mkRealSort())
      is LetExpression -> context.let(this.bindings) { this.inner.z3ify(context) }
      is BoundVariable -> context.boundVariable(this.name, this.sort.z3ify(context))
      is Ite -> this.z3ify(context)
      is RealLiteral -> this.z3ify(context)
      is RealNeg -> this.z3ify(context)
      is RealSub -> this.z3ify(context)
      is RealAdd -> this.z3ify(context)
      is RealMul -> this.z3ify(context)
      is RealDiv -> this.z3ify(context)
      is ToReal -> this.z3ify(context)
      is FPToReal -> this.z3ify(context)
      is ArraySelect<*, RealSort> -> this.z3ify(context)
      /* free constant and function symbols */
      is UserDeclaredExpression ->
          if (this.children.isEmpty()) {
            context.getConstant(this.name, this.sort.z3ify(context))
          } else {
            context.getFunction(
                this.name, this.children.map { it.z3ify(context) }, this.sort.z3ify(context))
          }
      is UserDefinedExpression -> this.expand().z3ify(context) as Expr<Z3RealSort>
      else -> throw IllegalArgumentException("Z3 can not visit expression $this!")
    }

fun RealLiteral.z3ify(context: Z3Context): Expr<Z3RealSort> =
    context.context.mkReal(this.value.toString())

fun RealNeg.z3ify(context: Z3Context): Expr<Z3RealSort> =
    context.context.mkUnaryMinus(this.inner.z3ify(context))

fun RealSub.z3ify(context: Z3Context): Expr<Z3RealSort> =
    context.context.mkSub(*this.terms.map { it.z3ify(context) }.toTypedArray())

fun RealAdd.z3ify(context: Z3Context): Expr<Z3RealSort> =
    context.context.mkAdd(*this.terms.map { it.z3ify(context) }.toTypedArray())

fun RealMul.z3ify(context: Z3Context): Expr<Z3RealSort> =
    context.context.mkMul(*this.factors.map { it.z3ify(context) }.toTypedArray())

fun RealDiv.z3ify(context: Z3Context): Expr<Z3RealSort> =
    makeLeftAssoc(this.terms, context) { lhs, rhs ->
      context.context.mkDiv(lhs as Expr<ArithSort>, rhs as Expr<ArithSort>)
    }
        as Expr<Z3RealSort>

fun ToReal.z3ify(context: Z3Context): Expr<Z3RealSort> =
    context.context.mkInt2Real(this.inner.z3ify(context))

fun FPToReal.z3ify(context: Z3Context): Expr<Z3RealSort> =
    context.context.mkFPToReal(this.inner.z3ify(context))

@JvmName("z3ifyFloatingPoint")
fun Expression<FPSort>.z3ify(context: Z3Context): Expr<Z3FPSort> =
    when (this) {
      is LocalExpression -> context.localVariable(this.name, this.sort.z3ify(context))
      is LetExpression -> context.let(this.bindings) { this.inner.z3ify(context) }
      is BoundVariable -> context.boundVariable(this.name, this.sort.z3ify(context))
      is Ite -> this.z3ify(context)
      is FPLiteral -> this.z3ify(context)
      is FPInfinity -> this.z3ify(context)
      is FPMinusInfinity -> this.z3ify(context)
      is FPZero -> this.z3ify(context)
      is FPMinusZero -> this.z3ify(context)
      is FPNaN -> this.z3ify(context)
      is FPAbs -> this.z3ify(context)
      is FPNeg -> this.z3ify(context)
      is FPAdd -> this.z3ify(context)
      is FPSub -> this.z3ify(context)
      is FPMul -> this.z3ify(context)
      is FPDiv -> this.z3ify(context)
      is FPFma -> this.z3ify(context)
      is FPSqrt -> this.z3ify(context)
      is FPRem -> this.z3ify(context)
      is FPRoundToIntegral -> this.z3ify(context)
      is FPMin -> this.z3ify(context)
      is FPMax -> this.z3ify(context)
      is BitVecToFP -> this.z3ify(context)
      is FPToFP -> this.z3ify(context)
      is RealToFP -> this.z3ify(context)
      is SBitVecToFP -> this.z3ify(context)
      is UBitVecToFP -> this.z3ify(context)
      is ArraySelect<*, FPSort> -> this.z3ify(context)
      /* free constant and function symbols */
      is UserDeclaredExpression ->
          if (this.children.isEmpty()) {
            context.getConstant(this.name, this.sort.z3ify(context))
          } else {
            context.getFunction(
                this.name, this.children.map { it.z3ify(context) }, this.sort.z3ify(context))
          }
      is UserDefinedExpression -> this.expand().z3ify(context) as Expr<Z3FPSort>
      else -> throw IllegalArgumentException("Z3 can not visit expression $this!")
    }

fun FPLiteral.z3ify(context: Z3Context): Expr<Z3FPSort> =
    context.context.mkFP(
        this.sign.z3ify(context), this.exponent.z3ify(context), this.significand.z3ify(context))

fun FPInfinity.z3ify(context: Z3Context): Expr<Z3FPSort> =
    context.context.mkFPInf(this.sort.z3ify(context), false)

fun FPMinusInfinity.z3ify(context: Z3Context): Expr<Z3FPSort> =
    context.context.mkFPInf(this.sort.z3ify(context), true)

fun FPZero.z3ify(context: Z3Context): Expr<Z3FPSort> =
    context.context.mkFPZero(this.sort.z3ify(context), false)

fun FPMinusZero.z3ify(context: Z3Context): Expr<Z3FPSort> =
    context.context.mkFPZero(this.sort.z3ify(context), true)

fun FPNaN.z3ify(context: Z3Context): Expr<Z3FPSort> =
    context.context.mkFPNaN(this.sort.z3ify(context))

fun FPAbs.z3ify(context: Z3Context): Expr<Z3FPSort> =
    context.context.mkFPAbs(this.inner.z3ify(context))

fun FPNeg.z3ify(context: Z3Context): Expr<Z3FPSort> =
    context.context.mkFPNeg(this.inner.z3ify(context))

fun FPAdd.z3ify(context: Z3Context): Expr<Z3FPSort> =
    context.context.mkFPAdd(
        this.roundingMode.z3ify(context),
        this.leftTerm.z3ify(context),
        this.rightTerm.z3ify(context))

fun FPSub.z3ify(context: Z3Context): Expr<Z3FPSort> =
    context.context.mkFPSub(
        this.roundingMode.z3ify(context),
        this.minuend.z3ify(context),
        this.subtrahend.z3ify(context))

fun FPMul.z3ify(context: Z3Context): Expr<Z3FPSort> =
    context.context.mkFPMul(
        this.roundingMode.z3ify(context),
        this.multiplier.z3ify(context),
        this.multiplicand.z3ify(context))

fun FPDiv.z3ify(context: Z3Context): Expr<Z3FPSort> =
    context.context.mkFPDiv(
        this.roundingMode.z3ify(context), this.dividend.z3ify(context), this.divisor.z3ify(context))

fun FPFma.z3ify(context: Z3Context): Expr<Z3FPSort> =
    context.context.mkFPFMA(
        this.roundingMode.z3ify(context),
        this.multiplier.z3ify(context),
        this.multiplicand.z3ify(context),
        this.summand.z3ify(context))

fun FPSqrt.z3ify(context: Z3Context): Expr<Z3FPSort> =
    context.context.mkFPSqrt(this.roundingMode.z3ify(context), this.inner.z3ify(context))

fun FPRem.z3ify(context: Z3Context): Expr<Z3FPSort> =
    context.context.mkFPRem(this.dividend.z3ify(context), this.divisor.z3ify(context))

fun FPRoundToIntegral.z3ify(context: Z3Context): Expr<Z3FPSort> =
    context.context.mkFPRoundToIntegral(this.roundingMode.z3ify(context), this.inner.z3ify(context))

fun FPMin.z3ify(context: Z3Context): Expr<Z3FPSort> =
    context.context.mkFPMin(this.lhs.z3ify(context), this.rhs.z3ify(context))

fun FPMax.z3ify(context: Z3Context): Expr<Z3FPSort> =
    context.context.mkFPMax(this.lhs.z3ify(context), this.rhs.z3ify(context))

fun BitVecToFP.z3ify(context: Z3Context): Expr<Z3FPSort> =
    context.context.mkFPToFP(this.inner.z3ify(context), this.sort.z3ify(context))

fun FPToFP.z3ify(context: Z3Context): Expr<Z3FPSort> =
    context.context.mkFPToFP(
        this.sort.z3ify(context), this.roundingMode.z3ify(context), this.inner.z3ify(context))

fun RealToFP.z3ify(context: Z3Context): Expr<Z3FPSort> =
    context.context.mkFPToFP(
        this.roundingMode.z3ify(context),
        this.inner.z3ify(context) as RealExpr,
        this.sort.z3ify(context))

fun SBitVecToFP.z3ify(context: Z3Context): Expr<Z3FPSort> =
    context.context.mkFPToFP(
        this.roundingMode.z3ify(context), this.inner.z3ify(context), this.sort.z3ify(context), true)

fun UBitVecToFP.z3ify(context: Z3Context): Expr<Z3FPSort> =
    context.context.mkFPToFP(
        this.roundingMode.z3ify(context),
        this.inner.z3ify(context),
        this.sort.z3ify(context),
        false)

@JvmName("z3ifyRoundingMode")
fun Expression<RoundingMode>.z3ify(context: Z3Context): Expr<FPRMSort> =
    when (this) {
      is LocalExpression -> context.localVariable(this.name, this.sort.z3ify(context))
      is LetExpression -> context.let(this.bindings) { this.inner.z3ify(context) }
      is BoundVariable -> context.boundVariable(this.name, this.sort.z3ify(context))
      is Ite -> this.z3ify(context)
      is RoundNearestTiesToEven -> this.z3ify(context)
      is RNE -> this.z3ify(context)
      is RoundNearestTiesToAway -> this.z3ify(context)
      is RNA -> this.z3ify(context)
      is RoundTowardPositive -> this.z3ify(context)
      is RTP -> this.z3ify(context)
      is RoundTowardNegative -> this.z3ify(context)
      is RTN -> this.z3ify(context)
      is RoundTowardZero -> this.z3ify(context)
      is RTZ -> this.z3ify(context)
      is ArraySelect<*, RoundingMode> -> this.z3ify(context)
      /* free constant and function symbols */
      is UserDeclaredExpression ->
          if (this.children.isEmpty()) {
            context.getConstant(this.name, this.sort.z3ify(context))
          } else {
            context.getFunction(
                this.name, this.children.map { it.z3ify(context) }, this.sort.z3ify(context))
          }
      is UserDefinedExpression -> this.expand().z3ify(context) as Expr<FPRMSort>
      else -> throw IllegalArgumentException("Z3 can not visit expression $this.expression!")
    }

fun RoundNearestTiesToEven.z3ify(context: Z3Context): Expr<FPRMSort> =
    context.context.mkFPRoundNearestTiesToEven()

fun RNE.z3ify(context: Z3Context): Expr<FPRMSort> = context.context.mkFPRNE()

fun RoundNearestTiesToAway.z3ify(context: Z3Context): Expr<FPRMSort> =
    context.context.mkFPRoundNearestTiesToAway()

fun RNA.z3ify(context: Z3Context): Expr<FPRMSort> = context.context.mkFPRNA()

fun RoundTowardPositive.z3ify(context: Z3Context): Expr<FPRMSort> =
    context.context.mkFPRoundTowardPositive()

fun RTP.z3ify(context: Z3Context): Expr<FPRMSort> = context.context.mkFPRTP()

fun RoundTowardNegative.z3ify(context: Z3Context): Expr<FPRMSort> =
    context.context.mkFPRoundTowardNegative()

fun RTN.z3ify(context: Z3Context): Expr<FPRMSort> = context.context.mkFPRTN()

fun RoundTowardZero.z3ify(context: Z3Context): Expr<FPRMSort> =
    context.context.mkFPRoundTowardZero()

fun RTZ.z3ify(context: Z3Context): Expr<FPRMSort> = context.context.mkFPRTZ()

/*
 * Z3´s StringSort is equivalent to a SeqSort<CharSort>>, mkStringSort returns a SeqSort<CharSort>>
 */
@JvmName("z3ifyString")
fun Expression<StringSort>.z3ify(context: Z3Context): Expr<SeqSort<CharSort>> =
    when (this) {
      is LocalExpression -> context.localVariable(this.name, this.sort.z3ify(context))
      is LetExpression -> context.let(this.bindings) { this.inner.z3ify(context) }
      is BoundVariable -> context.boundVariable(this.name, this.sort.z3ify(context))
      is Ite -> this.z3ify(context)
      is StrConcat -> this.z3ify(context)
      is StrAt -> this.z3ify(context)
      is StrSubstring -> this.z3ify(context)
      is StrReplace -> this.z3ify(context)
      is StrReplaceAll -> this.z3ify(context)
      is StrReplaceRegex -> this.z3ify(context)
      is StrReplaceAllRegex -> this.z3ify(context)
      is StrFromCode -> this.z3ify(context)
      is StrFromInt -> this.z3ify(context)
      is ArraySelect<*, StringSort> -> this.z3ify(context)
      /* free constant and function symbols */
      is UserDeclaredExpression ->
          if (this.children.isEmpty()) {
            context.getConstant(this.name, this.sort.z3ify(context))
          } else {
            context.getFunction(
                this.name, this.children.map { it.z3ify(context) }, this.sort.z3ify(context))
          }
      is UserDefinedExpression -> this.expand().z3ify(context) as Expr<SeqSort<CharSort>>
      else -> throw IllegalArgumentException("Z3 can not visit expression $this.expression!")
    }

fun StrConcat.z3ify(context: Z3Context): Expr<SeqSort<CharSort>> =
    context.context.mkConcat(*this.strings.map { it.z3ify(context) }.toTypedArray())

fun StrAt.z3ify(context: Z3Context): Expr<SeqSort<CharSort>> =
    context.context.mkAt(this.inner.z3ify(context), this.position.z3ify(context))

fun StrSubstring.z3ify(context: Z3Context): Expr<SeqSort<CharSort>> =
    context.context.mkExtract(inner.z3ify(context), start.z3ify(context), length.z3ify(context))

fun StrReplace.z3ify(context: Z3Context): Expr<SeqSort<CharSort>> =
    context.context.mkReplace(
        this.inner.z3ify(context), this.old.z3ify(context), this.new.z3ify(context))

// FIXME this probably only replaces the first occurrence, mkReplaceAll missing in C_API
fun StrReplaceAll.z3ify(context: Z3Context): Expr<SeqSort<CharSort>> =
    context.context.mkReplace(inner.z3ify(context), old.z3ify(context), new.z3ify(context))

fun StrReplaceRegex.z3ify(context: Z3Context): Expr<SeqSort<CharSort>> = TODO()

fun StrReplaceAllRegex.z3ify(context: Z3Context): Expr<SeqSort<CharSort>> = TODO()

fun StrFromCode.z3ify(context: Z3Context): Expr<SeqSort<CharSort>> =
    context.context.intToString(inner.z3ify(context))

fun StrFromInt.z3ify(context: Z3Context): Expr<SeqSort<CharSort>> =
    context.context.intToString(inner.z3ify(context))

@JvmName("z3ifyRegLan")
fun Expression<RegLan>.z3ify(context: Z3Context): Expr<ReSort<SeqSort<CharSort>>> =
    when (this) {
      is LocalExpression -> context.localVariable(this.name, this.sort.z3ify(context))
      is LetExpression -> context.let(this.bindings) { this.inner.z3ify(context) }
      is BoundVariable -> context.boundVariable(this.name, this.sort.z3ify(context))
      is RegexNone -> this.z3ify(context)
      is RegexAll -> this.z3ify(context)
      is RegexAllChar -> this.z3ify(context)
      is RegexConcat -> this.z3ify(context)
      is RegexUnion -> this.z3ify(context)
      is RegexIntersec -> this.z3ify(context)
      is RegexStar -> this.z3ify(context)
      is RegexComp -> this.z3ify(context)
      is RegexDiff -> this.z3ify(context)
      is RegexPlus -> this.z3ify(context)
      is RegexOption -> this.z3ify(context)
      is RegexRange -> this.z3ify(context)
      is RegexPower -> this.z3ify(context)
      is RegexLoop -> this.z3ify(context)
      /* free constant and function symbols */
      is UserDeclaredExpression ->
          if (this.children.isEmpty()) {
            context.getConstant(this.name, this.sort.z3ify(context))
          } else {
            context.getFunction(
                this.name, this.children.map { it.z3ify(context) }, this.sort.z3ify(context))
          }
      is UserDefinedExpression -> this.expand().z3ify(context) as Expr<ReSort<SeqSort<CharSort>>>
      else -> throw IllegalArgumentException("Z3 can not visit expression $this.expression!")
    }

fun RegexNone.z3ify(context: Z3Context): Expr<ReSort<SeqSort<CharSort>>> =
    context.context.mkEmptyRe(context.context.mkReSort(context.context.stringSort))

fun RegexAll.z3ify(context: Z3Context): Expr<ReSort<SeqSort<CharSort>>> =
    context.context.mkFullRe(context.context.mkReSort(context.context.stringSort))

fun RegexAllChar.z3ify(context: Z3Context): Expr<ReSort<SeqSort<CharSort>>> =
    context.context.mkAllcharRe(context.context.mkReSort(context.context.stringSort))

fun RegexConcat.z3ify(context: Z3Context): Expr<ReSort<SeqSort<CharSort>>> =
    context.context.mkConcat(
        *this.regex.map { it.z3ify(context) as ReExpr<SeqSort<CharSort>> }.toTypedArray())

fun RegexUnion.z3ify(context: Z3Context): Expr<ReSort<SeqSort<CharSort>>> =
    context.context.mkUnion(
        *this.regex.map { it.z3ify(context) as ReExpr<SeqSort<CharSort>> }.toTypedArray())

fun RegexIntersec.z3ify(context: Z3Context): Expr<ReSort<SeqSort<CharSort>>> =
    context.context.mkIntersect(
        *this.regex.map { it.z3ify(context) as ReExpr<SeqSort<CharSort>> }.toTypedArray())

fun RegexStar.z3ify(context: Z3Context): Expr<ReSort<SeqSort<CharSort>>> =
    context.context.mkStar(this.inner.z3ify(context))

fun RegexComp.z3ify(context: Z3Context): Expr<ReSort<SeqSort<CharSort>>> =
    context.context.mkComplement(this.inner.z3ify(context))

fun RegexDiff.z3ify(context: Z3Context): Expr<ReSort<SeqSort<CharSort>>> =
    makeLeftAssoc(this.regex, context) { lhs, rhs ->
      context.context.mkDiff(
          lhs as Expr<ReSort<SeqSort<CharSort>>>, rhs as Expr<ReSort<SeqSort<CharSort>>>)
    }
        as Expr<ReSort<SeqSort<CharSort>>>

fun RegexPlus.z3ify(context: Z3Context): Expr<ReSort<SeqSort<CharSort>>> =
    context.context.mkPlus(this.inner.z3ify(context))

fun RegexOption.z3ify(context: Z3Context): Expr<ReSort<SeqSort<CharSort>>> =
    context.context.mkOption(this.inner.z3ify(context))

fun RegexRange.z3ify(context: Z3Context): Expr<ReSort<SeqSort<CharSort>>> =
    context.context.mkRange(lhs.z3ify(context), rhs.z3ify(context))

fun RegexPower.z3ify(context: Z3Context): Expr<ReSort<SeqSort<CharSort>>> =
    context.context.mkPower(this.inner.z3ify(context), this.n)

fun RegexLoop.z3ify(context: Z3Context): Expr<ReSort<SeqSort<CharSort>>> =
    context.context.mkLoop(this.inner.z3ify(context), this.n, this.m)

@JvmName("z3ifyArrayEx")
fun Expression<ArraySort<*, *>>.z3ify(context: Z3Context): Expr<Z3ArraySort<Z3Sort, Z3Sort>> =
    when (this) {
      is LocalExpression ->
          context.localVariable(this.name, this.sort.z3ify(context))
              as Expr<com.microsoft.z3.ArraySort<com.microsoft.z3.Sort, com.microsoft.z3.Sort>>
      is LetExpression -> context.let(this.bindings) { this.inner.z3ify(context) }
      is ArrayStore -> (this as ArrayStore).z3ify(context)
      else ->
          if (context.constants[this.name.toString()] != null) {
            context.constants[this.name.toString()]!! as Expr<Z3ArraySort<Z3Sort, Z3Sort>>
          } else if (context.functions[this.name.toString()] != null) {
            TODO("Implement free function symbols")
          } else {
            throw IllegalArgumentException("Z3 can not visit expression $this!")
          }
    }

fun ArrayStore<*, *>.z3ify(context: Z3Context): Expr<Z3ArraySort<Z3Sort, Z3Sort>> =
    context.context.mkStore(
        this.array.z3ify(context) as Expr<Z3ArraySort<Z3Sort, Z3Sort>>,
        this.index.z3ify(context) as Expr<Z3Sort>,
        this.value.z3ify(context) as Expr<Z3Sort>)

fun Expression<UserDefinedSort>.z3ify(context: Z3Context): Expr<UninterpretedSort> =
    when (this) {
      is Ite -> this.z3ify(context)
      is LocalExpression ->
          context.localVariable(this.name, this.sort.z3ify(context)) as Expr<UninterpretedSort>
      is LetExpression -> context.let(this.bindings) { this.inner.z3ify(context) }
      is BoundVariable ->
          context.boundVariable(this.name, this.sort.z3ify(context)) as Expr<UninterpretedSort>
      is ArraySelect<*, UserDefinedSort> -> this.z3ify(context)
      else ->
          if (context.constants[this.name.toString()] != null) {
            context.constants[this.name.toString()]!! as Expr<UninterpretedSort>
          } else if (context.functions[this.name.toString()] != null) {
            context.functions[this.name.toString()]!!.apply(
                *this.children.map { it.z3ify(context) }.toTypedArray()) as Expr<UninterpretedSort>
          } else {
            throw IllegalArgumentException("Z3 can not visit expression $this!")
          }
    }

/*
 * Sort conversions
 */

fun Sort.z3ify(context: Z3Context): Z3Sort =
    when (this) {
      is BoolSort -> this.z3ify(context)
      is BVSort -> this.z3ify(context)
      is IntSort -> this.z3ify(context)
      is RealSort -> this.z3ify(context)
      is FPSort -> this.z3ify(context)
      is RoundingMode -> this.z3ify(context)
      is StringSort -> this.z3ify(context)
      is RegLan -> this.z3ify(context)
      is UserDefinedSort -> this.z3ify(context)
      is ArraySort<*, *> -> this.z3ify(context)
      // unknown sorts
      else -> throw IllegalStateException("Unknown or unsupported sort $this")
    }

fun BoolSort.z3ify(context: Z3Context): Z3BoolSort = context.context.mkBoolSort()

fun BVSort.z3ify(context: Z3Context): BitVecSort = context.context.mkBitVecSort(this.bits)

fun IntSort.z3ify(context: Z3Context): Z3IntSort = context.context.mkIntSort()

fun RealSort.z3ify(context: Z3Context): Z3RealSort = context.context.mkRealSort()

fun FPSort.z3ify(context: Z3Context): Z3FPSort =
    context.context.mkFPSort(this.exponentBits, this.significantBits)

fun RoundingMode.z3ify(context: Z3Context): FPRMSort = context.context.mkFPRoundingModeSort()

fun StringSort.z3ify(context: Z3Context): SeqSort<CharSort> =
    context.context.mkSeqSort(context.context.mkCharSort())

fun RegLan.z3ify(context: Z3Context): ReSort<SeqSort<CharSort>> =
    context.context.mkReSort(context.context.mkSeqSort(context.context.mkCharSort()))

fun UserDefinedSort.z3ify(context: Z3Context): UninterpretedSort =
    context.context.mkUninterpretedSort(this.name.toSMTString())

fun ArraySort<*, *>.z3ify(context: Z3Context): Z3ArraySort<*, *> =
    context.context.mkArraySort(this.x.z3ify(context), this.y.z3ify(context))

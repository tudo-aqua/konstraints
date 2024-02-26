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

package tools.aqua.konstraints.solvers.Z3

import com.microsoft.z3.ArithSort
import com.microsoft.z3.BitVecSort
import com.microsoft.z3.BoolSort as Z3BoolSort
import com.microsoft.z3.Expr
import com.microsoft.z3.IntSort as Z3IntSort
import tools.aqua.konstraints.smt.BVSort
import tools.aqua.konstraints.smt.BoolSort
import tools.aqua.konstraints.smt.Expression
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
fun Expression<*>.z3ify(context: Z3Context): Expr<*> =
    when (this.sort) {
      is BoolSort -> (this as Expression<BoolSort>).z3ify(context)
      is BVSort -> (this as Expression<BVSort>).z3ify(context)
      is IntSort -> (this as Expression<IntSort>).z3ify(context)
      else -> throw RuntimeException("Unknown sort ${this.sort}")
    }

@JvmName("z3ifyBool")
fun Expression<BoolSort>.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    when (this) {
      is True -> this.z3ify(context)
      is False -> this.z3ify(context)
      is Not -> this.z3ify(context)
      is Implies -> this.z3ify(context)
      is And -> this.z3ify(context)
      is Or -> this.z3ify(context)
      is XOr -> this.z3ify(context)
      is Equals -> this.z3ify(context)
      is Distinct -> this.z3ify(context)
      is BVUlt -> this.z3ify(context)
      is IntLessEq -> this.z3ify(context)
      is IntLess -> this.z3ify(context)
      is IntGreaterEq -> this.z3ify(context)
      is IntGreater -> this.z3ify(context)
      is Divisible -> this.z3ify(context)
      /* this also has to handle declared functions */
      else ->
          if (context.constants[this.symbol] != null) {
            context.constants[this.symbol]!! as Expr<com.microsoft.z3.BoolSort>
          } else if (context.functions[this.symbol] != null) {
            TODO("Implement free function symbols")
          } else {
            throw IllegalArgumentException("Z3 can not visit expression $this.expression!")
          }
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

fun Equals.z3ify(context: Z3Context): Expr<Z3BoolSort> {
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

fun Divisible.z3ify(context: Z3Context): Expr<Z3BoolSort> = TODO()

@JvmName("z3ifyBitVec")
fun Expression<BVSort>.z3ify(context: Z3Context): Expr<BitVecSort> =
    when (this) {
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
      else ->
          if (context.constants[this.symbol] != null) {
            context.constants[this.symbol]!! as Expr<BitVecSort>
          } else if (context.functions[this.symbol] != null) {
            TODO("Implement free function symbols")
          } else {
            throw IllegalArgumentException("Z3 can not visit expression $this.expression!")
          }
    }

fun BVLiteral.z3ify(context: Z3Context): Expr<BitVecSort> =
    context.context.mkBV(this.value, this.bits)

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

@JvmName("z3ifyInts")
fun Expression<IntSort>.z3ify(context: Z3Context): Expr<Z3IntSort> =
    when (this) {
      is IntLiteral -> this.z3ify(context)
      is IntNeg -> this.z3ify(context)
      is IntSub -> this.z3ify(context)
      is IntAdd -> this.z3ify(context)
      is IntMul -> this.z3ify(context)
      is IntDiv -> this.z3ify(context)
      is Mod -> this.z3ify(context)
      is Abs -> this.z3ify(context)
      else ->
          if (context.constants[this.symbol] != null) {
            context.constants[this.symbol]!! as Expr<Z3IntSort>
          } else if (context.functions[this.symbol] != null) {
            TODO("Implement free function symbols")
          } else {
            throw IllegalArgumentException("Z3 can not visit expression $this!")
          }
    }

fun IntLiteral.z3ify(context: Z3Context): Expr<Z3IntSort> = context.context.mkInt(this.value)

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

fun Abs.z3ify(context: Z3Context): Expr<Z3IntSort> = TODO()

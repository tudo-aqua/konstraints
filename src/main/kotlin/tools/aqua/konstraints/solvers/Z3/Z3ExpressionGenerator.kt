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

import com.microsoft.z3.BitVecSort
import com.microsoft.z3.BoolSort as Z3BoolSort
import com.microsoft.z3.Expr
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
    when {
      this.sort is BoolSort -> (this as Expression<BoolSort>).z3ify(context)
      this.sort is BVSort -> (this as Expression<BVSort>).z3ify(context)
      else -> throw RuntimeException("Unknown sort ${this.sort}")
    }

@JvmName("z3ifyBool")
fun Expression<BoolSort>.z3ify(context: Z3Context): Expr<Z3BoolSort> =
    when {
      this is True -> this.z3ify(context)
      this is False -> this.z3ify(context)
      this is Not -> this.z3ify(context)
      this is Implies -> this.z3ify(context)
      this is And -> this.z3ify(context)
      this is Or -> this.z3ify(context)
      this is XOr -> this.z3ify(context)
      this is Equals -> this.z3ify(context)
      this is Distinct -> this.z3ify(context)
      this is BVUlt -> this.z3ify(context)
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

@JvmName("z3ifyBitVec")
fun Expression<BVSort>.z3ify(context: Z3Context): Expr<BitVecSort> =
    when {
      this is BVLiteral -> this.z3ify(context)
      this is BVConcat -> this.z3ify(context)
      this is BVExtract -> this.z3ify(context)
      this is BVNot -> this.z3ify(context)
      this is BVNeg -> this.z3ify(context)
      this is BVAnd -> this.z3ify(context)
      this is BVOr -> this.z3ify(context)
      this is BVAdd -> this.z3ify(context)
      this is BVMul -> this.z3ify(context)
      this is BVUDiv -> this.z3ify(context)
      this is BVURem -> this.z3ify(context)
      this is BVShl -> this.z3ify(context)
      this is BVLShr -> this.z3ify(context)
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

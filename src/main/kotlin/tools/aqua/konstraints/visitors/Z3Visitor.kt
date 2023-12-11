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

package tools.aqua.konstraints.visitors

import com.microsoft.z3.BitVecSort
import com.microsoft.z3.BoolSort
import com.microsoft.z3.Context as ctx
import com.microsoft.z3.Expr
import com.microsoft.z3.Sort
import tools.aqua.konstraints.*

class Z3Visitor : CoreVisitor<Expr<*>>, FSBVVisitor<Expr<*>> {
  val context = ctx()

  override fun visit(expression: Expression<*>): Expr<*> =
      when (expression) {
        is True -> visit(expression)
        is False -> visit(expression)
        is Not -> visit(expression)
        is Implies -> visit(expression)
        is And -> visit(expression)
        is Or -> visit(expression)
        is XOr -> visit(expression)
        is Equals -> visit(expression)
        is Distinct -> visit(expression)
        is Ite -> visit(expression)
        is BVLiteral -> visit(expression)
        is BVConcat -> visit(expression)
        is BVExtract -> visit(expression)
        is BVNot -> visit(expression)
        is BVNeg -> visit(expression)
        is BVAnd -> visit(expression)
        is BVOr -> visit(expression)
        is BVAdd -> visit(expression)
        is BVMul -> visit(expression)
        is BVUDiv -> visit(expression)
        is BVURem -> visit(expression)
        is BVShl -> visit(expression)
        is BVLShr -> visit(expression)
        is BVUlt -> visit(expression)
        else -> throw IllegalArgumentException("Z3 visitor can not visit expression $expression!")
      }

  override fun visit(trueExpr: True): Expr<*> {
    return context.mkTrue()
  }

  override fun visit(falseExpr: False): Expr<*> {
    return context.mkFalse()
  }

  override fun visit(notExpr: Not): Expr<*> {
    return context.mkNot(visit(notExpr.inner) as Expr<BoolSort>)
  }

  override fun visit(impliesExpr: Implies): Expr<*> {
    return makeImplies(impliesExpr.statements)
  }

  private fun makeImplies(
      statements: List<Expression<tools.aqua.konstraints.BoolSort>>
  ): Expr<BoolSort> {
    return if (statements.size == 2) {
      /*
       * Implies can directly be constructed for only 2 statements
       */
      context.mkImplies(
          visit(statements[0]) as Expr<BoolSort>, visit(statements[1]) as Expr<BoolSort>)
    } else {
      /*
       * Unroll implies chain in the following way:
       * (=> A B C D)
       * (=> A (=> B (=> C D)))
       */
      context.mkImplies(
          visit(statements[0]) as Expr<BoolSort>,
          makeImplies(statements.slice(1 ..< statements.size)))
    }
  }

  override fun visit(andExpr: And): Expr<*> {
    return context.mkAnd(*andExpr.conjuncts.map { visit(it) as Expr<BoolSort> }.toTypedArray())
  }

  override fun visit(orExpr: Or): Expr<*> {
    return context.mkOr(*orExpr.disjuncts.map { visit(it) as Expr<BoolSort> }.toTypedArray())
  }

  override fun visit(xorExpr: XOr): Expr<*> {
    return context.mkOr(*xorExpr.disjuncts.map { visit(it) as Expr<BoolSort> }.toTypedArray())
  }

  override fun visit(equalsExpr: Equals): Expr<*> {
    return if (equalsExpr.statements.size == 2) {
      /*
       * Equals can directly be constructed for only 2 statements
       */
      context.mkImplies(
          visit(equalsExpr.statements[0]) as Expr<BoolSort>,
          visit(equalsExpr.statements[1]) as Expr<BoolSort>)
    } else {
      /*
       * Unroll equals chain in the following way:
       * (= A B C D)
       * (and (= A B) (= B C) (= C D))
       */
      context.mkAnd(
          *equalsExpr.statements
              .zipWithNext { a, b ->
                context.mkEq(visit(a) as Expr<BoolSort>, visit(b) as Expr<BoolSort>)
              }
              .toTypedArray())
    }
  }

  override fun visit(distinctExpr: Distinct): Expr<*> {
    return context.mkDistinct(*distinctExpr.statements.map { visit(it) }.toTypedArray())
  }

  override fun visit(iteExpr: Ite): Expr<*> {
    return context.mkITE(
        visit(iteExpr.statement) as Expr<BoolSort>, visit(iteExpr.then), visit(iteExpr.els))
  }

  override fun visit(bvLiteral: BVLiteral): Expr<*> {
    return context.mkBV(bvLiteral.value, bvLiteral.bits)
  }

  override fun visit(bvConcat: BVConcat): Expr<*> {
    return context.mkConcat(
        visit(bvConcat.lhs) as Expr<BitVecSort>, visit(bvConcat.rhs) as Expr<BitVecSort>)
  }

  override fun visit(bvExtract: BVExtract): Expr<*> {
    return context.mkExtract(bvExtract.i, bvExtract.j, visit(bvExtract.inner) as Expr<BitVecSort>)
  }

  override fun visit(bvNot: BVNot): Expr<*> {
    return context.mkBVNot(visit(bvNot.inner) as Expr<BitVecSort>)
  }

  override fun visit(bvNeg: BVNeg): Expr<*> {
    return context.mkBVNot(visit(bvNeg.inner) as Expr<BitVecSort>)
  }

  override fun visit(bvAnd: BVAnd): Expr<*> {
    return makeLeftAssoc(bvAnd.conjuncts) { lhs, rhs -> context.mkBVAND(lhs, rhs) }
  }

  override fun visit(bvOr: BVOr): Expr<*> {
    return makeLeftAssoc(bvOr.disjuncts) { lhs, rhs -> context.mkBVOR(lhs, rhs) }
  }

  override fun visit(bvAdd: BVAdd): Expr<*> {
    return makeLeftAssoc(bvAdd.summands) { lhs, rhs -> context.mkBVAdd(lhs, rhs) }
  }

  override fun visit(bvMul: BVMul): Expr<*> {
    return makeLeftAssoc(bvMul.factors) { lhs, rhs -> context.mkBVMul(lhs, rhs) }
  }

  override fun visit(bvuDiv: BVUDiv): Expr<*> {
    return context.mkBVUDiv(
        visit(bvuDiv.numerator) as Expr<BitVecSort>, visit(bvuDiv.denominator) as Expr<BitVecSort>)
  }

  override fun visit(bvuRem: BVURem): Expr<*> {
    return context.mkBVURem(
        visit(bvuRem.numerator) as Expr<BitVecSort>, visit(bvuRem.denominator) as Expr<BitVecSort>)
  }

  override fun visit(bvShl: BVShl): Expr<*> {
    return context.mkBVSHL(
        visit(bvShl.value) as Expr<BitVecSort>, visit(bvShl.distance) as Expr<BitVecSort>)
  }

  override fun visit(bvlShr: BVLShr): Expr<*> {
    return context.mkBVLSHR(
        visit(bvlShr.value) as Expr<BitVecSort>, visit(bvlShr.distance) as Expr<BitVecSort>)
  }

  override fun visit(bvUlt: BVUlt): Expr<*> {
    return context.mkBVULT(visit(bvUlt.lhs) as Expr<BitVecSort>, visit(bvUlt) as Expr<BitVecSort>)
  }

  /**
   * Build a left associative expression using [operation] (e.g. BVADD) S1 and S2 are Z3 target
   * sorts, R is a konstraints sort of the original expression
   */
  private fun <R : tools.aqua.konstraints.Sort, S1 : Sort, S2 : Sort> makeLeftAssoc(
      expressions: List<Expression<R>>,
      operation: (Expr<S1>, Expr<S2>) -> Expr<S1>
  ): Expr<S1> {
    return if (expressions.size == 2) {
      operation(visit(expressions[0]) as Expr<S1>, visit(expressions[1]) as Expr<S2>)
    } else {
      operation(
          makeLeftAssoc(expressions.dropLast(1), operation), visit(expressions.last()) as Expr<S2>)
    }
  }
}

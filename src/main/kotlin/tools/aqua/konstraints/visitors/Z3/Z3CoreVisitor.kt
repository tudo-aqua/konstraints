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

package tools.aqua.konstraints.visitors.Z3

import com.microsoft.z3.BoolSort
import com.microsoft.z3.Context
import com.microsoft.z3.Expr
import tools.aqua.konstraints.*
import tools.aqua.konstraints.visitors.AssociativeVisitor
import tools.aqua.konstraints.visitors.CoreVisitor

class Z3CoreVisitor(val context: Context, val generator: Z3ExpressionGenerator) :
    CoreVisitor<Expr<*>>, AssociativeVisitor {
  override fun visitUnknownExpression(expression: Expression<*>): Expr<*> {
    /*
     * If we find an expression from another theory e.g. BVUlt can appear inside a Not expression
     * we delegate handling this expression back to the Z3ExpressionGenerator to switch into the
     * appropriate visitor, here it would be the Z3BitVecVisitor
     */
    return generator.visit(expression)
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
    return makeRightAssoc(impliesExpr.statements, { expr -> visit(expr) }) { lhs, rhs ->
      context.mkImplies(lhs, rhs)
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
    val unrolled =
        makeChainable<com.microsoft.z3.Sort>(equalsExpr.statements, { expr -> visit(expr) }) {
            lhs,
            rhs ->
          context.mkEq(lhs, rhs)
        }

    /*
     * if we use the syntactic sugar variant we need to wrap the unrolled terms in an and-expression,
     * otherwise we can not wrap it as this would lead to a wrong SMT program
     */
    return if (unrolled.size == 1) {
      unrolled[0]
    } else {
      context.mkAnd(*unrolled.toTypedArray())
    }
  }

  override fun visit(distinctExpr: Distinct): Expr<*> {
    return context.mkDistinct(*distinctExpr.statements.map { visit(it) }.toTypedArray())
  }

  override fun visit(iteExpr: Ite): Expr<*> {
    return context.mkITE(
        visit(iteExpr.statement) as Expr<BoolSort>, visit(iteExpr.then), visit(iteExpr.els))
  }
}

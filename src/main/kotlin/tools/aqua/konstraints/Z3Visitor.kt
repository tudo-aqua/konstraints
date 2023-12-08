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

package tools.aqua.konstraints

import com.microsoft.z3.BoolSort
import com.microsoft.z3.Context as ctx
import com.microsoft.z3.Expr

class Z3Visitor : CoreVisitor<Expr<*>> {
  val context = ctx()

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
}

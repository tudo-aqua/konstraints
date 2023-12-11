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

import com.microsoft.z3.Expr
import tools.aqua.konstraints.*

class Z3ExpressionGenerator(val solver: Z3Solver) {
  private val coreVisitor = Z3CoreVisitor(solver.context, this)
  private val bitVecVisitor = Z3BitVecVisitor(solver.context, this)

  fun visit(expression: Expression<*>): Expr<*> =
      // TODO maybe create a helper function in each theory to check if an expression is from that
      // theory
      when (expression) {
        is True -> coreVisitor.visit(expression)
        is False -> coreVisitor.visit(expression)
        is Not -> coreVisitor.visit(expression)
        is Implies -> coreVisitor.visit(expression)
        is And -> coreVisitor.visit(expression)
        is Or -> coreVisitor.visit(expression)
        is XOr -> coreVisitor.visit(expression)
        is Equals -> coreVisitor.visit(expression)
        is Distinct -> coreVisitor.visit(expression)
        is Ite -> coreVisitor.visit(expression)
        is BVLiteral -> bitVecVisitor.visit(expression)
        is BVConcat -> bitVecVisitor.visit(expression)
        is BVExtract -> bitVecVisitor.visit(expression)
        is BVNot -> bitVecVisitor.visit(expression)
        is BVNeg -> bitVecVisitor.visit(expression)
        is BVAnd -> bitVecVisitor.visit(expression)
        is BVOr -> bitVecVisitor.visit(expression)
        is BVAdd -> bitVecVisitor.visit(expression)
        is BVMul -> bitVecVisitor.visit(expression)
        is BVUDiv -> bitVecVisitor.visit(expression)
        is BVURem -> bitVecVisitor.visit(expression)
        is BVShl -> bitVecVisitor.visit(expression)
        is BVLShr -> bitVecVisitor.visit(expression)
        is BVUlt -> bitVecVisitor.visit(expression)
        else -> {
          if (solver.constants[expression.symbol] != null) {
            solver.constants[expression.symbol]!!
          } else if (solver.functions[expression.symbol] != null) {
            TODO("Implement free function symbols")
          } else {
            throw IllegalArgumentException("Z3 can not visit expression $expression!")
          }
        }
      }
}

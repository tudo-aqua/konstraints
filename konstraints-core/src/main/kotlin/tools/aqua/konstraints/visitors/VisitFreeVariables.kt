/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2026 The Konstraints Authors
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

import tools.aqua.konstraints.smt.AnnotatedExpression
import tools.aqua.konstraints.smt.BinaryExpression
import tools.aqua.konstraints.smt.BitVecLiteral
import tools.aqua.konstraints.smt.BoundVariable
import tools.aqua.konstraints.smt.Char
import tools.aqua.konstraints.smt.ConstantExpression
import tools.aqua.konstraints.smt.ConstructorExpression
import tools.aqua.konstraints.smt.ExistsExpression
import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.smt.FloatingPointLiteral
import tools.aqua.konstraints.smt.ForallExpression
import tools.aqua.konstraints.smt.FreeExpression
import tools.aqua.konstraints.smt.HomogenousExpression
import tools.aqua.konstraints.smt.IntLiteral
import tools.aqua.konstraints.smt.Ite
import tools.aqua.konstraints.smt.LetExpression
import tools.aqua.konstraints.smt.LocalExpression
import tools.aqua.konstraints.smt.NAryExpression
import tools.aqua.konstraints.smt.RealLiteral
import tools.aqua.konstraints.smt.SelectorExpression
import tools.aqua.konstraints.smt.StringLiteral
import tools.aqua.konstraints.smt.TernaryExpression
import tools.aqua.konstraints.smt.TesterExpression
import tools.aqua.konstraints.smt.UnaryExpression

object FreeVariables : VisitByStructure<MutableList<FreeExpression<*>>> {
  fun of(expr: Expression<*>): List<FreeExpression<*>> {
    val list = mutableListOf<FreeExpression<*>>()
    visit(expr, list)
    return list
  }

  override fun visit(expr: ConstantExpression<*>, ctx: MutableList<FreeExpression<*>>) {}

  override fun visit(expr: UnaryExpression<*, *>, ctx: MutableList<FreeExpression<*>>) {}

  override fun visit(expr: BinaryExpression<*, *, *>, ctx: MutableList<FreeExpression<*>>) {}

  override fun visit(expr: TernaryExpression<*, *, *, *>, ctx: MutableList<FreeExpression<*>>) {}

  override fun visit(expr: HomogenousExpression<*, *>, ctx: MutableList<FreeExpression<*>>) {}

  override fun visit(expr: NAryExpression<*>, ctx: MutableList<FreeExpression<*>>) {}

  override fun visit(expr: FreeExpression<*>, ctx: MutableList<FreeExpression<*>>) {
    ctx.add(expr)
  }

  override fun visit(expr: LetExpression<*>, ctx: MutableList<FreeExpression<*>>) {}

  override fun visit(expr: ExistsExpression, ctx: MutableList<FreeExpression<*>>) {}

  override fun visit(expr: ForallExpression, ctx: MutableList<FreeExpression<*>>) {}

  override fun visit(expr: Ite<*>, ctx: MutableList<FreeExpression<*>>) {}

  override fun visit(expr: AnnotatedExpression<*>, ctx: MutableList<FreeExpression<*>>) {}

  override fun visit(expr: BoundVariable<*>, ctx: MutableList<FreeExpression<*>>) {}

  override fun visit(expr: LocalExpression<*>, ctx: MutableList<FreeExpression<*>>) {}

  override fun visit(expr: ConstructorExpression, ctx: MutableList<FreeExpression<*>>) {}

  override fun visit(expr: SelectorExpression<*>, ctx: MutableList<FreeExpression<*>>) {}

  override fun visit(expr: TesterExpression, ctx: MutableList<FreeExpression<*>>) {}

  override fun visit(literal: BitVecLiteral, ctx: MutableList<FreeExpression<*>>) {}

  override fun visit(literal: Char, ctx: MutableList<FreeExpression<*>>) {}

  override fun visit(literal: FloatingPointLiteral, ctx: MutableList<FreeExpression<*>>) {}

  override fun visit(literal: IntLiteral, ctx: MutableList<FreeExpression<*>>) {}

  override fun visit(literal: RealLiteral, ctx: MutableList<FreeExpression<*>>) {}

  override fun visit(literal: StringLiteral, ctx: MutableList<FreeExpression<*>>) {}
}

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
import tools.aqua.konstraints.smt.CharLiteral
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

object FreeVariables : VisitByStructure<MutableSet<FreeExpression<*>>> {
  fun of(expr: Expression<*>, policy: RecursionPolicy): Set<FreeExpression<*>> {
    val set = mutableSetOf<FreeExpression<*>>()
    visit(expr, set, policy)
    return set
  }

  override fun visit(expr: ConstantExpression<*>, ctx: MutableSet<FreeExpression<*>>) {}

  override fun visit(expr: UnaryExpression<*, *>, ctx: MutableSet<FreeExpression<*>>) {}

  override fun visit(expr: BinaryExpression<*, *, *>, ctx: MutableSet<FreeExpression<*>>) {}

  override fun visit(expr: TernaryExpression<*, *, *, *>, ctx: MutableSet<FreeExpression<*>>) {}

  override fun visit(expr: HomogenousExpression<*, *>, ctx: MutableSet<FreeExpression<*>>) {}

  override fun visit(expr: NAryExpression<*>, ctx: MutableSet<FreeExpression<*>>) {}

  override fun visit(expr: FreeExpression<*>, ctx: MutableSet<FreeExpression<*>>) {
    ctx.add(expr)
  }

  override fun visit(expr: LetExpression<*>, ctx: MutableSet<FreeExpression<*>>) {}

  override fun visit(expr: ExistsExpression, ctx: MutableSet<FreeExpression<*>>) {}

  override fun visit(expr: ForallExpression, ctx: MutableSet<FreeExpression<*>>) {}

  override fun visit(expr: Ite<*>, ctx: MutableSet<FreeExpression<*>>) {}

  override fun visit(expr: AnnotatedExpression<*>, ctx: MutableSet<FreeExpression<*>>) {}

  override fun visit(expr: BoundVariable<*>, ctx: MutableSet<FreeExpression<*>>) {}

  override fun visit(expr: LocalExpression<*>, ctx: MutableSet<FreeExpression<*>>) {}

  override fun visit(expr: ConstructorExpression, ctx: MutableSet<FreeExpression<*>>) {}

  override fun visit(expr: SelectorExpression<*>, ctx: MutableSet<FreeExpression<*>>) {}

  override fun visit(expr: TesterExpression, ctx: MutableSet<FreeExpression<*>>) {}

  override fun visit(literal: BitVecLiteral, ctx: MutableSet<FreeExpression<*>>) {}

  override fun visit(literal: CharLiteral, ctx: MutableSet<FreeExpression<*>>) {}

  override fun visit(literal: FloatingPointLiteral, ctx: MutableSet<FreeExpression<*>>) {}

  override fun visit(literal: IntLiteral, ctx: MutableSet<FreeExpression<*>>) {}

  override fun visit(literal: RealLiteral, ctx: MutableSet<FreeExpression<*>>) {}

  override fun visit(literal: StringLiteral, ctx: MutableSet<FreeExpression<*>>) {}
}

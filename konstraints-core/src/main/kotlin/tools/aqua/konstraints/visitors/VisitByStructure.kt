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
import tools.aqua.konstraints.smt.Literal
import tools.aqua.konstraints.smt.LocalExpression
import tools.aqua.konstraints.smt.NAryExpression
import tools.aqua.konstraints.smt.RealLiteral
import tools.aqua.konstraints.smt.SelectorExpression
import tools.aqua.konstraints.smt.StringLiteral
import tools.aqua.konstraints.smt.TernaryExpression
import tools.aqua.konstraints.smt.TesterExpression
import tools.aqua.konstraints.smt.UnaryExpression

interface VisitByStructure<T> {
  fun visit(expr: Expression<*>, ctx: T) {
    when (expr) {
      is ConstantExpression<*> -> visit(expr, ctx)
      is UnaryExpression<*, *> -> visit(expr, ctx)
      is BinaryExpression<*, *, *> -> visit(expr, ctx)
      is TernaryExpression<*, *, *, *> -> visit(expr, ctx)
      is HomogenousExpression<*, *> -> visit(expr, ctx)
      is NAryExpression<*> -> visit(expr, ctx)
      is FreeExpression<*> -> visit(expr, ctx)
      is LetExpression<*> -> visit(expr, ctx)
      is ExistsExpression -> visit(expr, ctx)
      is ForallExpression -> visit(expr, ctx)
      is Ite<*> -> visit(expr, ctx)
      is AnnotatedExpression<*> -> visit(expr, ctx)
      is BoundVariable<*> -> visit(expr, ctx)
      is LocalExpression<*> -> visit(expr, ctx)
      is Literal -> visit(expr, ctx)
      is ConstructorExpression -> visit(expr, ctx)
      is SelectorExpression<*> -> visit(expr, ctx)
      is TesterExpression -> visit(expr, ctx)
    }
    expr.children.forEach { visit(it, ctx) }
  }

  fun visit(expr: ConstantExpression<*>, ctx: T)

  fun visit(expr: UnaryExpression<*, *>, ctx: T)

  fun visit(expr: BinaryExpression<*, *, *>, ctx: T)

  fun visit(expr: TernaryExpression<*, *, *, *>, ctx: T)

  fun visit(expr: HomogenousExpression<*, *>, ctx: T)

  fun visit(expr: NAryExpression<*>, ctx: T)

  fun visit(expr: FreeExpression<*>, ctx: T)

  fun visit(expr: LetExpression<*>, ctx: T)

  fun visit(expr: ExistsExpression, ctx: T)

  fun visit(expr: ForallExpression, ctx: T)

  fun visit(expr: Ite<*>, ctx: T)

  fun visit(expr: AnnotatedExpression<*>, ctx: T)

  fun visit(expr: BoundVariable<*>, ctx: T)

  fun visit(expr: LocalExpression<*>, ctx: T)

  fun visit(expr: ConstructorExpression, ctx: T)

  fun visit(expr: SelectorExpression<*>, ctx: T)

  fun visit(expr: TesterExpression, ctx: T)

  fun visit(literal: Literal<*>, ctx: T) =
      when (literal) {
        is BitVecLiteral -> visit(literal, ctx)
        is Char -> visit(literal, ctx)
        is FloatingPointLiteral -> visit(literal, ctx)
        is IntLiteral -> visit(literal, ctx)
        is RealLiteral -> visit(literal, ctx)
        is StringLiteral -> visit(literal, ctx)
      }

  fun visit(literal: BitVecLiteral, ctx: T)

  fun visit(literal: Char, ctx: T)

  fun visit(literal: FloatingPointLiteral, ctx: T)

  fun visit(literal: IntLiteral, ctx: T)

  fun visit(literal: RealLiteral, ctx: T)

  fun visit(literal: StringLiteral, ctx: T)
}

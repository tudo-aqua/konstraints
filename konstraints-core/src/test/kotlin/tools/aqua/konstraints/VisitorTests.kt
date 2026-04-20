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

package tools.aqua.konstraints

import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import tools.aqua.konstraints.dsl.declaring
import tools.aqua.konstraints.dsl.eq
import tools.aqua.konstraints.dsl.smt
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.visitors.RecursionPolicy
import tools.aqua.konstraints.visitors.VisitByStructure

/**
 * Test visitor that adds the symbol of each free variable to a list in the order they were visited
 * in
 */
object OrderSensitiveVisitor : VisitByStructure<MutableList<Symbol>> {

  override fun visit(expr: ConstantExpression<*>, ctx: MutableList<Symbol>) {}

  override fun visit(expr: UnaryExpression<*, *>, ctx: MutableList<Symbol>) {}

  override fun visit(expr: BinaryExpression<*, *, *>, ctx: MutableList<Symbol>) {}

  override fun visit(expr: TernaryExpression<*, *, *, *>, ctx: MutableList<Symbol>) {}

  override fun visit(expr: HomogenousExpression<*, *>, ctx: MutableList<Symbol>) {}

  override fun visit(expr: NAryExpression<*>, ctx: MutableList<Symbol>) {}

  override fun visit(expr: FreeExpression<*>, ctx: MutableList<Symbol>) {
    ctx.add(expr.name)
  }

  override fun visit(expr: LetExpression<*>, ctx: MutableList<Symbol>) {}

  override fun visit(expr: ExistsExpression, ctx: MutableList<Symbol>) {}

  override fun visit(expr: ForallExpression, ctx: MutableList<Symbol>) {}

  override fun visit(expr: Ite<*>, ctx: MutableList<Symbol>) {}

  override fun visit(expr: AnnotatedExpression<*>, ctx: MutableList<Symbol>) {}

  override fun visit(expr: BoundVariable<*>, ctx: MutableList<Symbol>) {}

  override fun visit(expr: LocalExpression<*>, ctx: MutableList<Symbol>) {}

  override fun visit(expr: ConstructorExpression, ctx: MutableList<Symbol>) {}

  override fun visit(expr: SelectorExpression<*>, ctx: MutableList<Symbol>) {}

  override fun visit(expr: TesterExpression, ctx: MutableList<Symbol>) {}

  override fun visit(literal: BitVecLiteral, ctx: MutableList<Symbol>) {}

  override fun visit(literal: CharLiteral, ctx: MutableList<Symbol>) {}

  override fun visit(literal: FloatingPointLiteral, ctx: MutableList<Symbol>) {}

  override fun visit(literal: IntLiteral, ctx: MutableList<Symbol>) {}

  override fun visit(literal: RealLiteral, ctx: MutableList<Symbol>) {}

  override fun visit(literal: StringLiteral, ctx: MutableList<Symbol>) {}
}

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class VisitorTests {
  val program =
      smt(QF_BV) {
        val func by declaring(SMTBitVec(8), SMTBitVec(8), SMTBitVec(8))
        val foo by declaring(SMTBitVec(8))
        val bar by declaring(SMTBitVec(8))

        assert { func(foo(), func(foo(), bar())) eq func(func(foo(), bar()), foo()) }
      }

  @Test
  fun testVisitorIsInPreorder() {
    val order = mutableListOf<Symbol>()
    OrderSensitiveVisitor.visit(
        program.commands.filterIsInstance<Assert>().single().expr,
        order,
        RecursionPolicy.ITERATIVE,
    )
    val expected =
        listOf(
            "func".toSymbol(),
            "foo".toSymbol(),
            "func".toSymbol(),
            "foo".toSymbol(),
            "bar".toSymbol(),
            "func".toSymbol(),
            "func".toSymbol(),
            "foo".toSymbol(),
            "bar".toSymbol(),
            "foo".toSymbol(),
        )

    assert((order zip expected).all { (lhs, rhs) -> lhs == rhs })
  }

  @Test
  fun testIterativeAndRecursiveVisitInTheSameOrder() {
    val iterative = mutableListOf<Symbol>()
    OrderSensitiveVisitor.visit(
        program.commands.filterIsInstance<Assert>().single().expr,
        iterative,
        RecursionPolicy.ITERATIVE,
    )

    val recursive = mutableListOf<Symbol>()
    OrderSensitiveVisitor.visit(
        program.commands.filterIsInstance<Assert>().single().expr,
        recursive,
        RecursionPolicy.ITERATIVE,
    )

    assert((iterative zip recursive).all { (lhs, rhs) -> lhs == rhs })
  }
}

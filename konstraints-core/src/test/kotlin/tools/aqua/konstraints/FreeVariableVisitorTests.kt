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

import java.util.stream.Stream
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments.arguments
import org.junit.jupiter.params.provider.MethodSource
import tools.aqua.konstraints.dsl.bvand
import tools.aqua.konstraints.dsl.bvor
import tools.aqua.konstraints.dsl.declaringConst
import tools.aqua.konstraints.dsl.eq
import tools.aqua.konstraints.dsl.forall
import tools.aqua.konstraints.dsl.not
import tools.aqua.konstraints.dsl.smt
import tools.aqua.konstraints.smt.Assert
import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.smt.QF_BV
import tools.aqua.konstraints.smt.SMTBitVec
import tools.aqua.konstraints.smt.Symbol
import tools.aqua.konstraints.smt.toSymbol
import tools.aqua.konstraints.visitors.FreeVariables

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class FreeVariableVisitorTests {
  @ParameterizedTest
  @MethodSource("provideExpressionAndFreeVariables")
  fun testVisitFreeVariables(expr: Expression<*>, expected: List<Symbol>) {
    val freeVariables = FreeVariables.of(expr)

    assertEquals(expected.size, freeVariables.size)
    assert(
        expected.all { symbol ->
          freeVariables.find { expression -> expression.name == symbol } != null
        }
    )
  }

  fun provideExpressionAndFreeVariables() =
      Stream.of(
          arguments(
              smt(QF_BV) {
                    val s by declaringConst(SMTBitVec(32))
                    assert { not(s bvand s eq s) }
                  }
                  .commands
                  .filterIsInstance<Assert>()
                  .single()
                  .expr,
              listOf("s".toSymbol(), "s".toSymbol(), "s".toSymbol()),
          ),
          arguments(
              smt(QF_BV) {
                    val s by declaringConst(SMTBitVec(32))
                    val t by declaringConst(SMTBitVec(32))
                    assert { not((s bvor (t bvor t)) eq (s bvor t)) }
                  }
                  .commands
                  .filterIsInstance<Assert>()
                  .single()
                  .expr,
              listOf(
                  "s".toSymbol(),
                  "t".toSymbol(),
                  "t".toSymbol(),
                  "s".toSymbol(),
                  "t".toSymbol(),
              ),
          ),
          arguments(
              smt(QF_BV) {
                    val s by declaringConst(SMTBitVec(32))
                    val t by declaringConst(SMTBitVec(32))
                    assert { forall(SMTBitVec(32)) { x -> not((s bvor (x bvor x)) eq (s bvor t)) } }
                  }
                  .commands
                  .filterIsInstance<Assert>()
                  .single()
                  .expr,
              listOf("s".toSymbol(), "s".toSymbol(), "t".toSymbol()),
          ),
      )
}

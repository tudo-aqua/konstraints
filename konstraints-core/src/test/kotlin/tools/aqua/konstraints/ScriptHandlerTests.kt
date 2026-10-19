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

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import tools.aqua.konstraints.parser.SMTScriptParser
import tools.aqua.konstraints.parser.ScriptHandler
import tools.aqua.konstraints.smt.ALL
import tools.aqua.konstraints.smt.Assert
import tools.aqua.konstraints.smt.BoolSort
import tools.aqua.konstraints.smt.DeclareFun
import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.smt.MutableSMTProgram
import tools.aqua.konstraints.smt.Sort
import tools.aqua.konstraints.smt.Symbol
import tools.aqua.konstraints.smt.toSymbol

class ScriptHandlerTests {
  @Test
  fun `parseInto without handler appends every command`() {
    val program = MutableSMTProgram().apply { setLogic(ALL) }
    SMTScriptParser.parseInto(program, "(declare-fun x () Int)(assert (> x 0))")

    assertEquals(1, program.commands.count { it is DeclareFun<*> })
    assertEquals(1, program.commands.count { it is Assert })
  }

  @Test
  fun `handler intercepts assertions, declarations and push-pop`() {
    val program = MutableSMTProgram().apply { setLogic(ALL) }
    val assertions = mutableListOf<Expression<BoolSort>>()
    val handler =
        object : ScriptHandler {
          override fun assert(program: MutableSMTProgram, term: Expression<BoolSort>) {
            assertions += term
          }

          override fun declareFun(
              program: MutableSMTProgram,
              symbol: Symbol,
              parameters: List<Sort>,
              sort: Sort,
          ) {
            // tolerate repeated declarations
            if (program.context.getFuncOrNull(symbol) == null) {
              program.declareFun(symbol, parameters, sort)
            }
          }

          override fun push(program: MutableSMTProgram, n: Int) = Unit

          override fun pop(program: MutableSMTProgram, n: Int) = Unit
        }

    SMTScriptParser.parseInto(
        program,
        """
        (declare-fun x () Int)
        (push 1)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (> x y))
        (pop 1)
        (assert (< y 0))
        """,
        handler,
    )

    assertEquals(2, assertions.size)
    assertEquals(2, program.commands.count { it is DeclareFun<*> })
    assertEquals(0, program.commands.count { it is Assert })
    assertTrue("y".toSymbol() in program.context)
  }
}

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
import org.junit.jupiter.api.Test
import tools.aqua.konstraints.parser.SMTScriptParser
import tools.aqua.konstraints.smt.ALL
import tools.aqua.konstraints.smt.BitVecLiteral
import tools.aqua.konstraints.smt.BoolSort
import tools.aqua.konstraints.smt.MutableSMTProgram
import tools.aqua.konstraints.smt.SatStatus
import tools.aqua.konstraints.smt.StringLiteral
import tools.aqua.konstraints.smt.cast
import tools.aqua.konstraints.smt.toSymbol
import tools.aqua.konstraints.solvers.SolverSession

class SolverSessionTests {
  private fun program(declarations: String) =
      MutableSMTProgram(emptyList()).apply {
        setLogic(ALL)
        SMTScriptParser.parseInto(this, declarations)
      }

  @Test
  fun `push and pop are incremental and get-value returns literals`() {
    val program = program("(declare-fun x () (_ BitVec 32)) (declare-fun s () String)")
    val x = program.context.getFunc("x".toSymbol()).constructDynamic(emptyList(), emptyList())
    val s = program.context.getFunc("s".toSymbol()).constructDynamic(emptyList(), emptyList())

    SolverSession.z3().use { session ->
      program.commands.forEach { session.send(it) }

      session.assert(SMTScriptParser.parseTerm("(bvsgt x #x00000005)", program).cast<BoolSort>())
      session.push()
      session.assert(SMTScriptParser.parseTerm("(bvslt x #x00000005)", program).cast<BoolSort>())
      assertEquals(SatStatus.UNSAT, session.checkSat())
      session.pop()

      session.assert(SMTScriptParser.parseTerm("(= x #x00000007)", program).cast<BoolSort>())
      session.assert(SMTScriptParser.parseTerm("(= s \"a\"\"b\")", program).cast<BoolSort>())
      assertEquals(SatStatus.SAT, session.checkSat())

      val values = session.getValue(listOf(x, s), program)
      assertEquals(7, (values.getValue(x) as BitVecLiteral).value.toInt())
      // string literals keep their SMT-LIB escaping
      assertEquals("a\"\"b", (values.getValue(s) as StringLiteral).value)
    }
  }

  @Test
  fun `parseInto extends an existing program`() {
    val program = program("(declare-fun f (Int) (_ BitVec 32))")
    SMTScriptParser.parseInto(program, "(declare-fun o () Int) (assert (= (f o) #x00000001))")

    SolverSession.z3().use { session ->
      program.commands.forEach { session.send(it) }
      assertEquals(SatStatus.SAT, session.checkSat())
    }
  }
}

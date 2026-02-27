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
import org.junit.jupiter.api.assertDoesNotThrow
import tools.aqua.konstraints.parser.Parser
import tools.aqua.konstraints.smt.ConstructorDecl
import tools.aqua.konstraints.smt.Datatype
import tools.aqua.konstraints.smt.MutableSMTProgram
import tools.aqua.konstraints.smt.QuotingRule
import tools.aqua.konstraints.smt.SMTInt
import tools.aqua.konstraints.smt.SelectorDecl
import tools.aqua.konstraints.smt.toSymbol

class DatatypeTests {
  @Test
  fun testIntListConstructionFromParser() {
    val smt =
        "(set-logic QF_IDL)" +
            "(declare-datatype IntList( ( empty )( insert ( head Int ) ( tail IntList ) )))" +
            "(declare-const l IntList)" +
            "(assert (= l l))" +
            "(check-sat)"
    val prg = Parser(smt)

    assertEquals(
        prg.toSMTString(QuotingRule.SAME_AS_INPUT, false).replace('\n', ' ').replace(" ", ""),
        smt.replace('\n', ' ').replace(" ", ""),
    )
  }

  @Test
  fun testIntListConstructionFromProgram() {
    assertDoesNotThrow {
      val program = MutableSMTProgram()
      val intListDt =
          Datatype(0, "IntList".toSymbol()) { IntList ->
            listOf(
                ConstructorDecl("empty".toSymbol(), emptyList()),
                ConstructorDecl(
                    "insert".toSymbol(),
                    listOf(
                        SelectorDecl("head".toSymbol(), SMTInt),
                        SelectorDecl("tail".toSymbol(), IntList),
                    ),
                ),
            )
          }
      program.declareDatatype(intListDt)
    }
  }
}

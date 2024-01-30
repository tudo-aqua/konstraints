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

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.ValueSource
import org.petitparser.context.ParseError
import tools.aqua.konstraints.parser.ParseTreeVisitor
import tools.aqua.konstraints.parser.Parser
import tools.aqua.konstraints.parser.ProtoCommand

/*
 * Make Lifecycle per class because context needs to be the same for each test input
 */
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class VisitorTests {
  private val parseTreeVisitor = ParseTreeVisitor()

  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "(declare-fun A () Bool)",
              "(declare-fun B () Bool)",
              "(declare-fun C () Bool)",
              "(declare-fun D () (_ BitVec 32))",
              "(declare-fun E () (_ BitVec 16))",
              "(assert (and (or (not A) (not B)) (xor A B (not C)) (and B (or A C))))",
              "(declare-fun F (Bool (_ BitVec 32)) (_ BitVec 16))",
              "(declare-fun a () (_ BitVec 32))",
              "(declare-fun b () (_ BitVec 32))",
              "(assert (bvult a b))",
              "(assert (not (bvult a b)))",
              "(assert (and (bvult a b) (bvult b a)))",
              "(assert (bvult ((_ extract 15 0) D) E))"])
  fun testCommandVisiting(statement: String) {
    val result = Parser.command.parse(statement)

    if (result.isSuccess) {
      val command = parseTreeVisitor.visit(result.get<ProtoCommand>())
      println(command)
      assertEquals(statement, command.toString())
    } else {
      throw ParseError(result.failure(result.message))
    }
  }
}

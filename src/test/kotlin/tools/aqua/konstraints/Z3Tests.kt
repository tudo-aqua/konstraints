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

import java.util.concurrent.TimeUnit
import java.util.stream.Stream
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.Timeout
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import org.junit.jupiter.params.provider.ValueSource
import org.petitparser.context.ParseError
import tools.aqua.konstraints.parser.ParseTreeVisitor
import tools.aqua.konstraints.parser.Parser
import tools.aqua.konstraints.parser.ProtoCommand
import tools.aqua.konstraints.visitors.Z3.Z3Solver

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class Z3Tests {

  @ParameterizedTest
  @MethodSource("getInts")
  @Timeout(value = 3, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun test(id: Int) {
    /*
     * These test are currently not working with Z3 as the solver is not capable of solving them yet
     */
    if (id in listOf(524, 928, 1105, 1299, 1323, 1492)) {
      return
    }

    val parseTreeVisitor = ParseTreeVisitor()
    val solver = Z3Solver()
    val temp =
        javaClass
            .getResourceAsStream(
                "/QF_BV/20190311-bv-term-small-rw-Noetzli/bv-term-small-rw_$id.smt2")!!
            .bufferedReader()
            .readLines()
    val program = temp.map { it.trim('\r', '\n') }

    val satStatus =
        if (program.find { it.contains("unsat") } != null) {
          "unsat"
        } else if (program.find { it.contains("unknown") } != null) {
          return
        } else {
          "sat"
        }

    println("Expected result is $satStatus")

    val result = Parser.script.parse(program.joinToString(""))

    if (result.isSuccess) {
      val commands =
          result
              .get<List<Any>>()
              .filter { it is ProtoCommand || it is Command }
              .map { if (it is ProtoCommand) parseTreeVisitor.visit(it) else it } as List<Command>

      println(commands.joinToString("\n"))

      solver.use {
        commands.map { solver.visit(it) }

        // verify we get the correct status for the test
        assertEquals(satStatus, solver.status)

        // verify we parsed the correct program
        /*
        assertEquals(commands.filterIsInstance<Assert>().single().expression.toString(),
            solver.context.solver.assertions.last().toString())
        */
      }
    } else {
      throw ParseError(result.failure(result.message))
    }
  }

  private fun getInts(): Stream<Arguments> {
    return IntArray(1575) { it }.map { Arguments.arguments(it + 1) }.stream()
  }

  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "(declare-fun A () (_ BitVec 32))(declare-fun B () (_ BitVec 16))(assert (bvult ((_ extract 15 0) A) B))(check-sat)"])
  fun testExtract(program: String) {
    val parseTreeVisitor = ParseTreeVisitor()
    val solver = Z3Solver()

    val result = Parser.script.parse(program)

    if (result.isSuccess) {
      val commands =
          result
              .get<List<Any>>()
              .filter { it is ProtoCommand || it is Command }
              .map { if (it is ProtoCommand) parseTreeVisitor.visit(it) else it } as List<Command>

      println(commands.joinToString("\n"))

      solver.use {
        commands.map { solver.visit(it) }

        // verify we get the correct status for the test
        assertEquals("sat", solver.status)
      }
    } else {
      throw ParseError(result.failure(result.message))
    }
  }
}

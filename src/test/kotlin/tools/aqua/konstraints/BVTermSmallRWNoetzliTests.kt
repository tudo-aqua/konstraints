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

import java.io.File
import java.util.stream.Stream
import org.junit.jupiter.api.Assertions.assertNotNull
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import org.petitparser.context.ParseError
import tools.aqua.konstraints.parser.Context
import tools.aqua.konstraints.parser.ParseTreeVisitor
import tools.aqua.konstraints.parser.Parser
import tools.aqua.konstraints.parser.ProtoCommand
import kotlin.streams.toList

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class BVTermSmallRWNoetzliTests {
  @ParameterizedTest
  @MethodSource("getInts")
  fun testQF_BV(id: Int) {
    /*
     * reset context for each test, so symbols can be defined by every test
     */

    ParseTreeVisitor.context = Context()

    ParseTreeVisitor.context.registerTheory(CoreContext)
    ParseTreeVisitor.context.registerTheory(BitVectorExpressionContext)

    val temp =
      javaClass.getResourceAsStream("/QF_BV/20190311-bv-term-small-rw-Noetzli/bv-term-small-rw_$id.smt2")!!
        .bufferedReader()
        .readLines()
    val program = temp.map { it.trim('\r', '\n') }
    println(program.joinToString("\n"))
    println("\n==========================")
    println("**************************")
    println("==========================\n")

    val result = Parser.script.parse(program.joinToString(""))

    if (result.isSuccess) {
      /*
       * CheckSat is not a ProtoCommand instance as the parser directly returns the CheckSat object,
       * it is therefore filtered out here and missing in the output
       */
      val commands = result.get<List<Any>>().filterIsInstance<ProtoCommand>()

      commands.forEachIndexed { i, command ->
        val parsed = ParseTreeVisitor.visit(command)
        println(parsed)

        assertNotNull(program.find { it == parsed.toString() })
      }
    } else {
      throw ParseError(result.failure(result.message))
    }
  }

  private fun getInts(): Stream<Arguments> {
    return IntArray(1575) { it }.map { Arguments.arguments(it + 1) }.stream()
  }
}

/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2024 The Konstraints Authors
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
import java.util.concurrent.TimeUnit
import java.util.stream.Stream
import kotlin.streams.asStream
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Assumptions.assumeTrue
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.Timeout
import org.junit.jupiter.api.assertThrows
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.Arguments.arguments
import org.junit.jupiter.params.provider.MethodSource
import tools.aqua.konstraints.parser.Parser
import tools.aqua.konstraints.parser.SymbolAttributeValue
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.theories.BVSort
import tools.aqua.konstraints.theories.BVUlt

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class SMTProgramTests {
  @ParameterizedTest
  @MethodSource("getQFBVModelFiles")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun testModelGeneration(file: File) {
    val program = Parser.parse(file.bufferedReader().readLines().joinToString())

    assumeTrue(
        (program.info.find { attribute -> attribute.keyword == ":status" }?.value
                as SymbolAttributeValue)
            .symbol
            .toString() == "sat")

    program.solve()

    assertNotNull(program.model)
    print(program.model?.definitions?.joinToString("\n"))
  }

  fun getQFBVModelFiles(): Stream<Arguments> {
    val dir = File(javaClass.getResource("/QF_BV/Models/").file)

    return dir.walk()
        .filter { file: File -> file.isFile }
        .map { file: File -> Arguments.arguments(file) }
        .asStream()
  }

  @ParameterizedTest
  @MethodSource("getCommands")
  fun testProgramFromCode(commands: List<Command>) {
    val program = MutableSMTProgram()

    assertDoesNotThrow {
      program.addAll(commands)
      program.solve()
    }
  }

  fun getCommands(): Stream<Arguments> {
    return Stream.of(
        arguments(
            listOf(
                SetLogic(QF_BV),
                DeclareFun("A".symbol(), emptyList(), BVSort(8)),
                DeclareFun("B".symbol(), emptyList(), BVSort(8)),
                Assert(
                    BVUlt(
                        UserDeclaredExpression("A".symbol(), BVSort(8)),
                        UserDeclaredExpression("B".symbol(), BVSort(8)))),
                CheckSat)))
  }

  @ParameterizedTest
  @MethodSource("getIllegalCommands")
  fun testIllegalProgramFromCode(commands: List<Command>) {
    val program = MutableSMTProgram()

    assertThrows<RuntimeException> { program.addAll(commands) }
  }

  fun getIllegalCommands(): Stream<Arguments> {
    return Stream.of(
        arguments(
            listOf(
                SetLogic(QF_BV),
                Assert(
                    BVUlt(
                        UserDeclaredExpression("A".symbol(), BVSort(8)),
                        UserDeclaredExpression("B".symbol(), BVSort(8)))),
                CheckSat)))
  }
}

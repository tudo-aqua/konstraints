/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2025 The Konstraints Authors
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

import java.io.BufferedReader
import java.io.File
import java.util.concurrent.TimeUnit
import java.util.stream.Stream
import kotlin.streams.asStream
import kotlin.use
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assumptions.assumeTrue
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.Timeout
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import tools.aqua.konstraints.parser.Parser
import tools.aqua.konstraints.smt.GetModel
import tools.aqua.konstraints.smt.SymbolAttributeValue
import tools.aqua.konstraints.solvers.z3.Z3Solver

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class ModelTests {
  private fun loadResource(path: String) =
      File(javaClass.getResource(path)!!.file)
          .walk()
          .filter { file: File -> file.isFile }
          .map { file: File -> Arguments.arguments(file) }
          .asStream()

  private fun solve(file: File) {
    assumeTrue(file.length() < 5000000, "Skipped due to file size exceeding limit of 5000000")

    // TODO this creates a massiv memory leak (solver is not closed properly)
    val solver = Z3Solver()
    val result =
        Parser().parse(file.bufferedReader().use(BufferedReader::readLines).joinToString("\n"))

    result.add(GetModel)

    assumeTrue(
        (result.info.find { it.keyword == ":status" }?.value as SymbolAttributeValue)
            .symbol
            .toString() == "sat",
        "Skipped due to unknown or unsat status.")

    solver.use {
      solver.solve(result)

      // verify we get the correct status for the test
      assertEquals(
          (result.info.find { it.keyword == ":status" }?.value as SymbolAttributeValue)
              .symbol
              .toString(),
          solver.status.toString())
    }
  }

  @ParameterizedTest
  @MethodSource("getQFBVFile")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV(file: File) = solve(file)

  fun getQFBVFile(): Stream<Arguments> = loadResource("/QF_BV/20190311-bv-term-small-rw-Noetzli/")
}

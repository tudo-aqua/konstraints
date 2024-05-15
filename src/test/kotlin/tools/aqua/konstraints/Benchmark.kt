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

import java.io.BufferedInputStream
import java.io.BufferedReader
import java.io.InputStreamReader
import java.util.concurrent.TimeUnit
import java.util.stream.Stream
import org.apache.commons.compress.archivers.tar.TarArchiveInputStream
import org.apache.commons.compress.compressors.zstandard.ZstdCompressorInputStream
import org.junit.jupiter.api.*
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.Arguments.arguments
import org.junit.jupiter.params.provider.MethodSource
import tools.aqua.konstraints.parser.Parser
import tools.aqua.konstraints.solvers.z3.Z3Solver

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class Benchmark {

  fun benchmark(): Stream<Arguments> {
    val tarInput =
        TarArchiveInputStream(
            BufferedInputStream(
                ZstdCompressorInputStream(
                    javaClass.getResourceAsStream("/20190311-bv-term-small-rw-Noetzli.tar.zst"))))
    val programs = mutableListOf<String>()

    var entry = tarInput.nextEntry
    while (entry != null) {

      if (entry.isFile) {
        val reader = BufferedReader(InputStreamReader(tarInput))

        var program = ""
        reader.lines().forEach { program += it }
        programs.add(program)
      }

      entry = tarInput.nextEntry
    }

    return programs.map { arguments(it) }.stream()
  }

  @ParameterizedTest
  @MethodSource("benchmark")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun solve(program: String) {
    val solver = Z3Solver()

    val satStatus =
        if (program.contains("unsat")) {
          "unsat"
        } else if (program.contains("unknown")) {
          "unknown"
        } else {
          "sat"
        }

    /* ignore the test if assumption fails, ignores all unknown tests */
    Assumptions.assumeTrue(satStatus != "unknown")

    // TODO(Filter comments)
    val result = Parser.parse(program)

    solver.use {
      result.commands.map { solver.visit(it) }

      // verify we get the correct status for the test
      Assertions.assertEquals(satStatus, solver.status.toString())
    }
  }

  @Test
  fun test() {
    val str =
        ZstdCompressorInputStream(
            javaClass.getResourceAsStream("/20190311-bv-term-small-rw-Noetzli.tar.zst"))
  }
}

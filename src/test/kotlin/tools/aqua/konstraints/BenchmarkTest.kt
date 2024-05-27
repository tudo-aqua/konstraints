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

import java.util.concurrent.TimeUnit
import java.util.stream.Stream
import kotlin.streams.asStream
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Assumptions
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.TestInstance.Lifecycle.PER_CLASS
import org.junit.jupiter.api.Timeout
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.ParameterizedTest.INDEX_PLACEHOLDER
import org.junit.jupiter.params.provider.MethodSource
import tools.aqua.konstraints.parser.Parser
import tools.aqua.konstraints.solvers.z3.Z3Solver
import tools.aqua.konstraints.util.Benchmark
import tools.aqua.konstraints.util.loadBenchmarkDatabase
import tools.aqua.konstraints.util.loadBenchmarks
import tools.aqua.konstraints.util.selectTests
import tools.aqua.konstraints.util.toMetadata

private const val FAST = 1.0
private const val MEDIUM = 5.0

@TestInstance(PER_CLASS)
class BenchmarkTest {

  companion object {
    @JvmStatic private val metadata by lazy { loadBenchmarkDatabase().toMetadata() }

    @JvmStatic
    fun streamUnitTestZ3Benchmarks(): Stream<Benchmark> =
        loadBenchmarks(metadata.selectTests("z3", maxSpeed = FAST, maxPerGroup = 3)).asStream()

    @JvmStatic
    fun streamFastZ3Benchmarks(): Stream<Benchmark> =
        loadBenchmarks(metadata.selectTests("z3", maxSpeed = FAST)).asStream()

    @JvmStatic
    fun streamMediumZ3Benchmarks(): Stream<Benchmark> =
        loadBenchmarks(metadata.selectTests("z3", maxSpeed = MEDIUM)).asStream()

    @JvmStatic
    fun streamAllZ3Benchmarks(): Stream<Benchmark> =
        loadBenchmarks(metadata.selectTests("z3")).asStream()
  }

  @ParameterizedTest(name = "[$INDEX_PLACEHOLDER] {0}")
  @MethodSource("streamUnitTestZ3Benchmarks")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun solve(benchmark: Benchmark) {
    val solver = Z3Solver()

    val satStatus =
        if (benchmark.program.contains("unsat")) {
          "unsat"
        } else if (benchmark.program.contains("unknown")) {
          "unknown"
        } else {
          "sat"
        }

    /* ignore the test if assumption fails, ignores all unknown tests */
    Assumptions.assumeTrue(satStatus != "unknown")

    // TODO(Filter comments)
    val result = Parser.parse(benchmark.program)

    solver.use {
      result.commands.map { solver.visit(it) }

      // verify we get the correct status for the test
      Assertions.assertEquals(satStatus, solver.status.toString())
    }
  }
}

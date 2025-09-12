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

import java.io.BufferedReader
import java.io.File
import java.util.concurrent.TimeUnit
import kotlinx.benchmark.BenchmarkTimeUnit
import kotlinx.benchmark.Mode
import kotlinx.benchmark.Scope
import org.openjdk.jmh.annotations.Benchmark
import org.openjdk.jmh.annotations.BenchmarkMode
import org.openjdk.jmh.annotations.Measurement
import org.openjdk.jmh.annotations.OutputTimeUnit
import org.openjdk.jmh.annotations.Setup
import org.openjdk.jmh.annotations.State
import tools.aqua.konstraints.parser.Parser

@State(Scope.Benchmark)
@BenchmarkMode(Mode.All)
@OutputTimeUnit(BenchmarkTimeUnit.MILLISECONDS)
@Measurement(iterations = 1575, time = 1, timeUnit = TimeUnit.MILLISECONDS)
class ParserBenchmark {
  val programs =
      File(javaClass.getResource("/smt-benchmark/QF_BV/20190311-bv-small-rw-Noetzli")!!.file)
          .walk()
          .filter { file: File -> file.isFile }
          .map { file: File ->
            file.bufferedReader().use(BufferedReader::readLines).joinToString("\n")
          }
          .asSequence()

  var counter = 0
  var program = ""

  @Setup
  fun setProgram() {
    program = programs.elementAtOrElse(counter) { "" }
    counter++
  }

  @Benchmark
  fun QF_BV() {
    Parser().parse(program)
  }
}

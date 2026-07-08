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

import java.io.File
import kotlin.streams.asStream
import org.junit.jupiter.api.Assumptions.assumeTrue
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource
import tools.aqua.konstraints.parser.SMTScriptParser
import tools.aqua.konstraints.smt.SMTProgram
import tools.aqua.konstraints.solvers.NoDefaultSolverAvailableException

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class DefaultSolverTests {
  @ParameterizedTest
  @MethodSource("provideSMTPrograms")
  fun testDefaultSolver(program: SMTProgram) {
    try {
      program.solve(false)
    } catch (e: NoDefaultSolverAvailableException) {
      assumeTrue(false) // skip if no default solver is available
    }
  }

  fun provideSMTPrograms() =
      File(javaClass.getResource("/QF_IDL/")!!.file)
          .walk()
          .filter { file: File -> file.isFile }
          .map { file: File ->
            SMTScriptParser(file.bufferedReader().readLines().joinToString("\n"))
          }
          .asStream()
}

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
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.Timeout
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.Arguments.arguments
import org.junit.jupiter.params.provider.MethodSource
import tools.aqua.konstraints.parser.Parser
import tools.aqua.konstraints.smt.BVLiteral
import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.smt.FPLiteral
import tools.aqua.konstraints.smt.FPMinusZero
import tools.aqua.konstraints.smt.FPNaN
import tools.aqua.konstraints.smt.FPZero
import tools.aqua.konstraints.smt.GetModel
import tools.aqua.konstraints.smt.IntLiteral
import tools.aqua.konstraints.smt.RealDiv
import tools.aqua.konstraints.smt.RealLiteral
import tools.aqua.konstraints.smt.SMTProgram
import tools.aqua.konstraints.smt.StringLiteral
import tools.aqua.konstraints.smt.SymbolAttributeValue
import tools.aqua.konstraints.smt.bitvec
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

    @ParameterizedTest
    @MethodSource("provideProgramAndModel")
    fun testModel(program : String, term : Expression<*>) {
        val prg = Parser().parse(program)
        val solver = Z3Solver()

        solver.use {
            solver.solve(prg)
            assertEquals(term, solver.model.definitions.single().term)
        }
    }

    fun provideProgramAndModel(): Stream<Arguments> = Stream.of(
        arguments("(set-logic QF_BV)(declare-fun foo () (_ BitVec 8))(assert (= foo #b00000000))(check-sat)(get-model)",
            BVLiteral("#b00000000")),
        arguments("(set-logic QF_FP)(declare-fun foo () Float16)(assert (= foo (_ +zero 5 11)))(check-sat)(get-model)",
            FPZero(5, 11)),
        arguments("(set-logic QF_FP)(declare-fun foo () Float16)(assert (= foo (fp #b0 #b00000 #b0000000000)))(check-sat)(get-model)",
            FPZero(5, 11)),
        /*arguments("(set-logic QF_FP)(declare-fun foo () Float16)(assert (= foo (fp #b0 #b00000 #b0000000000)))(check-sat)(get-model)",
            FPLiteral("#b0".bitvec(), "#b00000".bitvec(), "#b0000000000".bitvec())),*/
        arguments("(set-logic QF_FP)(declare-fun foo () Float16)(assert (= foo (fp #b1 #b00000 #b0000000000)))(check-sat)(get-model)",
            FPMinusZero(5, 11)),
        arguments("(set-logic QF_S)(declare-fun foo () String)(assert (= (str.len foo) 0))(check-sat)(get-model)",
            StringLiteral("")),
        arguments("(set-logic QF_LIA)(declare-fun foo () Int)(assert (= foo 0))(check-sat)(get-model)",
            IntLiteral(0)),
        arguments("(set-logic QF_FP)(declare-fun foo () Float16)(assert (= foo (fp.add roundTowardZero foo (fp #b0 #b00000 #b0000000001))))(check-sat)(get-model)",
            FPNaN(5, 11)),
        arguments("(set-logic QF_LRA)(declare-fun foo () Real)(assert (= foo 0.0))(check-sat)(get-model)",
            RealLiteral(0)),
        arguments("(set-logic QF_LIRA)(declare-fun foo () Real)(assert (= foo (/ 2.0 5.0)))(check-sat)(get-model)",
            RealDiv(RealLiteral(2), RealLiteral(5))),
        /*arguments("(set-logic QF_LIRA)(declare-fun foo () Real)(assert (= foo 0.000000000000000000001))(check-sat)(get-model)",
            RealDiv(RealLiteral(1), RealLiteral(1000000000000000000000.0)))*/
    )

  @Test
  fun test() {
    val solver = Z3Solver()
    val program =
        Parser()
            .parse(
                "(set-logic QF_S)(declare-fun foo () String)(declare-fun bar () String)(assert (= (str.len foo) 0))(assert (= bar \"bar\"))(check-sat)(get-model)(exit)")

    solver.use {
      solver.solve(program)
      solver.model
    }
  }
}

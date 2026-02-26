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

import java.util.stream.Stream
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.Arguments.arguments
import org.junit.jupiter.params.provider.MethodSource
import tools.aqua.konstraints.dsl.BenchmarkCategory
import tools.aqua.konstraints.dsl.smt
import tools.aqua.konstraints.smt.BooleanOptionValue
import tools.aqua.konstraints.smt.CheckSat
import tools.aqua.konstraints.smt.ConstantAttributeValue
import tools.aqua.konstraints.smt.NumeralOptionValue
import tools.aqua.konstraints.smt.QF_UF
import tools.aqua.konstraints.smt.SMTBool
import tools.aqua.konstraints.smt.SatStatus
import tools.aqua.konstraints.smt.Sort
import tools.aqua.konstraints.smt.StringConstant
import tools.aqua.konstraints.smt.StringOptionValue
import tools.aqua.konstraints.smt.getFunc
import tools.aqua.konstraints.solvers.z3.Z3Solver

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class ProgramDSLTests {
  /*
   * make general tests
   * - test that all options/infos were added
   * - test that all options/infos have the right values
   * - test that assert has right expression
   * - test "in program" solving
   */
  val solver = Z3Solver()

  val program =
      smt(QF_UF) {
        setInfo {
          version("2.6")
          source("This is a test program")
          license("https://creativecommons.org/licenses/by/4.0/")
          category(BenchmarkCategory.CRAFTED)
          status(SatStatus.SAT)
          "flag" set_to "value"
        }

        // set all named options to their default value
        setOptions {
          diagnosticOutputChannel("stderr")
          globalDeclarations(false)
          printSuccess(false)
          produceAssertions(false)
          produceAssignments(false)
          produceModels(false)
          produceProofs(false)
          produceUnsatAssumptions(false)
          produceUnsatCores(false)
          randomSeed(0)
          regularOutputChannel("stdout")
          reproducibleResourceLimit(0)
          "option" set_to "value"
        }

        val x = const("x", SMTBool)

        assert { x }
        checkSat(solver)
        solver.close()
      }

  @ParameterizedTest
  @MethodSource("getInfoStringAndValue")
  fun testStringInfo(name: String, value: String) {
    assertEquals(
        ((program.info(name) as ConstantAttributeValue).constant as StringConstant).string,
        value,
    )
  }

  fun getInfoStringAndValue(): Stream<Arguments> =
      Stream.of(
          arguments("license", "https://creativecommons.org/licenses/by/4.0/"),
          arguments("category", "crafted"),
          arguments("status", "sat"),
          arguments("flag", "value"),
      )

  @ParameterizedTest
  @MethodSource("getBooleanOptionsAndValue")
  fun testBooleanOptions(name: String, value: Boolean) {
    assertEquals((program.option(name) as BooleanOptionValue).bool, value)
  }

  fun getBooleanOptionsAndValue(): Stream<Arguments> =
      Stream.of(
          arguments("global-declarations", false),
          arguments("print-success", false),
          arguments("produce-assertions", false),
          arguments("produce-assignments", false),
          arguments("produce-models", false),
          arguments("produce-proofs", false),
          arguments("produce-unsat-assumptions", false),
          arguments("produce-unsat-cores", false),
      )

  @ParameterizedTest
  @MethodSource("getStringOptionsAndValue")
  fun testStringOptions(name: String, value: String) {
    assertEquals((program.option(name) as StringOptionValue).string, value)
  }

  fun getStringOptionsAndValue(): Stream<Arguments> =
      Stream.of(
          arguments("diagnostic-output-channel", "stderr"),
          arguments("regular-output-channel", "stdout"),
          arguments("option", "value"),
      )

  @ParameterizedTest
  @MethodSource("getNumeralsOptionsAndValue")
  fun testNumeralsOptions(name: String, value: Int) {
    assertEquals((program.option(name) as NumeralOptionValue).numeral.toInt(), value)
  }

  fun getNumeralsOptionsAndValue(): Stream<Arguments> =
      Stream.of(arguments("random-seed", 0), arguments("reproducible-resource-limit", 0))

  @ParameterizedTest
  @MethodSource("getFunNameAndSort")
  fun testFunRegistration(name: String, sort: Sort) {
    assertEquals(program.context.getFunc(name).sort, sort)
  }

  fun getFunNameAndSort(): Stream<Arguments> = Stream.of(arguments("x", SMTBool))

  @Test
  fun testCheckSatExists() {
    assert(program.commands.filterIsInstance<CheckSat>().isNotEmpty())
  }

  @Test
  fun testSatStatusIsSet() {
    assertEquals(program.status, SatStatus.SAT)
  }
}

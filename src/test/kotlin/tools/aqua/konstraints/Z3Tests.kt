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
import java.util.concurrent.TimeUnit
import java.util.stream.Stream
import kotlin.streams.asStream
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assumptions.assumeTrue
import org.junit.jupiter.api.Disabled
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
import tools.aqua.konstraints.parser.SymbolAttributeValue
import tools.aqua.konstraints.smt.Command
import tools.aqua.konstraints.solvers.z3.Z3Solver

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class Z3Tests {

  private fun loadResource(path: String) =
      File(javaClass.getResource(path)!!.file)
          .walk()
          .filter { file: File -> file.isFile }
          .map { file: File -> Arguments.arguments(file) }
          .asStream()

  private fun solve(file: File) {
    val solver = Z3Solver()
    val result = Parser.parse(file.bufferedReader().readLines().joinToString(""))

    assumeTrue(
        (result.info.find { it.keyword == ":status" }?.value as SymbolAttributeValue)
            .symbol
            .toString() != "unknown")

    solver.use {
      result.commands.map { solver.visit(it) }

      // verify we get the correct status for the test
      assertEquals(
          (result.info.find { it.keyword == ":status" }?.value as SymbolAttributeValue)
              .symbol
              .toString(),
          solver.status.toString())
    }
  }

  @ParameterizedTest
  @MethodSource("getInts")
  @Timeout(value = 10, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV(id: Int) {
    /*
     * These test are currently not working with Z3 as the solver is not capable of solving them yet
     */
    if (id in listOf(524, 928, 1105, 1299, 1323, 1492)) {
      return
    }

    // For some reason these cases time out sometimes, skip them for now
    if (id in listOf(382, 426, 433, 672, 737, 776)) {
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
        assertEquals(satStatus, solver.status.toString())

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

  // disable these for now as they take too long to compute
  @Disabled
  @ParameterizedTest
  @MethodSource("getQFIDLFile")
  @Timeout(value = 60, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_IDL(file: File) = solve(file)

  fun getQFIDLFile(): Stream<Arguments> = loadResource("/QF_IDL/20210312-Bouvier/")

  @ParameterizedTest
  @MethodSource("getQFIDLLetFile")
  @Timeout(value = 60, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_IDL_Let(file: File) = solve(file)

  fun getQFIDLLetFile(): Stream<Arguments> = loadResource("/QF_IDL/Averest/binary_search")

  @ParameterizedTest
  @MethodSource("getQFRDLFile")
  @Timeout(value = 20, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_RDL(file: File) = solve(file)

  fun getQFRDLFile(): Stream<Arguments> = loadResource("/QF_RDL/scheduling/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getQFBVFile")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_Full(file: File) = solve(file)

  fun getQFBVFile(): Stream<Arguments> = loadResource("/non-incremental/QF_BV/")

  /* these tests take too long ignore for now */
  @Disabled
  @ParameterizedTest
  @MethodSource("getQFRDLLetFile")
  @Timeout(value = 60, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_RDL_Let(file: File) = solve(file)

  fun getQFRDLLetFile(): Stream<Arguments> = loadResource("/QF_RDL/sal/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getQFUFFile")
  @Timeout(value = 60, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_UF(file: File) = solve(file)

  fun getQFUFFile(): Stream<Arguments> = loadResource("/QF_UF/")

  @ParameterizedTest
  @MethodSource("getQFFPFile")
  @Timeout(value = 6000, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_FP(file: File) = solve(file)

  fun getQFFPFile(): Stream<Arguments> = loadResource("/QF_FP/")

  @ParameterizedTest
  @MethodSource("getQFAXFile")
  @Timeout(value = 20, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_AX(file: File) = solve(file)

  fun getQFAXFile(): Stream<Arguments> = loadResource("/QF_AX/aqua/")

  @ParameterizedTest
  @MethodSource("getQFIDLModelsFile")
  @Timeout(value = 20, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_IDL_Models(file: File) = solve(file)

  fun getQFIDLModelsFile(): Stream<Arguments> = loadResource("/QF_IDL/Models/")

  @ParameterizedTest
  @MethodSource("getQFBVModelsFile")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_Models(file: File) = solve(file)

  fun getQFBVModelsFile(): Stream<Arguments> = loadResource("/QF_BV/Models/")

  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "(set-logic QF_BV)(declare-fun A () (_ BitVec 32))(declare-fun B () (_ BitVec 16))(assert (bvult ((_ extract 15 0) A) B))(check-sat)"])
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
        assertEquals("sat", solver.status.toString())
      }
    } else {
      throw ParseError(result.failure(result.message))
    }
  }

  @ParameterizedTest
  @ValueSource(
      strings =
          [
              """
        (set-logic QF_BV) 
        (declare-fun x_0 () (_ BitVec 32))
        (declare-fun x_1 () (_ BitVec 32))
        (declare-fun x_2 () (_ BitVec 32))   
        (declare-fun y_0 () (_ BitVec 32))
        (declare-fun y_1 () (_ BitVec 32))   
        (assert (= x_1 (bvadd x_0 y_0))) 
        (assert (= y_1 (bvadd x_1 y_0)))
        (assert (= x_2 (bvadd x_1 y_1)))
        (assert (not (and (= x_2 y_0) (= y_1 x_0))))
        (check-sat)
        (exit)        
    """])
  fun testEquals(program: String) {
    val solver = Z3Solver()

    val result = Parser.parse(program)
    solver.use {
      result.commands.map { solver.visit(it) }

      // verify we get the correct status for the test
      assertEquals("sat", solver.status.toString())
    }
  }

  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "(set-logic QF_UF)(declare-fun A () Bool)(declare-fun B () Bool)(assert (let ((C (and A B))) (and C (not C))))(check-sat)"])
  fun testLet(program: String) {
    val solver = Z3Solver()

    val result = Parser.parse(program)
    solver.use {
      result.commands.map { solver.visit(it) }

      // verify we get the correct status for the test
      assertEquals("unsat", solver.status.toString())
    }
  }

  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "(set-logic QF_UF)(declare-fun A (Bool) Bool)(declare-fun B () Bool)(assert (and (A B) B))(check-sat)(exit)"])
  fun testFreeFunctions(program: String) {
    val solver = Z3Solver()

    val result = Parser.parse(program)
    solver.use {
      result.commands.map { solver.visit(it) }

      // verify we get the correct status for the test
      assertEquals("sat", solver.status.toString())
    }
  }

  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "(set-logic QF_BV)(set-info :status sat)(assert (exists ((A (_ BitVec 8)) (B (_ BitVec 8))) (= (bvadd A B) (bvmul A B))))(check-sat)",
              "(set-logic QF_IDL)(set-info :status unsat)(assert (forall ((A Int) (B Int)) (>= (* A B) (+ A B))))(check-sat)",
              "(set-logic QF_BV)(set-info :status unsat)(assert (forall ((A (_ BitVec 8))) (exists ((B (_ BitVec 8))) (bvult A B))))(check-sat)"])
  fun testQuantifier(program: String) {
    val solver = Z3Solver()

    val result = Parser.parse(program)

    solver.use {
      result.commands.map { solver.visit(it) }

      // verify we get the correct status for the test
      assertEquals(
          (result.info.find { it.keyword == ":status" }?.value as SymbolAttributeValue)
              .symbol
              .toString(),
          solver.status.toString())
    }
  }

  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "(set-logic QF_UF)(set-info :status sat)(declare-fun A () Bool)(push 1)(declare-fun B () Bool)(assert (= A B))(pop 1)(check-sat)"])
  fun testPushPop(program: String) {
    val solver = Z3Solver()

    val result = Parser.parse(program)

    solver.use {
      result.commands.map { solver.visit(it) }

      // verify we get the correct status for the test
      assertEquals(
          (result.info.find { it.keyword == ":status" }?.value as SymbolAttributeValue)
              .symbol
              .toString(),
          solver.status.toString())
    }
  }

  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "(set-logic QF_BV)(set-info :status sat)(declare-fun A () (_ BitVec 8))(define-fun B () (_ BitVec 8) (bvneg A))(assert (= A (bvneg B)))(check-sat)",
              "(set-logic QF_BV)(set-info :status sat)(define-fun bvugt8 ((lhs (_ BitVec 8)) (rhs (_ BitVec 8))) Bool (and (not (= lhs rhs)) (not (bvult lhs rhs))))(declare-fun A () (_ BitVec 8))(declare-fun B () (_ BitVec 8))(assert (bvugt8 A B))(check-sat)"])
  fun testDefineFun(program: String) {
    val solver = Z3Solver()

    val result = Parser.parse(program)

    solver.use {
      result.commands.map { solver.visit(it) }

      // verify we get the correct status for the test
      assertEquals(
          (result.info.find { it.keyword == ":status" }?.value as SymbolAttributeValue)
              .symbol
              .toString(),
          solver.status.toString())
    }
  }
}

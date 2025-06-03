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
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assumptions.assumeTrue
import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.Timeout
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import org.junit.jupiter.params.provider.ValueSource
import tools.aqua.konstraints.parser.Parser
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.smt.VarBinding
import tools.aqua.konstraints.solvers.z3.Z3Solver
import tools.aqua.konstraints.theories.*

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class Z3Tests {
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

    assumeTrue(
        (result.info.find { it.keyword == ":status" }?.value as SymbolAttributeValue)
            .symbol
            .toString() != "unknown",
        "Skipped due to unknown sat status.")

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
  @Timeout(value = 30, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_RDL(file: File) = solve(file)

  fun getQFRDLFile(): Stream<Arguments> = loadResource("/QF_RDL/scheduling/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getQFBVFile")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_Full(file: File) = solve(file)

  fun getQFBVFile(): Stream<Arguments> = loadResource("/QF_BV/")

  /* these tests take too long ignore for now */
  @Disabled
  @ParameterizedTest
  @MethodSource("getQFRDLLetFile")
  @Timeout(value = 60, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_RDL_Let(file: File) = solve(file)

  fun getQFRDLLetFile(): Stream<Arguments> = loadResource("/QF_RDL/sal/")

  @ParameterizedTest
  @MethodSource("getQFUFFile")
  @Timeout(value = 600, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_UF(file: File) = solve(file)

  fun getQFUFFile(): Stream<Arguments> = loadResource("/QF_UF/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getQFFPFile")
  @Timeout(value = 10, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_FP(file: File) = solve(file)

  fun getQFFPFile(): Stream<Arguments> = loadResource("/QF_FP/")

  @ParameterizedTest
  @MethodSource("getUFFile")
  @Timeout(value = 600, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun UF(file: File) = solve(file)

  fun getUFFile(): Stream<Arguments> = loadResource("/UF/")

  @ParameterizedTest
  @MethodSource("getQFAXFile")
  @Timeout(value = 20, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_AX(file: File) = solve(file)

  fun getQFAXFile(): Stream<Arguments> = loadResource("/QF_AX/aqua/")

  @ParameterizedTest
  @MethodSource("getQFABVFile")
  @Timeout(value = 600, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_ABV(file: File) = solve(file)

  fun getQFABVFile(): Stream<Arguments> = loadResource("/QF_ABV/bench_ab/")

  @ParameterizedTest
  @MethodSource("getQFFPLRAFile")
  @Timeout(value = 60, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_FPLRA(file: File) = solve(file)

  fun getQFFPLRAFile(): Stream<Arguments> = loadResource("/QF_FPLRA/")

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
    val solver = Z3Solver()

    val smtProgram = Parser().parse(program)

    solver.use {
      smtProgram.commands.map { solver.visit(it) }

      // verify we get the correct status for the test
      assertEquals("sat", solver.status.toString())
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

    val result = Parser().parse(program)
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

    val result = Parser().parse(program)
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

    val result = Parser().parse(program)
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

    val result = Parser().parse(program)

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

    val result = Parser().parse(program)

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

    val result = Parser().parse(program)

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
  @MethodSource("getTerms")
  fun testDirectSolvingMode(terms: List<Expression<BoolSort>>) {
    val solver = Z3Solver()

    val status = solver.solve(terms)

    println(status)
  }

  fun getTerms(): Stream<Arguments> {
    val program = MutableSMTProgram()
    val sort = BVSort(16)
    val lhs = program.declareConst("lhs".toSymbolWithQuotes(), sort)()
    val rhs = program.declareConst("rhs".toSymbolWithQuotes(), sort)()
    val msb_s =
        VarBinding(
            "?msb_s".toSymbolWithQuotes(), BVExtract(lhs.sort.bits - 1, lhs.sort.bits - 1, lhs))
    val msb_t =
        VarBinding(
            "?msb_t".toSymbolWithQuotes(), BVExtract(lhs.sort.bits - 1, lhs.sort.bits - 1, rhs))
    val abs_s =
        VarBinding(
            "?abs_s".toSymbolWithQuotes(),
            Ite(Equals(msb_s.instance, BVLiteral("#b0")), lhs, BVNeg(lhs)))
    val abs_t =
        VarBinding(
            "?abs_t".toSymbolWithQuotes(),
            Ite(Equals(msb_s.instance, BVLiteral("#b0")), rhs, BVNeg(rhs)))
    val u = VarBinding("u".toSymbolWithQuotes(), BVURem(abs_s.instance, abs_t.instance))

    val A = program.declareConst("A".toSymbolWithQuotes(), IntSort)()
    val B = program.declareConst("B".toSymbolWithQuotes(), IntSort)()

    return Stream.of(
        Arguments.arguments(listOf(And(IntGreaterEq(A, B), IntLessEq(A, B)))),
        Arguments.arguments(
            listOf(
                Equals(
                    LetExpression(
                        listOf(msb_s, msb_t),
                        LetExpression(
                            listOf(abs_s, abs_t),
                            LetExpression(
                                listOf(u),
                                Ite(
                                    Equals(u.instance, BVLiteral("#b0", sort.bits)),
                                    u.instance,
                                    Ite(
                                        And(
                                            Equals(msb_s.instance, BVLiteral("#b0")),
                                            Equals(msb_t.instance, BVLiteral("#b0"))),
                                        u.instance,
                                        Ite(
                                            And(
                                                Equals(msb_s.instance, BVLiteral("#b1")),
                                                Equals(msb_t.instance, BVLiteral("#b0"))),
                                            BVAdd(BVNeg(u.instance), rhs),
                                            Ite(
                                                And(
                                                    Equals(msb_s.instance, BVLiteral("#b0")),
                                                    Equals(msb_t.instance, BVLiteral("#b1"))),
                                                BVAdd(u.instance, rhs),
                                                BVNeg(u.instance)))))))),
                    BVSMod(lhs, rhs)))),
    /*Arguments.arguments(
            listOf(
                Equals(
                    LetExpression(
                        VarBinding(
                            "?msb_s".symbol(),
                            BVExtract(lhs.sort.bits - 1, lhs.sort.bits - 1, lhs)),
                        VarBinding(
                            "?msb_t".symbol(),
                            BVExtract(lhs.sort.bits - 1, lhs.sort.bits - 1, rhs))) { msb_s, msb_t ->
                          LetExpression(
                              VarBinding(
                                  "?abs_s".symbol(),
                                  Ite(Equals(msb_s, BVLiteral("#b0")), lhs, BVNeg(lhs))),
                              VarBinding(
                                  "?abs_t".symbol(),
                                  Ite(Equals(msb_s, BVLiteral("#b0")), rhs, BVNeg(rhs)))) {
                                  abs_s,
                                  abs_t ->
                                LetExpression(
                                    VarBinding(
                                        "u".symbol(),
                                        BVURem(
                                            abs_s castTo BVSort((abs_s.sort as BVSort).bits),
                                            abs_t castTo BVSort((abs_t.sort as BVSort).bits)))) { u
                                      ->
                                      Ite(
                                          Equals(u, BVLiteral("#b0", sort.bits)),
                                          u,
                                          Ite(
                                              And(
                                                  Equals(msb_s, BVLiteral("#b0")),
                                                  Equals(msb_t, BVLiteral("#b0"))),
                                              u,
                                              Ite(
                                                  And(
                                                      Equals(msb_s, BVLiteral("#b1")),
                                                      Equals(msb_t, BVLiteral("#b0"))),
                                                  BVAdd(
                                                      BVNeg(
                                                          u castTo
                                                              BVSort((abs_t.sort as BVSort).bits)),
                                                      rhs),
                                                  Ite(
                                                      And(
                                                          Equals(msb_s, BVLiteral("#b0")),
                                                          Equals(msb_t, BVLiteral("#b1"))),
                                                      BVAdd(
                                                          u castTo
                                                              BVSort((abs_t.sort as BVSort).bits),
                                                          rhs),
                                                      BVNeg(
                                                          u castTo
                                                              BVSort(
                                                                  (abs_t.sort as BVSort).bits))))))
                                    }
                              }
                        },
                    BVSMod(lhs, rhs))))*/ )
  }
}

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

// import dsl to construct test expressions
import java.io.BufferedReader
import java.io.File
import java.util.stream.Stream
import kotlin.io.bufferedReader
import kotlin.streams.asStream
import kotlin.use
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.assertDoesNotThrow
import org.junit.jupiter.api.assertThrows
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.Arguments.arguments
import org.junit.jupiter.params.provider.MethodSource
import tools.aqua.konstraints.dsl.*
import tools.aqua.konstraints.parser.Parser
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.smt.BVSort
import tools.aqua.konstraints.smt.BoolSort
import tools.aqua.konstraints.smt.FPSort
import tools.aqua.konstraints.smt.bitvec

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class SMTProgramTests {
  // test basic expressions
  val coreProgram = MutableSMTProgram().apply { setLogic(UF) }
  val coreFunA = coreProgram.declareConst("A!bool".toSymbolWithQuotes(), Bool)()
  val coreFunB = coreProgram.declareConst("B!bool".toSymbolWithQuotes(), Bool)()
  val coreExpressionA = (not { coreFunB and coreFunA }) eq (not(coreFunA) and not(coreFunB))

  val bvProgram =
      MutableSMTProgram().apply {
        setLogic(BV)
        declareFun(coreFunA.func as UserDeclaredSMTFunction<BoolSort>)
      }
  val bvFunA = bvProgram.declareConst("A!bitvec".toSymbolWithQuotes(), BVSort(8))()
  val bvFunB = bvProgram.declareConst("B!bitvec".toSymbolWithQuotes(), BVSort(8))()
  val bvExpressionA = (bvFunA bvadd bvFunB) eq bvneg((bvneg(bvFunA) bvadd bvneg(bvFunB)))
  val bvExpressionB = ite { coreFunA } then { bvFunA } otherwise { bvFunB } eq bvFunA

  val fpProgram = MutableSMTProgram().apply { setLogic(FP) }
  val fpFunA = fpProgram.declareConst("A!fp".toSymbolWithQuotes(), FPSort(3, 5))()
  val fpFunB = fpProgram.declareConst("B!fp".toSymbolWithQuotes(), FPSort(3, 5))()
  val fpExpressionA = (fpFunA fpadd fpFunB) eq (fpFunB fpadd fpFunA)

  val bvfpProgram =
      MutableSMTProgram().apply {
        setLogic(QF_BVFP)
        declareFun(fpFunA.func as UserDeclaredSMTFunction<FPSort>)
        declareFun(fpFunB.func as UserDeclaredSMTFunction<FPSort>)
        declareFun(bvFunA.func as UserDeclaredSMTFunction<BVSort>)
        declareFun(bvFunB.func as UserDeclaredSMTFunction<BVSort>)
      }
  val bvfpExpressionA =
      (fpFunA.toUBV(8) concat fpFunB.toUBV(8)) eq (bvneg(bvFunA) concat bvneg(bvFunB))

  // test literals
  val bvExpressionC = (bvFunA bvadd "#xFF".bitvec(8)) eq bvneg((bvneg(bvFunA) bvadd bvneg(bvFunB)))

  @ParameterizedTest
  @MethodSource("getExpressionsPositiv")
  fun testLogicConstaintsPositiv(program: MutableSMTProgram, expr: Expression<BoolSort>) {
    assertDoesNotThrow { program.assert(expr) }
  }

  private fun getExpressionsPositiv(): Stream<Arguments> {
    return Stream.of(
        arguments(coreProgram, coreExpressionA),
        arguments(bvProgram, bvExpressionA),
        arguments(fpProgram, fpExpressionA),
        arguments(bvfpProgram, bvfpExpressionA),
        arguments(bvProgram, bvExpressionB),
        arguments(bvProgram, bvExpressionC),
        arguments(
            coreProgram, exists(Bool) { local -> (local eq coreFunA) and (local eq coreFunB) }),
        arguments(
            coreProgram, forall(Bool) { local -> (local eq coreFunA) and (local eq coreFunB) }))
  }

  @ParameterizedTest
  @MethodSource("getExpressionsNegativ")
  fun testLogicConstaintsNegativ(logic: Logic, expr: Expression<BoolSort>) {
    val program = MutableSMTProgram()

    program.setLogic(logic)
    assertThrows<AssertionOutOfLogicBounds> { program.assert(expr) }
  }

  private fun getExpressionsNegativ(): Stream<Arguments> {
    return Stream.of(arguments(QF_UF, bvExpressionA), arguments(QF_UF, bvExpressionB))
  }

  @ParameterizedTest
  @MethodSource("getUnregisteredExpressions")
  fun testUnregisteredFunctionsThrowInAssert(
      program: MutableSMTProgram,
      expr: Expression<BoolSort>
  ) {
    assertThrows<IllegalArgumentException> { program.assert(expr) }
  }

  private fun getUnregisteredExpressions(): Stream<Arguments> {
    return Stream.of(
        arguments(
            coreProgram,
            UserDeclaredSMTFunction0("Unregistered!bool".toSymbolWithQuotes(), Bool)()))
  }

  private fun providePrograms(path: String) =
      File(javaClass.getResource(path)!!.file)
          .walk()
          .filter { file: File -> file.isFile }
          .map { file: File ->
            arguments(
                Parser()
                    .parse(file.bufferedReader().use(BufferedReader::readLines).joinToString("\n")))
          }
          .asStream()

  private fun provideQF_BV() = providePrograms("/QF_BV/20190311-bv-term-small-rw-Noetzli/")

  private fun provideQF_IDL() = providePrograms("/QF_IDL/")

  private fun provideQF_RDL() = providePrograms("/QF_RDL/")

  private fun provideUF() = providePrograms("/UF/")

  private fun provideFP() = providePrograms("/FP/")

  private fun provideCustom() =
      Stream.of(
          arguments(
              Parser()
                  .parse(
                      "(set-logic BVFP)\n" +
                          "(define-sort bitvec () (_ BitVec 8))\n" +
                          "(declare-const foo bitvec)\n" +
                          "(declare-const bar bitvec)\n" +
                          "(declare-const fpfoo Float16)\n" +
                          "(declare-const fpbar Float16)\n" +
                          "(declare-const rm RoundingMode)\n" +
                          "(assert (! (forall ((a bitvec)) (exists ((b bitvec)) (let ((c (bvand a b))) (and (= c #b00000000) (not (= a #b00000000)) (not (= b #b00000000)))))) :comment |Check that forall a there exists an inverse element w.r.t. addition|))\n" +
                          "(assert (= (bvneg foo) (bvxor foo bar)))\n" +
                          "(assert (bvult #b00000000 (ite (bvult foo bar) (bvneg foo) (bvneg bar))))\n" +
                          "(assert (not (fp.eq (fp.neg fpfoo) (fp.fma rm fpfoo fpbar fpfoo) (fp.add rm fpfoo fpbar))))\n" +
                          "(assert (fp.eq (fp.roundToIntegral RTZ fpfoo) (fp.roundToIntegral RTP fpfoo)))\n" +
                          "(check-sat)")))
}

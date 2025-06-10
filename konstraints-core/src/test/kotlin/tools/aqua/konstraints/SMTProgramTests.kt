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
import java.util.stream.Stream
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.assertDoesNotThrow
import org.junit.jupiter.api.assertThrows
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.Arguments.arguments
import org.junit.jupiter.params.provider.MethodSource
import tools.aqua.konstraints.dsl.*
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.smt.BVSort
import tools.aqua.konstraints.smt.BoolSort
import tools.aqua.konstraints.smt.FPSort
import tools.aqua.konstraints.smt.bitvec

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class SMTProgramTests {
  // test basic expressions
  val coreProgram = MutableSMTProgram().apply { setLogic(UF) }
  val coreFunA = coreProgram.declareConst("A!bool".toSymbolWithQuotes(), BoolSort)()
  val coreFunB = coreProgram.declareConst("B!bool".toSymbolWithQuotes(), BoolSort)()
  val coreExpressionA = (not { coreFunB and coreFunA }) eq (not(coreFunA) and not(coreFunB))

  val bvProgram =
      MutableSMTProgram().apply {
        setLogic(BV)
        declareFun(coreFunA.func as DeclaredSMTFunction<BoolSort>)
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
        declareFun(fpFunA.func as DeclaredSMTFunction<FPSort>)
        declareFun(fpFunB.func as DeclaredSMTFunction<FPSort>)
        declareFun(bvFunA.func as DeclaredSMTFunction<BVSort>)
        declareFun(bvFunB.func as DeclaredSMTFunction<BVSort>)
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
            coreProgram, exists(BoolSort) { local -> (local eq coreFunA) and (local eq coreFunB) }),
        arguments(
            coreProgram, forall(BoolSort) { local -> (local eq coreFunA) and (local eq coreFunB) }))
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
            UserDeclaredSMTFunction0("Unregistered!bool".toSymbolWithQuotes(), BoolSort)()))
  }
}

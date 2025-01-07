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
import tools.aqua.konstraints.theories.BVSort
import tools.aqua.konstraints.theories.BoolSort
import tools.aqua.konstraints.theories.FPSort
import tools.aqua.konstraints.theories.bitvec

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class SMTProgramTests {
  // test basic expressions
  val coreFunA = UserDeclaredExpression<BoolSort>("A".symbol(), BoolSort)
  val coreFunB = UserDeclaredExpression<BoolSort>("B".symbol(), BoolSort)
  val coreExpressionA = (not { coreFunB and coreFunA }) eq (not(coreFunA) and not(coreFunB))

  val bvFunA = UserDeclaredExpression<BVSort>("A".symbol(), BVSort(8))
  val bvFunB = UserDeclaredExpression<BVSort>("B".symbol(), BVSort(8))
  val bvExpressionA = (bvFunA bvadd bvFunB) eq bvneg((bvneg(bvFunA) bvadd bvneg(bvFunB)))
  val bvExpressionB = ite { coreFunA } then { bvFunA } otherwise { bvFunB } eq bvFunA

  val fpFunA = UserDeclaredExpression<FPSort>("A".symbol(), FPSort(3, 5))
  val fpFunB = UserDeclaredExpression<FPSort>("B".symbol(), FPSort(3, 5))
  val fpExpressionA = (fpFunA fpadd fpFunB) eq (fpFunB fpadd fpFunA)

  val bvfpExpressionA =
      (fpFunA.toUBV(8) concat fpFunB.toUBV(8)) eq (bvneg(bvFunA) concat bvneg(bvFunB))

  // test literals
  val bvExpressionC = (bvFunA bvadd "#xFF".bitvec(8)) eq bvneg((bvneg(bvFunA) bvadd bvneg(bvFunB)))

  @ParameterizedTest
  @MethodSource("getExpressionsPositiv")
  fun testLogicConstaintsPositiv(logic: Logic, expr: Expression<BoolSort>) {
    val program = MutableSMTProgram()

    program.setLogic(logic)
    assertDoesNotThrow { program.assert(expr) }
  }

  private fun getExpressionsPositiv(): Stream<Arguments> {
    return Stream.of(
        arguments(QF_UF, coreExpressionA),
        arguments(QF_BV, bvExpressionA),
        arguments(QF_FP, fpExpressionA),
        arguments(QF_BVFP, bvfpExpressionA),
        arguments(QF_BV, bvExpressionB),
        arguments(QF_BV, bvExpressionC))
  }

  @ParameterizedTest
  @MethodSource("getExpressionsNegativ")
  fun testLogicConstaintsNegativ(logic: Logic, expr: Expression<BoolSort>) {
    val program = MutableSMTProgram()

    program.setLogic(logic)
    assertThrows<IllegalArgumentException> { program.assert(expr) }
  }

  private fun getExpressionsNegativ(): Stream<Arguments> {
    return Stream.of(arguments(QF_UF, bvExpressionA), arguments(QF_UF, bvExpressionB))
  }
}

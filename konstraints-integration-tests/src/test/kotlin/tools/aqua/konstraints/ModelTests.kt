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
import org.junit.jupiter.params.provider.MethodSource
import tools.aqua.konstraints.dsl.*
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.solvers.InteractiveZ3Solver
import tools.aqua.konstraints.visitors.FreeVariables
import tools.aqua.konstraints.visitors.RecursionPolicy

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class TestModel {
  private fun provideProgram() =
      Stream.of(
          Arguments.arguments(
              smt(QF_BV) {
                val s by declaringConst(SMTBitVec(32))
                val t by declaringConst(SMTBitVec(32))
                assert { (s bvor (t bvor t)) eq (s bvor t) }
                checkSat()
                getModel()
              }
          ),
          Arguments.arguments(
              smt(QF_BVFP) {
                val `d_ackerman!0` by declaring(SMTBitVec(64))
                val fpsort = FPSort(11, 53)
                assert {
                  not(
                      not(
                          `d_ackerman!0`.instance.toFP(fpsort) fplt
                              4613937818241073152.bitvec(64).toFP(fpsort)
                      )
                  )
                }
                checkSat()
                getModel()
              }
          ),
          /*
           * this can be solved but the model contains 'as', which is not yet supported in constraints
          Arguments.arguments(
              smt(QF_ABV) {
                  val x by declaring(SMTArray(SMTBitVec(32), SMTBitVec(8)))
                  val y by declaring(SMTArray(SMTBitVec(32), SMTBitVec(8)))

                  assert {
                      0.bitvec(30) concat (x.instance select 0.bitvec(32)).extract(2, 1) eq 2.bitvec(32)
                  }

                  assert {
                      not(not((y.instance select 0.bitvec(32)).extract(3, 3) eq 0.bitvec(1)))
                  }

                  checkSat()
                  getModel()
              }
          )
           */
          Arguments.arguments(
              smt(QF_UF) {
                val circuit by declaringConst(SMTBool)
                val grn by declaringConst(SMTBool)
                val org by declaringConst(SMTBool)
                val prt by declaringConst(SMTBool)
                val rd1 by declaringConst(SMTBool)
                val rd2 by declaringConst(SMTBool)

                assert { circuit }
                assert {
                  not(
                      (prt and grn) or
                          org or
                          (not(prt) and rd1) or
                          rd2 or
                          (grn and not(prt)) or
                          (rd1 and prt)
                  )
                }

                checkSat()
                getModel()
              }
          ),
      )

  @ParameterizedTest
  @MethodSource("provideProgram")
  fun testModelContainsAllFreeVariables(program: SMTProgram) {
    val freeVariables =
        program.commands
            .filterIsInstance<Assert>()
            .map { assertion -> FreeVariables.of(assertion.expr, RecursionPolicy.RECURSIVE) }
            .reduce { a, b -> a + b }

    val model =
        InteractiveZ3Solver().use { solver ->
          solver.solve(program)
          solver.getModel()
        }

    assert(freeVariables.all { expression -> model.getDefinitionOrNull(expression.func!!) != null })
  }

  @Test
  fun testModelValueForBitvector() {
    val program =
        smt(QF_BV) {
          val s by declaringConst(SMTBitVec(8))
          assert { s eq 16.bitvec(8) }
          checkSat()
          getModel()
        }

    val variable =
        program.commands.filterIsInstance<DeclareFun<*>>().single() as DeclareFun<BitVecSort>

    val model =
        InteractiveZ3Solver().use { solver ->
          solver.solve(program)
          solver.getModel()
        }
    val actual = model.getConstantValue(variable.func)

    assertEquals(16, actual.value.toInt())
  }

  @Test
  fun testModelValueForFloatingPoint() {
    val program = MutableSMTProgram()
    program.setLogic(QF_FP)

    // store the function definition here so we can later retrieve its value from the model with the
    // correct type automatically deduced
    val s = program.declareConst("s".toSymbol(), SMTFP32)

    program.assert(Equals(s.instance, FloatingPointLiteral(4.25f)))
    program.checkSat()
    program.getModel()

    val model =
        InteractiveZ3Solver().use { solver ->
          solver.solve(program)
          solver.getModel()
        }

    // get constant value, this is automatically returned as a FloatingPointLiteral
    val actual = model.getConstantValue(s)

    assertEquals(4.25f, actual.asFloat())
  }

  @Test
  fun testModelValueForInteger() {
    val program = MutableSMTProgram()
    program.setLogic(QF_IDL)

    // store the function definition here so we can later retrieve its value from the model with the
    // correct type automatically deduced
    val s = program.declareConst("s".toSymbol(), SMTInt)

    program.assert(Equals(s.instance, IntSub(IntLiteral(3), IntNeg(IntLiteral(5)))))
    program.checkSat()
    program.getModel()

    val model =
        InteractiveZ3Solver().use { solver ->
          solver.solve(program)
          solver.getModel()
        }

    // get constant value, this is automatically returned as a FloatingPointLiteral
    val actual = model.getConstantValue(s)

    assertEquals(8, actual.value.toInt())
  }

  @Test
  fun testModelValueForString() {
    val program = MutableSMTProgram()
    program.setLogic(QF_S)

    val s = program.declareConst("s".toSymbol(), SMTString)

    program.assert(Equals(s.instance, StrConcat(StringLiteral("foo"), StringLiteral("bar"))))
    program.checkSat()
    program.getModel()

    val model =
        InteractiveZ3Solver().use { solver ->
          solver.solve(program)
          solver.getModel()
        }

    val actual = model.getConstantValue(s)

    assertEquals("foobar", actual.value)
  }
}

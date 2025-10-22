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

import java.util.stream.Stream
import kotlin.use
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.Arguments.arguments
import org.junit.jupiter.params.provider.MethodSource
import tools.aqua.konstraints.dsl.*
import tools.aqua.konstraints.parser.Parser
import tools.aqua.konstraints.smt.BVLiteral
import tools.aqua.konstraints.smt.Bool
import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.smt.FPMinusZero
import tools.aqua.konstraints.smt.FPNaN
import tools.aqua.konstraints.smt.FPZero
import tools.aqua.konstraints.smt.False
import tools.aqua.konstraints.smt.IntLiteral
import tools.aqua.konstraints.smt.RealDiv
import tools.aqua.konstraints.smt.RealLiteral
import tools.aqua.konstraints.smt.SMTInt
import tools.aqua.konstraints.smt.SortedVar
import tools.aqua.konstraints.smt.StringLiteral
import tools.aqua.konstraints.smt.toSymbolWithQuotes
import tools.aqua.konstraints.solvers.z3.Z3Solver

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class ModelTests {
  @ParameterizedTest
  @MethodSource("provideProgramAndModel")
  fun testModel(program: String, term: Expression<*>) {
    val prg = Parser().parse(program)
    val solver = Z3Solver()

    solver.use {
      solver.solve(prg)
      assertEquals(term, solver.model.definitions.single().term)
    }
  }

  fun provideProgramAndModel(): Stream<Arguments> =
      Stream.of(
          /*arguments(
              "(set-logic QF_LIA)(declare-fun foo (Int) Bool)(define-fun bar ((x Int)) Int (- (* x x) 4))(assert (forall ((x Int)) (ite (= (bar x) 0) (= (foo x) true) (= (foo x) false))))(check-sat)(get-model)",
              RealLiteral(1)),
          arguments(
              "(set-logic QF_LIA)(define-fun x1 ((a Int) (b Int)) Int (+ a b))(declare-fun y (Int Int) Int)(assert (forall ((a Int) (b Int))(=> (and (< a 40) (>= a 0)) (= (y a b) (x1 a b)))))(assert (forall ((a Int) (b Int))(=> (>= a 40) (= (y a b) 42))))(assert (forall ((a Int) (b Int))(=> (< a 0) (= (y a b) 23))))(check-sat)(get-model)",
              RealLiteral(1)),*/
          arguments(
              "(set-logic QF_LIA)(declare-fun foo (Int Int) Int)(assert (and (= (foo 2 0) 2) (= (foo 1 0) 1) (= (foo 0 0) 0) (= (foo 2 1) 3) (= (foo 1 1) 2) (= (foo 0 1) 1)))(check-sat)(get-model)",
              listOf(
                      SortedVar("x!0".toSymbolWithQuotes(), SMTInt),
                      SortedVar("x!1".toSymbolWithQuotes(), SMTInt),
                  )
                  .let {
                    val x0 = it[0].instance
                    val x1 = it[1].instance
                    ite((x0 eq 1) and (x1 eq 0)) then
                        IntLiteral(1) otherwise
                        (ite((x0 eq 0) and (x1 eq 0)) then
                            IntLiteral(0) otherwise
                            (ite((x0 eq 2) and (x1 eq 1)) then
                                IntLiteral(3) otherwise
                                (ite((x0 eq 0) and (x1 eq 1)) then
                                    IntLiteral(1) otherwise
                                    IntLiteral(2))))
                  },
          ),
          arguments(
              "(set-logic QF_LIA)(declare-fun foo (Int) Int)(assert (and (= (foo 2) 2) (= (foo 1) 1) (= (foo 0) 0)))(check-sat)(get-model)",
              listOf(SortedVar("x!0".toSymbolWithQuotes(), SMTInt)).let {
                val x0 = it[0].instance
                ite(x0 eq 1) then
                    IntLiteral(1) otherwise
                    (ite(x0 eq 0) then IntLiteral(0) otherwise IntLiteral(2))
              },
          ),
          arguments(
              "(set-logic QF_LIA)(declare-fun foo (Bool) Int)(assert (and (= (foo true) 1) (= (foo false) 0)))(check-sat)(get-model)",
              listOf(SortedVar("x!0".toSymbolWithQuotes(), Bool)).let {
                val x0 = it[0].instance
                ite(x0 eq False) then IntLiteral(0) otherwise IntLiteral(1)
              },
          ),
          arguments(
              "(set-logic QF_BV)(declare-fun foo () (_ BitVec 8))(assert (= foo #b00000000))(check-sat)(get-model)",
              BVLiteral("#b00000000"),
          ),
          arguments(
              "(set-logic QF_FP)(declare-fun foo () Float16)(assert (= foo (_ +zero 5 11)))(check-sat)(get-model)",
              FPZero(5, 11),
          ),
          arguments(
              "(set-logic QF_FP)(declare-fun foo () Float16)(assert (= foo (fp #b0 #b00000 #b0000000000)))(check-sat)(get-model)",
              FPZero(5, 11),
          ),
          /*arguments("(set-logic QF_FP)(declare-fun foo () Float16)(assert (= foo (fp #b0 #b00000 #b0000000000)))(check-sat)(get-model)",
          FPLiteral("#b0".bitvec(), "#b00000".bitvec(), "#b0000000000".bitvec())),*/
          arguments(
              "(set-logic QF_FP)(declare-fun foo () Float16)(assert (= foo (fp #b1 #b00000 #b0000000000)))(check-sat)(get-model)",
              FPMinusZero(5, 11),
          ),
          arguments(
              "(set-logic QF_S)(declare-fun foo () String)(assert (= (str.len foo) 0))(check-sat)(get-model)",
              StringLiteral(""),
          ),
          arguments(
              "(set-logic QF_LIA)(declare-fun foo () Int)(assert (= foo 0))(check-sat)(get-model)",
              IntLiteral(0),
          ),
          arguments(
              "(set-logic QF_FP)(declare-fun foo () Float16)(assert (= foo (fp.add roundTowardZero foo (fp #b0 #b00000 #b0000000001))))(check-sat)(get-model)",
              FPNaN(5, 11),
          ),
          arguments(
              "(set-logic QF_LRA)(declare-fun foo () Real)(assert (= foo 0.0))(check-sat)(get-model)",
              RealLiteral(0),
          ),
          arguments(
              "(set-logic QF_LIRA)(declare-fun foo () Real)(assert (= foo (/ 2.0 5.0)))(check-sat)(get-model)",
              RealDiv(RealLiteral(2), RealLiteral(5)),
          ),
          /*arguments("(set-logic QF_LIRA)(declare-fun foo () Real)(assert (= foo 0.000000000000000000001))(check-sat)(get-model)",
          RealDiv(RealLiteral(1), RealLiteral(1000000000000000000000.0)))*/
      )
}

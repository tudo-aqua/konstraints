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
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.assertThrows
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments.arguments
import org.junit.jupiter.params.provider.MethodSource
import org.junit.jupiter.params.provider.ValueSource
import tools.aqua.konstraints.parser.Parser
import tools.aqua.konstraints.smt.IllegalSymbolException
import tools.aqua.konstraints.smt.QuotingRule

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class SerializationTests {
  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "(set-logic QF_UF)\n(declare-fun foo () Bool)\n(declare-const |bar| Bool)\n(assert (= foo |bar|))\n(check-sat)",
              "(set-logic QF_UF)\n(declare-const |bar| Bool)\n(assert (forall ((|x| Bool)) (ite |x| (= |x| |bar|) (= (not |x|) |bar|))))\n(check-sat)",
              "(set-logic QF_UF)\n(assert (exists ((x Bool)) (= x (not x))))\n(check-sat)",
              "(set-logic QF_S)\n(declare-fun |42| (Int) String)\n(assert (= 0 (str.len (|42| 0))))\n(check-sat)",
              "(set-logic QF_S)\n(assert (= 0 (str.len \"\")))\n(check-sat)",
              "(set-logic QF_FPLRA)\n(declare-fun foo () (_ FloatingPoint 8 24))\n(define-fun rm () RoundingMode RTZ)\n(declare-const bar Real)\n(assert (= foo ((_ to_fp 8 24) rm bar)))\n(check-sat)",
              "(set-logic QF_LRA)\n(declare-const foo Real)\n(assert (= foo 42.0))\n(check-sat)",
              "(set-logic QF_FP)\n(declare-const foo Float16)\n(assert (= foo (fp #b0 #b00000 #b0000000000)))\n(check-sat)",
          ]
  )
  fun `test that SMTProgram toString() behaves like toSMTString(QuotingRule SAME_AS_INPUT)`(
      program: String
  ) {
    val prog = Parser().parse(program)
    assertEquals(program, prog.toSMTString(QuotingRule.SAME_AS_INPUT))
  }

  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "(set-logic QF_UF)\n(declare-fun foo () Bool)\n(declare-const |bar| Bool)\n(assert (= foo |bar|))\n(check-sat)",
              "(set-logic QF_UF)\n(declare-const |bar| Bool)\n(assert (forall ((|x| Bool)) (ite |x| (= |x| |bar|) (= (not |x|) |bar|))))\n(check-sat)",
              "(set-logic QF_UF)\n(assert (exists ((x Bool)) (= x (not x))))\n(check-sat)",
              "(set-logic QF_S)\n(declare-fun |42| (Int) String)\n(assert (= 0 (str.len (|42| 0))))\n(check-sat)",
              "(set-logic QF_S)\n(assert (= 0 (str.len \"\")))\n(check-sat)",
              "(set-logic QF_FPLRA)\n(declare-fun foo () (_ FloatingPoint 8 24))\n(define-fun rm () RoundingMode RTZ)\n(declare-const bar Real)\n(assert (= foo ((_ to_fp 8 24) rm bar)))\n(check-sat)",
              "(set-logic QF_LRA)\n(declare-const foo Real)\n(assert (= foo 42.0))\n(check-sat)",
              "(set-logic QF_FP)\n(declare-const foo Float16)\n(assert (= foo (fp #b0 #b00000 #b0000000000)))\n(check-sat)",
          ]
  )
  fun `test that toSMTString works with QuotingRule SAME_AS_INPUT`(program: String) {
    val prog = Parser().parse(program)
    assertEquals(program, prog.toSMTString(QuotingRule.SAME_AS_INPUT))
  }

  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "(set-logic QF_UF)\n(declare-fun foo () Bool)\n(declare-const |bar| Bool)\n(assert (= foo |bar|))\n(check-sat)",
              "(set-logic QF_UF)\n(declare-const |bar| Bool)\n(assert (forall ((|x| Bool)) (ite |x| (= |x| |bar|) (= (not |x|) |bar|))))\n(check-sat)",
              "(set-logic QF_UF)\n(assert (exists ((x Bool)) (= x (not x))))\n(check-sat)",
              "(set-logic QF_S)\n(declare-fun |42| (Int) String)\n(assert (= 0 (str.len (|42| 0))))\n(check-sat)",
              "(set-logic QF_S)\n(assert (= 0 (str.len \"\")))\n(check-sat)",
              "(set-logic QF_FPLRA)\n(declare-fun foo () (_ FloatingPoint 8 24))\n(define-fun rm () RoundingMode RTZ)\n(declare-const bar Real)\n(assert (= foo ((_ to_fp 8 24) rm bar)))\n(check-sat)",
              "(set-logic QF_LRA)\n(declare-const foo Real)\n(assert (= foo 42.0))\n(check-sat)",
              "(set-logic QF_FP)\n(declare-const foo Float16)\n(assert (= foo (fp #b0 #b00000 #b0000000000)))\n(check-sat)",
          ]
  )
  fun `test that toSMTString works with QuotingRule SAME_AS_INPUT and StringBuilder`(
      program: String
  ) {
    val prog = Parser().parse(program)
    assertEquals(program, prog.toSMTString(StringBuilder(), QuotingRule.SAME_AS_INPUT).toString())
  }

  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "(set-logic QF_UF)\n(declare-fun foo () Bool)\n(declare-const |bar| Bool)\n(assert (= foo |bar|))\n(check-sat)",
              "(set-logic QF_UF)\n(declare-const |bar| Bool)\n(assert (forall ((|x| Bool)) (ite |x| (= |x| |bar|) (= (not |x|) |bar|))))\n(check-sat)",
              "(set-logic QF_UF)\n(assert (exists ((x Bool)) (= x (not x))))\n(check-sat)",
              "(set-logic QF_S)\n(assert (= 0 (str.len \"\")))\n(check-sat)",
              "(set-logic QF_FPLRA)\n(declare-fun foo () (_ FloatingPoint 8 24))\n(define-fun rm () RoundingMode RTZ)\n(declare-const bar Real)\n(assert (= foo ((_ to_fp 8 24) rm bar)))\n(check-sat)",
              "(set-logic QF_LRA)\n(declare-const foo Real)\n(assert (= foo 42.0))\n(check-sat)",
              "(set-logic QF_FP)\n(declare-const foo Float16)\n(assert (= foo (fp #b0 #b00000 #b0000000000)))\n(check-sat)",
          ]
  )
  fun `test that toSMTString works with QuotingRule NEVER`(program: String) {
    val prog = Parser().parse(program)
    assertEquals(program.replace("|", ""), prog.toSMTString(QuotingRule.NEVER))
  }

  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "(set-logic QF_UF)\n(declare-fun foo () Bool)\n(declare-const |bar| Bool)\n(assert (= foo |bar|))\n(check-sat)",
              "(set-logic QF_UF)\n(declare-const |bar| Bool)\n(assert (forall ((|x| Bool)) (ite |x| (= |x| |bar|) (= (not |x|) |bar|))))\n(check-sat)",
              "(set-logic QF_UF)\n(assert (exists ((x Bool)) (= x (not x))))\n(check-sat)",
              "(set-logic QF_S)\n(assert (= 0 (str.len \"\")))\n(check-sat)",
              "(set-logic QF_FPLRA)\n(declare-fun foo () (_ FloatingPoint 8 24))\n(define-fun rm () RoundingMode RTZ)\n(declare-const bar Real)\n(assert (= foo ((_ to_fp 8 24) rm bar)))\n(check-sat)",
              "(set-logic QF_LRA)\n(declare-const foo Real)\n(assert (= foo 42.0))\n(check-sat)",
              "(set-logic QF_FP)\n(declare-const foo Float16)\n(assert (= foo (fp #b0 #b00000 #b0000000000)))\n(check-sat)",
          ]
  )
  fun `test that toSMTString works with QuotingRule NEVER and StringBuilder`(program: String) {
    val prog = Parser().parse(program)
    assertEquals(
        program.replace("|", ""),
        prog.toSMTString(StringBuilder(), QuotingRule.NEVER).toString(),
    )
  }

  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "(set-logic QF_S)\n(declare-fun |42| (Int) String)\n(assert (= 0 (str.len (|42| 0))))\n(check-sat)"
          ]
  )
  fun `test that toSMTString throws with QuotingRule NEVER when a non simple symbol is present`(
      program: String
  ) {
    val prog = Parser().parse(program)
    assertThrows<IllegalSymbolException> { prog.toSMTString(QuotingRule.NEVER) }
  }

  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "(set-logic QF_S)\n(declare-fun |42| (Int) String)\n(assert (= 0 (str.len (|42| 0))))\n(check-sat)"
          ]
  )
  fun `test that toSMTString throws with QuotingRule NEVER and StringBuilder when a non simple symbol is present`(
      program: String
  ) {
    val prog = Parser().parse(program)
    assertThrows<IllegalSymbolException> { prog.toSMTString(StringBuilder(), QuotingRule.NEVER) }
  }

  @ParameterizedTest
  @MethodSource("provideProgramsAndSerialization")
  fun `test that toSMTString works with QuotingRule WHEN_NEEDED`(
      program: String,
      expected: String,
  ) {
    val prog = Parser().parse(program)
    assertEquals(expected, prog.toSMTString(QuotingRule.WHEN_NEEDED))
  }

  @ParameterizedTest
  @MethodSource("provideProgramsAndSerialization")
  fun `test that toSMTString works with QuotingRule WHEN_NEEDED and StringBuilder`(
      program: String,
      expected: String,
  ) {
    val prog = Parser().parse(program)
    assertEquals(expected, prog.toSMTString(StringBuilder(), QuotingRule.WHEN_NEEDED).toString())
  }

  private fun provideProgramsAndSerialization() =
      Stream.of(
          arguments(
              "(set-logic QF_UF)\n(declare-fun foo () Bool)\n(declare-const |bar| Bool)\n(assert (= foo |bar|))\n(check-sat)",
              "(set-logic QF_UF)\n(declare-fun foo () Bool)\n(declare-const bar Bool)\n(assert (= foo bar))\n(check-sat)",
          ),
          arguments(
              "(set-logic QF_UF)\n(declare-const |bar| Bool)\n(assert (forall ((|x| Bool)) (ite |x| (= |x| |bar|) (= (not |x|) |bar|))))\n(check-sat)",
              "(set-logic QF_UF)\n(declare-const bar Bool)\n(assert (forall ((x Bool)) (ite x (= x bar) (= (not x) bar))))\n(check-sat)",
          ),
          arguments(
              "(set-logic QF_S)\n(declare-fun |42| (Int) String)\n(assert (= 0 (str.len (|42| 0))))\n(check-sat)",
              "(set-logic QF_S)\n(declare-fun |42| (Int) String)\n(assert (= 0 (str.len (|42| 0))))\n(check-sat)",
          ),
      )

  @ParameterizedTest
  @MethodSource("provideProgramsAndSerializationWithQuotes")
  fun `test that toSMTString works with QuotingRule ALWAYS`(program: String, expected: String) {
    val prog = Parser().parse(program)
    assertEquals(expected, prog.toSMTString(QuotingRule.ALWAYS))
  }

  @ParameterizedTest
  @MethodSource("provideProgramsAndSerializationWithQuotes")
  fun `test that toSMTString works with QuotingRule ALWAYS and StringBuilder`(
      program: String,
      expected: String,
  ) {
    val prog = Parser().parse(program)
    assertEquals(expected, prog.toSMTString(StringBuilder(), QuotingRule.ALWAYS).toString())
  }

  private fun provideProgramsAndSerializationWithQuotes() =
      Stream.of(
          arguments(
              "(set-logic QF_UF)\n(declare-fun foo () Bool)\n(declare-const |bar| Bool)\n(assert (= foo |bar|))\n(check-sat)",
              "(set-logic QF_UF)\n(declare-fun |foo| () |Bool|)\n(declare-const |bar| |Bool|)\n(assert (|=| |foo| |bar|))\n(check-sat)",
          ),
          arguments(
              "(set-logic QF_UF)\n(declare-const |bar| Bool)\n(assert (forall ((|x| Bool)) (ite |x| (= |x| |bar|) (= (not |x|) |bar|))))\n(check-sat)",
              "(set-logic QF_UF)\n(declare-const |bar| |Bool|)\n(assert (forall ((|x| |Bool|)) (|ite| |x| (|=| |x| |bar|) (|=| (|not| |x|) |bar|))))\n(check-sat)",
          ),
          arguments(
              "(set-logic QF_UF)\n(assert (exists ((x Bool)) (= x (not x))))\n(check-sat)",
              "(set-logic QF_UF)\n(assert (exists ((|x| |Bool|)) (|=| |x| (|not| |x|))))\n(check-sat)",
          ),
          arguments(
              "(set-logic QF_FPLRA)\n(declare-fun foo () (_ FloatingPoint 8 24))\n(define-fun rm () RoundingMode RTZ)\n(declare-const bar Real)\n(assert (= foo ((_ to_fp 8 24) rm bar)))\n(check-sat)",
              "(set-logic QF_FPLRA)\n(declare-fun |foo| () (_ |FloatingPoint| 8 24))\n(define-fun |rm| () |RoundingMode| |RTZ|)\n(declare-const |bar| |Real|)\n(assert (|=| |foo| ((_ |to_fp| 8 24) |rm| |bar|)))\n(check-sat)",
          ),
          arguments(
              "(set-logic QF_LRA)\n(declare-const foo Real)\n(assert (= foo 42.0))\n(check-sat)",
              "(set-logic QF_LRA)\n(declare-const |foo| |Real|)\n(assert (|=| |foo| 42.0))\n(check-sat)",
          ),
          arguments(
              "(set-logic QF_FP)\n(declare-const foo Float16)\n(assert (= foo (fp #b0 #b00000 #b0000000000)))\n(check-sat)",
              "(set-logic QF_FP)\n(declare-const |foo| |Float16|)\n(assert (|=| |foo| (fp #b0 #b00000 #b0000000000)))\n(check-sat)",
          ),
      )
}

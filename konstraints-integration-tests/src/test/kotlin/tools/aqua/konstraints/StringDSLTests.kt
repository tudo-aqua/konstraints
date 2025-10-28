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

import at
import comp
import concat
import contains
import diff
import fromCode
import in_re
import intersec
import length
import loop
import opt
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments.arguments
import org.junit.jupiter.params.provider.MethodSource
import plus
import power
import prefixof
import suffixof
import range
import replace
import replace_all
import star
import times
import substr
import indexof
import isDigit
import replace_re
import replace_re_all
import tools.aqua.konstraints.dsl.*
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.solvers.z3.Z3Solver
import union
import java.util.stream.Stream

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class StringDSLTests {
  val programs =
      listOf(
          smt(QF_S) {
            setInfo { status(SatStatus.SAT) }

            val s1 = const("s1", SMTString)
            val s2 = const("s2", SMTString)

            // construct language a|b*
            // (re.union (str.to_re "a") (re.* (str.to_re "b")))
            val re1 = "a" union "b".star()

            // construct language (a|b)*
            // (re.* (re.union (str.to_re "a") (str.to_re "b")))
            val re2 = ("a" union "b").star()

            // verify that re1 is subset of re2 by checking that s1 is in re1 and re2 but s2 is in
            // re2 but not in re1
            assert { s1 in_re re1 }
            assert { s1 in_re re2 }
            assert { s2 in_re re2 }
            assert { not(s2 in_re re1) }
            checkSat()
          },
          smt(QF_S) {
            setInfo { status(SatStatus.SAT) }

            // construct language (0|(1(01*0)*1))* (that is all binary number divisible by 3)
            // (re.union (str.to_re "0") (re.++ (str.to_re "1") (re.* (re.++ (re.* (str.to_re "01"))
            // (str.to_re "0"))) (str.to_re "1")))
            val re = "0" union ("1" * ("01".star() * "0").star() * "1")

            assert { "1111" in_re re }
            checkSat()
          },
          smt(QF_S) {
            setInfo { status(SatStatus.UNSAT) }

            // construct language (0|([1-9][0-9]*)) (all decimal numbers without leading zeros)
            // note that the brackets around the concat operation are necessary otherwise we get
            // ((0([1-9])|[0-9]*)
            // (re.union (str.to_re "0) (re.++ (re.range "1" "9") (re.* (re.range "0" "9"))))
            val re = "0" union (("1" range "9") concat ("0" range "9").star())

            assert { "05" in_re re }
            checkSat()
          },
          smt(QF_S) {
            setInfo { status(SatStatus.SAT) }

            // both languages match 'a' 4 or 0 times
            // (re.opt ((_ re.^ 4) (str.to_re "a")))
            val re1 = "a".power(4).opt()

            // (( _ re.loop 0 1) (str.to_re "aaaa"))
            val re2 = "aaaa".loop(0, 1)

            // re1 / re2 is the empty language
            val re3 = re1 diff re2

            assert { re3 eq RegexNone }
            checkSat()
          },
          smt(QF_S) {
            setInfo { status(SatStatus.SAT) }

            val s = const("s", SMTString)

            // language of all strings with length 0 or >=2
            // (re.diff re.all re.allchar)
            val re1 = RegexAll diff RegexAllChar

            // language of all strings consisting of at least 1 "0"
            // (re.+ (str.to_re "0"))
            val re2 = "0".plus()

            assert { (s in_re re1) and (s in_re re2) }
            checkSat()
          },
          smt(QF_S) {
              setInfo { status(SatStatus.SAT) }

              val s = const("s", SMTString)

              // language of all strings with length 0 or >=2
              // (re.diff re.all re.allchar)
              val re1 = RegexAll diff RegexAllChar

              // language of all strings with length 0 or >=2
              // (re.comp re.allchar)
              val re2 = RegexAllChar.comp()

              assert { (s in_re re1) and (s in_re re2) }
              checkSat()
          },
          smt(QF_S) {
              setInfo { status(SatStatus.SAT) }

              val s = const("s", SMTString)

              // (re.+ (str.to_re "a"))
              val re1 = "a".plus()

              // (re.++ (re.opt (str.to_re "b")) (re.+ (str.to_re "a")))
              val re2 = "b".opt() * "a".plus()

              assert { (s in_re re2) and not(s in_re (re2 intersec re1)) }
              checkSat()
          },
          smt(QF_S) {
              setInfo { status(SatStatus.SAT) }

              val s = const("s", SMTString)

              assert { s prefixof (s + s) }
              assert { s suffixof (s + s) }

              checkSat()
          },
          smt(QF_S) {
              setInfo { status(SatStatus.SAT) }

              val s = const("s", SMTString)
              val u = const("u", SMTString)
              val v = const("v", SMTString)

              assert { s eq (u + v) }
              assert { u prefixof s }
              assert { v suffixof s }
              assert { s contains u }
              assert { s contains v }

              checkSat()
          },
          smt(QF_SLIA) {
              setInfo { status(SatStatus.SAT) }

              val s = const("s", SMTString)
              val u = const("u", SMTString)
              val v = const("v", SMTString)

              assert { s eq (u + v) }
              assert { s.length() eq u.length() + v.length() }

              checkSat()
          },
          smt(QF_SLIA) {
              setInfo { status(SatStatus.SAT) }

              val s = const("s", SMTString)
              val u = const("u", SMTString)
              val v = const("v", SMTString)

              assert { s eq (u + v) }
              assert { u eq s.substr(0, u.length()) }
              assert { v eq s.substr(u.length() + 1, v.length()) }

              checkSat()
          },
          smt(QF_SLIA) {
              setInfo { status(SatStatus.SAT) }

              val s = const("s", SMTString)
              val u = const("u", SMTString)
              val v = const("v", SMTString)

              assert { s eq (u + v) }
              assert { s.replace(u, v) eq (v + v)}

              checkSat()
          },
          smt(QF_SLIA) {
              setInfo { status(SatStatus.SAT) }

              val s = const("s", SMTString)
              val u = const("u", SMTString)
              val v = const("v", SMTString)

              assert { s eq (u + v + u) }
              assert { s.replace_all(u, v) eq (v + v + v)}

              checkSat()
          },
          smt(QF_S) {
              setInfo { status(SatStatus.SAT) }

              val s = const("s", SMTString)
              val u = const("u", SMTString)
              val v = const("v", SMTString)

              assert { s eq (u + v) }
              assert { s.at(0) eq u.at(0)}

              checkSat()
          },
          smt(QF_SLIA) {
              setInfo { status(SatStatus.SAT) }

              val s = const("s", SMTString)
              val u = const("u", SMTString)
              val v = const("v", SMTString)

              assert { s eq (u + v) }
              assert { s.indexof(v, 0) eq u.length() }

              checkSat()
          },
          smt(QF_SLIA) {
              setInfo { status(SatStatus.SAT) }

              val re = "b".opt() * "a".plus()
              val s = const("s", SMTString)

              assert { s eq "abaaba" }
              assert { s.replace_re(re, "") eq "aaba" }

              checkSat()
          },
          smt(QF_SLIA) {
              setInfo { status(SatStatus.SAT) }

              val re = "b".opt() * "a".plus()
              val s = const("s", SMTString)

              assert { s eq "abaaba" }
              assert { s.replace_re_all(re, "") eq "aa" }

              checkSat()
          },
          smt(QF_S) {
              setInfo { status(SatStatus.SAT) }
              assert { "1".isDigit() }
              checkSat()
          },
          smt(QF_S) {
              setInfo { status(SatStatus.SAT) }
              assert { 65.fromCode() eq "A" }
              checkSat()
          })

    @ParameterizedTest
    @MethodSource("providePrograms")
    fun testStringDSL(program: SMTProgram) {
        Z3Solver().use { solver ->
            assertEquals(program.info("status").toString().trim('"'), solver.solve(program).toString())
        }
    }

    private fun providePrograms() = Stream.of(*programs.map { arguments(it) }.toTypedArray())
}

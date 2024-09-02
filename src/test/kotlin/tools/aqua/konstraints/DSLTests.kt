/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2024 The Konstraints Authors
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

import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.Arguments.arguments
import org.junit.jupiter.params.provider.MethodSource
import tools.aqua.konstraints.dsl.*
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.solvers.z3.Z3Solver
import tools.aqua.konstraints.theories.BVSort
import tools.aqua.konstraints.theories.BoolSort
import tools.aqua.konstraints.theories.IntSort
import tools.aqua.konstraints.theories.Not
import tools.aqua.konstraints.theories.bitvec
import java.util.stream.Stream

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class DSLTests {
  @Test
  fun testCoreDSL() {
    val solver = Z3Solver()

    val program =
        smt(QF_UF) {
          val A = const("A", BoolSort)
          val B = const("B", BoolSort)
          val C = const("C", BoolSort)

          val D = const("D", IntSort)
          val E = const("E", IntSort)

          assert {
            ite {
              A
            } then {
              B
            } otherwise {
              C
            }
          }

          assert {
            or {
              +(A and Not(A))
              +(B and Not(B))
            }
          }

          assert {
            or {
              and {
                +A
                +Not(A)
              }
              and {
                +B
                +Not(B)
              }
            }
          }

          assert {
            eq {
              +(A implies B)
              or {
                not { A }
                +B
              }
            }
          }
          
          assert {
            eq<IntSort> {
              add {
                +D
                +E
              }
              +(D + E)
            }
          }
        }

    val result = solver.solve(program)

    print(result)
  }

  @ParameterizedTest
  @MethodSource("getProgramAndStatus")
  fun testProgram(program: SMTProgram, expected: SatStatus) {
    val solver = Z3Solver()
    solver.solve(program)

    assertEquals(expected, solver.status)
  }

  private fun getProgramAndStatus() : Stream<Arguments> = Stream.of(
    arguments(
      smt(QF_BV) {
        val s = const(BVSort(32))
        val t = const(BVSort(32))

        assert {
          not {
            eq {
              +(s bvand s)
              +s
            }
          }
        }
      },
      SatStatus.UNSAT
    ),
    arguments(
      smt(QF_BV) {
        val s = const(BVSort(32))
        val t = const(BVSort(32))

        assert {
          not { (s bvand s) eq s }
        }
      },
      SatStatus.UNSAT
    ),
    arguments(
      smt(QF_BV) {
        val s = const(BVSort(32))
        val t = const(BVSort(32))

        assert {
          not { (s bvlshr s) eq "#b0".bitvec(32) }
        }
      },
      SatStatus.UNSAT
    ),
    arguments(
      smt(QF_BV) {
        val s = const(BVSort(32))
        val t = const(BVSort(32))

        assert {
          not { s bvor s eq s }
        }
      },
      SatStatus.UNSAT
    ),
    arguments(
      smt(QF_BV) {
        val s = const(BVSort(32))
        val t = const(BVSort(32))

        assert {
          not { s bvadd "#b0".bitvec(32) eq s }
        }
      },
      SatStatus.UNSAT
    ),
    arguments(
      smt(QF_BV) {
        val s = const(BVSort(32))
        val t = const(BVSort(32))

        assert {
          not { s bvmul "#b0".bitvec(32) eq "#b0".bitvec(32) }
        }
      },
      SatStatus.UNSAT
    ),
  )
}

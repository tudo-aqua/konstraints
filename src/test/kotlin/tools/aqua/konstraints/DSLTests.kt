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

import org.junit.jupiter.api.Test
import tools.aqua.konstraints.dsl.*
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.solvers.z3.Z3Solver
import tools.aqua.konstraints.theories.BoolSort
import tools.aqua.konstraints.theories.Not

class DSLTests {
  @Test
  fun testCoreDSL() {
    val solver = Z3Solver()

    val program =
        smt(QF_UF) {
          val A = const("A", BoolSort)
          val B = const("B", BoolSort)
          val C = const("C", BoolSort)

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
        }

    val result = solver.solve(program)

    print(result)
  }
}

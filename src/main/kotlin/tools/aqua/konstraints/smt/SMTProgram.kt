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

package tools.aqua.konstraints.smt

import tools.aqua.konstraints.parser.Attribute
import tools.aqua.konstraints.parser.Context
import tools.aqua.konstraints.solvers.Z3.Z3Solver

enum class SatStatus {
  SAT, // program is satisfiable
  UNSAT, // program is unsatisfiable
  UNKNOWN, // solver timed out
  PENDING; // solve has not been called yet on program

  override fun toString() =
      when (this) {
        SAT -> "sat"
        UNSAT -> "unsat"
        UNKNOWN -> "unknown"
        PENDING -> "pending"
      }
}

class SMTProgram(val commands: List<Command>, val context: Context) {
  var model: Model? = null
  var status = SatStatus.PENDING
  val info: List<Attribute>

  init {
    info = commands.filterIsInstance<SetInfo>().map { it.attribute }
  }

  /*
   * currently uses Z3 to solve eventually use an abstract Solver interface
   */
  fun solve() {
    // TODO maybe save solver as well
    val solver = Z3Solver()

    solver.use {
      status = solver.solve(this)

      println(status)

      if (solver.isModelAvailable()) {
        model = solver.getModel()
      }
    }
  }
}

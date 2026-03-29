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

package tools.aqua.konstraints.solvers

import kotlin.collections.eachCount
import tools.aqua.konstraints.smt.Model
import tools.aqua.konstraints.smt.SMTProgram
import tools.aqua.konstraints.smt.SatStatus

class MajorityVoteSolver(
    override val solvers: Iterable<Solver>,
    val policy: ExecutionPolicy,
    val defaultStatus: SatStatus,
    val resultFilter: (Solver, SatStatus) -> Boolean,
    val earlyAbort: Boolean = true,
) : MetaSolver {
  override fun solve(program: SMTProgram) = solve(program, policy)

  override fun getModel(): Model {
    TODO("Not yet implemented")
  }

  /** Return majority verdict */
  override fun solve(program: SMTProgram, policy: ExecutionPolicy) =
      when (policy) {
        ExecutionPolicy.PARALLEL ->
            solveParallel(program, resultFilter, ::abortCondition, ::majorityAnswer)
        ExecutionPolicy.SEQUENTIAL -> majorityAnswer(solveSequential(program))
      }

  private fun abortCondition(results: List<SatStatus>) =
      if (earlyAbort) {
        results.size > solvers.count() / 2
      } else {
        false
      }

  private fun majorityAnswer(results: List<SatStatus>) =
      results.groupingBy { it }.eachCount().maxByOrNull { it.value }?.key ?: defaultStatus

  override fun close() {
    // empty
  }
}

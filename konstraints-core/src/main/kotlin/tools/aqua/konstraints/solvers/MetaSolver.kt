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

import java.lang.Thread.sleep
import kotlinx.coroutines.*
import tools.aqua.konstraints.smt.SMTProgram
import tools.aqua.konstraints.smt.SatStatus

enum class ExecutionPolicy {
  SEQUENTIAL,
  PARALLEL,
}

interface MetaSolver : Solver {
  val solvers: Iterable<Solver>

  fun solve(program: SMTProgram, policy: ExecutionPolicy): SatStatus

  /**
   * Execute solvers sequentially.
   *
   * @return List of [SatStatus]
   */
  fun solveSequential(program: SMTProgram) =
      solvers.map { solver -> solver.use { solver -> solver.solve(program) } }

  /**
   * Execute solvers sequentially, returns first result for which [condition] returns true.
   *
   * @return [SatStatus]
   */
  fun solveSequential(program: SMTProgram, condition: (Solver, SatStatus) -> Boolean): SatStatus {
    solvers.map { solver ->
      val status = solver.use { solver -> solver.solve(program) }
      if (condition(solver, status)) {
        return status
      }
    }

    return SatStatus.UNKNOWN
  }

  /**
   * Execute solvers in parallel.
   *
   * @return List of [SatStatus]
   */
  fun solveParallel(program: SMTProgram) = runBlocking {
    solvers.map { solver -> async { solver.use { solver -> solver.solve(program) } } }.awaitAll()
  }

  /**
   * Execute solvers in parallel, returns first result for which [condition] returns true or
   * [SatStatus.UNKNOWN] if condition is false for all results
   *
   * @return List of [SatStatus]
   */
  fun solveParallel(
      program: SMTProgram,
      validateResult: (Solver, SatStatus) -> Boolean,
      abortCondition: (List<SatStatus>) -> Boolean,
      reduceResult: (List<SatStatus>) -> SatStatus,
  ): SatStatus {
    val globalSolverScope = CoroutineScope(Dispatchers.IO + SupervisorJob())
    val startTime = System.currentTimeMillis()

    val deferreds =
        solvers.map { solver ->
          globalSolverScope.async {
            try {
              solver.solve(program)
            } catch (e: Exception) {
              SatStatus.ERROR
            }
          } to solver
        }

    val results = mutableListOf<SatStatus>()

    try {
      while (System.currentTimeMillis() - startTime < 300000L && deferreds.any { it.first.isActive }) {
        deferreds.forEach { (deferred, solver) ->
          // this works since isCompleted is only true if the job completed and we did not get the result yet
          if (deferred.isCompleted) {
            val status = @OptIn(ExperimentalCoroutinesApi::class) deferred.getCompleted()

            if (validateResult(solver, status)) {
              results.add(status)
            }

            if (abortCondition(results)) {
              return reduceResult(results) // IMMEDIATE EXIT
            }
          }
        }
        sleep(1)
      }
      return if (results.isNotEmpty())  reduceResult(results) else SatStatus.TIMEOUT
    } finally {
      CoroutineScope(Dispatchers.IO).launch {
        solvers.forEach {
          try {
            (it as InteractiveCLISolver).closeForcibly()
          } catch (e: Exception) {}
        }
        globalSolverScope.cancel()
      }
    }
  }
}

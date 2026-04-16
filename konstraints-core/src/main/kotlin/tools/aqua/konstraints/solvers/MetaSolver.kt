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
  val solvers: List<Solver>

  fun solve(program: SMTProgram, policy: ExecutionPolicy): SatStatus

  /**
   * Execute solvers sequentially.
   *
   * @return reduceResult with a list of individual results
   */
  fun solveSequential(
      program: SMTProgram,
      validateResult: (Solver, SatStatus) -> Boolean,
      reduceResult: (List<SatStatus>) -> SatStatus,
      default: SatStatus,
      timeout: Long,
  ) = solveSequential(program, validateResult, { status -> false }, reduceResult, default, timeout)

  /**
   * Execute solvers sequentially, returns first result for which [condition] returns true.
   *
   * @return [SatStatus]
   */
  fun solveSequential(
      program: SMTProgram,
      validateResult: (Solver, SatStatus) -> Boolean,
      abortCondition: (List<SatStatus>) -> Boolean,
      reduceResult: (List<SatStatus>) -> SatStatus,
      default: SatStatus,
      timeout: Long,
  ): SatStatus {
    val results = mutableListOf<SatStatus>()
    solvers.map { solver ->
      val startTime = System.currentTimeMillis()
      val globalSolverScope = CoroutineScope(SupervisorJob())
      val deferred =
          globalSolverScope.async {
            try {
              solver.solve(program)
            } catch (e: Exception) {
              SatStatus.ERROR
            }
          } to solver

      try {
        var status = SatStatus.PENDING
        while (System.currentTimeMillis() - startTime < timeout && deferred.first.isActive) {
          deferred.let { (deferred, solver) ->
            // this works since isCompleted is only true if the job completed and we did not get the
            // result yet
            if (deferred.isCompleted) {
              status = @OptIn(ExperimentalCoroutinesApi::class) deferred.getCompleted()

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
        // if status is still pending we timed out
        if (status == SatStatus.PENDING) SatStatus.TIMEOUT else default
      } finally {
        // asynchronously shut down solver
        CoroutineScope(Dispatchers.IO).launch {
          solvers.forEach {
            try {
              // forcibly close all interactive solvers hope that other solvers close cooperates
              if (it is InteractiveCLISolver) it.closeForcibly() else it.close()
            } catch (e: Exception) {}
          }
          globalSolverScope.cancel()
        }
      }
    }

    // finally return combined result or default if no solver was able to solve the program
    return if (results.isNotEmpty()) reduceResult(results) else default
  }

  /**
   * Execute solvers in parallel.
   *
   * @return List of [SatStatus]
   */
  fun solveParallel(
      program: SMTProgram,
      validateResult: (Solver, SatStatus) -> Boolean,
      reduceResult: (List<SatStatus>) -> SatStatus,
      default: SatStatus,
      timeout: Long,
  ) = solveParallel(program, validateResult, { status -> false }, reduceResult, default, timeout)

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
      default: SatStatus,
      timeout: Long,
  ): SatStatus {
    val globalSolverScope = CoroutineScope(SupervisorJob())
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
      while (
          System.currentTimeMillis() - startTime < timeout && deferreds.any { it.first.isActive }
      ) {
        deferreds.forEach { (deferred, solver) ->
          // this works since isCompleted is only true if the job completed and we did not get the
          // result yet
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
      // return reduced result if we had at least one valid result
      // otherwise return timeout when all solvers timed out or default if all solvers terminated
      // without a valid result
      return if (results.isNotEmpty()) reduceResult(results)
      else if (System.currentTimeMillis() - startTime < 300000L) SatStatus.TIMEOUT else default
    } finally {
      CoroutineScope(Dispatchers.IO).launch {
        solvers.forEach {
          try {
            // forcibly close all interactive solvers hope that other solvers close cooperates
            if (it is InteractiveCLISolver) it.closeForcibly() else it.close()
          } catch (e: Exception) {}
        }
        globalSolverScope.cancel()
      }
    }
  }
}

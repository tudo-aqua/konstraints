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

import tools.aqua.konstraints.smt.Model
import tools.aqua.konstraints.smt.SMTProgram
import tools.aqua.konstraints.smt.SatStatus

interface Solver : AutoCloseable {
  /**
   * Solves the provided program using [this] solver.
   *
   * If [produceModel] is true this will also return a model if [program] is SAT.
   *
   * @throws TimeoutException if timeout is reached.
   */
  fun solve(program: SMTProgram, produceModel: Boolean, timeout: Long): Pair<SatStatus, Model?>
}

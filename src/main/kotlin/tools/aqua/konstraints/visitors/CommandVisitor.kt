/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2023 The Konstraints Authors
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

package tools.aqua.konstraints.visitors

import tools.aqua.konstraints.*

interface CommandVisitor<T> {
  fun visit(command: Command): T =
      when (command) {
        is Assert -> visit(command)
        is DeclareConst -> visit(command)
        is DeclareFun -> visit(command)
        is CheckSat -> visit(command)
        is Exit -> visit(command)
        is SetInfo -> visit(command)
        is SetOption -> visit(command)
        is SetLogic -> visit(command)
      }

  fun visit(assert: Assert): T

  fun visit(declareConst: DeclareConst): T

  fun visit(declareFun: DeclareFun): T

  fun visit(checkSat: CheckSat): T

  fun visit(exit: Exit): T

  fun visit(setInfo: SetInfo): T

  fun visit(setOption: SetOption): T

  fun visit(setLogic: SetLogic): T
}

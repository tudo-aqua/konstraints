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

package tools.aqua.konstraints.parser

import tools.aqua.konstraints.smt.Assert
import tools.aqua.konstraints.smt.BoolSort
import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.smt.MutableSMTProgram
import tools.aqua.konstraints.smt.Sort
import tools.aqua.konstraints.smt.Symbol

/**
 * Decides what happens with the commands read by [SMTScriptParser.parseInto]. Terms are always
 * parsed over the context of the program, so a handler that does not declare a symbol must make
 * sure that it is declared otherwise (e.g. by skipping only repeated declarations).
 *
 * The default implementations append every command to the program.
 */
interface ScriptHandler {
  /** `(assert term)` */
  fun assert(program: MutableSMTProgram, term: Expression<BoolSort>) {
    program.assert(Assert(term))
  }

  /** `(declare-const symbol sort)` */
  fun declareConst(program: MutableSMTProgram, symbol: Symbol, sort: Sort) {
    program.declareConst(symbol, sort)
  }

  /** `(declare-fun symbol (parameters) sort)` */
  fun declareFun(program: MutableSMTProgram, symbol: Symbol, parameters: List<Sort>, sort: Sort) {
    program.declareFun(symbol, parameters, sort)
  }

  /** `(push n)` */
  fun push(program: MutableSMTProgram, n: Int) {
    program.push(n)
  }

  /** `(pop n)` */
  fun pop(program: MutableSMTProgram, n: Int) {
    program.pop(n)
  }

  /** Appends every command to the program. */
  object AppendToProgram : ScriptHandler
}

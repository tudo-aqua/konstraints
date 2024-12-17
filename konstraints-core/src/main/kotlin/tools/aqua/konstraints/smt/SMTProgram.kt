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

import tools.aqua.konstraints.parser.ParseContext
import tools.aqua.konstraints.theories.BoolSort

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

abstract class SMTProgram(commands: List<Command>, var context: ParseContext?) {
  var model: Model? = null
  var status = SatStatus.PENDING
  val info: List<Attribute>
  var logic: Logic? = null
    protected set

  protected val _commands: MutableList<Command> = commands.toMutableList()
  val commands: List<Command>
    get() = _commands.toList()

  init {
    info = commands.filterIsInstance<SetInfo>().map { it.attribute }
  }

  fun assert(expr: Expression<BoolSort>) {
    // check expr is in logic when logic is set
    if (logic != null) {
      require(
          expr.all {
            (it.theories.isEmpty() or it.theories.any { it in logic!!.theories }) and
                (it.sort.theories.isEmpty() or it.sort.theories.any { it in logic!!.theories })
          }) {
            "Expression not in boundaries of logic"
          }
    }

    // check all symbols are known

    _commands.add(Assert(expr))
  }

  fun declareConst(name: Symbol, parameter: List<Sort>, sort: Sort) {

  }

  fun declareFun() {

  }
}

class MutableSMTProgram(commands: List<Command>, context: ParseContext?) :
    SMTProgram(commands, context) {
  constructor(commands: List<Command>) : this(commands, null)

  constructor() : this(emptyList(), null)

  /**
   * Inserts [command] at the end of the program
   *
   * Checks if [command] is legal w.r.t. the [context]
   */
  fun add(command: Command) {
    add(command, _commands.size)
  }

  /**
   * Inserts [command] at [index] into the program
   *
   * Checks if [command] is legal w.r.t. the [context]
   */
  fun add(command: Command, index: Int) {
    if (command is Assert) {
      require(command.expression.all { context!!.contains(it) })
    }

    updateContext(command)
    _commands.add(index, command)
  }

  /**
   * Inserts all [commands] at the end of the program
   *
   * For each command checks if it is legal w.r.t. the [context]
   */
  fun addAll(commands: List<Command>) = commands.forEach { add(it) }

  // conflicting jvm signature with setter of property logic
  /**
   * Set logic used by the SMT-Program this should only be done once
   *
   * @throws [RuntimeException] if logic was already set
   */
  @JvmName("setlogic")
  fun setLogic(logic: Logic) {
    if (this.logic != null) {
      throw RuntimeException("Logic already set")
    }

    this.logic = logic
    context = ParseContext(logic)
  }

  private fun updateContext(command: Command) {
    when (command) {
      is SetLogic -> setLogic(command.logic)
      is DeclareConst -> context?.registerFunction(command)
      is DeclareFun -> context?.registerFunction(command)
      is DeclareSort -> context?.registerSort(command)
      else -> return
    }
  }
}

class DefaultSMTProgram(commands: List<Command>, context: ParseContext) :
    SMTProgram(commands, context)

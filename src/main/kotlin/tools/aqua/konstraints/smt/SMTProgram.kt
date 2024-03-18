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
import tools.aqua.konstraints.theories.BitVectorExpressionContext

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

abstract class SMTProgram(commands: List<Command>, val context: Context) {
  var model: Model? = null
  var status = SatStatus.PENDING
  val info: List<Attribute>

  protected val _commands: MutableList<Command> = commands.toMutableList()
  val commands: List<Command>
    get() = _commands.toList()

  init {
    info = commands.filterIsInstance<SetInfo>().map { it.attribute }
  }

  /*
   * currently uses Z3 to solve eventually use an abstract Solver interface
   */
  fun solve() {
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

class MutableSMTProgram(commands: List<Command>, context: Context) : SMTProgram(commands, context) {
  constructor(commands: List<Command>) : this(commands, Context())

  constructor() : this(emptyList(), Context())

  /**
   * Inserts [command] at the end of the program Checks if [command] is legal w.r.t. the [context]
   */
  fun add(command: Command) {
    if (command is Assert) {
      require(command.expression.all { context.contains(it) })
    }

    updateContext(command)
    _commands.add(command)
  }

  /**
   * Inserts [command] at [index] into the program Checks if [command] is legal w.r.t. the [context]
   */
  fun add(command: Command, index: Int) {
    _commands.add(index, command)
  }

  /**
   * Inserts all [commands] at the end of the program For each command checks if it is legal w.r.t.
   * the [context]
   */
  fun addAll(commands: List<Command>) = commands.forEach { add(it) }

  fun setLogic(logic: Logic) {
    if (commands.filterIsInstance<SetLogic>().isNotEmpty()) {
      throw RuntimeException("Logic already set")
    }

    when (logic) {
      Logic.AUFLIA -> TODO()
      Logic.AUFLIRA -> TODO()
      Logic.AUFNIRA -> TODO()
      Logic.LIA -> TODO()
      Logic.LRA -> TODO()
      Logic.QF_ABV -> TODO()
      Logic.QF_AUFBV -> TODO()
      Logic.QF_AUFLIA -> TODO()
      Logic.QF_AX -> TODO()
      Logic.QF_BV -> context.registerTheory(BitVectorExpressionContext)
      Logic.QF_IDL -> TODO()
      Logic.QF_LIA -> TODO()
      Logic.QF_LRA -> TODO()
      Logic.QF_NIA -> TODO()
      Logic.QF_NRA -> TODO()
      Logic.QF_RDL -> TODO()
      Logic.QF_UF -> TODO()
      Logic.QF_UFBV -> TODO()
      Logic.QF_UFIDL -> TODO()
      Logic.QF_UFLIA -> TODO()
      Logic.QF_UFLRA -> TODO()
      Logic.QF_UFNRA -> TODO()
      Logic.UFLRA -> TODO()
      Logic.UFNIA -> TODO()
      Logic.QF_FP -> TODO()
    }
  }

  private fun updateContext(command: Command) {
    when (command) {
      is SetLogic -> setLogic(command.logic)
      is DeclareConst -> context.registerFunction(command)
      is DeclareFun -> context.registerFunction(command)
      is DeclareSort -> context.registerSort(command)
      else -> return
    }
  }
}

class DefaultSMTProgram(commands: List<Command>, context: Context) : SMTProgram(commands, context)

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

import java.io.BufferedReader
import java.io.InputStreamReader
import java.io.OutputStreamWriter
import tools.aqua.konstraints.parser.CheckSatResponse
import tools.aqua.konstraints.parser.ErrorResponse
import tools.aqua.konstraints.parser.GetModelResponse
import tools.aqua.konstraints.parser.ResponseParser
import tools.aqua.konstraints.parser.SolverResponse
import tools.aqua.konstraints.parser.SuccessResponse
import tools.aqua.konstraints.parser.UnsupportedResponse
import tools.aqua.konstraints.smt.BooleanOptionValue
import tools.aqua.konstraints.smt.Command
import tools.aqua.konstraints.smt.Model
import tools.aqua.konstraints.smt.MutableSMTProgram
import tools.aqua.konstraints.smt.NullOp
import tools.aqua.konstraints.smt.QuotingRule
import tools.aqua.konstraints.smt.SMTProgram
import tools.aqua.konstraints.smt.SatStatus
import tools.aqua.konstraints.smt.SetOption

class InteractiveZ3Solver : InteractiveCLISolver("z3", "-in")

open class InteractiveCLISolver(val name: String, vararg solverOptions: String) : Solver {

  // TODO this should have more exception handling
  val process: Process = ProcessBuilder(name, *solverOptions).redirectErrorStream(true).start()

  val writer = OutputStreamWriter(process.outputStream, Charsets.UTF_8)
  val reader = BufferedReader(InputStreamReader(process.inputStream, Charsets.UTF_8))

  private var _model: Model? = null

  private fun writeCommand(cmd: Command) {
    cmd.toSMTString(writer, QuotingRule.SAME_AS_INPUT, true)
    writer.write("\n")
    writer.flush()
  }

  private fun writeCommand(cmd: String) {
    writer.write(cmd)
    writer.write("\n")
    writer.flush()
  }

  private fun processCommand(cmd: Command, program: SMTProgram, timeout: Long) {
    writeCommand(cmd)
    val response = ResponseParser.parse(reader, program as MutableSMTProgram)

    processResponse(response, program)
  }

  private fun processCommand(cmd: String, program: SMTProgram, timeout: Long) {
    writeCommand(cmd)
    val response = ResponseParser.parse(reader, program as MutableSMTProgram)

    processResponse(response, program)
  }

  protected open fun processResponse(response: SolverResponse, program: SMTProgram) {
    when (response) {
      is CheckSatResponse -> program.status = response.status
      is ErrorResponse -> throw SolverError(response.msg)
      is SuccessResponse -> Unit
      is UnsupportedResponse -> throw SolverUnsupportedOperationException()
      is GetModelResponse -> {
        _model = response.model
        program.model = _model
      }
    }
  }

  override fun solve(
      program: SMTProgram,
      produceModel: Boolean,
      timeout: Long,
  ): Pair<SatStatus, Model?> {
    processCommand(SetOption(":print-success", BooleanOptionValue(true)), program, timeout)
    processCommand(SetOption(":produce-models", BooleanOptionValue(produceModel)), program, timeout)
    program.commands.filter { it !is NullOp }.forEach { processCommand(it, program, timeout) }

    processCommand("(check-sat)", program, timeout)
    if (produceModel && program.status == SatStatus.SAT) {
      processCommand("(get-model)", program, timeout)
    }

    return program.status to null
  }

  override fun close() {
    writer.write("(exit)")
    writer.close()
    reader.close()
    process.destroy()
  }

  fun reset() {
    writer.write("(reset)\n")
    writer.flush()
  }
}

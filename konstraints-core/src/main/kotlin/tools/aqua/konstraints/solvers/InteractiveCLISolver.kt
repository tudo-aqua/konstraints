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
import tools.aqua.konstraints.parser.*
import tools.aqua.konstraints.smt.*

class InteractiveZ3Solver : InteractiveCLISolver("z3", "-in")

class InteractiveCVC5Solver : InteractiveCLISolver("cvc5", "--interactive")

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

  private fun processCommand(cmd: Command, program: SMTProgram, timeout: Long) {
    writeCommand(cmd)
    val response =
        try {
          ResponseParser.parse(reader, program as MutableSMTProgram)
        } catch (e: Exception) {
          ErrorResponse(e.message ?: "")
        }

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

  override fun solve(program: SMTProgram): SatStatus {
    processCommand(SetOption(":print-success", BooleanOptionValue(true)), program, 1000L)
    program.commands.forEach {
      val timeout = 5000L
      processCommand(it, program, timeout)
    }

    return program.status
  }

  override fun getModel(): Model {
    return _model!!
  }

  fun closeForcibly() {
    // IMPORTANT kill the process first, or it waits for the writer and reader to close
    process.destroyForcibly()
    writer.close()
    reader.close()
  }

  override fun close() {
    writer.close()
    reader.close()
    process.destroy()
  }

  fun reset() {
    writer.write("(reset)\n")
    writer.flush()
  }
}

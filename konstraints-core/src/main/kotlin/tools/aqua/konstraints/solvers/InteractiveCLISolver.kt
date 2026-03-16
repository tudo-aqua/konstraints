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
import java.lang.Thread.sleep
import kotlinx.coroutines.TimeoutCancellationException
import kotlinx.coroutines.runBlocking
import kotlinx.coroutines.runInterruptible
import kotlinx.coroutines.withTimeout
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
import tools.aqua.konstraints.smt.QuotingRule
import tools.aqua.konstraints.smt.SMTProgram
import tools.aqua.konstraints.smt.SatStatus
import tools.aqua.konstraints.smt.SetOption

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

  /**
   * Wait for a solver response, kill the solver after [timeout] milliseconds and throw a
   * [SolverTimeoutException]
   */
  private fun waitResponse(timeout: Long) = runBlocking {
    try {
      withTimeout(timeout) {
        runInterruptible {
          // wait for reader to become available
          // sleep in the body of the loop because sleep is an interruptible function
          while (!reader.ready()) {
            sleep(1)
          }
        }
      }
    } catch (e: TimeoutCancellationException) {
      process.destroyForcibly()

      throw SolverTimeoutException(timeout)
    }

    /*
    var lines = ""
    while(reader.ready()) {
      lines += reader.readLine() + '\n'
    }
    lines
    */
  }

  private fun processCommand(cmd: Command, program: SMTProgram, timeout: Long) {
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

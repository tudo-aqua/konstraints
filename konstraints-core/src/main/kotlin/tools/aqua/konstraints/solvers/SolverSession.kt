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
import tools.aqua.konstraints.parser.GetValueResponse
import tools.aqua.konstraints.parser.ResponseParser
import tools.aqua.konstraints.parser.SolverResponse
import tools.aqua.konstraints.parser.SuccessResponse
import tools.aqua.konstraints.parser.UnsupportedResponse
import tools.aqua.konstraints.smt.Assert
import tools.aqua.konstraints.smt.BoolSort
import tools.aqua.konstraints.smt.BooleanOptionValue
import tools.aqua.konstraints.smt.Command
import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.smt.Model
import tools.aqua.konstraints.smt.NumeralOptionValue
import tools.aqua.konstraints.smt.Pop
import tools.aqua.konstraints.smt.Push
import tools.aqua.konstraints.smt.QuotingRule
import tools.aqua.konstraints.smt.SMTProgram
import tools.aqua.konstraints.smt.SatStatus
import tools.aqua.konstraints.smt.SetOption

/**
 * A long-lived connection to an SMT solver process that speaks SMT-LIB on stdin and stdout.
 *
 * In contrast to [Solver], which replays a whole [SMTProgram] for every query, a session sends each
 * command as it is issued. Push, pop and repeated check-sat calls are therefore truly incremental.
 * Terms in responses (get-value, get-model) are parsed over the declarations of the [SMTProgram]
 * passed to the respective call.
 */
class SolverSession(val dialect: SolverDialect, command: List<String> = dialect.command) :
    AutoCloseable {

  companion object {
    @JvmStatic fun z3() = SolverSession(SolverDialect.Z3)

    @JvmStatic fun cvc5() = SolverSession(SolverDialect.CVC5)
  }

  private val process: Process = ProcessBuilder(command).redirectErrorStream(true).start()
  private val writer = OutputStreamWriter(process.outputStream, Charsets.UTF_8)
  private val reader = BufferedReader(InputStreamReader(process.inputStream, Charsets.UTF_8))

  init {
    send(SetOption(":print-success", BooleanOptionValue(true)))
  }

  /** Sends [command] and expects a success response. */
  fun send(command: Command) {
    write { command.toSMTString(it, QuotingRule.SAME_AS_INPUT, true) }
    expectSuccess(ResponseParser.parseGeneralResponse(reader))
  }

  fun setOption(name: String, value: Boolean) = send(SetOption(name, BooleanOptionValue(value)))

  /** Sets a per-query timeout in milliseconds, or disables it if [millis] is not positive. */
  fun setTimeout(millis: Long) {
    val option = dialect.timeoutOption ?: throw SolverUnsupportedOperationException()
    send(SetOption(option, NumeralOptionValue(maxOf(millis, 0L).toBigInteger())))
  }

  fun assert(expr: Expression<BoolSort>) = send(Assert(expr))

  fun push(n: Int = 1) = send(Push(n))

  fun pop(n: Int = 1) = send(Pop(n))

  fun checkSat(): SatStatus {
    write { it.append("(check-sat)") }
    return when (val response = ResponseParser.parseCheckSatResponse(reader)) {
      is CheckSatResponse -> response.status
      else -> fail(response)
    }
  }

  /** Returns the values of [terms] in the current model. Requires a preceding sat result. */
  fun getValue(terms: List<Expression<*>>, program: SMTProgram): Map<Expression<*>, Expression<*>> {
    if (terms.isEmpty()) return emptyMap()

    write { out ->
      out.append("(get-value (")
      terms.forEachIndexed { i, term ->
        if (i > 0) out.append(" ")
        term.toSMTString(out, QuotingRule.SAME_AS_INPUT, true)
      }
      out.append("))")
    }
    return when (val response = ResponseParser.parseGetValueResponse(reader, program)) {
      is GetValueResponse -> response.values.toMap()
      else -> fail(response)
    }
  }

  fun getModel(program: SMTProgram): Model {
    write { it.append("(get-model)") }
    return when (val response = ResponseParser.parseModelResponse(reader, program)) {
      is GetModelResponse -> response.model
      else -> fail(response)
    }
  }

  /** Returns the raw response to `(get-info [keyword])`, e.g. `(:reason-unknown "timeout")`. */
  fun getInfo(keyword: String): String {
    write { it.append("(get-info $keyword)") }
    return reader.readParenthesizedMessage()
  }

  override fun close() {
    try {
      writer.write("(exit)\n")
      writer.flush()
      writer.close()
    } catch (_: java.io.IOException) {
      // the process is already gone
    } finally {
      reader.close()
      process.destroy()
    }
  }

  private inline fun write(block: (Appendable) -> Unit) {
    block(writer)
    writer.write("\n")
    writer.flush()
  }

  private fun expectSuccess(response: SolverResponse) {
    if (response !is SuccessResponse) fail(response)
  }

  private fun fail(response: SolverResponse): Nothing =
      when (response) {
        is ErrorResponse -> throw SolverError(response.msg)
        is UnsupportedResponse -> throw SolverUnsupportedOperationException()
        else -> throw UnexpectedSolverResponseException(response.toString())
      }
}

/** Command line and solver-specific option names of the solvers supported by [SolverSession]. */
enum class SolverDialect(val command: List<String>, val timeoutOption: String?) {
  Z3(listOf("z3", "-in"), ":timeout"),
  CVC5(listOf("cvc5", "--interactive", "--incremental"), ":tlimit-per"),
}

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
import tools.aqua.konstraints.parser.EchoResponse
import tools.aqua.konstraints.parser.ErrorResponse
import tools.aqua.konstraints.parser.GetModelResponse
import tools.aqua.konstraints.parser.ResponseParser
import tools.aqua.konstraints.parser.SolverResponse
import tools.aqua.konstraints.parser.SuccessResponse
import tools.aqua.konstraints.parser.UnsupportedResponse
import tools.aqua.konstraints.smt.Assert
import tools.aqua.konstraints.smt.BooleanOptionValue
import tools.aqua.konstraints.smt.Command
import tools.aqua.konstraints.smt.DeclareConst
import tools.aqua.konstraints.smt.DeclareFun
import tools.aqua.konstraints.smt.DeclareSort
import tools.aqua.konstraints.smt.DefineConst
import tools.aqua.konstraints.smt.DefineFun
import tools.aqua.konstraints.smt.DefineSort
import tools.aqua.konstraints.smt.Model
import tools.aqua.konstraints.smt.NullOp
import tools.aqua.konstraints.smt.Pop
import tools.aqua.konstraints.smt.Push
import tools.aqua.konstraints.smt.QuotingRule
import tools.aqua.konstraints.smt.SMTProgram
import tools.aqua.konstraints.smt.SatStatus
import tools.aqua.konstraints.smt.SetInfo
import tools.aqua.konstraints.smt.SetLogic
import tools.aqua.konstraints.smt.SetOption
import tools.aqua.konstraints.visitors.CommandVisitor

class InteractiveZ3Solver : InteractiveCLISolver("z3", "-in")

open class InteractiveCLISolver(val name: String, vararg solverOptions: String) :
    Solver, CommandVisitor<Unit> {

  // TODO this should have more exception handling
  val process: Process = ProcessBuilder(name, *solverOptions).redirectErrorStream(true).start()

  val writer = OutputStreamWriter(process.outputStream, Charsets.UTF_8)
  val reader = BufferedReader(InputStreamReader(process.inputStream, Charsets.UTF_8))

  private var status = SatStatus.PENDING
  private var model: Model? = null
  private lateinit var program: SMTProgram
  private var timeout = 0

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

  protected open fun processResponse(response: SolverResponse) {
    when (response) {
      is CheckSatResponse -> status = response.status
      is ErrorResponse -> throw SolverError(response.msg)
      is SuccessResponse -> Unit
      is UnsupportedResponse -> throw SolverUnsupportedOperationException()
      is GetModelResponse -> model = response.model
      is EchoResponse -> Unit
    }
  }

  override fun solve(
      program: SMTProgram,
      produceModel: Boolean,
      timeout: Long,
  ): Pair<SatStatus, Model?> {
    // TODO if this solver was used before/is still open from a previous solve,
    // the old program is still in the solver and we need to call reset

    this.program = program

    visit(SetOption(":print-success", BooleanOptionValue(true)))
    visit(SetOption(":produce-models", BooleanOptionValue(produceModel)))
    program.commands.filter { it !is NullOp }.forEach { visit(it) }

    checkSat()
    if (produceModel && status == SatStatus.SAT) {
      getModel()
    }

    return status to model
  }

  private fun checkSat() {
    writeCommand("(check-sat)")
    val response = ResponseParser.parseCheckSatResponse(reader)

    processResponse(response)
  }

  private fun getModel() {
    writeCommand("(get-model)")
    val response = ResponseParser.parseModelResponse(reader, program)

    processResponse(response)
  }

  override fun close() {
    writer.write("(exit)")
    writer.flush()
    writer.close()

    reader.close()
    process.destroy()
  }

  fun reset() {
    writer.write("(reset)\n")
    writer.flush()
  }

  override fun visit(assert: Assert) {
    writeCommand(assert)
    val response = ResponseParser.parseGeneralResponse(reader)

    processResponse(response)
  }

  override fun visit(declareConst: DeclareConst<*>) {
    writeCommand(declareConst)
    val response = ResponseParser.parseGeneralResponse(reader)

    processResponse(response)
  }

  override fun visit(declareFun: DeclareFun<*>) {
    writeCommand(declareFun)
    val response = ResponseParser.parseGeneralResponse(reader)

    processResponse(response)
  }

  override fun visit(setInfo: SetInfo) {
    writeCommand(setInfo)
    val response = ResponseParser.parseGeneralResponse(reader)

    processResponse(response)
  }

  override fun visit(setOption: SetOption) {
    writeCommand(setOption)
    val response = ResponseParser.parseGeneralResponse(reader)

    processResponse(response)
  }

  override fun visit(setLogic: SetLogic) {
    writeCommand(setLogic)
    val response = ResponseParser.parseGeneralResponse(reader)

    processResponse(response)
  }

  override fun visit(declareSort: DeclareSort) {
    writeCommand(declareSort)
    val response = ResponseParser.parseGeneralResponse(reader)

    processResponse(response)
  }

  override fun visit(defineConst: DefineConst<*>) {
    writeCommand(defineConst)
    val response = ResponseParser.parseGeneralResponse(reader)

    processResponse(response)
  }

  override fun visit(defineFun: DefineFun<*>) {
    writeCommand(defineFun)
    val response = ResponseParser.parseGeneralResponse(reader)

    processResponse(response)
  }

  override fun visit(push: Push) {
    writeCommand(push)
    val response = ResponseParser.parseGeneralResponse(reader)

    processResponse(response)
  }

  override fun visit(pop: Pop) {
    writeCommand(pop)
    val response = ResponseParser.parseGeneralResponse(reader)

    processResponse(response)
  }

  override fun visit(defineSort: DefineSort) {
    writeCommand(defineSort)
    val response = ResponseParser.parseGeneralResponse(reader)

    processResponse(response)
  }

  override fun visit(nullOp: NullOp) {}
}

package tools.aqua.konstraints.solvers

import tools.aqua.konstraints.smt.Assert
import tools.aqua.konstraints.smt.CheckSat
import tools.aqua.konstraints.smt.DeclareConst
import tools.aqua.konstraints.smt.DeclareFun
import tools.aqua.konstraints.smt.DeclareSort
import tools.aqua.konstraints.smt.DefineConst
import tools.aqua.konstraints.smt.DefineFun
import tools.aqua.konstraints.smt.DefineSort
import tools.aqua.konstraints.smt.Exit
import tools.aqua.konstraints.smt.GetModel
import tools.aqua.konstraints.smt.Model
import tools.aqua.konstraints.smt.Pop
import tools.aqua.konstraints.smt.Push
import tools.aqua.konstraints.smt.SMTProgram
import tools.aqua.konstraints.smt.SatStatus
import tools.aqua.konstraints.smt.SetInfo
import tools.aqua.konstraints.smt.SetLogic
import tools.aqua.konstraints.smt.SetOption
import tools.aqua.konstraints.visitors.CommandVisitor
import java.io.BufferedReader
import java.io.InputStreamReader
import java.io.OutputStreamWriter

class GenericSolver(val solverName : String, vararg solverOptions: String) : Solver, CommandVisitor<Unit> {
    // TODO this should have more exception handling
    val process: Process = ProcessBuilder(solverName, *solverOptions).redirectErrorStream(true).start()

    val writer = OutputStreamWriter(process.outputStream, Charsets.UTF_8)
    val reader = BufferedReader(InputStreamReader(process.inputStream, Charsets.UTF_8))

    private fun sendCommand(cmd: String) {
        writer.write(cmd + "\n")
        writer.flush()
    }

    private fun waitResponse(): String {
        // wait for new input
        while (!reader.ready());

        return reader.readLine()
    }

    override fun solve(program: SMTProgram): SatStatus {
        // so we can listen for the success or error response after every command
        // alternatively maybe wait for x amount of time for response then assume success?
        //sendCommand("(set-option :print-success true)")
        program.commands.forEach(::visit)

        return program.status
    }

    override val modelOrNull: Model?
        get() = TODO("Not yet implemented")
    override val isModelAvailable: Boolean
        get() = TODO("Not yet implemented")

    override fun close() {
        writer.close()
        reader.close()
        process.destroy()
    }

    override fun visit(assert: Assert) {
        sendCommand(assert.toString())
    }

    override fun visit(declareConst: DeclareConst<*>) {
        sendCommand(declareConst.toString())
    }

    override fun visit(declareFun: DeclareFun<*>) {
        sendCommand(declareFun.toString())
    }

    override fun visit(checkSat: CheckSat) {
        sendCommand(checkSat.toString())

        println(waitResponse())
    }

    override fun visit(exit: Exit) {
        sendCommand(exit.toString())
    }

    override fun visit(setInfo: SetInfo) {
        sendCommand(setInfo.toString())
    }

    override fun visit(setOption: SetOption) {
        sendCommand(setOption.toString())
    }

    override fun visit(setLogic: SetLogic) {
        sendCommand(setLogic.toString())
    }

    override fun visit(declareSort: DeclareSort) {
        sendCommand(declareSort.toString())
    }

    override fun visit(getModel: GetModel) {
        sendCommand(getModel.toString())
    }

    override fun visit(defineConst: DefineConst) {
        sendCommand(defineConst.toString())
    }

    override fun visit(defineFun: DefineFun) {
        sendCommand(defineFun.toString())
    }

    override fun visit(push: Push) {
        sendCommand(push.toString())
    }

    override fun visit(pop: Pop) {
        sendCommand(pop.toString())
    }

    override fun visit(defineSort: DefineSort) {
        sendCommand(defineSort.toString())
    }
}
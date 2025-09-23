package tools.aqua.konstraints.solvers

import org.petitparser.parser.Parser
import org.petitparser.parser.combinators.ChoiceParser
import org.petitparser.parser.combinators.SequenceParser
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

import org.petitparser.parser.primitive.StringParser.of
import tools.aqua.konstraints.parser.Parser.Companion.string
import tools.aqua.konstraints.parser.plus
import tools.aqua.konstraints.parser.times
import tools.aqua.konstraints.smt.BooleanOptionValue
import tools.aqua.konstraints.smt.Command
import tools.aqua.konstraints.smt.QuotingRule

/** Cleaner syntax for [ChoiceParser]. */
operator fun Parser.plus(other: Parser): ChoiceParser = or(other)

/** Cleaner syntax for [SequenceParser] */
operator fun Parser.times(other: Parser): SequenceParser = seq(other)

/** Infix syntax for [trim] parser. */
infix fun Parser.trim(both: Parser): Parser = trim(both)

// TODO add missing solver responses
enum class SolverResponseType {
    SUCCESS,
    UNSUPPORTED,
    ERROR,
    CHECK_SAT
}

interface SolverResponse {
    val type: SolverResponseType
}

object SuccessResponse : SolverResponse {
    override val type: SolverResponseType = SolverResponseType.SUCCESS
}

object UnsupportedResponse : SolverResponse {
    override val type: SolverResponseType = SolverResponseType.UNSUPPORTED
}

class ErrorResponse(val msg : String) : SolverResponse {
    override val type: SolverResponseType = SolverResponseType.ERROR
}

class CheckSatResponse(val status : SatStatus) : SolverResponse {
    override val type: SolverResponseType = SolverResponseType.CHECK_SAT
}

object ResponseParser {
    private val lparen = of("(")
    private val rparen = of(")")

    val success = of("success").map { _: Any -> SuccessResponse }
    val unsupported = of("unsupported").map { _: Any -> UnsupportedResponse }
    val error = (lparen * of("error") * string * rparen).map { results : ArrayList<Any> -> ErrorResponse(results[2] as String) }
    val generelResponse = success + unsupported + error

    val checkSat = of("sat").map { _: Any -> SatStatus.SAT } +
            of("unsat").map { _: Any -> SatStatus.UNSAT } +
            of("unknown").map { _: Any -> SatStatus.UNKNOWN }
    val checkSatResponse = checkSat.map { status: SatStatus -> CheckSatResponse(status) } + error
}

// TODO CommandVisitor should maybe be removed in favor of moving its functionality to the solver interface
class GenericSolver(val name : String, vararg solverOptions: String) : Solver, CommandVisitor<Unit> {

    // TODO this should have more exception handling
    val process: Process = ProcessBuilder(name, *solverOptions).redirectErrorStream(true).start()

    val writer = OutputStreamWriter(process.outputStream, Charsets.UTF_8)
    val reader = BufferedReader(InputStreamReader(process.inputStream, Charsets.UTF_8))

    private fun sendCommand(cmd: Command) {
        writer.write(cmd.toSMTString(QuotingRule.SAME_AS_INPUT) + "\n")
        writer.flush()
    }

    private fun waitResponse(): String {
        // wait for new input
        while (!reader.ready());

        return reader.readLine()
    }

    // TODO this should probably be suspending to allow for timeouts
    override suspend fun solve(program: SMTProgram): SatStatus {
        // so we can listen for the success or error response after every command
        // alternatively maybe wait for x amount of time for response then assume success?
        sendCommand(SetOption(":print-success", BooleanOptionValue(true)))
        program.commands.forEach(::visit)

        // program.toSMTString(writer, QuotingRule.SAME_AS_INPUT)
        // writer.flush()

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

    fun reset() {
        writer.write("(reset)\n")
        writer.flush()
    }

    override fun visit(assert: Assert) {
        sendCommand(assert)
    }

    override fun visit(declareConst: DeclareConst<*>) {
        sendCommand(declareConst)
    }

    override fun visit(declareFun: DeclareFun<*>) {
        sendCommand(declareFun)
    }

    override fun visit(checkSat: CheckSat) {
        sendCommand(checkSat)
    }

    // TODO this maybe should call close since the solver is shutdown
    override fun visit(exit: Exit) {
        sendCommand(exit)
    }

    override fun visit(setInfo: SetInfo) {
        sendCommand(setInfo)
    }

    override fun visit(setOption: SetOption) {
        sendCommand(setOption)
    }

    override fun visit(setLogic: SetLogic) {
        sendCommand(setLogic)
    }

    override fun visit(declareSort: DeclareSort) {
        sendCommand(declareSort)
    }

    override fun visit(getModel: GetModel) {
        sendCommand(getModel)
    }

    override fun visit(defineConst: DefineConst) {
        sendCommand(defineConst)
    }

    override fun visit(defineFun: DefineFun) {
        sendCommand(defineFun)
    }

    override fun visit(push: Push) {
        sendCommand(push)
    }

    override fun visit(pop: Pop) {
        sendCommand(pop)
    }

    override fun visit(defineSort: DefineSort) {
        sendCommand(defineSort)
    }
}
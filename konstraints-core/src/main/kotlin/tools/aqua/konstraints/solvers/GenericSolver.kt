package tools.aqua.konstraints.solvers

import kotlinx.coroutines.TimeoutCancellationException
import kotlinx.coroutines.runBlocking
import kotlinx.coroutines.runInterruptible
import kotlinx.coroutines.withTimeout
import org.petitparser.parser.Parser
import org.petitparser.parser.combinators.ChoiceParser
import org.petitparser.parser.combinators.SequenceParser
import tools.aqua.konstraints.smt.Model
import tools.aqua.konstraints.smt.SMTProgram
import tools.aqua.konstraints.smt.SatStatus
import tools.aqua.konstraints.smt.SetOption
import java.io.BufferedReader
import java.io.InputStreamReader
import java.io.OutputStreamWriter

import org.petitparser.parser.primitive.StringParser.of
import tools.aqua.konstraints.parser.Parser.Companion.string
import tools.aqua.konstraints.parser.plus
import tools.aqua.konstraints.parser.times
import tools.aqua.konstraints.smt.BooleanOptionValue
import tools.aqua.konstraints.smt.Command
import tools.aqua.konstraints.smt.Exit
import tools.aqua.konstraints.smt.QuotingRule
import java.lang.Thread.sleep
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import java.util.concurrent.TimeoutException
import kotlin.jvm.javaClass
import tools.aqua.konstraints.parser.Parser as SMTParser
import java.nio.channels.Pipe

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

sealed interface SolverResponse {
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

    private val success = of("success").map { _: Any -> SuccessResponse }
    private val unsupported = of("unsupported").map { _: Any -> UnsupportedResponse }
    private val error = (lparen * of("error") * string * rparen).map { results : ArrayList<Any> -> ErrorResponse(results[2] as String) }

    private val checkSatResponse = of("sat").map { _: Any -> CheckSatResponse(SatStatus.SAT) } +
            of("unsat").map { _: Any -> CheckSatResponse(SatStatus.UNSAT) } +
            of("unknown").map { _: Any -> CheckSatResponse(SatStatus.UNKNOWN) }

    private val generelResponse = success + unsupported + error + checkSatResponse

    fun parse(response: String) : SolverResponse {
        val result = generelResponse.parse(response)

        if(result.isSuccess) {
            return result.get<SolverResponse>()
        } else {
            throw UnexpectedSolverResponseException(response)
        }
    }
}

open class GenericSolver(val name : String, vararg solverOptions: String) : Solver {

    // TODO this should have more exception handling
    val process: Process = ProcessBuilder(name, *solverOptions).redirectErrorStream(true).start()

    val writer = OutputStreamWriter(process.outputStream, Charsets.UTF_8)
    val reader = BufferedReader(InputStreamReader(process.inputStream, Charsets.UTF_8))

    private fun sendCommand(cmd: Command) {
        cmd.toSMTString(writer, QuotingRule.SAME_AS_INPUT)
        writer.flush()
    }

    /**
     * Wait for a solver response, kill the solver after [timeout] milliseconds and throw a [SolverTimeoutException]
     */
    private fun waitResponse(timeout: Long): String = runBlocking {
        try {
            withTimeout(timeout) {
                runInterruptible {
                    while (!reader.ready()) {
                        sleep(1)
                    }

                    // TODO multiline output
                    reader.readLine()
                }
            }
        } catch (e: TimeoutCancellationException) {
            process.destroyForcibly()

            throw SolverTimeoutException(timeout)
        }
    }

    private fun processCommand(cmd: Command, program: SMTProgram, timeout: Long) {
        sendCommand(cmd)
        processResponse(ResponseParser.parse(waitResponse(timeout)), program)
    }

    protected open fun processResponse(response: SolverResponse, program: SMTProgram) {
        when (response) {
            is CheckSatResponse -> program.status = response.status
            is ErrorResponse -> throw SolverException(response.msg)
            is SuccessResponse -> Unit
            is UnsupportedResponse -> throw SolverUnsupportedOperationException()
        }
    }

    override fun solve(program: SMTProgram, timeout: Long): SatStatus {
        sendCommand(SetOption(":print-success", BooleanOptionValue(true)))
        program.commands.forEach {
            processCommand(it, program, timeout)
        }

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
}

open class SolverException(message: String) : RuntimeException(message)

class SolverTimeoutException(duration: Long) : SolverException("Solver timed out after $duration ms")

class UnexpectedSolverResponseException(response: String) : SolverException("Unexpected solver response: $response")

class SolverUnsupportedOperationException() : SolverException("Unsupported")
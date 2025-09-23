package tools.aqua.konstraints

import kotlinx.coroutines.runBlocking
import kotlinx.coroutines.withTimeoutOrNull
import org.junit.jupiter.api.AfterAll
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.Timeout
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import tools.aqua.konstraints.parser.Parser
import tools.aqua.konstraints.smt.SMTProgram
import tools.aqua.konstraints.smt.SymbolAttributeValue
import tools.aqua.konstraints.solvers.GenericSolver
import java.io.BufferedReader
import java.io.File
import java.util.concurrent.TimeUnit
import kotlin.streams.asStream
import kotlin.time.Duration

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class GenericSolverTests {
    val solver = GenericSolver("z3", "-in")

    private fun loadResource(path: String) =
        File(javaClass.getResource(path)!!.file)
            .walk()
            .filter { file: File -> file.isFile }
            .map { file: File -> Arguments.arguments(Parser().parse(file.bufferedReader().use(BufferedReader::readLines).joinToString("\n"))) }
            .asStream()

    @ParameterizedTest
    @MethodSource("loadQF_BV")
    fun testGenericZ3(program : SMTProgram) {
        solver.reset()
        runBlocking {
            withTimeoutOrNull(1000) {
                solver.solve(program)
            }
        }
    }

    @AfterAll
    fun close() {
        solver.close()
    }

    private fun loadQF_BV() = loadResource("/QF_BV/20190311-bv-term-small-rw-Noetzli/")
}
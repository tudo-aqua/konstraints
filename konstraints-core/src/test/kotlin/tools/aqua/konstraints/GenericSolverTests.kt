package tools.aqua.konstraints

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

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class GenericSolverTests {
    private fun loadResource(path: String) =
        File(javaClass.getResource(path)!!.file)
            .walk()
            .filter { file: File -> file.isFile }
            .map { file: File -> Arguments.arguments(Parser().parse(file.bufferedReader().use(BufferedReader::readLines).joinToString("\n"))) }
            .asStream()

    @ParameterizedTest
    @MethodSource("loadQF_BV")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun testGenericZ3(program : SMTProgram) {
        GenericSolver("z3", "-in").use { solver ->
            solver.solve(program)

            /*assertEquals(
                (program.info.find { it.keyword == ":status" }?.value as SymbolAttributeValue)
                    .symbol
                    .toString(),
                program.status.toString())*/
        }
    }

    private fun loadQF_BV() = loadResource("/QF_BV/20190311-bv-term-small-rw-Noetzli/")
}
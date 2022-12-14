package tools.aqua.constraints.runner

import com.github.h0tk3y.betterParse.grammar.parseToEnd
import org.junit.Test
import tools.aqua.constraints.smtlib.SMTLibParser
import tools.aqua.constraints.z3.Z3SMTLibSolver

class RunnerTest {
    @Test
    fun testExample1() {
        val smtProblem = RunnerTest::class.java.getResource("/QF_BV/debugging.smt").readText()
        val log = SMTLibParser().parseToEnd(smtProblem).execute( Z3SMTLibSolver() )
        log.forEach { println(it) }
        // Add assert
    }
}
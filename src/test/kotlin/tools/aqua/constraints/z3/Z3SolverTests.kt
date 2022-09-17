package tools.aqua.constraints.z3

import com.github.h0tk3y.betterParse.grammar.parseToEnd
import org.junit.Test
import tools.aqua.constraints.expressions.SMTLibExamples
import tools.aqua.constraints.smtlib.Assert
import tools.aqua.constraints.smtlib.SMTLibParser
import tools.aqua.constraints.solver.SMTLibSatSolver

class Z3SolverTests {

    @Test
    fun testExample1() {
        val log = SMTLibParser().parseToEnd(SMTLibExamples.example1).execute( Z3SMTLibSolver() )
        log.forEach { println(it) }
    }

    @Test
    fun testExample2() {
        val log = SMTLibParser().parseToEnd(SMTLibExamples.example2).execute( Z3SMTLibSolver() )
        log.forEach { println(it) }
    }

    @Test
    fun testExample3() {
        val log = SMTLibParser().parseToEnd(SMTLibExamples.example3).execute( Z3SMTLibSolver() )
        log.forEach { println(it) }
    }

    @Test
    fun testExample4() {
        val log = SMTLibParser().parseToEnd(SMTLibExamples.example4).execute( Z3SMTLibSolver() )
        log.forEach { println(it) }
    }
}
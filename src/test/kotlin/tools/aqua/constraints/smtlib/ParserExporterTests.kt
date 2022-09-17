package tools.aqua.constraints.smtlib

import com.github.h0tk3y.betterParse.grammar.parseToEnd
import org.junit.Test
import tools.aqua.constraints.expressions.SMTLibExamples

class ParserExporterTests {

    @Test
    fun testExample1() {
        val program = SMTLibParser().parseToEnd(SMTLibExamples.example1).toString()
        println(program)
        val program2 = SMTLibParser().parseToEnd(program).toString()
        assert( program == program2)
    }

    @Test
    fun testExample2() {
        val program = SMTLibParser().parseToEnd(SMTLibExamples.example2).toString()
        println(program)
        val program2 = SMTLibParser().parseToEnd(program).toString()
        assert( program == program2)
    }

    @Test
    fun testExample3() {
        val program = SMTLibParser().parseToEnd(SMTLibExamples.example3).toString()
        println(program)
        val program2 = SMTLibParser().parseToEnd(program).toString()
        assert( program == program2)
    }

    @Test
    fun testExample4() {
        val program = SMTLibParser().parseToEnd(SMTLibExamples.example4).toString()
        println(program)
        val program2 = SMTLibParser().parseToEnd(program).toString()
        assert( program == program2)
    }

    @Test
    fun testExample5() {
        val program = SMTLibParser().parseToEnd(SMTLibExamples.example5).toString()
        println(program)
        val program2 = SMTLibParser().parseToEnd(program).toString()
        assert( program == program2)
    }

    @Test
    fun testExample6() {
        val program = SMTLibParser().parseToEnd(SMTLibExamples.example6).toString()
        println(program)
        val program2 = SMTLibParser().parseToEnd(program).toString()
        assert( program == program2)
    }
}
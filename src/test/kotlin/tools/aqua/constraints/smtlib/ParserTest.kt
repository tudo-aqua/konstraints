package tools.aqua.constraints.smtlib

import com.github.h0tk3y.betterParse.grammar.parseToEnd
import org.junit.Test
import tools.aqua.constraints.expressions.SMTLibExamples

class ParserTest {

    @Test
    fun testDeclareFun1() {
        val program = SMTLibParser().parseToEnd("(assert\n" +
                " (= z\$101 (ite (= f00 (_ bv0 1)) (_ bv1 1) (_ bv0 1))))")
        println(program)
    }
}
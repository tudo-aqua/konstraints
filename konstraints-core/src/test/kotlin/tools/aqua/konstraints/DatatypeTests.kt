package tools.aqua.konstraints

import org.junit.jupiter.api.Test
import tools.aqua.konstraints.parser.Parser

class DatatypeTests {
    @Test
    fun intListTest() {
        val smt = "(set-logic QF_IDL)" +
            "(declare-datatype IntList( ( empty )( insert ( head Int ) ( tail IntList ) )))" +
                "(declare-const l IntList)" +
                "(assert (= l l))" +
                "(check-sat)"
        val prg = Parser(smt)
        println(prg.toString())
    }
}
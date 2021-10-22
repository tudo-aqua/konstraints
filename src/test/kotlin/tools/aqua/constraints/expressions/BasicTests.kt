package tools.aqua.constraints.expressions

import com.github.h0tk3y.betterParse.grammar.parseToEnd
import org.junit.Assert.assertEquals
import org.junit.Test
import tools.aqua.constraints.smtlib.export.SMTLibExport
import tools.aqua.constraints.smtlib.parser.SMTLibParser
import tools.aqua.constraints.visitors.FreeVariables
import tools.aqua.constraints.z3.NativeExpressionGenerator

class BasicTests {

    @Test
    fun testVisitor() {

        val lit = FPLiteral(Float32,"1", "00000000", "00000000000000000000000")

        val eq = FPEq(
                lit,
                FPNaN(Float32)
        )

        println("LIT TYPE: ${lit.type}")

        println( SMTLibExport.export(eq) )

        assertEquals("x", "x")
    }

    @Test
    fun testWalker() {
        val min = FPMin(Float32,
                FPLiteral(Float32,"1", "00000000", "00000000000000000000000"),
                FPVariable("myFloat", Float32)
        )

        val vars = FreeVariables.of(min)
        println(SMTLibExport.declare(vars[0]))

        assertEquals("x", "x")
    }

    @Test
    fun testSolver() {

        val a = BooleanVariable("a")
        val b = BooleanVariable("b")

        val and = And(arrayOf(a, b));

        val s = NativeExpressionGenerator()
        s.solve(and)

        assertEquals("x", "x")
    }

    @Test
    fun testConversion() {

        val a = FPVariable("a", Float32)

        val to_sbv = FPtoSBV<BitVec32, Float32>(BitVec32, RoundingMode.RNE, a)

        println( SMTLibExport.export(to_sbv) )

        assertEquals("x", "x")
    }

    @Test
    fun testParser() {
        val expr = "(fp.eq (fp #b1 #b00000000 #b00000000000000000000000) (fp #b1 #b00000000 #b00000000000000000000000))"
        println(SMTLibExport.export(SMTLibParser.parseToEnd(expr)))
    }
}
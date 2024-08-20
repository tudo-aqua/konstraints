package tools.aqua.konstraints

import org.junit.jupiter.api.Test
import tools.aqua.konstraints.dsl.*
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.solvers.z3.Z3Solver
import tools.aqua.konstraints.theories.BoolSort
import tools.aqua.konstraints.theories.Not
import kotlin.reflect.KProperty

class DSLTests {
    @Test
    fun testCoreDSL() {
        val solver = Z3Solver()

        val program = smt {
            val A = declareConst("A", BoolSort)
            val B by Const(BoolSort)

            assert {
                +((A and B).finalize() or (A and Not(B)).finalize())
            }
        }

        val result = solver.solve(program)

        print(result)
    }
}

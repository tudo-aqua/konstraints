package tools.aqua.konstraints.solvers

import tools.aqua.konstraints.dsl.bvult
import tools.aqua.konstraints.dsl.declaringConst
import tools.aqua.konstraints.dsl.smt
import tools.aqua.konstraints.smt.BitVecLiteral
import tools.aqua.konstraints.smt.Model
import tools.aqua.konstraints.smt.QF_BV
import tools.aqua.konstraints.smt.SMTBitVec
import tools.aqua.konstraints.smt.SMTProgram

class MajorityVoteSolver(override val solvers: Iterable<Solver>, val policy: ExecutionPolicy) : MetaSolver {
    override fun solve(program: SMTProgram) = solve(program, policy)

    override fun getModel(): Model {
        TODO("Not yet implemented")
    }

    override fun solve(
        program: SMTProgram,
        policy: ExecutionPolicy
    ) =
        when (policy) {
            ExecutionPolicy.PARALLEL -> solveParallel(program)
            ExecutionPolicy.SEQUENTIAL -> solveSequential(program)
        }.groupingBy { it }.eachCount().maxBy { it.value }.key

    override fun close() {
        // empty
    }
}

fun main() {
    val solver = MajorityVoteSolver(
        listOf(InteractiveZ3Solver(), InteractiveCVC5Solver()), ExecutionPolicy.PARALLEL
    )

    val program = smt(QF_BV) {
        val x by declaringConst(SMTBitVec(8))

        assert(x bvult BitVecLiteral(0, 8))
        checkSat()
    }

    val status = solver.use { solver ->
        solver.solve(program)
    }

    println(status)
}

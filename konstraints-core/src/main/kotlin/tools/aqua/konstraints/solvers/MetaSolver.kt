package tools.aqua.konstraints.solvers

import kotlinx.coroutines.*
import tools.aqua.konstraints.smt.SMTProgram
import tools.aqua.konstraints.smt.SatStatus

enum class ExecutionPolicy {
    SEQUENTIAL, PARALLEL
}

interface MetaSolver : Solver {
    val solvers: Iterable<Solver>

    fun solve(program : SMTProgram, policy: ExecutionPolicy): SatStatus

    /**
     * Execute solvers sequentially.
     * @return List of [SatStatus]
     */
    fun solveSequential(program : SMTProgram) = solvers.map { solver -> solver.use { solver -> solver.solve(program) } }

    /**
     * Execute solvers sequentially, returns first result for which [condition] returns true.
     * @return [SatStatus]
     */
    fun solveSequential(program : SMTProgram, condition : (Solver, SatStatus) -> Boolean) : SatStatus {
        solvers.map { solver ->
            val status = solver.use { solver -> solver.solve(program) }
            if (condition(solver, status)) {
                return status
            }
        }

        return SatStatus.UNKNOWN
    }

    /**
     * Execute solvers in parallel.
     * @return List of [SatStatus]
     */
    fun solveParallel(program : SMTProgram) =
        runBlocking {
            solvers.map { solver -> async { solver.use { solver -> solver.solve(program) } } }.awaitAll()
        }

    /**
     * Execute solvers in parallel, returns first result for which [condition] returns true
     * @return List of [SatStatus]
     */
    fun solveParallel(program : SMTProgram, condition : (Solver, SatStatus) -> Boolean): SatStatus = TODO()
}
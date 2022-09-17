package tools.aqua.constraints.solver

import tools.aqua.constraints.expressions.BooleanExpression
import tools.aqua.constraints.smtlib.SMTLibSolver
import tools.aqua.constraints.visitors.FreeVariables

/**
 * Inteface for simple sat solvers (á la JConstraints)
 */
interface SMTSatSolver {

    fun isSatisfiable(vararg expr: BooleanExpression) : SatResult
}

/**
 * Implementation of SMTSatSolver that uses a SMTLibSolver
 */
class SMTLibSatSolver(val solver: SMTLibSolver) : SMTSatSolver {

    override fun isSatisfiable(vararg expr: BooleanExpression): SatResult {
        expr.flatMap{ FreeVariables.of(it) }.distinct().forEach { solver.declareFunction(  it.symbol, emptyList(), it.type ) }
        expr.forEach { solver.assert(it) }
        return solver.checkSat()
    }

}
package tools.aqua.constraints.analysis

import tools.aqua.constraints.expressions.BooleanExpression

interface Solver {

    fun isSatisbiable(vararg expr:BooleanExpression) : SolverResult

}
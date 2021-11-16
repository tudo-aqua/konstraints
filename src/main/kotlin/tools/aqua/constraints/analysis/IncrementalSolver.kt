package tools.aqua.constraints.analysis

import tools.aqua.constraints.expressions.BooleanExpression

interface IncrementalSolver {

    fun add(vararg expr: BooleanExpression)

    fun push()

    fun pop()

}
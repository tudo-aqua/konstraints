package tools.aqua.constraints.analysis

import tools.aqua.constraints.expressions.BooleanExpression

interface WitnessProvider {

    fun solveWithWitness(vararg expr: BooleanExpression)
}
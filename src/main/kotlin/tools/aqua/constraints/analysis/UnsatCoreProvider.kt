package tools.aqua.constraints.analysis

import tools.aqua.constraints.expressions.BooleanExpression

interface UnsatCoreProvider {

    fun solveAndProvideUnsatCore(vararg expr: BooleanExpression) : UnsatCoreProviderResult

}
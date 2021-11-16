package tools.aqua.constraints.analysis

import tools.aqua.constraints.expressions.BooleanExpression

interface ModelGenerator {

    fun findModel(vararg expr:BooleanExpression) : ModelGeneratorResult
}
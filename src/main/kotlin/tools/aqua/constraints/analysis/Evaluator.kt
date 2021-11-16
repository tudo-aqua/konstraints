package tools.aqua.constraints.analysis

import tools.aqua.constraints.expressions.Expression
import tools.aqua.constraints.expressions.Sort

interface Evaluator {

    fun <T: Sort> evaluate(expression:Expression<T>) : EvaluationResult<T>

}
package tools.aqua.constraints.analysis

import tools.aqua.constraints.expressions.Literal
import tools.aqua.constraints.expressions.Sort

interface EvaluationResult<T: Sort>

data class ValueResult<T: Sort>(val value: Literal<T>) : EvaluationResult<T>

data class NoValueResult<T: Sort>(val notes: String) : EvaluationResult<T>


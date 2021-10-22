package tools.aqua.constraints.analysis

import tools.aqua.constraints.expressions.Literal
import tools.aqua.constraints.expressions.Sort

data class EvaluationResult<T: Sort>(val value: Literal<T>?, val notes:String)



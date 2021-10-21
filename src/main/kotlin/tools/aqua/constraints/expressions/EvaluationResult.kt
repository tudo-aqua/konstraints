package tools.aqua.constraints.expressions

data class EvaluationResult<T:Sort>(val value:Literal<T>?, val notes:String)



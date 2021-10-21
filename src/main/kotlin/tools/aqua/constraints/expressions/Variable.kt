package tools.aqua.constraints.expressions

abstract class Variable<T : Sort>(override val symbol:String, override val type:T) : Expression<T> {

    override fun evaluate(vals: Valuation): EvaluationResult<T> {
        return if (vals.containsKey(this)) {
            EvaluationResult(vals[this] as Literal<T>, "")
        }
        else {
            EvaluationResult(null, "no value in valuation for variable $symbol")
        }
    }
}

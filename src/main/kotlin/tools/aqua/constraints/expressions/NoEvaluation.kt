package tools.aqua.constraints.expressions

/**
 * provides boilerplate implementation for missing evaluation
 */
abstract class NoEvaluation<T:Sort> : Expression<T> {

    /**
     * returns null value and note of missing implementation
     */
    override fun evaluate(vals: Valuation): EvaluationResult<T> =
            EvaluationResult(null, "eval not implemented for $symbol")

}
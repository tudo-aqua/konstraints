package tools.aqua.constraints.expressions

/**
 * Marker interface for function expressions
 */
interface FunctionExpression<T : Sort> : Expression<T>

/**
 * Function declaration
 */
data class Function<T : FunctionSort>(override val symbol:String, override val type:T) :
    FunctionExpression<T>, Variable<T>(symbol, type) {

    override fun toString(): String = super<Variable>.toString()
}

/**
 * Function application
 */
data class Application<T : Sort>(val function:Function<*>, val args:List<Expression<*>>) :
    FunctionExpression<T>,  Variable<T>(function.symbol, function.type.returnType) {
    override fun toString(): String = "($symbol ${args.joinToString(" ")})"
}

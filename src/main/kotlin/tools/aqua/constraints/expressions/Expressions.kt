package tools.aqua.constraints.expressions

/**
 * Marker interface for all expressions
 *
 * T : evaluation type of the expression
 */
interface Expression<T : Sort> {

    /**
     * SMTLib operator symbol of this expression
     */
    val symbol:String
}

/**
 * AbstractExpression is the class that all expression types
 * extend.
 *
 * Implements marker interface Expression
 * Adds default constructor to marker interface.
 */
abstract class AbstractExpression<T:Sort>(override val symbol: String = "") : Expression<T>


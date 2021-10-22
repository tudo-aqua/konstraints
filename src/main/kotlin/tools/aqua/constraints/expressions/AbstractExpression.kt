package tools.aqua.constraints.expressions

/**
 * sets symbol and type of expression
 */
abstract class AbstractExpression<T:Sort>(
        override val symbol: String = "",
        override val type : Sort = NoSort) : Expression<T>

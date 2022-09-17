package tools.aqua.constraints.expressions

/*
 * Marker interfaces used by VisitByStructure
 */

abstract class Literal<T : Sort>(override val symbol: String) : AbstractExpression<T>(symbol) {
    override fun toString() = symbol
}

abstract class Variable<T : Sort>(override val symbol: String, open val type:Sort) : AbstractExpression<T>(symbol) {
    override fun toString() = symbol
}

abstract class UnaryExpression<T : Sort, I : Expression<*>>(
    override val symbol: String, open val inner : I) : AbstractExpression<T>(symbol) {
    override fun toString(): String = "($symbol $inner)"
}

abstract class BinaryExpression<T : Sort, I : Expression<*>>(
    override val symbol: String, open val left : I, open val right : I) : AbstractExpression<T>(symbol) {
    override fun toString(): String = "($symbol $left $right)"
}

abstract class ITEExpression<T : Sort>(override val symbol: String,
    open val cnd : BooleanExpression, open val thn : Expression<T>, open val els : Expression<T>) : AbstractExpression<T>(symbol) {
    override fun toString(): String = "($symbol $cnd $thn $els)"
}

abstract class ExpressionWithBoundVariables<T : Sort>(override val symbol: String,
    open val vars  : List<Variable<*>>, open val inner : Expression<T>) : AbstractExpression<T>(symbol) {
    override fun toString(): String = "($symbol (${vars.joinToString(" ") { "(${it.symbol} ${it.type})" }}) $inner)"
}

abstract class ExpressionWithLocalVariables<T : Sort>(override val symbol: String,
    open val vars  : Map<Variable<*>, Expression<*>>, open val inner : Expression<T>) : AbstractExpression<T>(symbol) {
    override fun toString(): String = "($symbol (${vars.map { "(${it.key} ${it.value})" }.joinToString(" ")}) $inner)"
}

abstract class NAryExpression<T : Sort, I : Expression<*>>(
    override val symbol: String, open val children : List<I>) : AbstractExpression<T>(symbol) {
    override fun toString(): String = "($symbol ${children.joinToString(" ")})"
}


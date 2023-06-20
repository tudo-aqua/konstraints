abstract class Expression<T : Sort> {
    abstract val symbol : String
    abstract val sort: T

    override fun toString() = symbol
}

class BasicExpression<T : Sort>(override val symbol : String, override val sort : T) : Expression<T>() {
    override fun toString() = "$symbol"
}

class UnaryExpression<T : Sort>(symbol: String, override val sort : T, val other: Expression<T>) : Expression<T>() {
    override val symbol = symbol
    override fun toString() = "($symbol ${other})"
}

class BinaryExpression<T : Sort>(symbol: String, override val sort : T, val left: Expression<T>, val right: Expression<T>) : Expression<T>() {
    override val symbol = symbol
    override fun toString() = "($symbol ${left} ${right})"
}

class NAryExpression<T : Sort>(symbol: String, override val sort : T, val tokens: List<Expression<T>>) : Expression<T>() {
    override val symbol = symbol
    override fun toString() = "($symbol ${tokens.joinToString(" ")})"
}
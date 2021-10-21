package tools.aqua.constraints.expressions

interface Literal<T : Sort> : Expression<T>

interface UnaryExpression<T : Sort, I : Expression<*>> : Expression<T> {
    val inner : I
}

interface BinaryExpression<T : Sort, I : Expression<*>> : Expression<T> {
    val left  : I
    val right : I
}

interface ITEExpression<T : Sort> : Expression<T> {
    val cnd : BooleanExpression
    val thn : Expression<T>
    val els : Expression<T>
}

interface NAryExpression<T : Sort, I : Expression<*>> : Expression<T> {
    val children : Array<I>
}


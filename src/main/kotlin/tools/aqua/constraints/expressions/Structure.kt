package tools.aqua.constraints.expressions

interface Literal<T : Sort> : Expression<T>

interface Variable<T : Sort> : Expression<T>

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

interface ExpressionWithBoundVariables<T : Sort> : Expression<T> {
    val vars  : Array<Variable<*>>
    val inner : Expression<T>
}

interface ExpressionWithLocalVariables<T : Sort> : Expression<T> {
    val vars  : Map<Variable<*>, Expression<*>>
    val inner : Expression<T>
}
interface NAryExpression<T : Sort, I : Expression<*>> : Expression<T> {
    val children : Array<I>
}


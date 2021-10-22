package tools.aqua.constraints.expressions


data class Ite<T:Sort> (override val type:T, override val cnd : BooleanExpression,
                        override val thn : Expression<T>, override val els : Expression<T>) :
        ITEExpression<T>, AbstractExpression<T>("ite")

data class Let<T:Sort> (override val type:T, override val vars:Map<Variable<*>,Expression<*>>, override val inner: Expression<T>) :
        ExpressionWithLocalVariables<T>, AbstractExpression<T>("let")
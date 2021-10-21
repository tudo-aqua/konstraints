package tools.aqua.constraints.expressions


interface BVExpression<T : BVSort> : Expression<T>

interface BVBooleanExpression<T : BVSort> : BooleanExpression

/**
 * bv add
 */
data class BVAdd<T : BVSort>(override val type:T, override val left : Expression<T>, override val right : Expression<T>) :
        BVExpression<T>, BinaryExpression<T, Expression<T>>, NoEvaluation<T>() {
    override val symbol = "bvadd"
}

/**
 * bv signed less
 */
data class BVSLeq<T : BVSort>(override val left : Expression<T>, override val right : Expression<T>) :
        BVBooleanExpression<T>, BinaryExpression<BoolSort, Expression<T>>, NoEvaluation<BoolSort>() {
    override val symbol = "bvsle"
    override val type = BoolSort
}

data class BPVariable<T : BVSort>(override val symbol:String, override val type:T) :
    Variable<T>(symbol, type), BVExpression<T>

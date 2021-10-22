package tools.aqua.constraints.expressions


abstract class BVExpression<T : BVSort>(override val symbol: String = "") : AbstractExpression<T>(symbol)
abstract class BVBooleanExpression<I : BVSort>(override val symbol: String) : BooleanExpression(symbol)

/*
 * Arithmetic
 */

data class BVAdd<T : BVSort>(override val type:T, override val left : Expression<T>, override val right : Expression<T>) :
        BinaryExpression<T, Expression<T>>, BVExpression<T>("bvadd")

/*
 * Comparisons
 */

data class BVSLeq<I : BVSort>(override val left : Expression<I>, override val right : Expression<I>) :
        BinaryExpression<BoolSort, Expression<I>>, BVBooleanExpression<I>("bvsle")

/*
 * Variables
 */

data class BPVariable<T : BVSort>(override val symbol:String, override val type:T) :
    Variable<T>, BVExpression<T>()

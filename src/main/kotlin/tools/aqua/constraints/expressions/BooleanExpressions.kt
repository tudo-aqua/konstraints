package tools.aqua.constraints.expressions;

abstract class BooleanExpression(override val symbol: String = "") : AbstractExpression<BoolSort>(symbol, BoolSort)

/**
 * Core Boolean
 */

data class And(override val children : Array<BooleanExpression>) :
        NAryExpression<BoolSort, BooleanExpression>, BooleanExpression("and")

data class Or(override val children : Array<BooleanExpression>) :
        NAryExpression<BoolSort, BooleanExpression>, BooleanExpression("or")

data class Xor(override val left : BooleanExpression, override val right : BooleanExpression) :
    BinaryExpression<BoolSort, BooleanExpression>, BooleanExpression("xor")

data class Implies(override val left : BooleanExpression, override val right : BooleanExpression) :
        BinaryExpression<BoolSort, BooleanExpression>, BooleanExpression("=>")

data class Not(override val inner : BooleanExpression) :
        UnaryExpression<BoolSort, BooleanExpression>, BooleanExpression("not")

/**
 * Quantified: Exists
 */
data class Exists(override val vars : Array<Variable<*>>, override val inner : BooleanExpression) :
        ExpressionWithBoundVariables<BoolSort>, BooleanExpression("exists")

data class Forall(override val vars : Array<Variable<*>>, override val inner : BooleanExpression) :
        ExpressionWithBoundVariables<BoolSort>, BooleanExpression("forall")

/**
 * Equality/Distinct for all sorts
 */
data class Eq<I:Sort> (override val left : Expression<I>, override val right : Expression<I>) :
        BinaryExpression<BoolSort, Expression<I>>, BooleanExpression("=")

data class Distinct<I:Sort>(override val children : Array<Expression<I>>) :
        NAryExpression<BoolSort, Expression<I>>, BooleanExpression("distinct")

/**
 * Variable
 */
data class BooleanVariable(override val symbol:String) :
    Variable<BoolSort>, BooleanExpression()

/**
 * Constants
 */
object True  : Literal<BoolSort>, BooleanExpression("true")
object False : Literal<BoolSort>, BooleanExpression("false")

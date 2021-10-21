package tools.aqua.constraints.expressions;

interface BooleanExpression : Expression<BoolSort>

/**
 * Core And
 */
data class And(override val children : Array<BooleanExpression>) :
        BooleanExpression, NAryExpression<BoolSort, BooleanExpression>, NoEvaluation<BoolSort>() {
    override val symbol = "and"
    override val type = BoolSort
}

/**
 * Core Or
 */
data class Or(override val children : Array<BooleanExpression>) :
    BooleanExpression, NAryExpression<BoolSort, BooleanExpression>, NoEvaluation<BoolSort>() {
    override val symbol = "or"
    override val type = BoolSort
}

/**
 * Core Xor
 */
data class Xor(override val left : BooleanExpression, override val right : BooleanExpression) :
    BooleanExpression, BinaryExpression<BoolSort, BooleanExpression>, NoEvaluation<BoolSort>() {
    override val symbol = "xor"
    override val type = BoolSort
}

/**
 * Core Implies
 */
data class Implies(override val left : BooleanExpression, override val right : BooleanExpression) :
    BooleanExpression, BinaryExpression<BoolSort, BooleanExpression>, NoEvaluation<BoolSort>() {
    override val symbol = "=>"
    override val type = BoolSort
}

/**
 * Core Not
 */
data class Not(override val inner : BooleanExpression) :
        BooleanExpression, UnaryExpression<BoolSort, BooleanExpression>, NoEvaluation<BoolSort>() {
    override val symbol = "not"
    override val type = BoolSort
}

/**
 * Equality for all sorts
 */
data class Eq<I:Sort> (override val left : Expression<I>, override val right : Expression<I>) :
        BooleanExpression, BinaryExpression<BoolSort, Expression<I>>, NoEvaluation<BoolSort>() {
    override val symbol = "="
    override val type = BoolSort
}

/**
 * Distinct for all sorts
 */
data class Distinct<I:Sort>(override val children : Array<Expression<I>>) :
    BooleanExpression, NAryExpression<BoolSort, Expression<I>>, NoEvaluation<BoolSort>() {
    override val symbol = "distinct"
    override val type = BoolSort
}

/**
 * ITE for all sorts
 */
data class Ite<T:Sort> (override val type:T, override val cnd : BooleanExpression,
                        override val thn : Expression<T>, override val els : Expression<T>) :
    Expression<T>, ITEExpression<T>, NoEvaluation<T>() {
    override val symbol = "ite"
}

/**
 * Variable
 */
data class BooleanVariable(override val symbol:String) :
    Variable<BoolSort>(symbol, BoolSort), BooleanExpression

/**
 * True named literal
 */
object True : BooleanExpression, Literal<BoolSort> {
    override val symbol = "true"
    override val type = BoolSort
    override fun evaluate(vals: Valuation): EvaluationResult<BoolSort> =
        EvaluationResult(this, "")
    override fun toString(): String {
        return this.symbol
    }
}

/**
 * False named literal
 */
object False : BooleanExpression, Literal<BoolSort> {
    override val symbol = "false"
    override val type = BoolSort
    override fun evaluate(vals: Valuation): EvaluationResult<BoolSort> =
        EvaluationResult(this, "")
    override fun toString(): String {
        return this.symbol
    }
}
package tools.aqua.constraints.expressions;

// Cf. https://smtlib.cs.uiowa.edu/theories-Core.shtml

/**
 * Marker interface Boolean expressions
 */
interface BooleanExpression : Expression<BoolSort>

/*
 * Boolean expressions
 */

/**
 * SMTLib and
 */
data class And(override val children : List<BooleanExpression>) : BooleanExpression,
        NAryExpression<BoolSort, BooleanExpression>("and", children) {
    override fun toString() = super<NAryExpression>.toString()
}

/**
 * SMTLib or
 */
data class Or(override val children : List<BooleanExpression>) : BooleanExpression,
        NAryExpression<BoolSort, BooleanExpression>("or", children) {
    override fun toString() = super<NAryExpression>.toString()
}

/**
 * SMTLib xor
 */
data class Xor(override val left : BooleanExpression, override val right : BooleanExpression) : BooleanExpression,
    BinaryExpression<BoolSort, BooleanExpression>("xor", left, right) {
    override fun toString() = super<BinaryExpression>.toString()
}

/**
 * SMTLib =>
 */
data class Implies(override val left : BooleanExpression, override val right : BooleanExpression) : BooleanExpression,
        BinaryExpression<BoolSort, BooleanExpression>("=>", left, right) {
    override fun toString() = super<BinaryExpression>.toString()
}

/**
 * SMTLib not
 */
data class Not(override val inner : BooleanExpression) : BooleanExpression,
        UnaryExpression<BoolSort, BooleanExpression>("not", inner) {
    override fun toString() = super<UnaryExpression>.toString()
}

/*
 * Quantified expressions
 */

/**
 * SMTLib exists
 */
data class Exists(override val vars : List<Variable<*>>, override val inner : BooleanExpression) : BooleanExpression,
        ExpressionWithBoundVariables<BoolSort>("exists", vars, inner)

/**
 * SMTLib forall
 */
data class Forall(override val vars : List<Variable<*>>, override val inner : BooleanExpression) : BooleanExpression,
        ExpressionWithBoundVariables<BoolSort>("forall", vars, inner)

/*
 * Variables, literals, constants
 */

/**
 * Boolean variable
 */
data class BooleanVariable(override val symbol:String) : BooleanExpression, Variable<BoolSort>(symbol, BoolSort) {
    override fun toString() = super<Variable>.toString()
}

/**
 * Boolean constant: true
 */
object True  : BooleanExpression, Literal<BoolSort>("true")

/**
 * Boolean constant: false
 */
object False : BooleanExpression, Literal<BoolSort>("false")


/*
 * Core expressions that are not Boolean
 */

/**
 * SMTLib = (for all sorts)
 */
data class Eq<I:Sort>(override val left : Expression<I>, override val right : Expression<I>) : BooleanExpression,
    BinaryExpression<BoolSort, Expression<I>>("=", left, right) {
    override fun toString(): String = super<BinaryExpression>.toString()
}

/**
 * SMTLib distinct (for all sorts)
 */
data class Distinct<I:Sort>(override val children : List<Expression<I>>) : BooleanExpression,
    NAryExpression<BoolSort, Expression<I>>("distinct", children)

/**
 * SMTLib ite
 */
data class Ite<T:Sort> (override val cnd : BooleanExpression, override val thn : Expression<T>, override val els : Expression<T>) :
    ITEExpression<T>("ite", cnd, thn, els) {

    override fun toString(): String = "($symbol $cnd $thn $els)"
}

/**
 * SMTLib let
 */
data class Let<T:Sort> (override val vars:Map<Variable<*>,Expression<*>>, override val inner: Expression<T>) :
    ExpressionWithLocalVariables<T>("let", vars, inner)

/**
 * Generic variable class
 */
data class TypedVariable<T:Sort>(override val symbol:String, override val type:T) :
    Variable<T>(symbol, type)
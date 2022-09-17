package tools.aqua.constraints.expressions;

// TODO: many missing operations
// TODO: missing literals

/**
 * Marker interface for bit vector expressions
 */
interface NumericExpression<T : NumericSort> : Expression<T>
/**
 * Marker interface for bit vector Boolean expressions
 */
interface NumericBooleanExpression<I : NumericSort> : BooleanExpression

/*
 * Numeric expressions
 */

/**
 * SMTLib +
 */
data class Add<T: NumericSort>(override val children : List<NumericExpression<T>>) :
    NumericExpression<T>, NAryExpression<T, NumericExpression<T>>("+", children) {

    override fun toString() = super<NAryExpression>.toString()
}

/**
 * SMTLib -
 */
data class Sub<T: NumericSort>(override val left : NumericExpression<T>, override val right : NumericExpression<T>) :
    NumericExpression<T>, BinaryExpression<T, NumericExpression<T>>("-", left, right) {

    override fun toString() = super<BinaryExpression>.toString()
}

/**
 * SMTLib *
 */
data class Mul<T: NumericSort>(override val children : List<NumericExpression<T>>) :
    NumericExpression<T>, NAryExpression<T, NumericExpression<T>>("*", children) {

    override fun toString() = super<NAryExpression>.toString()
}

/**
 * SMTLib div
 */
data class Div<T: NumericSort>(override val left : NumericExpression<T>, override val right : NumericExpression<T>) :
    NumericExpression<T>, BinaryExpression<T, NumericExpression<T>>("/", left, right)

/**
 * SMTLib mod
 */
data class Mod(override val left : NumericExpression<IntSort>, override val right : NumericExpression<IntSort>) :
    NumericExpression<IntSort>, BinaryExpression<IntSort, NumericExpression<IntSort>>("mod", left, right)

/**
 * SMTLib - (unary)
 */
data class Neg<T: NumericSort>(override val inner : NumericExpression<T>) :
    NumericExpression<T>, UnaryExpression<T, NumericExpression<T>>("-", inner) {

    override fun toString() = super<UnaryExpression>.toString()
}

/**
 * SMTLib abs
 */
data class Abs(override val inner : NumericExpression<IntSort>) :
    NumericExpression<IntSort>, UnaryExpression<IntSort, NumericExpression<IntSort>>("abs", inner)

/*
 * Numeric Boolean expressions
 */

/**
 * SMTLib >
 */
data class Gt<I: NumericSort>(override val left : NumericExpression<I>, override val right : NumericExpression<I>) :
    NumericBooleanExpression<I>, BinaryExpression<BoolSort, NumericExpression<I>>(">", left, right)

/**
 * SMTLib <
 */
data class Lt<I: NumericSort>(override val left : NumericExpression<I>, override val right : NumericExpression<I>) :
    NumericBooleanExpression<I>, BinaryExpression<BoolSort, NumericExpression<I>>("<", left, right)

/**
 * SMTLib >=
 */
data class GEq<I: NumericSort>(override val left : NumericExpression<I>, override val right : NumericExpression<I>) :
    NumericBooleanExpression<I>, BinaryExpression<BoolSort, NumericExpression<I>>(">=", left, right)

/**
 * SMTLib <=
 */
data class LEq<I: NumericSort>(override val left : NumericExpression<I>, override val right : NumericExpression<I>) :
    NumericBooleanExpression<I>, BinaryExpression<BoolSort, NumericExpression<I>>("<=", left, right)


/*
 * Variables and literals
 */

/**
 * Integer literal
 */
data class IntLiteral(val value:Int) : NumericExpression<IntSort>, Literal<IntSort>("$value") {
    override fun toString(): String = super<Literal>.toString()
}

/**
 * Numeric variable
 */
data class NumericVariable<T : NumericSort>(override val symbol:String, override val type:T) :
    NumericExpression<T>, Variable<T>(symbol, type) {

    override fun toString() = super<Variable>.toString()
}

/*
 * Conversions
 */


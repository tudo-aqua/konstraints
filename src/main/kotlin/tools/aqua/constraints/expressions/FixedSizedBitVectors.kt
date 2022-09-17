package tools.aqua.constraints.expressions

// Cf. https://smtlib.cs.uiowa.edu/theories-FixedSizeBitVectors.shtml

// TODO: many missing operations
// TODO: missing literals

/**
 * Marker interface for bit vector expressions
 */
interface BVExpression<T : BVSort> : Expression<T>
/**
 * Marker interface for bit vector Boolean expressions
 */
interface BVBooleanExpression<I : BVSort> : BooleanExpression

/*
 * Arithmetic
 */

/**
 * SMTLib bvadd
 */
data class BVAdd<T : BVSort>(override val left : Expression<T>, override val right : Expression<T>) : BVExpression<T>,
        BinaryExpression<T, Expression<T>>("bvadd", left, right) {

        override fun toString(): String = super<BinaryExpression>.toString()
}

/**
 * SMTLib bvsub
 */
data class BVSub<T : BVSort>(override val left : Expression<T>, override val right : Expression<T>) : BVExpression<T>,
        BinaryExpression<T, Expression<T>>("bvsub", left, right) {

        override fun toString(): String = super<BinaryExpression>.toString()
}

/**
 * SMTLib bvmul
 */
data class BVMul<T : BVSort>(override val left : Expression<T>, override val right : Expression<T>) : BVExpression<T>,
        BinaryExpression<T, Expression<T>>("bvmul", left, right) {

        override fun toString(): String = super<BinaryExpression>.toString()
}

/**
 * SMTLib bvdiv
 */
data class BVDiv<T : BVSort>(override val left : Expression<T>, override val right : Expression<T>) : BVExpression<T>,
        BinaryExpression<T, Expression<T>>("bvdiv", left, right) {

        override fun toString(): String = super<BinaryExpression>.toString()
}

/*
 * Comparisons
 */

/**
 * SMTLib bvsle
 */
data class BVSLeq<I : BVSort>(override val left : Expression<I>, override val right : Expression<I>) : BVBooleanExpression<I>,
        BinaryExpression<BoolSort, Expression<I>>("bvsle", left, right) {

        override fun toString(): String = super<BinaryExpression>.toString()
}

/*
 * Variables, literals, constants
 */

/**
 * Bit vector variable
 */
data class BVVariable<T : BVSort>(override val symbol:String, override val type:T) : BVExpression<T>,
        Variable<T>(symbol, type) {

        override fun toString(): String = super<Variable>.toString()
}

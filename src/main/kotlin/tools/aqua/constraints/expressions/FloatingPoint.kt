package tools.aqua.constraints.expressions;

// Cf. https://smtlib.cs.uiowa.edu/theories-FloatingPoint.shtml

// TODO: many missing operations

/**
 * SMTLib floating point rounding modes:
 *
 * roundNearestTiesToEven RNE
 * roundNearestTiesToAway RNA
 * roundTowardPositive    RTP
 * roundTowardNegative    RTN
 * roundTowardZero        RTZ
 **/
enum class RoundingMode {

        RNE, RNA, RTP, RTN, RTZ;
        override fun toString() = when(this) {
                RNE -> "roundNearestTiesToEven"
                RNA -> "roundNearestTiesToAway"
                RTP -> "roundTowardPositive"
                RTN -> "roundTowardNegative"
                RTZ -> "roundTowardZero"
        }
}

/**
 * Marker interface for floating point expressions
 */
interface FPExpression<T : FPSort> : Expression<T>

/**
 * Marker interface for floating point Boolean expressions
 */
interface FPBooleanExpression<I: FPSort> : BooleanExpression

/*
 * Arithmetic
 */

/**
 * SMTLib fp.add
 */
data class FPAdd<T : FPSort>(val rnd: RoundingMode, override val left : Expression<T>, override val right : Expression<T>) :
        FPExpression<T>, BinaryExpression<T, Expression<T>>("fp.add", left, right) {
        override fun toString(): String = "($symbol $rnd $left $right)"
}

/**
 * SMTLib fp.sub
 */
data class FPSub<T : FPSort>(val rnd: RoundingMode, override val left : Expression<T>, override val right : Expression<T>) :
        FPExpression<T>, BinaryExpression<T, Expression<T>>("fp.sub", left, right) {
        override fun toString(): String = "($symbol $rnd $left $right)"
}

/**
 * SMTLib fp.mul
 */
data class FPMul<T : FPSort>(val rnd : RoundingMode, override val left : Expression<T>, override val right : Expression<T>)  :
        FPExpression<T>, BinaryExpression<T, Expression<T>>("fp.mul", left, right) {
        override fun toString(): String = "($symbol $rnd $left $right)"
}

/**
 * SMTLib fp.div
 */
data class FPDiv<T : FPSort>(val rnd: RoundingMode, override val left : Expression<T>, override val right : Expression<T>) :
        FPExpression<T>, BinaryExpression<T, Expression<T>>("fp.div", left, right) {
        override fun toString(): String = "($symbol $rnd $left $right)"
}

/**
 * SMTLib fp.rem
 */
data class FPRem<T : FPSort>(val rnd: RoundingMode, override val left : Expression<T>, override val right : Expression<T>)  :
        FPExpression<T>, BinaryExpression<T, Expression<T>>("fp.rem", left, right) {
        override fun toString(): String = "($symbol $rnd $left $right)"
}

/**
 * SMTLib fp.min
 */
data class FPMin<T : FPSort>(override val left : Expression<T>, override val right : Expression<T>)  :
        FPExpression<T>, BinaryExpression<T, Expression<T>>("fp.min", left, right)

/**
 * SMTLib fp.max
 */
data class FPMax<T : FPSort>(override val left : Expression<T>, override val right : Expression<T>) :
        FPExpression<T>, BinaryExpression<T, Expression<T>>("fp.max", left, right)

/*
 * Comparisons
 */

/**
 * SMTLib fp.eq
 */
data class FPEq<I : FPSort>(override val left : Expression<I>, override val right : Expression<I>) :
        FPBooleanExpression<I>, BinaryExpression<BoolSort, Expression<I>>("fp.eq", left, right) {
        override fun toString() = super<BinaryExpression>.toString()
}

/*
 * Conversions
 */

/**
 * SMTLib (_ to_fp eb sb) RoundingMode (_ BitVec m) (_ FloatingPoint eb sb)
 */
data class FPtoFPfromBV<T : FPSort, I : BVSort>(val type:T, override val inner : BVExpression<I>) :
        FPExpression<T>, UnaryExpression<T, BVExpression<I>>("(_ to_fp ${type.eBits} ${type.mBits})", inner)

/**
 * SMTLib (_ fp.to_sbv m) RoundingMode (_ FloatingPoint eb sb) (_ BitVec m)
 */
data class FPtoSBV<T : BVSort, I : FPSort>(val type:T, val rnd:RoundingMode, override val inner : FPExpression<I>) :
    BVExpression<T>, UnaryExpression<T, FPExpression<I>>( "(_ fp.to_sbv ${type.bits})", inner) {
        override fun toString(): String = "($symbol $rnd $inner)"
    }

/*
 * Variables, literals, constants
 */

/**
 * Floating point variable
 */
data class FPVariable<T : FPSort>(override val symbol:String, override val type:T) :
        FPExpression<T>, Variable<T>(symbol, type)

/**
 * Floating point literal
 */
data class FPLiteral<T : FPSort>(val sBit:String, val eBits: String, val mBits: String) :
        FPExpression<T>,  Literal<T>("fp") {
        override fun toString(): String = "($symbol #b$sBit #b$eBits #b$mBits)"
}

/*
 * Constants
 */

/**
 * SMTLib (_ NaN eb sb)
 */
data class FPNaN<T : FPSort>(val type:T) : FPExpression<T>, Literal<T>("_ NaN") {
        override fun toString(): String = "($symbol ${type.eBits} ${type.mBits})"
}


package tools.aqua.constraints.expressions;

enum class RoundingMode {RNE, RNA, RTZ}

abstract class FPExpression<T : FPSort>(override val symbol: String = "") : AbstractExpression<T>(symbol)
abstract class FPBooleanExpression<I: FPSort>(override val symbol: String) : BooleanExpression(symbol)

/*
 * Arithmetic
 */

data class FPAdd<T : FPSort>(override val type:T, val rnd: RoundingMode, override val left : Expression<T>, override val right : Expression<T>) :
        BinaryExpression<T, Expression<T>>, FPExpression<T>("fp.add")

data class FPSub<T : FPSort>(override val type:T, val rnd: RoundingMode, override val left : Expression<T>, override val right : Expression<T>) :
        BinaryExpression<T, Expression<T>>, FPExpression<T>("fp.sub")

data class FPMul<T : FPSort>(override val type:T, val rnd : RoundingMode, override val left : Expression<T>, override val right : Expression<T>) :
        BinaryExpression<T, Expression<T>>, FPExpression<T>("fp.mul")

data class FPDiv<T : FPSort>(override val type:T, val rnd: RoundingMode, override val left : Expression<T>, override val right : Expression<T>) :
        BinaryExpression<T, Expression<T>>, FPExpression<T>("fp.div")

data class FPRem<T : FPSort>(override val type:T, val rnd: RoundingMode, override val left : Expression<T>, override val right : Expression<T>) :
        BinaryExpression<T, Expression<T>>, FPExpression<T>("fp.rem")

data class FPMin<T : FPSort>(override val type:T, override val left : Expression<T>, override val right : Expression<T>) :
        BinaryExpression<T, Expression<T>>, FPExpression<T>("fp.min")

data class FPMax<T : FPSort>(override val type:T, override val left : Expression<T>, override val right : Expression<T>) :
        BinaryExpression<T, Expression<T>>, FPExpression<T>("fp.max")

/*
 * Comparisons
 */

data class FPEq<I : FPSort>(override val left : Expression<I>, override val right : Expression<I>) :
        BinaryExpression<BoolSort, Expression<I>>, FPBooleanExpression<I>("fp.eq")

/*
 * Conversions
 */

data class FPtoFPfromBV<T : FPSort, I : BVSort>(override val type:T, override val inner : BVExpression<I>) :
        UnaryExpression<T, BVExpression<I>>, FPExpression<T>("(_ to_fp ${type.eBits} ${type.mBits})")

data class FPtoSBV<T : BVSort, I : FPSort>(override val type:T, val rnd:RoundingMode, override val inner : FPExpression<I>) :
    UnaryExpression<T, FPExpression<I>>, BVExpression<T>( "(_ fp.to_sbv ${type.bits})")

/*
 * Variables / Literals
 */

data class FPVariable<T : FPSort>(override val symbol:String, override val type:T) :
    Variable<T>, FPExpression<T>()

data class FPLiteral<T : FPSort>(override val type:T, val sBit:String, val eBits: String, val mBits: String) :
        Literal<T>, FPExpression<T>("fp")

/*
 * Constants
 */

data class FPNaN<T : FPSort>(override val type:T) : Literal<T>,  FPExpression<T>("_ NaN")


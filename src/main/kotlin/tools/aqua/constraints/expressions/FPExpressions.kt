package tools.aqua.constraints.expressions;


enum class RoundingMode {RNE, RNA, RTZ}

interface FPExpression<T : FPSort> : Expression<T>

interface FPBooleanExpression<T : FPSort> : BooleanExpression

data class FPAdd<T : FPSort>(override val type:T, val rnd: RoundingMode, override val left : Expression<T>, override val right : Expression<T>) :
        FPExpression<T>, BinaryExpression<T, Expression<T>>, NoEvaluation<T>() {
    override val symbol = "fp.add"
}

data class FPSub<T : FPSort>(override val type:T, val rnd: RoundingMode, override val left : Expression<T>, override val right : Expression<T>) :
        FPExpression<T>, BinaryExpression<T, Expression<T>>, NoEvaluation<T>() {
    override val symbol = "fp.sub"
}

data class FPMul<T : FPSort>(override val type:T, val rnd : RoundingMode, override val left : Expression<T>, override val right : Expression<T>) :
        FPExpression<T>, BinaryExpression<T, Expression<T>>, NoEvaluation<T>() {
    override val symbol = "fp.mul"
}

data class FPDiv<T : FPSort>(override val type:T, val rnd: RoundingMode, override val left : Expression<T>, override val right : Expression<T>) :
        FPExpression<T>, BinaryExpression<T, Expression<T>>, NoEvaluation<T>() {
    override val symbol = "fp.div"
}

data class FPRem<T : FPSort>(override val type:T, val rnd: RoundingMode, override val left : Expression<T>, override val right : Expression<T>) :
        FPExpression<T>, BinaryExpression<T, Expression<T>>, NoEvaluation<T>() {
    override val symbol = "fp.rem"
}
data class FPMin<T : FPSort>(override val type:T, override val left : Expression<T>, override val right : Expression<T>) :
        FPExpression<T>,  BinaryExpression<T, Expression<T>>, NoEvaluation<T>() {
    override val symbol = "fp.min"
}

data class FPMax<T : FPSort>(override val type:T, override val left : Expression<T>, override val right : Expression<T>) :
        FPExpression<T>, BinaryExpression<T, Expression<T>>, NoEvaluation<T>() {
    override val symbol = "fp.max"
}

data class FPEq<T : FPSort>(override val left : Expression<T>, override val right : Expression<T>) :
        FPBooleanExpression<T>, BinaryExpression<BoolSort, Expression<T>>, NoEvaluation<BoolSort>() {
    override val symbol = "fp.eq"
    override val type = BoolSort
}

data class FPtoFPfromBV<T : FPSort, I : BVSort>(override val type:T, override val inner : BVExpression<I>) :
        FPExpression<T>, UnaryExpression<T, BVExpression<I>>, NoEvaluation<T>() {
    override val symbol = "(_ to_fp ${type.eBits} ${type.mBits})"
}

/**
 * fp.to_sbv
 */
data class FPtoSBV<T : BVSort, I : FPSort>(override val type:T, val rnd:RoundingMode, override val inner : FPExpression<I>) :
    BVExpression<T>, UnaryExpression<T, FPExpression<I>>, NoEvaluation<T>() {
    override val symbol = "(_ fp.to_sbv ${type.bits})"
}

/**
 * variable
 */
data class FPVariable<T : FPSort>(override val symbol:String, override val type:T) :
    Variable<T>(symbol, type), FPExpression<T>

/**
 * constant
 */
data class FPLiteral<T : FPSort>(override val type:T, val sBit:String, val eBits: String, val mBits: String) :
        FPExpression<T>, Literal<T> {
    override val symbol = "fp"
    override fun evaluate(vals: Valuation): EvaluationResult<T> = EvaluationResult(this, "")
}

/**
 * NaN
 */
data class FPNaN<T : FPSort>(override val type:T) :
        FPExpression<T>, Literal<T> {
    override val symbol = "_ NaN"
    override fun evaluate(vals: Valuation): EvaluationResult<T> = EvaluationResult(this, "")
}


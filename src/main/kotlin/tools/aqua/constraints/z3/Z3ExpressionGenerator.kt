package tools.aqua.constraints.z3

import com.microsoft.z3.*
import com.microsoft.z3.RealSort
import tools.aqua.constraints.visitors.VisitByType
import tools.aqua.constraints.expressions.*
import tools.aqua.constraints.expressions.FPSort
import tools.aqua.constraints.expressions.IntSort
import tools.aqua.constraints.expressions.Sort

class Z3ExpressionGenerator : VisitByType<Z3Context, Expr<*>>() {

    // TODO: add missing cases

    // Boolean

    override fun visit(expr: And, z3ctx: Z3Context): Expr<*> =
        z3ctx.context.mkAnd(*expr.children.map { c -> visit(c, z3ctx) as BoolExpr }.toTypedArray())

    override fun visit(expr: Or, z3ctx: Z3Context): Expr<*> =
        z3ctx.context.mkOr(*expr.children.map { c -> visit(c, z3ctx) as BoolExpr }.toTypedArray())

    override fun visit(expr: Xor, z3ctx: Z3Context): Expr<*> =
        z3ctx.context.mkXor(visit(expr.left, z3ctx) as BoolExpr, visit(expr.right, z3ctx) as BoolExpr)

    override fun visit(expr: Implies, z3ctx: Z3Context): Expr<*> =
        z3ctx.context.mkImplies(visit(expr.left, z3ctx) as BoolExpr, visit(expr.right, z3ctx) as BoolExpr)

    override fun visit(expr: Not, z3ctx: Z3Context): Expr<*> =
        z3ctx.context.mkNot(visit(expr.inner, z3ctx) as BoolExpr)

    override fun visit(expr: BooleanVariable, z3ctx: Z3Context): Expr<*> = z3ctx.constants[expr.symbol]!!

    override fun visit(expr: True, z3ctx: Z3Context): Expr<*> = z3ctx.context.mkTrue()
    override fun visit(expr: False, z3ctx: Z3Context): Expr<*> = z3ctx.context.mkFalse()

    override fun visit(expr: Eq<*>, z3ctx: Z3Context): Expr<*> =
        z3ctx.context.mkEq(visit(expr.left, z3ctx), visit(expr.right, z3ctx))

    override fun <I : Sort> visit(expr: Distinct<I>, z3ctx: Z3Context): Expr<*> =
        z3ctx.context.mkDistinct(*expr.children.map { c -> visit(c, z3ctx) }.toTypedArray())

    // Numeric

    override fun <T:NumericSort> visit(expr:Add<T>, z3ctx: Z3Context) : Expr<*> =
        z3ctx.context.mkAdd( *expr.children.map{ visit(it, z3ctx) as ArithExpr }.toTypedArray() )

    override fun <T:NumericSort> visit(expr:Sub<T>, z3ctx: Z3Context) : Expr<*> =
        z3ctx.context.mkSub( visit(expr.left, z3ctx) as ArithExpr, visit(expr.right, z3ctx) as ArithExpr )

    override fun <T:NumericSort> visit(expr:Mul<T>, z3ctx: Z3Context) : Expr<*> =
        z3ctx.context.mkMul( *expr.children.map{ visit(it, z3ctx) as ArithExpr }.toTypedArray() )

    override fun <T:NumericSort> visit(expr:Neg<T>, z3ctx: Z3Context) : Expr<*> =
        z3ctx.context.mkUnaryMinus( visit(expr.inner, z3ctx) as ArithExpr )

    override fun <T:NumericSort> visit(expr:NumericVariable<T>, z3ctx: Z3Context) : Expr<*> =
        when (expr.type) {
            is IntSort -> z3ctx.context.mkIntConst(expr.symbol)
            is RealSort -> z3ctx.context.mkRealConst(expr.symbol)
            else -> error("unsupported sort: ${expr.type}")
        }

    override fun visit(expr:IntLiteral, z3ctx: Z3Context) : Expr<*> =
        z3ctx.context.mkInt(expr.value)

    // Bitvector

    override fun <T : BVSort> visit(expr: FPtoSBV<T, *>, z3ctx: Z3Context) =
        // FIXME: dummy implementation
        z3ctx.context.mkBV(0, 32)

    // Float

    override fun <T : FPSort> visit(expr: FPNaN<T>, z3ctx: Z3Context) =
        z3ctx.context.mkFPNaN( z3ctx.context.mkFPSort32()) // FIXME: dummy sort

    override fun <T : FPSort> visit(expr: FPLiteral<T>, z3ctx: Z3Context) =
        // TODO: test
        z3ctx.context.mkFP(
            z3ctx.context.mkBV(expr.sBit.toInt(2), 1),
            z3ctx.context.mkBV(expr.eBits.toLong(2), expr.eBits.length),
            z3ctx.context.mkBV(expr.mBits.toLong(2), expr.mBits.length))

    override fun <T : FPSort> visit(expr: FPEq<T>, z3ctx: Z3Context) = z3ctx.context.mkFPEq(
        visit(expr.left, z3ctx) as FPExpr,
        visit(expr.right, z3ctx) as FPExpr)

    // Global

    override fun <T : Sort> visit(expr: Variable<T>, z3ctx: Z3Context) = z3ctx.constants[expr.symbol]!!

    override fun <T : Sort> visit(expr: Ite<T>, z3ctx: Z3Context): Expr<*> =
        z3ctx.context.mkITE( visit(expr.cnd, z3ctx) as BoolExpr, visit(expr.thn, z3ctx), visit(expr.els, z3ctx))

    // Uninterpreted functions

    override fun <T : Sort> visit(expr: Application<T>, z3ctx: Z3Context): Expr<*> =
        z3ctx.context.mkApp(z3ctx.functions[expr.symbol]!!, *expr.args.map{ visit(it, z3ctx) }.toTypedArray() )

}
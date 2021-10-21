package tools.aqua.constraints.z3

import com.microsoft.z3.*
import tools.aqua.constraints.visitors.VisitByType
import tools.aqua.constraints.expressions.*
import tools.aqua.constraints.expressions.BoolSort
import tools.aqua.constraints.expressions.FPSort
import tools.aqua.constraints.expressions.Sort

class NativeExpressionGenerator : VisitByType<Context, Expr<*>>() {

    private val variables = HashMap<Variable<*>, Expr<*>>()

    // Boolean

    override fun visit(expr: And, ctx : Context) : Expr<*> =
        ctx.mkAnd( *expr.children.map { c -> visit(c, ctx) as BoolExpr }.toTypedArray() )

    override fun visit(expr: Or, ctx: Context): Expr<*> =
        ctx.mkOr( *expr.children.map { c -> visit(c, ctx) as BoolExpr }.toTypedArray() )

    override fun visit(expr: Xor, ctx: Context): Expr<*> =
        ctx.mkXor(visit(expr.left, ctx) as BoolExpr, visit(expr.right, ctx) as BoolExpr)

    override fun visit(expr: Implies, ctx: Context): Expr<*> =
        ctx.mkImplies(visit(expr.left, ctx) as BoolExpr, visit(expr.right, ctx) as BoolExpr)

    override fun visit(expr: Not, ctx: Context): Expr<*> =
        ctx.mkNot(visit(expr.inner, ctx) as BoolExpr)

    override fun visit(expr: True, ctx: Context): Expr<*>  = ctx.mkTrue()
    override fun visit(expr: False, ctx: Context): Expr<*> = ctx.mkFalse()

    override fun <I : Sort> visit(expr: Eq<I>, ctx: Context): Expr<*> =
        ctx.mkEq( visit(expr.left, ctx), visit(expr.right, ctx))

    override fun <I : Sort> visit(expr: Distinct<I>, ctx: Context): Expr<*> =
        ctx.mkDistinct( *expr.children.map { c -> visit(c, ctx) }.toTypedArray() )

    // Bitvector

    override fun <T:BVSort> visit(expr : FPtoSBV<T,*>, ctx : Context) =
        // FIXME: dummy implementation
        ctx.mkBV(0,32)

    // Float

    override fun <T : FPSort> visit(expr: FPNaN<T>, ctx: Context) =
        ctx.mkFPNaN(sort(expr.type, ctx) as com.microsoft.z3.FPSort)

    override fun <T : FPSort> visit(expr: FPLiteral<T>, ctx: Context) =
        // FIXME: dummy implementation
        ctx.mkFP(0.0, sort(expr.type, ctx) as com.microsoft.z3.FPSort)

    override fun <T : FPSort> visit(expr: FPEq<T>, ctx: Context) = ctx.mkFPEq(
        visit(expr.left, ctx) as FPExpr,
        visit(expr.right, ctx) as FPExpr)

    // Global

    override fun <T : Sort> visit(expr: Variable<T>, ctx: Context) =
        getOrCreateVariable(expr, ctx)

    override fun <T : Sort> visit(expr: Ite<T>, ctx: Context): Expr<*> =
        ctx.mkITE( visit(expr.cnd, ctx) as BoolExpr, visit(expr.thn, ctx), visit(expr.els, ctx))

    private fun getOrCreateVariable(v:Variable<*>, ctx:Context ) : Expr<*> {
        if (!variables.containsKey(v)) {
            variables[v] = when (v.type) {
                is BoolSort -> ctx.mkBoolConst(v.symbol)
                else -> throw Exception("Sort not supported.")
            }
        }
        return variables[v]!!
    }

    private fun sort(sort:Sort, ctx: Context) : com.microsoft.z3.Sort = when(sort) {
        is BoolSort -> ctx.mkBoolSort()
        is Float32 -> ctx.mkFPSort32()
        is FPSort -> ctx.mkFPSort(sort.eBits, sort.mBits)
        else -> throw Exception("sort not supported.")
    }

    // Public API

    fun solve(expr:BooleanExpression) {
        val ctx = Context()
        val z3Expr = visit(expr, ctx) as BoolExpr
        val solver =ctx.mkSolver()
        solver.add(z3Expr)
        val status = solver.check()
        println("STATUS: $status")
    }


}
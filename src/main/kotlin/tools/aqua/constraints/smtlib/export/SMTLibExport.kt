package tools.aqua.constraints.smtlib.export

import tools.aqua.constraints.expressions.*
import tools.aqua.constraints.visitors.VisitByType


object SMTLibExport : VisitByType<Appendable, Unit>() {

    // Boolean

    override fun visit(expr: And, ctx: Appendable) = paren(ctx, expr, *expr.children)
    override fun visit(expr: Or, ctx: Appendable) = paren(ctx, expr, *expr.children)
    override fun visit(expr: Xor, ctx: Appendable) = paren(ctx, expr, expr.left, expr.right)
    override fun visit(expr: Implies, ctx: Appendable) = paren(ctx, expr, expr.left, expr.right)
    override fun visit(expr: Not, ctx: Appendable) = paren(ctx, expr, expr.inner)

    override fun visit(expr: True, ctx: Appendable)  { ctx.append(expr.symbol) }
    override fun visit(expr: False, ctx: Appendable) { ctx.append(expr.symbol) }

    override fun <I : Sort> visit(expr: Eq<I>, ctx: Appendable) = paren(ctx, expr, expr.left, expr.right)
    override fun <I : Sort> visit(expr: Distinct<I>, ctx: Appendable) = paren(ctx, expr, *expr.children)

    // Bitvector

    override fun <T:BVSort> visit(expr : FPtoSBV<T,*>, ctx : Appendable) =
        paren(ctx, expr, "(${expr.rnd} RoundingMode)", expr.inner)

    // Float

    override fun <T : FPSort> visit(expr: FPEq<T>, ctx: Appendable) =
            paren(ctx, expr, expr.left, expr.right)

    override fun <T : FPSort> visit(expr: FPNaN<T>, ctx: Appendable) =
            paren(ctx, expr, expr.type.eBits.toString(), expr.type.mBits.toString())

    override fun <T : FPSort> visit(expr: FPLiteral<T>, ctx: Appendable) =
            paren(ctx, expr,"#b" + expr.sBit, "#b" + expr.eBits, "#b" + expr.mBits)

    // Global

    override fun <T:Sort> visit(expr: Variable<T>, ctx : Appendable) {
        ctx.append(expr.symbol)
    }

    override fun <T : Sort> visit(expr: Ite<T>, ctx: Appendable) =
        paren(ctx, expr, expr.cnd, expr.thn, expr.els)

    // Helpers

    private fun paren(ctx: Appendable, expr:Expression<*>, vararg children:Expression<*>) {
        ctx.append("(")
        ctx.append(expr.symbol)
        for (child in children) {
            ctx.append(" ")
            visit(child, ctx)
        }
        ctx.append(")")
    }

    private fun paren(ctx: Appendable, expr:Expression<*>, vararg args:String) {
        ctx.append("(")
        ctx.append(expr.symbol)
        for (a in args) {
            ctx.append(" ").append(a)
        }
        ctx.append(")")
    }

    private fun paren(ctx: Appendable, expr:Expression<*>, param:String, vararg children:Expression<*>) {
        ctx.append("(")
        ctx.append(expr.symbol).append(" ").append(param)
        for (child in children) {
            ctx.append(" ")
            visit(child, ctx)
        }
        ctx.append(")")
    }

    // Public API

    fun declare(v : Variable<*>) : String = "(declare-const ${v.symbol} ${v.type})"

    fun export(expr : Expression<*>) : String {
        val sb = StringBuilder()
        visit(expr, sb)
        return sb.toString()
    }

}
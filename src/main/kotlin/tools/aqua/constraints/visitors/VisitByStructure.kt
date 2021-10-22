package tools.aqua.constraints.visitors

import tools.aqua.constraints.expressions.*

/**
 * Basis for Structural Case Splits
 */
open class VisitByStructure<in H> {

    open fun visit (expr : Literal<*>, ctx : H) {}

    open fun visit (expr : Variable<*>, ctx : H) {}

    open fun visit (expr : UnaryExpression<*,*>, ctx : H) {
        visit(expr.inner, ctx)
    }

    open fun visit (expr : BinaryExpression<*,*>, ctx : H) {
        visit(expr.left, ctx)
        visit(expr.right, ctx)
    }

    open fun visit (expr : NAryExpression<*,*>, ctx : H) =
        expr.children.forEach { visit(it, ctx) }

    open fun visit (expr : ITEExpression<*>, ctx : H) {
        visit(expr.cnd, ctx)
        visit(expr.thn, ctx)
        visit(expr.els, ctx)
    }

    open fun visit (expr : ExpressionWithBoundVariables<*>, ctx : H) {
        // TODO: what about vars?
        visit(expr.inner, ctx)
    }

    open fun visit (expr : ExpressionWithLocalVariables<*>, ctx : H) {
        // TODO: what about vars / terms?
        visit(expr.inner, ctx)
    }

    fun <T: Sort> visit(expr : Expression<T>, ctx : H) {
        when (expr) {
            is Literal<*> -> visit(expr, ctx)
            is Variable<*> -> visit(expr, ctx)
            is UnaryExpression<*,*> -> visit(expr, ctx)
            is BinaryExpression<*,*> -> visit(expr, ctx)
            is NAryExpression<*,*> -> visit(expr, ctx)
            is ITEExpression<*> -> visit(expr, ctx)
            is ExpressionWithBoundVariables<*> -> visit(expr, ctx)
            is ExpressionWithLocalVariables<*> -> visit(expr, ctx)
            else -> Exception("missing case for: $expr")
        }
    }
}
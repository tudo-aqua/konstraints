package tools.aqua.constraints.visitors

import tools.aqua.constraints.expressions.*

/**
 * Basis for Type-Based Case Analysis
 */
abstract class VisitByType<in H, out R> {

    // Boolean

    private fun visit(expr : BooleanExpression, ctx : H) : R= when (expr) {
        is And -> visit(expr, ctx)
        is Or -> visit(expr, ctx)
        is Xor -> visit(expr, ctx)
        is Implies -> visit(expr, ctx)
        is Not -> visit(expr, ctx)
        is True -> visit(expr, ctx)
        is False -> visit(expr, ctx)
        is Eq<*> -> visit(expr, ctx)
        is Distinct<*> -> visit(expr, ctx)
        else -> missingCase(expr)
    }

    abstract fun visit(expr:And, ctx : H) : R
    abstract fun visit(expr:Or, ctx : H) : R
    abstract fun visit(expr:Xor, ctx : H) : R
    abstract fun visit(expr:Implies, ctx : H) : R
    abstract fun visit(expr:Not, ctx : H) : R
    abstract fun visit(expr:True, ctx : H) : R
    abstract fun visit(expr:False, ctx : H) : R

    abstract fun <I:Sort> visit(expr:Eq<I>, ctx : H) : R
    abstract fun <I:Sort> visit(expr:Distinct<I>, ctx : H) : R

    // Int

    // Real

    // Bitvector

    private fun <T : BVSort> visit(expr : BVExpression<T>, ctx : H) : R = when (expr) {
        is FPtoSBV<T,*> -> visit(expr, ctx)
        else -> missingCase(expr)
    }

    abstract fun <T:BVSort> visit(expr : FPtoSBV<T,*>, ctx : H) : R

    // FloatingPoint

    private fun <T : FPSort> visit(expr : FPExpression<T>, ctx : H) : R = when (expr) {
        is FPNaN<T> -> visit(expr, ctx)
        is FPLiteral<T> -> visit(expr, ctx)
        else -> missingCase(expr)
    }

    abstract fun <T:FPSort> visit(expr : FPNaN<T>, ctx : H) : R

    abstract fun <T:FPSort> visit(expr : FPLiteral<T>, ctx : H) : R

    private fun <I:FPSort> visit(expr : FPBooleanExpression<I>, ctx : H) : R = when (expr) {
        is FPEq<I> -> visit(expr, ctx)
        else -> missingCase(expr)
    }

    abstract fun <T:FPSort> visit(expr : FPEq<T>, ctx : H) : R

    // String

    // Equality and Uninterpreted Functions

    // Array Theory

    // Top Level

    fun <T:Sort> visit(expr : Expression<T>, ctx : H) : R = when (expr) {
        // variables can be handled uniformly
        is Variable<T> -> visit(expr, ctx)
        // more specific types first
        is Ite -> visit(expr, ctx)
        is FPBooleanExpression<*> -> visit(expr, ctx)
        is BooleanExpression -> visit(expr, ctx)
        is FPExpression<*> -> visit(expr, ctx)
        is BVExpression<*> -> visit(expr, ctx)
        else -> missingCase(expr)
    }

    abstract fun <T:Sort> visit(expr: Variable<T>, ctx : H) : R
    abstract fun <T:Sort> visit(expr:Ite<T>, ctx : H) : R

    // Helper

    private fun <T:Sort> missingCase(expr : Expression<T>) : R {
        throw Exception("missing case for: $expr")
    }

}
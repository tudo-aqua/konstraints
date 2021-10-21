package tools.aqua.constraints.visitors

import tools.aqua.constraints.expressions.Expression
import tools.aqua.constraints.expressions.Variable
import java.util.*


object FreeVariables : VisitByStructure<MutableList<Variable<*>>>() {

    override fun visit (expr : Variable<*>, ctx : MutableList<Variable<*>> ) {
        ctx.add(expr)
    }

    fun of(expr: Expression<*>) : List<Variable<*>> {
        val list = LinkedList<Variable<*>>()
        visit(expr, list)
        return list
    }
}
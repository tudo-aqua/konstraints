package tools.aqua.constraints.analysis;

import tools.aqua.constraints.expressions.Expression
import tools.aqua.constraints.expressions.Sort

interface Simplifier {

    fun <T:Sort> simplify(expr:Expression<T>) : Expression<T>
}

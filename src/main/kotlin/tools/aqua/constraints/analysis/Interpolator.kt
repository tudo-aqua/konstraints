package tools.aqua.constraints.analysis

import tools.aqua.constraints.expressions.BooleanExpression

interface Interpolator {

    fun interpolate(a:BooleanExpression, b:BooleanExpression) : Interpolant

}
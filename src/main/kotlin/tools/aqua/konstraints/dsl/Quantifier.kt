package tools.aqua.konstraints.dsl

import tools.aqua.konstraints.parser.SortedVar
import tools.aqua.konstraints.theories.*
import tools.aqua.konstraints.smt.*
import java.util.*

fun Builder<BoolSort>.exists(vararg sorts : Sort, block: Builder<BoolSort>.(List<Expression<*>>) -> Expression<BoolSort>): ExistsExpression {
    val sortedVars = sorts.map { SortedVar("|$it!${UUID.randomUUID()}|".symbol(), it) }

    children.add(ExistsExpression(sortedVars, Builder<BoolSort>().block(sortedVars.map { it.instance })))

    return children.last() as ExistsExpression
}

fun Builder<BoolSort>.forall(vararg sorts : Sort, block: Builder<BoolSort>.(List<Expression<*>>) -> Expression<BoolSort>): ForallExpression {
    val sortedVars = sorts.map { SortedVar("|$it!${UUID.randomUUID()}|".symbol(), it) }

    children.add(ForallExpression(sortedVars, Builder<BoolSort>().block(sortedVars.map { it.instance })))

    return children.last() as ForallExpression
}
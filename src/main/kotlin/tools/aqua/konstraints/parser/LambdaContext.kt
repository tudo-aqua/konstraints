package tools.aqua.konstraints.parser

import tools.aqua.konstraints.Expression
import tools.aqua.konstraints.Sort

object LambdaContext {
    val funs : MutableMap<String, ((List<Expression<*>>) -> Expression<*>)> = mutableMapOf()
    val sorts : MutableMap<String, Sort> = mutableMapOf()
}

interface Context
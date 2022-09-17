package tools.aqua.constraints.solver

import tools.aqua.constraints.expressions.Expression
import tools.aqua.constraints.expressions.Sort
import tools.aqua.constraints.expressions.Variable

/**
 * Basic interface for solver results
 */
interface SolverResult

interface SatResult : SolverResult

object Sat : SatResult {
    override fun toString() = "SATISFIABLE"
}

object Unsat : SatResult {
    override fun toString() = "UNSATISFIABLE"
}

object DontKnow : SatResult {
    override fun toString(): String {
        TODO("what is the SMTLib value of dont know?")
    }
}

/**
 * Values returned by (get-values)
 */
interface Values : Map<Variable<*>, Expression<*>>, SolverResult

/**
 * Function definitions are the basic parts of models
 */
data class FunctionDefinition(val name:String, val params:List<Variable<*>>, val type: Sort, val value:Expression<*>) {
    private val keyword = "define-fun"

    override fun toString(): String = "($keyword $name (${params.map{ "(${it.symbol} ${it.type})" }.joinToString(" ")}) $type $value)"
}

/**
 * Model returned by (get-model)
 */
data class Model(val elements:Map<String,FunctionDefinition>) : SolverResult {

    override fun toString(): String = "(${elements.values.joinToString(" ")})"
}
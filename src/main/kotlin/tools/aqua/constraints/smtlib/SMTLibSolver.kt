package tools.aqua.constraints.smtlib

import tools.aqua.constraints.expressions.BooleanExpression
import tools.aqua.constraints.expressions.Sort
import tools.aqua.constraints.expressions.Variable
import tools.aqua.constraints.solver.Model
import tools.aqua.constraints.solver.Values
import tools.aqua.constraints.solver.SatResult

/**
 * Interface for solvers provide SMTLib commands as API
 */
interface SMTLibSolver {

    fun setLogic(logic: Logic)

    fun setOption(option:String, value: String)

    fun declareFunction(name:String, argTypes:List<Sort>, type: Sort)

    fun assert(expr:BooleanExpression)

    fun checkSat() : SatResult

    fun getModel() : Model

    fun getValues(vars:List<Variable<*>>) : Values {
        error("get-values not supported.")
    }

    fun push(d:Int)

    fun pop(d:Int)
}
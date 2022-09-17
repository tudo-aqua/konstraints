package tools.aqua.constraints.smtlib

import tools.aqua.constraints.expressions.BooleanExpression
import tools.aqua.constraints.expressions.Sort
import tools.aqua.constraints.expressions.Variable
import tools.aqua.constraints.solver.SolverResult

/**
 * SMT Logics
 *
 * cf. https://smtlib.cs.uiowa.edu/logics.shtml
 */
enum class Logic {
    AUFLIA, //Closed formulas over the theory of linear integer arithmetic and arrays extended with free sort and function symbols but restricted to arrays with integer indices and values.
    AUFLIRA, //Closed linear formulas with free sort and function symbols over one- and two-dimentional arrays of integer index and real value.
    AUFNIRA, //Closed formulas with free function and predicate symbols over a theory of arrays of arrays of integer index and real value.
    LIA, //Closed linear formulas over linear integer arithmetic.
    LRA, //Closed linear formulas in linear real arithmetic.
    QF_ABV, //Closed quantifier-free formulas over the theory of bitvectors and bitvector arrays.
    QF_AUFBV, //Closed quantifier-free formulas over the theory of bitvectors and bitvector arrays extended with free sort and function symbols.
    QF_AUFLIA, //Closed quantifier-free linear formulas over the theory of integer arrays extended with free sort and function symbols.
    QF_AX, //Closed quantifier-free formulas over the theory of arrays with extensionality.
    QF_BV, //Closed quantifier-free formulas over the theory of fixed-size bitvectors.
    QF_IDL, //Difference Logic over the integers. In essence, Boolean combinations of inequations of the form x - y < b where x and y are integer variables and b is an integer constant.
    QF_LIA, //Unquantified linear integer arithmetic. In essence, Boolean combinations of inequations between linear polynomials over integer variables.
    QF_LRA, //Unquantified linear real arithmetic. In essence, Boolean combinations of inequations between linear polynomials over real variables.
    QF_NIA, //Quantifier-free integer arithmetic.
    QF_NRA, //Quantifier-free real arithmetic.
    QF_RDL, //Difference Logic over the reals. In essence, Boolean combinations of inequations of the form x - y < b where x and y are real variables and b is a rational constant.
    QF_UF, //Unquantified formulas built over a signature of uninterpreted (i.e., free) sort and function symbols.
    QF_UFBV, //Unquantified formulas over bitvectors with uninterpreted sort function and symbols.
    QF_UFIDL, //Difference Logic over the integers (in essence) but with uninterpreted sort and function symbols.
    QF_UFLIA, //Unquantified linear integer arithmetic with uninterpreted sort and function symbols.
    QF_UFLRA, //Unquantified linear real arithmetic with uninterpreted sort and function symbols.
    QF_UFNRA, //Unquantified non-linear real arithmetic with uninterpreted sort and function symbols.
    UFLRA, //Linear real arithmetic with uninterpreted sort and function symbols.
    UFNIA //Non-linear integer arithmetic with uninterpreted sort and function symbols.
}

/**
 * marker interface for SMTLib statements
 */
abstract class SMTLibStatement(val keyword:String) {

    abstract fun execute(target: SMTLibSolver) : Any

    override fun toString() = "($keyword)"
}

/**
 * SMTLib script
 */
data class SMTLibScript(val statements: List<SMTLibStatement>) {

    fun execute(target: SMTLibSolver) : List<SolverResult> =
        statements.map { it.execute(target) }.filterIsInstance<SolverResult>().toList()

    override fun toString(): String = statements.joinToString("\n")
}

/**
 * SMTLib command (declare-fun ...)
 */
data class FunctionDeclaration(val name:String, val argTypes:List<Sort>, val type:Sort) :
    SMTLibStatement("declare-fun") {

    override fun execute(target: SMTLibSolver) {
        target.declareFunction(name, argTypes, type)
    }

    override fun toString(): String = "($keyword $name (${argTypes.joinToString(" ")}) $type)"
}

/**
 * SMTLib command (assert ...)
 */
data class Assert(val assertion:BooleanExpression) :
    SMTLibStatement("assert") {

    override fun execute(target: SMTLibSolver) {
        target.assert(assertion)
    }

    override fun toString(): String = "($keyword $assertion)"
}

/**
 * SMTLib command (set-option)
 */
data class SetOption(val option:String, val value:String) :
    SMTLibStatement("set-option") {

    override fun execute(target: SMTLibSolver) {
        target.setOption(option, value)
    }

    override fun toString(): String = "($keyword $option $value)"
}

/**
 * SMTLib command (set-logic)
 */
data class SetLogic(val logic:Logic) :
    SMTLibStatement("set-logic") {

    override fun execute(target: SMTLibSolver) {
        target.setLogic(logic)
    }

    override fun toString(): String = "($keyword $logic)"
}

/**
 * SMTLib command (get-value)
 */
data class GetValue(val vars: List<Variable<*>>) :
    SMTLibStatement("get-value") {

    override fun execute(target: SMTLibSolver) = target.getValues(vars)

    override fun toString(): String = "($keyword (${vars.joinToString(" ")}))"
}

/**
 * SMTLib command (pop i)
 */
data class Push(val d:Int) :
    SMTLibStatement("push") {

    override fun execute(target: SMTLibSolver) {
        target.push(d)
    }

    override fun toString(): String = "($keyword $d)"
}

/**
 * SMTLib command (pop i)
 */
data class Pop(val d:Int) :
    SMTLibStatement("pop") {

    override fun execute(target: SMTLibSolver) {
        target.pop(d)
    }

    override fun toString(): String = "($keyword $d)"
}

/**
 * SMTLib command (check-sat)
 */
object CheckSat : SMTLibStatement("check-sat") {

    override fun execute(target: SMTLibSolver) = target.checkSat()
}

/**
 * SMTLib command (get-model)
 */
object GetModel : SMTLibStatement("get-model") {

    override fun execute(target: SMTLibSolver) = target.getModel()
}

/**
 * SMTLib command (exit)
 */
object Exit : SMTLibStatement("exit") {
    override fun execute(target: SMTLibSolver) {
        // do nothing?
    }
}

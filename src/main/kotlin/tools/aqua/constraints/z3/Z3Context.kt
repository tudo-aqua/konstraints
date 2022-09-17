package tools.aqua.constraints.z3

import com.microsoft.z3.Context
import com.microsoft.z3.Expr
import com.microsoft.z3.FuncDecl
import tools.aqua.constraints.expressions.Sort

class Z3Context {

    internal val context = Context()
    internal var solver = context.mkSolver()
    internal val params = context.mkParams()

    internal val constants = HashMap<String, Expr<*>>()
    internal val functions = HashMap<String, FuncDecl<*>>()
    internal val sorts = HashMap<Sort, com.microsoft.z3.Sort>()
}
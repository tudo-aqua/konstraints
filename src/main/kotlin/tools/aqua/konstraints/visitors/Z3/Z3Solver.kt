package tools.aqua.konstraints.visitors.Z3

import com.microsoft.z3.*
import com.microsoft.z3.BoolSort
import com.microsoft.z3.Sort
import tools.aqua.konstraints.*
import tools.aqua.konstraints.visitors.CommandVisitor

class Z3Solver : CommandVisitor<Unit> {
    val context = Context()
    val solver = context.mkSolver()
    val expressionGenerator = Z3ExpressionGenerator(this)

    internal val constants = HashMap<String, Expr<*>>()
    internal val functions = HashMap<String, FuncDecl<*>>()
    internal val sorts = HashMap<tools.aqua.konstraints.Sort, com.microsoft.z3.Sort>()

    override fun visit(assert: Assert) {
        solver.add(expressionGenerator.visit(assert.expression) as Expr<BoolSort>)
    }

    override fun visit(declareConst: DeclareConst) {
        TODO("Not yet implemented")
    }

    override fun visit(declareFun: DeclareFun) {
        if (declareFun.parameters.isNotEmpty()) {
            functions[declareFun.name.toString()]?.let {
                error("function already declared.")
            }
            functions[declareFun.name.toString()] = context.mkFuncDecl(declareFun.name.toSMTString(),
                declareFun.parameters.map{ getOrCreateSort(it)}.toTypedArray(),
                getOrCreateSort(declareFun.sort))
        }
        else {
            constants[declareFun.name.toString()]?.let {
                error("constant already declared.")
            }
            constants[declareFun.name.toString()] = when (declareFun.sort) {
                is tools.aqua.konstraints.BoolSort -> context.mkBoolConst(declareFun.name.toSMTString())
                is BVSort -> context.mkBVConst(declareFun.name.toSMTString(), declareFun.sort.bits)
                else -> error("Sort ${declareFun.sort} not supported.")
            }
        }
    }

    private fun getOrCreateSort(sort: tools.aqua.konstraints.Sort): Sort {
        sorts[sort]?.let { return sorts[sort]!! }
        sorts[sort] = when (sort) {
            is BoolSort -> context.mkBoolSort()
            is IntSort -> context.mkIntSort()
            else -> error("unsupported sort $sort")
        }
        return sorts[sort]!!
    }

    override fun visit(checkSat: CheckSat) {
        return when (solver.check()) {
            Status.UNSATISFIABLE -> println("Unsat")
            Status.UNKNOWN -> println("DontKnow")
            Status.SATISFIABLE -> println("Sat")
        }
    }

}
package tools.aqua.constraints.z3

import com.github.h0tk3y.betterParse.grammar.parseToEnd
import com.microsoft.z3.Expr
import com.microsoft.z3.Status
import tools.aqua.constraints.expressions.*
import tools.aqua.constraints.smtlib.*
import tools.aqua.constraints.solver.*

class Z3SMTLibSolver : SMTLibSolver {

    private val z3Ctx = Z3Context()

    override fun setLogic(logic: Logic) {
        z3Ctx.solver = z3Ctx.context.mkSolver(logic.toString())
        z3Ctx.solver.setParameters(z3Ctx.params)
    }

    override fun setOption(option: String, value: String) {
        println("options ignored for now.")
        // z3Ctx.params.add(option, value)
       //  z3Ctx.solver.setParameters(z3Ctx.params)
    }

    override fun declareFunction(name:String, argTypes:List<Sort>, type: Sort) {
        if (argTypes.isNotEmpty()) {
            z3Ctx.functions[name]?.let {
                error("function already declared.")
            }
            z3Ctx.functions[name] =  z3Ctx.context.mkFuncDecl(name,
                argTypes.map{ getOrCreateSort(it, z3Ctx )}.toTypedArray(),
                getOrCreateSort(type, z3Ctx))
        }
        else {
            z3Ctx.constants[name]?.let {
                error("constant already declared.")
            }
            z3Ctx.constants[name] = when (type) {
                is BoolSort -> z3Ctx.context.mkBoolConst(name)
                is IntSort -> z3Ctx.context.mkIntConst(name)
                else -> error("Sort $type not supported.")
            }
        }
    }


    private fun getOrCreateSort(sort: Sort, z3Ctx: Z3Context): com.microsoft.z3.Sort {
        z3Ctx.sorts[sort]?.let { return z3Ctx.sorts[sort]!! }
        z3Ctx.sorts[sort] = when (sort) {
            is BoolSort -> z3Ctx.context.mkBoolSort()
            is IntSort -> z3Ctx.context.mkIntSort()
            is Float32 -> z3Ctx.context.mkFPSort32()
            is FPSort -> z3Ctx.context.mkFPSort(sort.eBits, sort.mBits)
            else -> error("unsupported sort $sort")
        }
        return z3Ctx.sorts[sort]!!
    }



    override fun assert(expr: BooleanExpression) {
        z3Ctx.solver.add( Z3ExpressionGenerator().visit(expr, z3Ctx ) as Expr<com.microsoft.z3.BoolSort> )
    }

    override fun checkSat(): SatResult {
        return when (z3Ctx.solver.check()) {
            Status.UNSATISFIABLE -> Unsat
            Status.UNKNOWN -> DontKnow
            Status.SATISFIABLE -> Sat
        }
    }

    override fun getModel(): Model {
        try {
            println(z3Ctx.solver.model.toString())
            return SMTLibModelParser().parseToEnd(z3Ctx.solver.model.toString())
        }
        catch (e:com.microsoft.z3.Z3Exception) {
            error( e.message ?: "z3 error w/o message" )
        }
    }

    override fun push(d: Int) {
        for (i in 1..d) {
            z3Ctx.solver.push()
        }
    }

    override fun pop(d: Int) {
        z3Ctx.solver.pop(d)
    }

}
package tools.aqua.konstraints.visitors

import tools.aqua.konstraints.*

interface CommandVisitor<T> {
    fun visit(command: Command) : T = when(command) {
        is Assert -> visit(command)
        is DeclareConst -> visit(command)
        is DeclareFun -> visit(command)
        is CheckSat -> visit(command)
        /* this is only needed because SimpleCommand exists, but I think it is not really necessary */
        else -> throw Exception()
    }

    fun visit(assert: Assert) : T

    fun visit(declareConst: DeclareConst) : T

    fun visit(declareFun: DeclareFun) : T

    fun visit(checkSat : CheckSat) : T
}
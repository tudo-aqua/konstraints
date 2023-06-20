
class SMTProgram(commands: List<Command>) {
    // checkWellSorted, etc...
}


interface Command {
    val command : String
}

abstract class SimpleCommand(override val command: String) : Command {
    override fun toString(): String ="($command)"
}

object CheckSat : SimpleCommand("check-sat")

data class Assert(val expression : Expression<BoolSort>) : SimpleCommand("assert $expression") {
    override fun toString(): String = super.toString()
}

data class DeclareConst(var expression : Expression<*>) :
    SimpleCommand("declare-const $expression ${expression.sort}"){
    override fun toString(): String ="($command)"
}

// DeclareConst(expr, expr.sort)
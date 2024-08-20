package tools.aqua.konstraints.dsl

import com.microsoft.z3.Expr
import tools.aqua.konstraints.parser.Context
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.theories.And
import tools.aqua.konstraints.theories.BoolSort
import tools.aqua.konstraints.theories.Or
import kotlin.reflect.KProperty

@DslMarker
annotation class SMTDSL

@SMTDSL
class AndBuilder(val conjuncts: MutableList<Expression<BoolSort>>) {
    constructor(vararg conjuncts: Expression<BoolSort>): this(conjuncts.toMutableList())

    infix fun and(other: Expression<BoolSort>): AndBuilder {
        conjuncts.add(other)
        return this
    }

    fun finalize() = And(conjuncts.toList())
}

@SMTDSL
class OrBuilder(val disjuncts: MutableList<Expression<BoolSort>>) {
    constructor(vararg conjuncts: Expression<BoolSort>): this(conjuncts.toMutableList())

    infix fun or(other: Expression<BoolSort>): OrBuilder {
        disjuncts.add(other)
        return this
    }

    fun finalize() = Or(disjuncts.toList())
}

@SMTDSL
class AssertBuilder {
    var expr: Expression<BoolSort>? = null

    operator fun Expression<BoolSort>.unaryPlus() {
        require(expr == null)

        expr = this
    }

    operator fun AndBuilder.unaryPlus() {
        require(this@AssertBuilder.expr == null)

        this@AssertBuilder.expr = this.finalize()
    }

    operator fun OrBuilder.unaryPlus() {
        require(this@AssertBuilder.expr == null)

        this@AssertBuilder.expr = this.finalize()
    }

    fun finalize() = if (expr != null) Assert(expr!!) else throw RuntimeException()
}

@SMTDSL
class SMTProgramBuilder {
    private val commands = mutableListOf<Command>()
    private val context = Context(QF_UF)

    fun assert(init: AssertBuilder.() -> Unit) {
        val cmd = AssertBuilder()
        cmd.init()

        commands.add(cmd.finalize())
    }

    fun <T: Sort> declareConst(name: String, sort: T): Expression<T>  {
        context.registerFunction(name, emptyList(), sort)
        commands.add(DeclareConst(name.symbol(), sort))

        return UserDeclaredExpression(name.symbol(), sort)
    }

    fun finalize() = DefaultSMTProgram(commands.also { it.add(CheckSat) }.toList(), context)
}

fun smt(init: SMTProgramBuilder.() -> Unit): SMTProgram {
    val program = SMTProgramBuilder()
    program.init()

    return program.finalize()
}


infix fun Expression<BoolSort>.and(other: Expression<BoolSort>): AndBuilder {
    return AndBuilder(this, other)
}

infix fun Expression<BoolSort>.or(other: Expression<BoolSort>): OrBuilder {
    return OrBuilder(this, other)
}

class Const<T: Sort>(val sort: T) {
    private var expr: Expression<T>? = null

    operator fun getValue(ref: Any?, property: KProperty<*>): Expression<T> {
        if (expr == null)
            expr = UserDeclaredExpression(property.name.symbol(), sort)

        return expr!!
    }
}
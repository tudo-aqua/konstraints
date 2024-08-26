package tools.aqua.konstraints.dsl

import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.smt.Ite
import tools.aqua.konstraints.smt.Sort
import tools.aqua.konstraints.theories.BoolSort

@SMTDSL
class ITE1(val statement: Expression<BoolSort>) {
    infix fun<T : Sort> then(expr: Builder<T>.() -> Expression<T>): ITE2<T> =
        ITE2(statement, Builder<T>().expr())
}

class ITE2<T : Sort>(val statement: Expression<BoolSort>, val then: Expression<T>) {
    infix fun otherwise(expr: Builder<T>.() -> Expression<T>): Ite<T> =
        Ite(statement, then, Builder<T>().expr())
}

fun ite(init: Builder<BoolSort>.() -> Expression<BoolSort>): ITE1 =
    ITE1(Builder<BoolSort>().init())
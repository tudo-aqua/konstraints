package tools.aqua.konstraints.dsl

import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.theories.*

infix fun Expression<BVSort>.bvand(other: Expression<BVSort>) =
    if (this is BVAnd) {
        BVAnd(*this.children.toTypedArray(), other)
    } else {
        BVAnd(this, other)
    }

infix fun Expression<BVSort>.bvor(other: Expression<BVSort>) =
    if (this is BVOr) {
        BVOr(*this.children.toTypedArray(), other)
    } else {
        BVOr(this, other)
    }

infix fun Expression<BVSort>.bvadd(other: Expression<BVSort>) =
    if (this is BVAdd) {
        BVAdd(*this.children.toTypedArray(), other)
    } else {
        BVAdd(this, other)
    }

infix fun Expression<BVSort>.bvmul(other: Expression<BVSort>) =
    if (this is BVMul) {
        BVMul(*this.children.toTypedArray(), other)
    } else {
        BVMul(this, other)
    }

infix fun Expression<BVSort>.concat(other: Expression<BVSort>) = BVConcat(this, other)
infix fun Expression<BVSort>.bvudiv(denominator: Expression<BVSort>) = BVUDiv(this, denominator)
infix fun Expression<BVSort>.bvurem(denominator: Expression<BVSort>) = BVURem(this, denominator)
infix fun Expression<BVSort>.bvshl(distance: Expression<BVSort>) = BVShl(this, distance)
infix fun Expression<BVSort>.bvlshr(distance: Expression<BVSort>) = BVLShr(this, distance)
infix fun Expression<BVSort>.bvult(distance: Expression<BVSort>) = BVUlt(this, distance)

fun Builder<BVSort>.extract(i : Int, j: Int, block: Builder<BVSort>.() -> Expression<BVSort>): BVExtract {
    this.children.add(BVExtract(i, j, Builder<BVSort>().block()))

    return this.children.last() as BVExtract
}

private fun Builder<BVSort>.makeUnaryOperation(block: Builder<BVSort>.() -> Expression<BVSort>, operation: (Expression<BVSort>) -> Expression<BVSort>): Expression<BVSort> {
    this.children.add(operation(Builder<BVSort>().block()))

    return this.children.last()
}

fun Builder<BVSort>.bvnot(block: Builder<BVSort>.() -> Expression<BVSort>) = this.makeUnaryOperation(block, ::BVNot)
fun Builder<BVSort>.bvneg(block: Builder<BVSort>.() -> Expression<BVSort>) = this.makeUnaryOperation(block, ::BVNeg)

private fun Builder<BVSort>.makeBinaryOperation(init: Builder<BVSort>.() -> Unit, operation: (Expression<BVSort>, Expression<BVSort>) -> Expression<BVSort>): Expression<BVSort> {
    val builder = Builder<BVSort>()
    builder.init()

    require(builder.children.size == 2)

    this.children.add(operation(builder.children[0], builder.children[1]))

    return this.children.last()
}

fun Builder<BVSort>.concat(init: Builder<BVSort>.() -> Unit) = this.makeBinaryOperation(init, ::BVConcat)
fun Builder<BVSort>.bvurem(init: Builder<BVSort>.() -> Unit) = this.makeBinaryOperation(init, ::BVURem)
fun Builder<BVSort>.bvudiv(init: Builder<BVSort>.() -> Unit) = this.makeBinaryOperation(init, ::BVUDiv)
fun Builder<BVSort>.bvshl(init: Builder<BVSort>.() -> Unit) = this.makeBinaryOperation(init, ::BVShl)
fun Builder<BVSort>.bvlshr(init: Builder<BVSort>.() -> Unit) = this.makeBinaryOperation(init, ::BVLShr)

private fun Builder<BVSort>.makeOperation(init: Builder<BVSort>.() -> Unit, operation: (List<Expression<BVSort>>) -> Expression<BVSort>): Expression<BVSort> {
    val builder = Builder<BVSort>()
    builder.init()

    this.children.add(operation(builder.children))

    return this.children.last()
}

fun Builder<BVSort>.bvand(init: Builder<BVSort>.() -> Unit) = this.makeOperation(init, ::BVAnd)
fun Builder<BVSort>.bvor(init: Builder<BVSort>.() -> Unit) = this.makeOperation(init, ::BVOr)
fun Builder<BVSort>.bvadd(init: Builder<BVSort>.() -> Unit) = this.makeOperation(init, ::BVAdd)
fun Builder<BVSort>.bvmul(init: Builder<BVSort>.() -> Unit) = this.makeOperation(init, ::BVMul)
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

/*
 * Bitvector infix operations
 */
infix fun Expression<BVSort>.concat(other: Expression<BVSort>) = BVConcat(this, other)
infix fun Expression<BVSort>.bvudiv(denominator: Expression<BVSort>) = BVUDiv(this, denominator)
infix fun Expression<BVSort>.bvurem(denominator: Expression<BVSort>) = BVURem(this, denominator)
infix fun Expression<BVSort>.bvshl(distance: Expression<BVSort>) = BVShl(this, distance)
infix fun Expression<BVSort>.bvlshr(distance: Expression<BVSort>) = BVLShr(this, distance)
infix fun Expression<BVSort>.bvnand(rhs: Expression<BVSort>) = BVNAnd(this, rhs)
infix fun Expression<BVSort>.bvnor(rhs: Expression<BVSort>) = BVNOr(this, rhs)
infix fun Expression<BVSort>.bvxor(rhs: Expression<BVSort>) =
    if (this is BVXOr) {
        BVXOr(*this.children.toTypedArray(), rhs)
    } else {
        BVXOr(this, rhs)
    }
infix fun Expression<BVSort>.bvxnor(rhs: Expression<BVSort>) = BVXNOr(this, rhs)
infix fun Expression<BVSort>.bvcomp(rhs: Expression<BVSort>) = BVComp(this, rhs)
infix fun Expression<BVSort>.bvsub(rhs: Expression<BVSort>) = BVSub(this, rhs)
infix fun Expression<BVSort>.bvsdiv(denominator: Expression<BVSort>) = BVSDiv(this, denominator)
infix fun Expression<BVSort>.bvsrem(denominator: Expression<BVSort>) = BVSRem(this, denominator)
infix fun Expression<BVSort>.bvsmod(rhs: Expression<BVSort>) = BVSMod(this, rhs)
infix fun Expression<BVSort>.bvashr(distance: Expression<BVSort>) = BVAShr(this, distance)

/*
 * bitvector comparison operators
 */

infix fun Expression<BVSort>.bvult(distance: Expression<BVSort>) = BVUlt(this, distance)
infix fun Expression<BVSort>.bvule(distance: Expression<BVSort>) = BVULe(this, distance)
infix fun Expression<BVSort>.bvugt(distance: Expression<BVSort>) = BVUGt(this, distance)
infix fun Expression<BVSort>.bvuge(distance: Expression<BVSort>) = BVUGe(this, distance)
infix fun Expression<BVSort>.bvslt(distance: Expression<BVSort>) = BVSLt(this, distance)
infix fun Expression<BVSort>.bvsle(distance: Expression<BVSort>) = BVSLe(this, distance)
infix fun Expression<BVSort>.bvsgt(distance: Expression<BVSort>) = BVSGt(this, distance)
infix fun Expression<BVSort>.bvsge(distance: Expression<BVSort>) = BVSGe(this, distance)

/*
 * parameterized bitvector operations
 */

private fun Builder<BVSort>.makeUnaryParameterizedOperation(i: Int, block: Builder<BVSort>.() -> Expression<BVSort>, operation: (Int, Expression<BVSort>) -> Expression<BVSort>): Expression<BVSort> {
    this.children.add(operation(i, Builder<BVSort>().block()))

    return this.children.last()
}

fun Builder<BVSort>.repeat(i: Int, block: Builder<BVSort>.() -> Expression<BVSort>) = this.makeUnaryParameterizedOperation(i, block, ::Repeat)
fun Builder<BVSort>.zeroExtend(i: Int, block: Builder<BVSort>.() -> Expression<BVSort>) = this.makeUnaryParameterizedOperation(i, block, ::ZeroExtend)
fun Builder<BVSort>.signExtend(i: Int, block: Builder<BVSort>.() -> Expression<BVSort>) = this.makeUnaryParameterizedOperation(i, block, ::SignExtend)
fun Builder<BVSort>.rotateLeft(i: Int, block: Builder<BVSort>.() -> Expression<BVSort>) = this.makeUnaryParameterizedOperation(i, block, ::RotateLeft)
fun Builder<BVSort>.rotateRight(i: Int, block: Builder<BVSort>.() -> Expression<BVSort>) = this.makeUnaryParameterizedOperation(i, block, ::RotateRight)

fun Builder<BVSort>.extract(i : Int, j: Int, block: Builder<BVSort>.() -> Expression<BVSort>): BVExtract {
    this.children.add(BVExtract(i, j, Builder<BVSort>().block()))

    return this.children.last() as BVExtract
}

/*
 * Unary bitvector operations
 */

private fun Builder<BVSort>.makeUnaryOperation(block: Builder<BVSort>.() -> Expression<BVSort>, operation: (Expression<BVSort>) -> Expression<BVSort>): Expression<BVSort> {
    this.children.add(operation(Builder<BVSort>().block()))

    return this.children.last()
}

fun Builder<BVSort>.bvnot(block: Builder<BVSort>.() -> Expression<BVSort>) = this.makeUnaryOperation(block, ::BVNot)
fun Builder<BVSort>.bvneg(block: Builder<BVSort>.() -> Expression<BVSort>) = this.makeUnaryOperation(block, ::BVNeg)

/*
 * left-associative bitvector operations
 */

private fun Builder<BVSort>.makeOperation(init: Builder<BVSort>.() -> Unit, operation: (List<Expression<BVSort>>) -> Expression<BVSort>): Expression<BVSort> {
    val builder = Builder<BVSort>()
    builder.init()

    require(builder.children.isNotEmpty())

    if(builder.children.size == 1) {
        this.children.add(builder.children.single())
    } else {
        this.children.add(operation(builder.children))
    }

    return this.children.last()
}

fun Builder<BVSort>.bvand(init: Builder<BVSort>.() -> Unit) = this.makeOperation(init, ::BVAnd)
fun Builder<BVSort>.bvor(init: Builder<BVSort>.() -> Unit) = this.makeOperation(init, ::BVOr)
fun Builder<BVSort>.bvadd(init: Builder<BVSort>.() -> Unit) = this.makeOperation(init, ::BVAdd)
fun Builder<BVSort>.bvmul(init: Builder<BVSort>.() -> Unit) = this.makeOperation(init, ::BVMul)
fun Builder<BVSort>.bvxor(init: Builder<BVSort>.() -> Unit) = this.makeOperation(init, ::BVXOr)
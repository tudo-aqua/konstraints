/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2024 The Konstraints Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package tools.aqua.konstraints.dsl

import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.theories.*

infix fun Expression<BVSort>.bvand(other: Expression<BVSort>) =
    if (this is BVAnd) {
      BVAnd(this.children+other)
    } else {
      BVAnd(this, other)
    }

infix fun Expression<BVSort>.bvand(other: () -> Expression<BVSort>): BVAnd = this bvand other()

infix fun (() -> Expression<BVSort>).bvand(other: Expression<BVSort>): BVAnd = this() bvand other

infix fun (() -> Expression<BVSort>).bvand(other: () -> Expression<BVSort>): BVAnd =
    this() bvand other()

infix fun Expression<BVSort>.bvor(other: Expression<BVSort>) =
    if (this is BVOr) {
      BVOr(this.children+other)
    } else {
      BVOr(this, other)
    }

infix fun Expression<BVSort>.bvor(other: () -> Expression<BVSort>): BVOr = this bvor other()

infix fun (() -> Expression<BVSort>).bvor(other: Expression<BVSort>): BVOr = this() bvor other

infix fun (() -> Expression<BVSort>).bvor(other: () -> Expression<BVSort>): BVOr =
    this() bvor other()

infix fun Expression<BVSort>.bvadd(other: Expression<BVSort>) =
    if (this is BVAdd) {
      BVAdd(this.children+other)
    } else {
      BVAdd(this, other)
    }

infix fun Expression<BVSort>.bvadd(other: () -> Expression<BVSort>): BVAdd = this bvadd other()

infix fun (() -> Expression<BVSort>).bvadd(other: Expression<BVSort>): BVAdd = this() bvadd other

infix fun (() -> Expression<BVSort>).bvadd(other: () -> Expression<BVSort>): BVAdd =
    this() bvadd other()

infix fun Expression<BVSort>.bvmul(other: Expression<BVSort>) =
    if (this is BVMul) {
      BVMul(this.children + other)
    } else {
      BVMul(this, other)
    }

infix fun Expression<BVSort>.bvmul(other: () -> Expression<BVSort>): BVMul = this bvmul other()

infix fun (() -> Expression<BVSort>).bvmul(other: Expression<BVSort>): BVMul = this() bvmul other

infix fun (() -> Expression<BVSort>).bvmul(other: () -> Expression<BVSort>): BVMul =
    this() bvmul other()

/*
 * Bitvector infix operations
 */
infix fun Expression<BVSort>.concat(other: Expression<BVSort>) = BVConcat(this, other)

infix fun Expression<BVSort>.concat(other: () -> Expression<BVSort>) = BVConcat(this, other())

infix fun (() -> Expression<BVSort>).concat(other: Expression<BVSort>) = BVConcat(this(), other)

infix fun (() -> Expression<BVSort>).concat(other: () -> Expression<BVSort>) =
    BVConcat(this(), other())

infix fun Expression<BVSort>.bvudiv(denominator: Expression<BVSort>) = BVUDiv(this, denominator)

infix fun Expression<BVSort>.bvudiv(other: () -> Expression<BVSort>) = BVUDiv(this, other())

infix fun (() -> Expression<BVSort>).bvudiv(other: Expression<BVSort>) = BVUDiv(this(), other)

infix fun (() -> Expression<BVSort>).bvudiv(other: () -> Expression<BVSort>) =
    BVUDiv(this(), other())

infix fun Expression<BVSort>.bvurem(denominator: Expression<BVSort>) = BVURem(this, denominator)

infix fun Expression<BVSort>.bvurem(other: () -> Expression<BVSort>) = BVURem(this, other())

infix fun (() -> Expression<BVSort>).bvurem(other: Expression<BVSort>) = BVURem(this(), other)

infix fun (() -> Expression<BVSort>).bvurem(other: () -> Expression<BVSort>) =
    BVURem(this(), other())

infix fun Expression<BVSort>.bvshl(distance: Expression<BVSort>) = BVShl(this, distance)

infix fun Expression<BVSort>.bvshl(other: () -> Expression<BVSort>) = BVShl(this, other())

infix fun (() -> Expression<BVSort>).bvshl(other: Expression<BVSort>) = BVShl(this(), other)

infix fun (() -> Expression<BVSort>).bvshl(other: () -> Expression<BVSort>) = BVShl(this(), other())

infix fun Expression<BVSort>.bvlshr(distance: Expression<BVSort>) = BVLShr(this, distance)

infix fun Expression<BVSort>.bvlshr(other: () -> Expression<BVSort>) = BVLShr(this, other())

infix fun (() -> Expression<BVSort>).bvlshr(other: Expression<BVSort>) = BVLShr(this(), other)

infix fun (() -> Expression<BVSort>).bvlshr(other: () -> Expression<BVSort>) =
    BVLShr(this(), other())

infix fun Expression<BVSort>.bvnand(rhs: Expression<BVSort>) = BVNAnd(this, rhs)

infix fun Expression<BVSort>.bvnand(other: () -> Expression<BVSort>) = BVNAnd(this, other())

infix fun (() -> Expression<BVSort>).bvnand(other: Expression<BVSort>) = BVNAnd(this(), other)

infix fun (() -> Expression<BVSort>).bvnand(other: () -> Expression<BVSort>) =
    BVNAnd(this(), other())

infix fun Expression<BVSort>.bvnor(rhs: Expression<BVSort>) = BVNOr(this, rhs)

infix fun Expression<BVSort>.bvnor(other: () -> Expression<BVSort>) = BVNOr(this, other())

infix fun (() -> Expression<BVSort>).bvnor(other: Expression<BVSort>) = BVNOr(this(), other)

infix fun (() -> Expression<BVSort>).bvnor(other: () -> Expression<BVSort>) = BVNOr(this(), other())

infix fun Expression<BVSort>.bvxor(rhs: Expression<BVSort>) =
    if (this is BVXOr) {
      BVXOr(this.children+rhs)
    } else {
      BVXOr(this, rhs)
    }

infix fun Expression<BVSort>.bvxor(other: () -> Expression<BVSort>) = BVXOr(this, other())

infix fun (() -> Expression<BVSort>).bvxor(other: Expression<BVSort>) = BVXOr(this(), other)

infix fun (() -> Expression<BVSort>).bvxor(other: () -> Expression<BVSort>) = BVXOr(this(), other())

infix fun Expression<BVSort>.bvxnor(rhs: Expression<BVSort>) = BVXNOr(this, rhs)

infix fun Expression<BVSort>.bvxnor(other: () -> Expression<BVSort>) = BVXNOr(this, other())

infix fun (() -> Expression<BVSort>).bvxnor(other: Expression<BVSort>) = BVXNOr(this(), other)

infix fun (() -> Expression<BVSort>).bvxnor(other: () -> Expression<BVSort>) =
    BVXNOr(this(), other())

infix fun Expression<BVSort>.bvcomp(rhs: Expression<BVSort>) = BVComp(this, rhs)

infix fun Expression<BVSort>.bvcomp(other: () -> Expression<BVSort>) = BVComp(this, other())

infix fun (() -> Expression<BVSort>).bvcomp(other: Expression<BVSort>) = BVComp(this(), other)

infix fun (() -> Expression<BVSort>).bvcomp(other: () -> Expression<BVSort>) =
    BVComp(this(), other())

infix fun Expression<BVSort>.bvsub(rhs: Expression<BVSort>) = BVSub(this, rhs)

infix fun Expression<BVSort>.bvsub(other: () -> Expression<BVSort>) = BVSub(this, other())

infix fun (() -> Expression<BVSort>).bvsub(other: Expression<BVSort>) = BVSub(this(), other)

infix fun (() -> Expression<BVSort>).bvsub(other: () -> Expression<BVSort>) = BVSub(this(), other())

infix fun Expression<BVSort>.bvsdiv(denominator: Expression<BVSort>) = BVSDiv(this, denominator)

infix fun Expression<BVSort>.bvsdiv(other: () -> Expression<BVSort>) = BVSDiv(this, other())

infix fun (() -> Expression<BVSort>).bvsdiv(other: Expression<BVSort>) = BVSDiv(this(), other)

infix fun (() -> Expression<BVSort>).bvsdiv(other: () -> Expression<BVSort>) =
    BVSDiv(this(), other())

infix fun Expression<BVSort>.bvsrem(denominator: Expression<BVSort>) = BVSRem(this, denominator)

infix fun Expression<BVSort>.bvsrem(other: () -> Expression<BVSort>) = BVSRem(this, other())

infix fun (() -> Expression<BVSort>).bvsrem(other: Expression<BVSort>) = BVSRem(this(), other)

infix fun (() -> Expression<BVSort>).bvsrem(other: () -> Expression<BVSort>) =
    BVSRem(this(), other())

infix fun Expression<BVSort>.bvsmod(rhs: Expression<BVSort>) = BVSMod(this, rhs)

infix fun Expression<BVSort>.bvsmod(other: () -> Expression<BVSort>) = BVSMod(this, other())

infix fun (() -> Expression<BVSort>).bvsmod(other: Expression<BVSort>) = BVSMod(this(), other)

infix fun (() -> Expression<BVSort>).bvsmod(other: () -> Expression<BVSort>) =
    BVSMod(this(), other())

infix fun Expression<BVSort>.bvashr(distance: Expression<BVSort>) = BVAShr(this, distance)

infix fun Expression<BVSort>.bvashr(other: () -> Expression<BVSort>) = BVAShr(this, other())

infix fun (() -> Expression<BVSort>).bvashr(other: Expression<BVSort>) = BVAShr(this(), other)

infix fun (() -> Expression<BVSort>).bvashr(other: () -> Expression<BVSort>) =
    BVAShr(this(), other())

/*
 * bitvector comparison operators
 */

infix fun Expression<BVSort>.bvult(distance: Expression<BVSort>) = BVUlt(this, distance)

infix fun Expression<BVSort>.bvult(other: () -> Expression<BVSort>) = BVUlt(this, other())

infix fun (() -> Expression<BVSort>).bvult(other: Expression<BVSort>) = BVUlt(this(), other)

infix fun (() -> Expression<BVSort>).bvult(other: () -> Expression<BVSort>) = BVUlt(this(), other())

infix fun Expression<BVSort>.bvule(distance: Expression<BVSort>) = BVULe(this, distance)

infix fun Expression<BVSort>.bvule(other: () -> Expression<BVSort>) = BVULe(this, other())

infix fun (() -> Expression<BVSort>).bvule(other: Expression<BVSort>) = BVULe(this(), other)

infix fun (() -> Expression<BVSort>).bvule(other: () -> Expression<BVSort>) = BVULe(this(), other())

infix fun Expression<BVSort>.bvugt(distance: Expression<BVSort>) = BVUGt(this, distance)

infix fun Expression<BVSort>.bvugt(other: () -> Expression<BVSort>) = BVUGt(this, other())

infix fun (() -> Expression<BVSort>).bvugt(other: Expression<BVSort>) = BVUGt(this(), other)

infix fun (() -> Expression<BVSort>).bvugt(other: () -> Expression<BVSort>) = BVUGt(this(), other())

infix fun Expression<BVSort>.bvuge(distance: Expression<BVSort>) = BVUGe(this, distance)

infix fun Expression<BVSort>.bvuge(other: () -> Expression<BVSort>) = BVUGe(this, other())

infix fun (() -> Expression<BVSort>).bvuge(other: Expression<BVSort>) = BVUGe(this(), other)

infix fun (() -> Expression<BVSort>).bvuge(other: () -> Expression<BVSort>) = BVUGe(this(), other())

infix fun Expression<BVSort>.bvslt(distance: Expression<BVSort>) = BVSLt(this, distance)

infix fun Expression<BVSort>.bvslt(other: () -> Expression<BVSort>) = BVSLt(this, other())

infix fun (() -> Expression<BVSort>).bvslt(other: Expression<BVSort>) = BVSLt(this(), other)

infix fun (() -> Expression<BVSort>).bvslt(other: () -> Expression<BVSort>) = BVSLt(this(), other())

infix fun Expression<BVSort>.bvsle(distance: Expression<BVSort>) = BVSLe(this, distance)

infix fun Expression<BVSort>.bvsle(other: () -> Expression<BVSort>) = BVSLe(this, other())

infix fun (() -> Expression<BVSort>).bvsle(other: Expression<BVSort>) = BVSLe(this(), other)

infix fun (() -> Expression<BVSort>).bvsle(other: () -> Expression<BVSort>) = BVSLe(this(), other())

infix fun Expression<BVSort>.bvsgt(distance: Expression<BVSort>) = BVSGt(this, distance)

infix fun Expression<BVSort>.bvsgt(other: () -> Expression<BVSort>) = BVSGt(this, other())

infix fun (() -> Expression<BVSort>).bvsgt(other: Expression<BVSort>) = BVSGt(this(), other)

infix fun (() -> Expression<BVSort>).bvsgt(other: () -> Expression<BVSort>) = BVSGt(this(), other())

infix fun Expression<BVSort>.bvsge(distance: Expression<BVSort>) = BVSGe(this, distance)

infix fun Expression<BVSort>.bvsge(other: () -> Expression<BVSort>) = BVSGe(this, other())

infix fun (() -> Expression<BVSort>).bvsge(other: Expression<BVSort>) = BVSGe(this(), other)

infix fun (() -> Expression<BVSort>).bvsge(other: () -> Expression<BVSort>) = BVSGe(this(), other())

/*
 * parameterized bitvector operations
 */

fun repeat(i: Int, block: () -> Expression<BVSort>) = Repeat(i, block())

fun repeat(i: Int, expr: Expression<BVSort>) = Repeat(i, expr)

fun zeroExtend(i: Int, block: () -> Expression<BVSort>) = ZeroExtend(i, block())

fun zeroExtend(i: Int, expr: Expression<BVSort>) = ZeroExtend(i, expr)

fun signExtend(i: Int, block: () -> Expression<BVSort>) = SignExtend(i, block())

fun signExtend(i: Int, expr: Expression<BVSort>) = SignExtend(i, expr)

fun rotateLeft(i: Int, block: () -> Expression<BVSort>) = RotateLeft(i, block())

fun rotateLeft(i: Int, expr: Expression<BVSort>) = RotateLeft(i, expr)

fun rotateRight(i: Int, block: () -> Expression<BVSort>) = RotateRight(i, block())

fun rotateRight(i: Int, expr: Expression<BVSort>) = RotateRight(i, expr)

fun extract(i: Int, j: Int, block: () -> Expression<BVSort>) = BVExtract(i, j, block())

fun extract(i: Int, j: Int, expr: Expression<BVSort>) = BVExtract(i, j, expr)

/*
 * Unary bitvector operations
 */

fun bvnot(block: () -> Expression<BVSort>) = BVNot(block())

fun bvnot(expr: Expression<BVSort>) = BVNot(expr)

fun bvneg(block: () -> Expression<BVSort>) = BVNeg(block())

fun bvneg(expr: Expression<BVSort>) = BVNeg(expr)

/*
 * left-associative bitvector operations
 */

private fun makeOperation(
    init: Builder<BVSort>.() -> Unit,
    operation: (List<Expression<BVSort>>) -> Expression<BVSort>
): Expression<BVSort> {
  val builder = Builder<BVSort>()
  builder.init()

  require(builder.children.isNotEmpty())

  return if (builder.children.size == 1) {
    builder.children.single()
  } else {
    operation(builder.children)
  }
}

// TODO add more options e.g. bvand(list: List<Expression>)
fun bvand(init: Builder<BVSort>.() -> Unit) = makeOperation(init, ::BVAnd)

fun bvor(init: Builder<BVSort>.() -> Unit) = makeOperation(init, ::BVOr)

fun bvadd(init: Builder<BVSort>.() -> Unit) = makeOperation(init, ::BVAdd)

fun bvmul(init: Builder<BVSort>.() -> Unit) = makeOperation(init, ::BVMul)

fun bvxor(init: Builder<BVSort>.() -> Unit) = makeOperation(init, ::BVXOr)

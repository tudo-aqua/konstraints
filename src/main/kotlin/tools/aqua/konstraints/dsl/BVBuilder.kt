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

/**
 * Implements a bitwise and operation: [this] and [other].
 *
 * If [this] is a [BVAnd] object, unpacks the children and returns a new combined BVAnd.
 */

infix fun Expression<BVSort>.bvand(other: Expression<BVSort>) =
    if (this is BVAnd) {
      BVAnd(this.children+other)
    } else {
      BVAnd(this, other)
    }

/**
 * Implements a bitwise and operation: [this] and [other].
 *
 * If [this] is a [BVAnd] object, unpacks the children and returns a new combined BVAnd.
 */
infix fun Expression<BVSort>.bvand(other: () -> Expression<BVSort>): BVAnd = this bvand other()

/**
 * Implements a bitwise and operation: [this] and [other].
 *
 * If [this] is a [BVAnd] object, unpacks the children and returns a new combined BVAnd.
 */
infix fun (() -> Expression<BVSort>).bvand(other: Expression<BVSort>): BVAnd = this() bvand other

/**
 * Implements a bitwise and operation: [this] and [other].
 *
 * If [this] is a [BVAnd] object, unpacks the children and returns a new combined BVAnd.
 */
infix fun (() -> Expression<BVSort>).bvand(other: () -> Expression<BVSort>): BVAnd =
    this() bvand other()

/**
 * Implements a bitwise or operation: [this] or [other].
 *
 * If [this] is a [BVOr] object, unpacks the children and returns a new combined BVOr.
 */
infix fun Expression<BVSort>.bvor(other: Expression<BVSort>) =
    if (this is BVOr) {
      BVOr(this.children+other)
    } else {
      BVOr(this, other)
    }

/**
 * Implements a bitwise or operation: [this] or [other].
 *
 * If [this] is a [BVOr] object, unpacks the children and returns a new combined BVOr.
 */
infix fun Expression<BVSort>.bvor(other: () -> Expression<BVSort>): BVOr = this bvor other()

/**
 * Implements a bitwise or operation: [this] or [other].
 *
 * If [this] is a [BVOr] object, unpacks the children and returns a new combined BVOr.
 */
infix fun (() -> Expression<BVSort>).bvor(other: Expression<BVSort>): BVOr = this() bvor other

/**
 * Implements a bitwise or operation: [this] or [other].
 *
 * If [this] is a [BVOr] object, unpacks the children and returns a new combined BVOr.
 */
infix fun (() -> Expression<BVSort>).bvor(other: () -> Expression<BVSort>): BVOr =
    this() bvor other()

/**
 * Implements a bitvector addition operation: [this] + [other].
 *
 * If [this] is a [BVAdd] object, unpacks the children and returns a new combined BVAdd.
 */
infix fun Expression<BVSort>.bvadd(other: Expression<BVSort>) =
    if (this is BVAdd) {
      BVAdd(this.children+other)
    } else {
      BVAdd(this, other)
    }

/**
 * Implements a bitvector addition operation: [this] + [other].
 *
 * If [this] is a [BVAdd] object, unpacks the children and returns a new combined BVAdd.
 */
infix fun Expression<BVSort>.bvadd(other: () -> Expression<BVSort>): BVAdd = this bvadd other()

/**
 * Implements a bitvector addition operation: [this] + [other].
 *
 * If [this] is a [BVAdd] object, unpacks the children and returns a new combined BVAdd.
 */
infix fun (() -> Expression<BVSort>).bvadd(other: Expression<BVSort>): BVAdd = this() bvadd other

/**
 * Implements a bitvector addition operation: [this] + [other].
 *
 * If [this] is a [BVAdd] object, unpacks the children and returns a new combined BVAdd.
 */
infix fun (() -> Expression<BVSort>).bvadd(other: () -> Expression<BVSort>): BVAdd =
    this() bvadd other()

/**
 * Implements a bitvector multiplication operation: [this] * [other].
 *
 * If [this] is a [BVMul] object, unpacks the children and returns a new combined BVMul.
 */
infix fun Expression<BVSort>.bvmul(other: Expression<BVSort>) =
    if (this is BVMul) {
      BVMul(this.children + other)
    } else {
      BVMul(this, other)
    }

/**
 * Implements a bitvector multiplication operation: [this] * [other].
 *
 * If [this] is a [BVMul] object, unpacks the children and returns a new combined BVMul.
 */
infix fun Expression<BVSort>.bvmul(other: () -> Expression<BVSort>): BVMul = this bvmul other()

/**
 * Implements a bitvector multiplication operation: [this] * [other].
 *
 * If [this] is a [BVMul] object, unpacks the children and returns a new combined BVMul.
 */
infix fun (() -> Expression<BVSort>).bvmul(other: Expression<BVSort>): BVMul = this() bvmul other

/**
 * Implements a bitvector multiplication operation: [this] * [other].
 *
 * If [this] is a [BVMul] object, unpacks the children and returns a new combined BVMul.
 */
infix fun (() -> Expression<BVSort>).bvmul(other: () -> Expression<BVSort>): BVMul =
    this() bvmul other()

/**
 * Implements bitvector concatenation operation: [this].[other].
 */
infix fun Expression<BVSort>.concat(other: Expression<BVSort>) = BVConcat(this, other)

/**
 * Implements bitvector concatenation operation: [this].[other].
 */
infix fun Expression<BVSort>.concat(other: () -> Expression<BVSort>) = BVConcat(this, other())

/**
 * Implements bitvector concatenation operation: [this].[other].
 */
infix fun (() -> Expression<BVSort>).concat(other: Expression<BVSort>) = BVConcat(this(), other)

/**
 * Implements bitvector concatenation operation: [this].[other].
 */
infix fun (() -> Expression<BVSort>).concat(other: () -> Expression<BVSort>) = BVConcat(this(), other())

/**
 * Implements bitvector division operation: [this]/[denominator].
 */
infix fun Expression<BVSort>.bvudiv(denominator: Expression<BVSort>) = BVUDiv(this, denominator)

/**
 * Implements bitvector division operation: [this]/[denominator].
 */
infix fun Expression<BVSort>.bvudiv(denominator: () -> Expression<BVSort>) = BVUDiv(this, denominator())

/**
 * Implements bitvector division operation: [this]/[denominator].
 */
infix fun (() -> Expression<BVSort>).bvudiv(denominator: Expression<BVSort>) = BVUDiv(this(), denominator)

/**
 * Implements bitvector division operation: [this]/[denominator].
 */
infix fun (() -> Expression<BVSort>).bvudiv(denominator: () -> Expression<BVSort>) = BVUDiv(this(), denominator())

/**
 * Implements bitvector unsigned remainder operation: [this] bvurem [denominator].
 */
infix fun Expression<BVSort>.bvurem(denominator: Expression<BVSort>) = BVURem(this, denominator)

/**
 * Implements bitvector unsigned remainder operation: [this] bvurem [denominator].
 */
infix fun Expression<BVSort>.bvurem(denominator: () -> Expression<BVSort>) = BVURem(this, denominator())

/**
 * Implements bitvector unsigned remainder operation: [this] bvurem [denominator].
 */
infix fun (() -> Expression<BVSort>).bvurem(denominator: Expression<BVSort>) = BVURem(this(), denominator)

/**
 * Implements bitvector unsigned remainder operation: [this] bvurem [denominator].
 */
infix fun (() -> Expression<BVSort>).bvurem(denominator: () -> Expression<BVSort>) = BVURem(this(), denominator())

/**
 * Implements bitvector left shift operation: [this] bvshl [distance].
 */
infix fun Expression<BVSort>.bvshl(distance: Expression<BVSort>) = BVShl(this, distance)

/**
 * Implements bitvector left shift operation: [this] bvshl [distance].
 */
infix fun Expression<BVSort>.bvshl(distance: () -> Expression<BVSort>) = BVShl(this, distance())

/**
 * Implements bitvector left shift operation: [this] bvshl [distance].
 */
infix fun (() -> Expression<BVSort>).bvshl(distance: Expression<BVSort>) = BVShl(this(), distance)

/**
 * Implements bitvector left shift operation: [this] bvshl [distance].
 */
infix fun (() -> Expression<BVSort>).bvshl(distance: () -> Expression<BVSort>) = BVShl(this(), distance())

/**
 * Implements bitvector logical right shift operation: [this] bvlshr [distance].
 */
infix fun Expression<BVSort>.bvlshr(distance: Expression<BVSort>) = BVLShr(this, distance)

/**
 * Implements bitvector logical right shift operation: [this] bvlshr [distance].
 */
infix fun Expression<BVSort>.bvlshr(distance: () -> Expression<BVSort>) = BVLShr(this, distance())

/**
 * Implements bitvector logical right shift operation: [this] bvlshr [distance].
 */
infix fun (() -> Expression<BVSort>).bvlshr(distance: Expression<BVSort>) = BVLShr(this(), distance)

/**
 * Implements bitvector logical right shift operation: [this] bvlshr [distance].
 */
infix fun (() -> Expression<BVSort>).bvlshr(distance: () -> Expression<BVSort>) = BVLShr(this(), distance())

/**
 * Implements a bitwise nand operation: [this] nand [other].
 *
 * If [this] is a [BVNAnd] object, unpacks the children and returns a new combined BVNAnd.
 */
infix fun Expression<BVSort>.bvnand(other: Expression<BVSort>) = BVNAnd(this, other)

/**
 * Implements a bitwise nand operation: [this] nand [other].
 *
 * If [this] is a [BVNAnd] object, unpacks the children and returns a new combined BVNAnd.
 */
infix fun Expression<BVSort>.bvnand(other: () -> Expression<BVSort>) = BVNAnd(this, other())

/**
 * Implements a bitwise nand operation: [this] nand [other].
 *
 * If [this] is a [BVNAnd] object, unpacks the children and returns a new combined BVNAnd.
 */
infix fun (() -> Expression<BVSort>).bvnand(other: Expression<BVSort>) = BVNAnd(this(), other)

/**
 * Implements a bitwise nand operation: [this] nand [other].
 *
 * If [this] is a [BVNAnd] object, unpacks the children and returns a new combined BVNAnd.
 */
infix fun (() -> Expression<BVSort>).bvnand(other: () -> Expression<BVSort>) = BVNAnd(this(), other())

/**
 * Implements a bitwise nor operation: [this] nor [other].
 *
 * If [this] is a [BVNOr] object, unpacks the children and returns a new combined BVNor.
 */
infix fun Expression<BVSort>.bvnor(other: Expression<BVSort>) = BVNOr(this, other)

/**
 * Implements a bitwise nor operation: [this] nor [other].
 *
 * If [this] is a [BVNOr] object, unpacks the children and returns a new combined BVNor.
 */
infix fun Expression<BVSort>.bvnor(other: () -> Expression<BVSort>) = BVNOr(this, other())

/**
 * Implements a bitwise nor operation: [this] nor [other].
 *
 * If [this] is a [BVNOr] object, unpacks the children and returns a new combined BVNor.
 */
infix fun (() -> Expression<BVSort>).bvnor(other: Expression<BVSort>) = BVNOr(this(), other)

/**
 * Implements a bitwise nor operation: [this] nor [other].
 *
 * If [this] is a [BVNOr] object, unpacks the children and returns a new combined BVNor.
 */
infix fun (() -> Expression<BVSort>).bvnor(other: () -> Expression<BVSort>) = BVNOr(this(), other())

/**
 * Implements a bitwise xor operation: [this] xor [other].
 *
 * If [this] is a [BVXOr] object, unpacks the children and returns a new combined BVXor.
 */
infix fun Expression<BVSort>.bvxor(other: Expression<BVSort>) =
    if (this is BVXOr) {
      BVXOr(this.children+other)
    } else {
      BVXOr(this, other)
    }

/**
 * Implements a bitwise xor operation: [this] xor [other].
 *
 * If [this] is a [BVXOr] object, unpacks the children and returns a new combined BVXor.
 */
infix fun Expression<BVSort>.bvxor(other: () -> Expression<BVSort>) = BVXOr(this, other())

/**
 * Implements a bitwise xor operation: [this] xor [other].
 *
 * If [this] is a [BVXOr] object, unpacks the children and returns a new combined BVXor.
 */
infix fun (() -> Expression<BVSort>).bvxor(other: Expression<BVSort>) = BVXOr(this(), other)

/**
 * Implements a bitwise xor operation: [this] xor [other].
 *
 * If [this] is a [BVXOr] object, unpacks the children and returns a new combined BVXor.
 */
infix fun (() -> Expression<BVSort>).bvxor(other: () -> Expression<BVSort>) = BVXOr(this(), other())

/**
 * Implements a bitwise xnor operation: [this] xnor [rhs].
 *
 * If [this] is a [BVXNOr] object, unpacks the children and returns a new combined BVXNor.
 */
infix fun Expression<BVSort>.bvxnor(rhs: Expression<BVSort>) = BVXNOr(this, rhs)

/**
 * Implements a bitwise xnor operation: [this] xnor [other].
 *
 * If [this] is a [BVXNOr] object, unpacks the children and returns a new combined BVXNor.
 */
infix fun Expression<BVSort>.bvxnor(other: () -> Expression<BVSort>) = BVXNOr(this, other())

/**
 * Implements a bitwise xnor operation: [this] xnor [other].
 *
 * If [this] is a [BVXNOr] object, unpacks the children and returns a new combined BVXNor.
 */
infix fun (() -> Expression<BVSort>).bvxnor(other: Expression<BVSort>) = BVXNOr(this(), other)

/**
 * Implements a bitwise xnor operation: [this] xnor [other].
 *
 * If [this] is a [BVXNOr] object, unpacks the children and returns a new combined BVXNor.
 */
infix fun (() -> Expression<BVSort>).bvxnor(other: () -> Expression<BVSort>) =
    BVXNOr(this(), other())

/**
 * Implements bitwise comparison operator: [this] bvcomp [other].
 */
infix fun Expression<BVSort>.bvcomp(other: Expression<BVSort>) = BVComp(this, other)

/**
 * Implements bitwise comparison operator: [this] bvcomp [other].
 */
infix fun Expression<BVSort>.bvcomp(other: () -> Expression<BVSort>) = BVComp(this, other())

/**
 * Implements bitwise comparison operator: [this] bvcomp [other].
 */
infix fun (() -> Expression<BVSort>).bvcomp(other: Expression<BVSort>) = BVComp(this(), other)

/**
 * Implements bitwise comparison operator: [this] bvcomp [other].
 */
infix fun (() -> Expression<BVSort>).bvcomp(other: () -> Expression<BVSort>) = BVComp(this(), other())

/**
 * Implements bitvector subtraction operator: [this] - [subtrahend].
 */
infix fun Expression<BVSort>.bvsub(subtrahend: Expression<BVSort>) = BVSub(this, subtrahend)

/**
 * Implements bitvector subtraction operator: [this] - [subtrahend].
 */
infix fun Expression<BVSort>.bvsub(subtrahend: () -> Expression<BVSort>) = BVSub(this, subtrahend())

/**
 * Implements bitvector subtraction operator: [this] - [subtrahend].
 */
infix fun (() -> Expression<BVSort>).bvsub(subtrahend: Expression<BVSort>) = BVSub(this(), subtrahend)

/**
 * Implements bitvector subtraction operator: [this] - [subtrahend].
 */
infix fun (() -> Expression<BVSort>).bvsub(subtrahend: () -> Expression<BVSort>) = BVSub(this(), subtrahend())

/**
 * Implements bitvector signed division operator: [this]/[denominator].
 */
infix fun Expression<BVSort>.bvsdiv(denominator: Expression<BVSort>) = BVSDiv(this, denominator)

/**
 * Implements bitvector signed division operator: [this]/[denominator].
 */
infix fun Expression<BVSort>.bvsdiv(denominator: () -> Expression<BVSort>) = BVSDiv(this, denominator())

/**
 * Implements bitvector signed division operator: [this]/[denominator].
 */
infix fun (() -> Expression<BVSort>).bvsdiv(denominator: Expression<BVSort>) = BVSDiv(this(), denominator)

/**
 * Implements bitvector signed division operator: [this]/[denominator].
 */
infix fun (() -> Expression<BVSort>).bvsdiv(denominator: () -> Expression<BVSort>) = BVSDiv(this(), denominator())

/**
 * Implements bitvector signed remainder operator: [this]/[denominator].
 */
infix fun Expression<BVSort>.bvsrem(denominator: Expression<BVSort>) = BVSRem(this, denominator)

/**
 * Implements bitvector signed remainder operator: [this]/[denominator].
 */
infix fun Expression<BVSort>.bvsrem(denominator: () -> Expression<BVSort>) = BVSRem(this, denominator())

/**
 * Implements bitvector signed remainder operator: [this]/[denominator].
 */
infix fun (() -> Expression<BVSort>).bvsrem(denominator: Expression<BVSort>) = BVSRem(this(), denominator)

/**
 * Implements bitvector signed remainder operator: [this]/[denominator].
 */
infix fun (() -> Expression<BVSort>).bvsrem(denominator: () -> Expression<BVSort>) = BVSRem(this(), denominator())

/**
 * Implements bitvector signed modulo operator: [this]/[other].
 */
infix fun Expression<BVSort>.bvsmod(other: Expression<BVSort>) = BVSMod(this, other)

/**
 * Implements bitvector signed modulo operator: [this]/[other].
 */
infix fun Expression<BVSort>.bvsmod(other: () -> Expression<BVSort>) = BVSMod(this, other())

/**
 * Implements bitvector signed modulo operator: [this]/[other].
 */
infix fun (() -> Expression<BVSort>).bvsmod(other: Expression<BVSort>) = BVSMod(this(), other)

/**
 * Implements bitvector signed modulo operator: [this]/[other].
 */
infix fun (() -> Expression<BVSort>).bvsmod(other: () -> Expression<BVSort>) = BVSMod(this(), other())

/**
 * Implements arithmetic shift right operator.
 *
 * Shifts [this] by [distance] to the right.
 */
infix fun Expression<BVSort>.bvashr(distance: Expression<BVSort>) = BVAShr(this, distance)

/**
 * Implements arithmetic shift right operator.
 *
 * Shifts [this] by [distance] to the right.
 */
infix fun Expression<BVSort>.bvashr(distance: () -> Expression<BVSort>) = BVAShr(this, distance())

/**
 * Implements arithmetic shift right operator.
 *
 * Shifts [this] by [distance] to the right.
 */
infix fun (() -> Expression<BVSort>).bvashr(distance: Expression<BVSort>) = BVAShr(this(), distance)

/**
 * Implements arithmetic shift right operator.
 *
 * Shifts [this] by [distance] to the right.
 */
infix fun (() -> Expression<BVSort>).bvashr(distance: () -> Expression<BVSort>) = BVAShr(this(), distance())

/*
 * bitvector comparison operators
 */

/**
 * Unsigned less than operator for bitvectors: [this] < [other].
 */
infix fun Expression<BVSort>.bvult(other: Expression<BVSort>) = BVUlt(this, other)

/**
 * Unsigned less than operator for bitvectors: [this] < [other].
 */
infix fun Expression<BVSort>.bvult(other: () -> Expression<BVSort>) = BVUlt(this, other())

/**
 * Unsigned less than operator for bitvectors: [this] < [other].
 */
infix fun (() -> Expression<BVSort>).bvult(other: Expression<BVSort>) = BVUlt(this(), other)

/**
 * Unsigned less than operator for bitvectors: [this] < [other].
 */
infix fun (() -> Expression<BVSort>).bvult(other: () -> Expression<BVSort>) = BVUlt(this(), other())

/**
 * Unsigned less equals operator for bitvectors: [this] <= [other].
 */
infix fun Expression<BVSort>.bvule(other: Expression<BVSort>) = BVULe(this, other)

/**
 * Unsigned less equals operator for bitvectors: [this] <= [other].
 */
infix fun Expression<BVSort>.bvule(other: () -> Expression<BVSort>) = BVULe(this, other())

/**
 * Unsigned less equals operator for bitvectors: [this] <= [other].
 */
infix fun (() -> Expression<BVSort>).bvule(other: Expression<BVSort>) = BVULe(this(), other)

/**
 * Unsigned less equals operator for bitvectors: [this] <= [other].
 */
infix fun (() -> Expression<BVSort>).bvule(other: () -> Expression<BVSort>) = BVULe(this(), other())

/**
 * Unsigned greater than operator for bitvectors: [this] > [other].
 */
infix fun Expression<BVSort>.bvugt(other: Expression<BVSort>) = BVUGt(this, other)

/**
 * Unsigned greater than operator for bitvectors: [this] > [other].
 */
infix fun Expression<BVSort>.bvugt(other: () -> Expression<BVSort>) = BVUGt(this, other())

/**
 * Unsigned greater than operator for bitvectors: [this] > [other].
 */
infix fun (() -> Expression<BVSort>).bvugt(other: Expression<BVSort>) = BVUGt(this(), other)

/**
 * Unsigned greater than operator for bitvectors: [this] > [other].
 */
infix fun (() -> Expression<BVSort>).bvugt(other: () -> Expression<BVSort>) = BVUGt(this(), other())

/**
 * Unsigned greater equals operator for bitvectors: [this] >= [other].
 */
infix fun Expression<BVSort>.bvuge(other: Expression<BVSort>) = BVUGe(this, other)

/**
 * Unsigned greater equals operator for bitvectors: [this] >= [other].
 */
infix fun Expression<BVSort>.bvuge(other: () -> Expression<BVSort>) = BVUGe(this, other())

/**
 * Unsigned greater equals operator for bitvectors: [this] >= [other].
 */
infix fun (() -> Expression<BVSort>).bvuge(other: Expression<BVSort>) = BVUGe(this(), other)

/**
 * Unsigned greater equals operator for bitvectors: [this] >= [other].
 */
infix fun (() -> Expression<BVSort>).bvuge(other: () -> Expression<BVSort>) = BVUGe(this(), other())

/**
 * Signed less than operator for bitvectors: [this] >= [other].
 */
infix fun Expression<BVSort>.bvslt(other: Expression<BVSort>) = BVSLt(this, other)

/**
 * Signed less than operator for bitvectors: [this] >= [other].
 */
infix fun Expression<BVSort>.bvslt(other: () -> Expression<BVSort>) = BVSLt(this, other())

/**
 * Signed less than operator for bitvectors: [this] >= [other].
 */
infix fun (() -> Expression<BVSort>).bvslt(other: Expression<BVSort>) = BVSLt(this(), other)

/**
 * Signed less than operator for bitvectors: [this] >= [other].
 */
infix fun (() -> Expression<BVSort>).bvslt(other: () -> Expression<BVSort>) = BVSLt(this(), other())

/**
 * Signed less equals operator for bitvectors: [this] <= [other].
 */
infix fun Expression<BVSort>.bvsle(other: Expression<BVSort>) = BVSLe(this, other)

/**
 * Signed less equals operator for bitvectors: [this] <= [other].
 */
infix fun Expression<BVSort>.bvsle(other: () -> Expression<BVSort>) = BVSLe(this, other())

/**
 * Signed less equals operator for bitvectors: [this] <= [other].
 */
infix fun (() -> Expression<BVSort>).bvsle(other: Expression<BVSort>) = BVSLe(this(), other)

/**
 * Signed less equals operator for bitvectors: [this] <= [other].
 */
infix fun (() -> Expression<BVSort>).bvsle(other: () -> Expression<BVSort>) = BVSLe(this(), other())

/**
 * Signed greater than operator for bitvectors: [this] > [other].
 */
infix fun Expression<BVSort>.bvsgt(other: Expression<BVSort>) = BVSGt(this, other)

/**
 * Signed greater than operator for bitvectors: [this] > [other].
 */
infix fun Expression<BVSort>.bvsgt(other: () -> Expression<BVSort>) = BVSGt(this, other())

/**
 * Signed greater than operator for bitvectors: [this] > [other].
 */
infix fun (() -> Expression<BVSort>).bvsgt(other: Expression<BVSort>) = BVSGt(this(), other)

/**
 * Signed greater than operator for bitvectors: [this] > [other].
 */
infix fun (() -> Expression<BVSort>).bvsgt(other: () -> Expression<BVSort>) = BVSGt(this(), other())

/**
 * Signed greater equals operator for bitvectors: [this] >= [other].
 */
infix fun Expression<BVSort>.bvsge(other: Expression<BVSort>) = BVSGe(this, other)

/**
 * Signed greater equals operator for bitvectors: [this] >= [other].
 */
infix fun Expression<BVSort>.bvsge(other: () -> Expression<BVSort>) = BVSGe(this, other())

/**
 * Signed greater equals operator for bitvectors: [this] >= [other].
 */
infix fun (() -> Expression<BVSort>).bvsge(other: Expression<BVSort>) = BVSGe(this(), other)

/**
 * Signed greater equals operator for bitvectors: [this] >= [other].
 */
infix fun (() -> Expression<BVSort>).bvsge(other: () -> Expression<BVSort>) = BVSGe(this(), other())

/*
 * parameterized bitvector operations
 */

/**
 * Repeat the result of [block] [i]-times.
 */
fun repeat(i: Int, block: () -> Expression<BVSort>) = Repeat(i, block())

/**
 * Repeat [expr] [i]-times.
 */
fun repeat(i: Int, expr: Expression<BVSort>) = Repeat(i, expr)

/**
 * Extends the result of [block] to equivalent bitvector of size m+i.
 */
fun zeroExtend(i: Int, block: () -> Expression<BVSort>) = ZeroExtend(i, block())

/**
 * Extends [expr] to equivalent bitvector of size m+i.
 */
fun zeroExtend(i: Int, expr: Expression<BVSort>) = ZeroExtend(i, expr)

/**
 * Extends the result of [block] to equivalent signed bitvector of size m+i.
 */
fun signExtend(i: Int, block: () -> Expression<BVSort>) = SignExtend(i, block())

/**
 * Extends [expr] to equivalent signed bitvector of size m+i.
 */
fun signExtend(i: Int, expr: Expression<BVSort>) = SignExtend(i, expr)

/**
 * Rotates the result of [block] to the left [i]-times.
 */
fun rotateLeft(i: Int, block: () -> Expression<BVSort>) = RotateLeft(i, block())

/**
 * Rotates [expr] to the left [i]-times.
 */
fun rotateLeft(i: Int, expr: Expression<BVSort>) = RotateLeft(i, expr)

/**
 * Rotates the result of [block] to the right [i]-times.
 */
fun rotateRight(i: Int, block: () -> Expression<BVSort>) = RotateRight(i, block())

/**
 * Rotates [expr] to the right [i]-times.
 */
fun rotateRight(i: Int, expr: Expression<BVSort>) = RotateRight(i, expr)

/**
 * Extracts bits from [j] to [i] from the result of [block].
 *
 * This results in a bitvector of size [i] - [j] + 1. [i] and [j] are inclusive.
 */
fun extract(i: Int, j: Int, block: () -> Expression<BVSort>) = BVExtract(i, j, block())

/**
 * Extracts bits from [j] to [i] from [expr].
 *
 * This results in a bitvector of size [i] - [j] + 1. [i] and [j] are inclusive.
 */
fun extract(i: Int, j: Int, expr: Expression<BVSort>) = BVExtract(i, j, expr)

/*
 * Unary bitvector operations
 */

/**
 * Bitwise negation operator
 */
fun bvnot(block: () -> Expression<BVSort>) = BVNot(block())

/**
 * Bitwise negation operator
 */
fun bvnot(expr: Expression<BVSort>) = BVNot(expr)

/**
 * 2's complement unary minus
 */
fun bvneg(block: () -> Expression<BVSort>) = BVNeg(block())

/**
 * 2's complement unary minus
 */
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

/**
 * Bitwise-and operator for BVSort Expressions.
 *
 * Use [Builder.unaryPlus] inside the [init] lambda to add Expressions to the addition operation.
 * If only a single subexpression is added, the expression is returned directly.
 *
 * @throws [IllegalArgumentException] if no expression is added inside the [init] lambda
 */
fun bvand(init: Builder<BVSort>.() -> Unit) = makeOperation(init, ::BVAnd)

/**
 * Bitwise-or operator for BVSort Expressions.
 *
 * Use [Builder.unaryPlus] inside the [init] lambda to add Expressions to the addition operation.
 * If only a single subexpression is added, the expression is returned directly.
 *
 * @throws [IllegalArgumentException] if no expression is added inside the [init] lambda
 */
fun bvor(init: Builder<BVSort>.() -> Unit) = makeOperation(init, ::BVOr)

/**
 * Addition operator for BVSort Expressions.
 *
 * Use [Builder.unaryPlus] inside the [init] lambda to add Expressions to the addition operation.
 * If only a single subexpression is added, the expression is returned directly.
 *
 * @throws [IllegalArgumentException] if no expression is added inside the [init] lambda
 */
fun bvadd(init: Builder<BVSort>.() -> Unit) = makeOperation(init, ::BVAdd)

/**
 * Multiplication operator for BVSort Expressions.
 *
 * Use [Builder.unaryPlus] inside the [init] lambda to add Expressions to the addition operation.
 * If only a single subexpression is added, the expression is returned directly.
 *
 * @throws [IllegalArgumentException] if no expression is added inside the [init] lambda
 */
fun bvmul(init: Builder<BVSort>.() -> Unit) = makeOperation(init, ::BVMul)

/**
 * Bitwise-xor operator for BVSort Expressions.
 *
 * Use [Builder.unaryPlus] inside the [init] lambda to add Expressions to the addition operation.
 * If only a single subexpression is added, the expression is returned directly.
 *
 * @throws [IllegalArgumentException] if no expression is added inside the [init] lambda
 */
fun bvxor(init: Builder<BVSort>.() -> Unit) = makeOperation(init, ::BVXOr)

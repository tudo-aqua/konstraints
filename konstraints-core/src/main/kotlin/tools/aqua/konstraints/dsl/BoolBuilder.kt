/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2025 The Konstraints Authors
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

import java.math.BigDecimal
import java.math.BigInteger
import tools.aqua.konstraints.smt.And
import tools.aqua.konstraints.smt.BoolSort
import tools.aqua.konstraints.smt.Distinct
import tools.aqua.konstraints.smt.Equals
import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.smt.FPLiteral
import tools.aqua.konstraints.smt.FPSort
import tools.aqua.konstraints.smt.Implies
import tools.aqua.konstraints.smt.IntLiteral
import tools.aqua.konstraints.smt.IntSort
import tools.aqua.konstraints.smt.Not
import tools.aqua.konstraints.smt.Or
import tools.aqua.konstraints.smt.QF_UF
import tools.aqua.konstraints.smt.RealLiteral
import tools.aqua.konstraints.smt.RealSort
import tools.aqua.konstraints.smt.SMTInt
import tools.aqua.konstraints.smt.Sort
import tools.aqua.konstraints.smt.StringLiteral
import tools.aqua.konstraints.smt.StringSort
import tools.aqua.konstraints.smt.XOr

/**
 * Creates a logical implication: [this] => [other].
 *
 * If [this] is an [tools.aqua.konstraints.smt.Implies] object, unpacks the children and returns a
 * new combined Implies.
 */
infix fun Expression<BoolSort>.implies(other: Expression<BoolSort>) =
    if (this is Implies) {
      Implies(children + other)
    } else {
      Implies(this, other)
    }

/**
 * Creates a logical implication: [this] => [other].
 *
 * If [this] is an [Implies] object, unpacks the children and returns a new combined Implies.
 */
infix fun Expression<BoolSort>.implies(other: () -> Expression<BoolSort>) = this implies other()

/**
 * Creates a logical implication: [this] => [other].
 *
 * If [this] is an [Implies] object, unpacks the children and returns a new combined Implies.
 */
infix fun (() -> Expression<BoolSort>).implies(other: Expression<BoolSort>) = this() implies other

/**
 * Creates a logical implication: [this] => [other].
 *
 * If [this] is an [Implies] object, unpacks the children and returns a new combined Implies.
 */
infix fun (() -> Expression<BoolSort>).implies(other: () -> Expression<BoolSort>) =
    this() implies other()

/**
 * Creates a logical and: [this] and [other].
 *
 * If [this] is an [And] object, unpacks the children and returns a new combined And.
 */
infix fun Expression<BoolSort>.and(other: Expression<BoolSort>) =
    if (this is And) {
      And(this.children + other)
    } else {
      And(this, other)
    }

/**
 * Creates a logical and: [this] and [other].
 *
 * If [this] is an [And] object, unpacks the children and returns a new combined And.
 */
infix fun Expression<BoolSort>.and(other: () -> Expression<BoolSort>) = this and other()

/**
 * Creates a logical and: [this] and [other].
 *
 * If [this] is an [And] object, unpacks the children and returns a new combined And.
 */
infix fun (() -> Expression<BoolSort>).and(other: Expression<BoolSort>) = this() and other

/**
 * Creates a logical and: [this] and [other].
 *
 * If [this] is an [And] object, unpacks the children and returns a new combined And.
 */
infix fun (() -> Expression<BoolSort>).and(other: () -> Expression<BoolSort>) = this() and other()

/**
 * Creates a logical or: [this] or [other].
 *
 * If [this] is an [Or] object, unpacks the children and returns a new combined Or.
 */
infix fun Expression<BoolSort>.or(other: Expression<BoolSort>): Or =
    if (this is Or) {
      Or(children + other)
    } else {
      Or(this, other)
    }

/**
 * Creates a logical or: [this] or [other].
 *
 * If [this] is an [Or] object, unpacks the children and returns a new combined Or.
 */
infix fun Expression<BoolSort>.or(other: () -> Expression<BoolSort>) = this or other()

/**
 * Creates a logical or: [this] or [other].
 *
 * If [this] is an [Or] object, unpacks the children and returns a new combined Or.
 */
infix fun (() -> Expression<BoolSort>).or(other: Expression<BoolSort>) = this() or other

/**
 * Creates a logical or: [this] or [other].
 *
 * If [this] is an [Or] object, unpacks the children and returns a new combined Or.
 */
infix fun (() -> Expression<BoolSort>).or(other: () -> Expression<BoolSort>) = this() or other()

/**
 * Creates a logical xor: [this] xor [other].
 *
 * If [this] is an [XOr] object, unpacks the children and returns a new combined XOr.
 */
infix fun Expression<BoolSort>.xor(other: Expression<BoolSort>): XOr =
    if (this is XOr) {
      XOr(this.children + other)
    } else {
      XOr(this, other)
    }

/**
 * Creates a logical xor: [this] xor [other].
 *
 * If [this] is an [XOr] object, unpacks the children and returns a new combined XOr.
 */
infix fun Expression<BoolSort>.xor(other: () -> Expression<BoolSort>) = this xor other()

/**
 * Creates a logical xor: [this] xor [other].
 *
 * If [this] is an [XOr] object, unpacks the children and returns a new combined XOr.
 */
infix fun (() -> Expression<BoolSort>).xor(other: Expression<BoolSort>) = this() xor other

/**
 * Creates a logical xor: [this] xor [other].
 *
 * If [this] is an [XOr] object, unpacks the children and returns a new combined XOr.
 */
infix fun (() -> Expression<BoolSort>).xor(other: () -> Expression<BoolSort>) = this() xor other()

/**
 * Creates an equals: [this] equals [other].
 *
 * If [this] is an [tools.aqua.konstraints.smt.Equals] object, unpacks the children and returns a
 * new combined Equals.
 */
infix fun <T : Sort> Expression<T>.eq(other: Expression<T>) =
    if (this is Equals<*>) {
      Equals(this.children as List<Expression<T>> + other)
    } else {
      Equals(this, other)
    }

infix fun <T : Sort> Expression<T>.eq(other: (() -> Expression<T>)) = this eq other()

infix fun <T : Sort> (() -> Expression<T>).eq(other: Expression<T>) = this() eq other

infix fun <T : Sort> (() -> Expression<T>).eq(other: (() -> Expression<T>)) = this() eq other()

// allow chaining of equals
/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqByteIntSort") infix fun Byte.eq(expr: Expression<IntSort>) = IntLiteral(this) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqByteIntSort")
infix fun Byte.eq(expr: (() -> Expression<IntSort>)) = IntLiteral(this) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqByteIntSort")
infix fun (() -> Byte).eq(expr: Expression<IntSort>) = IntLiteral(this()) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqByteIntSort")
infix fun (() -> Byte).eq(expr: (() -> Expression<IntSort>)) = IntLiteral(this()) eq expr()

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortByte") infix fun Expression<IntSort>.eq(other: Byte) = this eq IntLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortByte")
infix fun Expression<IntSort>.eq(other: (() -> Byte)) = this eq IntLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortByte")
infix fun (() -> Expression<IntSort>).eq(other: Byte) = this() eq IntLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortByte")
infix fun (() -> Expression<IntSort>).eq(other: (() -> Byte)) = this() eq IntLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortByteEquals")
infix fun Equals<IntSort>.eq(other: Byte) = this eq IntLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortByteEquals")
infix fun Equals<IntSort>.eq(other: (() -> Byte)) = this eq IntLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortByteEquals")
infix fun (() -> Equals<IntSort>).eq(other: Byte) = this() eq IntLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortByteEquals")
infix fun (() -> Equals<IntSort>).eq(other: (() -> Byte)) = this() eq IntLiteral(other())

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqByteIntSortEquals") infix fun Byte.eq(expr: Equals<IntSort>) = IntLiteral(this) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqByteIntSortEquals")
infix fun Byte.eq(expr: (() -> Equals<IntSort>)) = IntLiteral(this) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqByteIntSortEquals")
infix fun (() -> Byte).eq(expr: Equals<IntSort>) = IntLiteral(this()) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqByteIntSortEquals")
infix fun (() -> Byte).eq(expr: (() -> Equals<IntSort>)) = IntLiteral(this()) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqShortIntSort") infix fun Short.eq(expr: Expression<IntSort>) = IntLiteral(this) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqShortIntSort")
infix fun Short.eq(expr: (() -> Expression<IntSort>)) = IntLiteral(this) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqShortIntSort")
infix fun (() -> Short).eq(expr: Expression<IntSort>) = IntLiteral(this()) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqShortIntSort")
infix fun (() -> Short).eq(expr: (() -> Expression<IntSort>)) = IntLiteral(this()) eq expr()

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortShort")
infix fun Expression<IntSort>.eq(other: Short) = this eq IntLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortShort")
infix fun Expression<IntSort>.eq(other: (() -> Short)) = this eq IntLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortShort")
infix fun (() -> Expression<IntSort>).eq(other: Short) = this() eq IntLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortShort")
infix fun (() -> Expression<IntSort>).eq(other: (() -> Short)) = this() eq IntLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortShortEquals")
infix fun Equals<IntSort>.eq(other: Short) = this eq IntLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortShortEquals")
infix fun Equals<IntSort>.eq(other: (() -> Short)) = this eq IntLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortShortEquals")
infix fun (() -> Equals<IntSort>).eq(other: Short) = this() eq IntLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortShortEquals")
infix fun (() -> Equals<IntSort>).eq(other: (() -> Short)) = this() eq IntLiteral(other())

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqShortIntSortEquals")
infix fun Short.eq(expr: Equals<IntSort>) = IntLiteral(this) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqShortIntSortEquals")
infix fun Short.eq(expr: (() -> Equals<IntSort>)) = IntLiteral(this) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqShortIntSortEquals")
infix fun (() -> Short).eq(expr: Equals<IntSort>) = IntLiteral(this()) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqShortIntSortEquals")
infix fun (() -> Short).eq(expr: (() -> Equals<IntSort>)) = IntLiteral(this()) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqIntIntSort") infix fun Int.eq(expr: Expression<IntSort>) = IntLiteral(this) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqIntIntSort")
infix fun Int.eq(expr: (() -> Expression<IntSort>)) = IntLiteral(this) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqIntIntSort")
infix fun (() -> Int).eq(expr: Expression<IntSort>) = IntLiteral(this()) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqIntIntSort")
infix fun (() -> Int).eq(expr: (() -> Expression<IntSort>)) = IntLiteral(this()) eq expr()

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortInt") infix fun Expression<IntSort>.eq(other: Int) = this eq IntLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortInt")
infix fun Expression<IntSort>.eq(other: (() -> Int)) = this eq IntLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortInt")
infix fun (() -> Expression<IntSort>).eq(other: Int) = this() eq IntLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortInt")
infix fun (() -> Expression<IntSort>).eq(other: (() -> Int)) = this() eq IntLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortIntEquals") infix fun Equals<IntSort>.eq(other: Int) = this eq IntLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortIntEquals")
infix fun Equals<IntSort>.eq(other: (() -> Int)) = this eq IntLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortIntEquals")
infix fun (() -> Equals<IntSort>).eq(other: Int) = this() eq IntLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortIntEquals")
infix fun (() -> Equals<IntSort>).eq(other: (() -> Int)) = this() eq IntLiteral(other())

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqIntIntSortEquals") infix fun Int.eq(expr: Equals<IntSort>) = IntLiteral(this) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqIntIntSortEquals")
infix fun Int.eq(expr: (() -> Equals<IntSort>)) = IntLiteral(this) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqIntIntSortEquals")
infix fun (() -> Int).eq(expr: Equals<IntSort>) = IntLiteral(this()) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqIntIntSortEquals")
infix fun (() -> Int).eq(expr: (() -> Equals<IntSort>)) = IntLiteral(this()) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqLongIntSort") infix fun Long.eq(expr: Expression<IntSort>) = IntLiteral(this) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqLongIntSort")
infix fun Long.eq(expr: (() -> Expression<IntSort>)) = IntLiteral(this) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqLongIntSort")
infix fun (() -> Long).eq(expr: Expression<IntSort>) = IntLiteral(this()) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqLongIntSort")
infix fun (() -> Long).eq(expr: (() -> Expression<IntSort>)) = IntLiteral(this()) eq expr()

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortLong") infix fun Expression<IntSort>.eq(other: Long) = this eq IntLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortLong")
infix fun Expression<IntSort>.eq(other: (() -> Long)) = this eq IntLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortLong")
infix fun (() -> Expression<IntSort>).eq(other: Long) = this() eq IntLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortLong")
infix fun (() -> Expression<IntSort>).eq(other: (() -> Long)) = this() eq IntLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortLongEquals")
infix fun Equals<IntSort>.eq(other: Long) = this eq IntLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortLongEquals")
infix fun Equals<IntSort>.eq(other: (() -> Long)) = this eq IntLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortLongEquals")
infix fun (() -> Equals<IntSort>).eq(other: Long) = this() eq IntLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortLongEquals")
infix fun (() -> Equals<IntSort>).eq(other: (() -> Long)) = this() eq IntLiteral(other())

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqLongIntSortEquals") infix fun Long.eq(expr: Equals<IntSort>) = IntLiteral(this) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqLongIntSortEquals")
infix fun Long.eq(expr: (() -> Equals<IntSort>)) = IntLiteral(this) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqLongIntSortEquals")
infix fun (() -> Long).eq(expr: Equals<IntSort>) = IntLiteral(this()) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqLongIntSortEquals")
infix fun (() -> Long).eq(expr: (() -> Equals<IntSort>)) = IntLiteral(this()) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqBigIntegerIntSort")
infix fun BigInteger.eq(expr: Expression<IntSort>) = IntLiteral(this) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqBigIntegerIntSort")
infix fun BigInteger.eq(expr: (() -> Expression<IntSort>)) = IntLiteral(this) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqBigIntegerIntSort")
infix fun (() -> BigInteger).eq(expr: Expression<IntSort>) = IntLiteral(this()) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqBigIntegerIntSort")
infix fun (() -> BigInteger).eq(expr: (() -> Expression<IntSort>)) = IntLiteral(this()) eq expr()

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortBigInteger")
infix fun Expression<IntSort>.eq(other: BigInteger) = this eq IntLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortBigInteger")
infix fun Expression<IntSort>.eq(other: (() -> BigInteger)) = this eq IntLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortBigInteger")
infix fun (() -> Expression<IntSort>).eq(other: BigInteger) = this() eq IntLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortBigInteger")
infix fun (() -> Expression<IntSort>).eq(other: (() -> BigInteger)) = this() eq IntLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortBigIntegerEquals")
infix fun Equals<IntSort>.eq(other: BigInteger) = this eq IntLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortBigIntegerEquals")
infix fun Equals<IntSort>.eq(other: (() -> BigInteger)) = this eq IntLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortBigIntegerEquals")
infix fun (() -> Equals<IntSort>).eq(other: BigInteger) = this() eq IntLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [IntLiteral]
 */
@JvmName("eqIntSortBigIntegerEquals")
infix fun (() -> Equals<IntSort>).eq(other: (() -> BigInteger)) = this() eq IntLiteral(other())

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqBigIntegerIntSortEquals")
infix fun BigInteger.eq(expr: Equals<IntSort>) = IntLiteral(this) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqBigIntegerIntSortEquals")
infix fun BigInteger.eq(expr: (() -> Equals<IntSort>)) = IntLiteral(this) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqBigIntegerIntSortEquals")
infix fun (() -> BigInteger).eq(expr: Equals<IntSort>) = IntLiteral(this()) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [IntLiteral]
 */
@JvmName("eqBigIntegerIntSortEquals")
infix fun (() -> BigInteger).eq(expr: (() -> Equals<IntSort>)) = IntLiteral(this()) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqByteRealSort") infix fun Byte.eq(expr: Expression<RealSort>) = RealLiteral(this) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqByteRealSort")
infix fun Byte.eq(expr: (() -> Expression<RealSort>)) = RealLiteral(this) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqByteRealSort")
infix fun (() -> Byte).eq(expr: Expression<RealSort>) = RealLiteral(this()) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqByteRealSort")
infix fun (() -> Byte).eq(expr: (() -> Expression<RealSort>)) = RealLiteral(this()) eq expr()

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortByte")
infix fun Expression<RealSort>.eq(other: Byte) = this eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortByte")
infix fun Expression<RealSort>.eq(other: (() -> Byte)) = this eq RealLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortByte")
infix fun (() -> Expression<RealSort>).eq(other: Byte) = this() eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortByte")
infix fun (() -> Expression<RealSort>).eq(other: (() -> Byte)) = this() eq RealLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortByteEquals")
infix fun Equals<RealSort>.eq(other: Byte) = this eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortByteEquals")
infix fun Equals<RealSort>.eq(other: (() -> Byte)) = this eq RealLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortByteEquals")
infix fun (() -> Equals<RealSort>).eq(other: Byte) = this() eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortByteEquals")
infix fun (() -> Equals<RealSort>).eq(other: (() -> Byte)) = this() eq RealLiteral(other())

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqByteRealSortEquals")
infix fun Byte.eq(expr: Equals<RealSort>) = RealLiteral(this) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqByteRealSortEquals")
infix fun Byte.eq(expr: (() -> Equals<RealSort>)) = RealLiteral(this) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqByteRealSortEquals")
infix fun (() -> Byte).eq(expr: Equals<RealSort>) = RealLiteral(this()) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqByteRealSortEquals")
infix fun (() -> Byte).eq(expr: (() -> Equals<RealSort>)) = RealLiteral(this()) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqShortRealSort")
infix fun Short.eq(expr: Expression<RealSort>) = RealLiteral(this) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqShortRealSort")
infix fun Short.eq(expr: (() -> Expression<RealSort>)) = RealLiteral(this) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqShortRealSort")
infix fun (() -> Short).eq(expr: Expression<RealSort>) = RealLiteral(this()) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqShortRealSort")
infix fun (() -> Short).eq(expr: (() -> Expression<RealSort>)) = RealLiteral(this()) eq expr()

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortShort")
infix fun Expression<RealSort>.eq(other: Short) = this eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortShort")
infix fun Expression<RealSort>.eq(other: (() -> Short)) = this eq RealLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortShort")
infix fun (() -> Expression<RealSort>).eq(other: Short) = this() eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortShort")
infix fun (() -> Expression<RealSort>).eq(other: (() -> Short)) = this() eq RealLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortShortEquals")
infix fun Equals<RealSort>.eq(other: Short) = this eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortShortEquals")
infix fun Equals<RealSort>.eq(other: (() -> Short)) = this eq RealLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortShortEquals")
infix fun (() -> Equals<RealSort>).eq(other: Short) = this() eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortShortEquals")
infix fun (() -> Equals<RealSort>).eq(other: (() -> Short)) = this() eq RealLiteral(other())

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqShortRealSortEquals")
infix fun Short.eq(expr: Equals<RealSort>) = RealLiteral(this) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqShortRealSortEquals")
infix fun Short.eq(expr: (() -> Equals<RealSort>)) = RealLiteral(this) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqShortRealSortEquals")
infix fun (() -> Short).eq(expr: Equals<RealSort>) = RealLiteral(this()) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqShortRealSortEquals")
infix fun (() -> Short).eq(expr: (() -> Equals<RealSort>)) = RealLiteral(this()) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqIntRealSort") infix fun Int.eq(expr: Expression<RealSort>) = RealLiteral(this) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqIntRealSort")
infix fun Int.eq(expr: (() -> Expression<RealSort>)) = RealLiteral(this) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqIntRealSort")
infix fun (() -> Int).eq(expr: Expression<RealSort>) = RealLiteral(this()) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqIntRealSort")
infix fun (() -> Int).eq(expr: (() -> Expression<RealSort>)) = RealLiteral(this()) eq expr()

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortInt") infix fun Expression<RealSort>.eq(other: Int) = this eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortInt")
infix fun Expression<RealSort>.eq(other: (() -> Int)) = this eq RealLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortInt")
infix fun (() -> Expression<RealSort>).eq(other: Int) = this() eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortInt")
infix fun (() -> Expression<RealSort>).eq(other: (() -> Int)) = this() eq RealLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortIntEquals")
infix fun Equals<RealSort>.eq(other: Int) = this eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortIntEquals")
infix fun Equals<RealSort>.eq(other: (() -> Int)) = this eq RealLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortIntEquals")
infix fun (() -> Equals<RealSort>).eq(other: Int) = this() eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortIntEquals")
infix fun (() -> Equals<RealSort>).eq(other: (() -> Int)) = this() eq RealLiteral(other())

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqIntRealSortEquals") infix fun Int.eq(expr: Equals<RealSort>) = RealLiteral(this) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqIntRealSortEquals")
infix fun Int.eq(expr: (() -> Equals<RealSort>)) = RealLiteral(this) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqIntRealSortEquals")
infix fun (() -> Int).eq(expr: Equals<RealSort>) = RealLiteral(this()) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqIntRealSortEquals")
infix fun (() -> Int).eq(expr: (() -> Equals<RealSort>)) = RealLiteral(this()) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqLongRealSort") infix fun Long.eq(expr: Expression<RealSort>) = RealLiteral(this) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqLongRealSort")
infix fun Long.eq(expr: (() -> Expression<RealSort>)) = RealLiteral(this) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqLongRealSort")
infix fun (() -> Long).eq(expr: Expression<RealSort>) = RealLiteral(this()) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqLongRealSort")
infix fun (() -> Long).eq(expr: (() -> Expression<RealSort>)) = RealLiteral(this()) eq expr()

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortLong")
infix fun Expression<RealSort>.eq(other: Long) = this eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortLong")
infix fun Expression<RealSort>.eq(other: (() -> Long)) = this eq RealLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortLong")
infix fun (() -> Expression<RealSort>).eq(other: Long) = this() eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortLong")
infix fun (() -> Expression<RealSort>).eq(other: (() -> Long)) = this() eq RealLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortLongEquals")
infix fun Equals<RealSort>.eq(other: Long) = this eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortLongEquals")
infix fun Equals<RealSort>.eq(other: (() -> Long)) = this eq RealLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortLongEquals")
infix fun (() -> Equals<RealSort>).eq(other: Long) = this() eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortLongEquals")
infix fun (() -> Equals<RealSort>).eq(other: (() -> Long)) = this() eq RealLiteral(other())

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqLongRealSortEquals")
infix fun Long.eq(expr: Equals<RealSort>) = RealLiteral(this) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqLongRealSortEquals")
infix fun Long.eq(expr: (() -> Equals<RealSort>)) = RealLiteral(this) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqLongRealSortEquals")
infix fun (() -> Long).eq(expr: Equals<RealSort>) = RealLiteral(this()) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqLongRealSortEquals")
infix fun (() -> Long).eq(expr: (() -> Equals<RealSort>)) = RealLiteral(this()) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqBigIntegerRealSort")
infix fun BigInteger.eq(expr: Expression<RealSort>) = RealLiteral(this) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqBigIntegerRealSort")
infix fun BigInteger.eq(expr: (() -> Expression<RealSort>)) = RealLiteral(this) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqBigIntegerRealSort")
infix fun (() -> BigInteger).eq(expr: Expression<RealSort>) = RealLiteral(this()) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqBigIntegerRealSort")
infix fun (() -> BigInteger).eq(expr: (() -> Expression<RealSort>)) = RealLiteral(this()) eq expr()

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortBigInteger")
infix fun Expression<RealSort>.eq(other: BigInteger) = this eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortBigInteger")
infix fun Expression<RealSort>.eq(other: (() -> BigInteger)) = this eq RealLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortBigInteger")
infix fun (() -> Expression<RealSort>).eq(other: BigInteger) = this() eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortBigInteger")
infix fun (() -> Expression<RealSort>).eq(other: (() -> BigInteger)) =
    this() eq RealLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortBigIntegerEquals")
infix fun Equals<RealSort>.eq(other: BigInteger) = this eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortBigIntegerEquals")
infix fun Equals<RealSort>.eq(other: (() -> BigInteger)) = this eq RealLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortBigIntegerEquals")
infix fun (() -> Equals<RealSort>).eq(other: BigInteger) = this() eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortBigIntegerEquals")
infix fun (() -> Equals<RealSort>).eq(other: (() -> BigInteger)) = this() eq RealLiteral(other())

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqBigIntegerRealSortEquals")
infix fun BigInteger.eq(expr: Equals<RealSort>) = RealLiteral(this) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqBigIntegerRealSortEquals")
infix fun BigInteger.eq(expr: (() -> Equals<RealSort>)) = RealLiteral(this) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqBigIntegerRealSortEquals")
infix fun (() -> BigInteger).eq(expr: Equals<RealSort>) = RealLiteral(this()) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqBigIntegerRealSortEquals")
infix fun (() -> BigInteger).eq(expr: (() -> Equals<RealSort>)) = RealLiteral(this()) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqFloatRealSort")
infix fun Float.eq(expr: Expression<RealSort>) = RealLiteral(this) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqFloatRealSort")
infix fun Float.eq(expr: (() -> Expression<RealSort>)) = RealLiteral(this) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqFloatRealSort")
infix fun (() -> Float).eq(expr: Expression<RealSort>) = RealLiteral(this()) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqFloatRealSort")
infix fun (() -> Float).eq(expr: (() -> Expression<RealSort>)) = RealLiteral(this()) eq expr()

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortFloat")
infix fun Expression<RealSort>.eq(other: Float) = this eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortFloat")
infix fun Expression<RealSort>.eq(other: (() -> Float)) = this eq RealLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortFloat")
infix fun (() -> Expression<RealSort>).eq(other: Float) = this() eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortFloat")
infix fun (() -> Expression<RealSort>).eq(other: (() -> Float)) = this() eq RealLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortFloatEquals")
infix fun Equals<RealSort>.eq(other: Float) = this eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortFloatEquals")
infix fun Equals<RealSort>.eq(other: (() -> Float)) = this eq RealLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortFloatEquals")
infix fun (() -> Equals<RealSort>).eq(other: Float) = this() eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortFloatEquals")
infix fun (() -> Equals<RealSort>).eq(other: (() -> Float)) = this() eq RealLiteral(other())

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqFloatRealSortEquals")
infix fun Float.eq(expr: Equals<RealSort>) = RealLiteral(this) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqFloatRealSortEquals")
infix fun Float.eq(expr: (() -> Equals<RealSort>)) = RealLiteral(this) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqFloatRealSortEquals")
infix fun (() -> Float).eq(expr: Equals<RealSort>) = RealLiteral(this()) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqFloatRealSortEquals")
infix fun (() -> Float).eq(expr: (() -> Equals<RealSort>)) = RealLiteral(this()) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqDoubleRealSort")
infix fun Double.eq(expr: Expression<RealSort>) = RealLiteral(this) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqDoubleRealSort")
infix fun Double.eq(expr: (() -> Expression<RealSort>)) = RealLiteral(this) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqDoubleRealSort")
infix fun (() -> Double).eq(expr: Expression<RealSort>) = RealLiteral(this()) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqDoubleRealSort")
infix fun (() -> Double).eq(expr: (() -> Expression<RealSort>)) = RealLiteral(this()) eq expr()

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortDouble")
infix fun Expression<RealSort>.eq(other: Double) = this eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortDouble")
infix fun Expression<RealSort>.eq(other: (() -> Double)) = this eq RealLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortDouble")
infix fun (() -> Expression<RealSort>).eq(other: Double) = this() eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortDouble")
infix fun (() -> Expression<RealSort>).eq(other: (() -> Double)) = this() eq RealLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortDoubleEquals")
infix fun Equals<RealSort>.eq(other: Double) = this eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortDoubleEquals")
infix fun Equals<RealSort>.eq(other: (() -> Double)) = this eq RealLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortDoubleEquals")
infix fun (() -> Equals<RealSort>).eq(other: Double) = this() eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortDoubleEquals")
infix fun (() -> Equals<RealSort>).eq(other: (() -> Double)) = this() eq RealLiteral(other())

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqDoubleRealSortEquals")
infix fun Double.eq(expr: Equals<RealSort>) = RealLiteral(this) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqDoubleRealSortEquals")
infix fun Double.eq(expr: (() -> Equals<RealSort>)) = RealLiteral(this) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqDoubleRealSortEquals")
infix fun (() -> Double).eq(expr: Equals<RealSort>) = RealLiteral(this()) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqDoubleRealSortEquals")
infix fun (() -> Double).eq(expr: (() -> Equals<RealSort>)) = RealLiteral(this()) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqBigDecimalRealSort")
infix fun BigDecimal.eq(expr: Expression<RealSort>) = RealLiteral(this) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqBigDecimalRealSort")
infix fun BigDecimal.eq(expr: (() -> Expression<RealSort>)) = RealLiteral(this) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqBigDecimalRealSort")
infix fun (() -> BigDecimal).eq(expr: Expression<RealSort>) = RealLiteral(this()) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqBigDecimalRealSort")
infix fun (() -> BigDecimal).eq(expr: (() -> Expression<RealSort>)) = RealLiteral(this()) eq expr()

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortBigDecimal")
infix fun Expression<RealSort>.eq(other: BigDecimal) = this eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortBigDecimal")
infix fun Expression<RealSort>.eq(other: (() -> BigDecimal)) = this eq RealLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortBigDecimal")
infix fun (() -> Expression<RealSort>).eq(other: BigDecimal) = this() eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortBigDecimal")
infix fun (() -> Expression<RealSort>).eq(other: (() -> BigDecimal)) =
    this() eq RealLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortBigDecimalEquals")
infix fun Equals<RealSort>.eq(other: BigDecimal) = this eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortBigDecimalEquals")
infix fun Equals<RealSort>.eq(other: (() -> BigDecimal)) = this eq RealLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortBigDecimalEquals")
infix fun (() -> Equals<RealSort>).eq(other: BigDecimal) = this() eq RealLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [RealLiteral]
 */
@JvmName("eqRealSortBigDecimalEquals")
infix fun (() -> Equals<RealSort>).eq(other: (() -> BigDecimal)) = this() eq RealLiteral(other())

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqBigDecimalRealSortEquals")
infix fun BigDecimal.eq(expr: Equals<RealSort>) = RealLiteral(this) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqBigDecimalRealSortEquals")
infix fun BigDecimal.eq(expr: (() -> Equals<RealSort>)) = RealLiteral(this) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqBigDecimalRealSortEquals")
infix fun (() -> BigDecimal).eq(expr: Equals<RealSort>) = RealLiteral(this()) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [RealLiteral]
 */
@JvmName("eqBigDecimalRealSortEquals")
infix fun (() -> BigDecimal).eq(expr: (() -> Equals<RealSort>)) = RealLiteral(this()) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [StringLiteral]
 */
@JvmName("eqStringStringSort")
infix fun String.eq(expr: Expression<StringSort>) = StringLiteral(this) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [StringLiteral]
 */
@JvmName("eqStringStringSort")
infix fun String.eq(expr: (() -> Expression<StringSort>)) = StringLiteral(this) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [StringLiteral]
 */
@JvmName("eqStringStringSort")
infix fun (() -> String).eq(expr: Expression<StringSort>) = StringLiteral(this()) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [StringLiteral]
 */
@JvmName("eqStringStringSort")
infix fun (() -> String).eq(expr: (() -> Expression<StringSort>)) = StringLiteral(this()) eq expr()

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [StringLiteral]
 */
@JvmName("eqStringSortString")
infix fun Expression<StringSort>.eq(other: String) = this eq StringLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [StringLiteral]
 */
@JvmName("eqStringSortString")
infix fun Expression<StringSort>.eq(other: (() -> String)) = this eq StringLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [StringLiteral]
 */
@JvmName("eqStringSortString")
infix fun (() -> Expression<StringSort>).eq(other: String) = this() eq StringLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [StringLiteral]
 */
@JvmName("eqStringSortString")
infix fun (() -> Expression<StringSort>).eq(other: (() -> String)) =
    this() eq StringLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [StringLiteral]
 */
@JvmName("eqStringSortStringEquals")
infix fun Equals<StringSort>.eq(other: String) = this eq StringLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [StringLiteral]
 */
@JvmName("eqStringSortStringEquals")
infix fun Equals<StringSort>.eq(other: (() -> String)) = this eq StringLiteral(other())

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [StringLiteral]
 */
@JvmName("eqStringSortStringEquals")
infix fun (() -> Equals<StringSort>).eq(other: String) = this() eq StringLiteral(other)

/**
 * SMT equality (= [this] [other])
 * - [other] is converted to [StringLiteral]
 */
@JvmName("eqStringSortStringEquals")
infix fun (() -> Equals<StringSort>).eq(other: (() -> String)) = this() eq StringLiteral(other())

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [StringLiteral]
 */
@JvmName("eqStringStringSortEquals")
infix fun String.eq(expr: Equals<StringSort>) = StringLiteral(this) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [StringLiteral]
 */
@JvmName("eqStringStringSortEquals")
infix fun String.eq(expr: (() -> Equals<StringSort>)) = StringLiteral(this) eq expr()

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [StringLiteral]
 */
@JvmName("eqStringStringSortEquals")
infix fun (() -> String).eq(expr: Equals<StringSort>) = StringLiteral(this()) eq expr

/**
 * SMT equality (= [this] [expr])
 * - [this] is converted to [StringLiteral]
 */
@JvmName("eqStringStringSortEquals")
infix fun (() -> String).eq(expr: (() -> Equals<StringSort>)) = StringLiteral(this()) eq expr()

@JvmName("eqByteByte") infix fun Byte.eq(rhs: Byte) = IntEqBuffer(this.toLong(), rhs.toLong())

@JvmName("eqByteShort") infix fun Byte.eq(rhs: Short) = IntEqBuffer(this.toLong(), rhs.toLong())

@JvmName("eqByteInt") infix fun Byte.eq(rhs: Int) = IntEqBuffer(this.toLong(), rhs.toLong())

@JvmName("eqByteLong") infix fun Byte.eq(rhs: Long) = IntEqBuffer(this.toLong(), rhs)

@JvmName("eqByteByteLambda")
infix fun Byte.eq(rhs: (() -> Byte)) = IntEqBuffer(this.toLong(), rhs().toLong())

@JvmName("eqByteShortLambda")
infix fun Byte.eq(rhs: (() -> Short)) = IntEqBuffer(this.toLong(), rhs().toLong())

@JvmName("eqByteIntLambda")
infix fun Byte.eq(rhs: (() -> Int)) = IntEqBuffer(this.toLong(), rhs().toLong())

@JvmName("eqByteLongLambda")
infix fun Byte.eq(rhs: (() -> Long)) = IntEqBuffer(this.toLong(), rhs())

@JvmName("eqByteLambdaByte")
infix fun (() -> Byte).eq(rhs: Byte) = IntEqBuffer(this().toLong(), rhs.toLong())

@JvmName("eqByteLambdaShort")
infix fun (() -> Byte).eq(rhs: Short) = IntEqBuffer(this().toLong(), rhs.toLong())

@JvmName("eqByteLambdaInt")
infix fun (() -> Byte).eq(rhs: Int) = IntEqBuffer(this().toLong(), rhs.toLong())

@JvmName("eqByteLambdaLong")
infix fun (() -> Byte).eq(rhs: Long) = IntEqBuffer(this().toLong(), rhs)

@JvmName("eqByteLambdaByteLambda")
infix fun (() -> Byte).eq(rhs: (() -> Byte)) = IntEqBuffer(this().toLong(), rhs().toLong())

@JvmName("eqByteLambdaShortLambda")
infix fun (() -> Byte).eq(rhs: (() -> Short)) = IntEqBuffer(this().toLong(), rhs().toLong())

@JvmName("eqByteLambdaIntLambda")
infix fun (() -> Byte).eq(rhs: (() -> Int)) = IntEqBuffer(this().toLong(), rhs().toLong())

@JvmName("eqByteLambdaLongLambda")
infix fun (() -> Byte).eq(rhs: (() -> Long)) = IntEqBuffer(this().toLong(), rhs())

@JvmName("eqShortByte") infix fun Short.eq(rhs: Byte) = IntEqBuffer(this.toLong(), rhs.toLong())

@JvmName("eqShortShort") infix fun Short.eq(rhs: Short) = IntEqBuffer(this.toLong(), rhs.toLong())

@JvmName("eqShortInt") infix fun Short.eq(rhs: Int) = IntEqBuffer(this.toLong(), rhs.toLong())

@JvmName("eqShortLong") infix fun Short.eq(rhs: Long) = IntEqBuffer(this.toLong(), rhs)

@JvmName("eqShortByteLambda")
infix fun Short.eq(rhs: (() -> Byte)) = IntEqBuffer(this.toLong(), rhs().toLong())

@JvmName("eqShortShortLambda")
infix fun Short.eq(rhs: (() -> Short)) = IntEqBuffer(this.toLong(), rhs().toLong())

@JvmName("eqShortIntLambda")
infix fun Short.eq(rhs: (() -> Int)) = IntEqBuffer(this.toLong(), rhs().toLong())

@JvmName("eqShortLongLambda")
infix fun Short.eq(rhs: (() -> Long)) = IntEqBuffer(this.toLong(), rhs())

@JvmName("eqShortLambdaByte")
infix fun (() -> Short).eq(rhs: Byte) = IntEqBuffer(this().toLong(), rhs.toLong())

@JvmName("eqShortLambdaShort")
infix fun (() -> Short).eq(rhs: Short) = IntEqBuffer(this().toLong(), rhs.toLong())

@JvmName("eqShortLambdaInt")
infix fun (() -> Short).eq(rhs: Int) = IntEqBuffer(this().toLong(), rhs.toLong())

@JvmName("eqShortLambdaLong")
infix fun (() -> Short).eq(rhs: Long) = IntEqBuffer(this().toLong(), rhs)

@JvmName("eqShortLambdaByteLambda")
infix fun (() -> Short).eq(rhs: (() -> Byte)) = IntEqBuffer(this().toLong(), rhs().toLong())

@JvmName("eqShortLambdaShortLambda")
infix fun (() -> Short).eq(rhs: (() -> Short)) = IntEqBuffer(this().toLong(), rhs().toLong())

@JvmName("eqShortLambdaIntLambda")
infix fun (() -> Short).eq(rhs: (() -> Int)) = IntEqBuffer(this().toLong(), rhs().toLong())

@JvmName("eqShortLambdaLongLambda")
infix fun (() -> Short).eq(rhs: (() -> Long)) = IntEqBuffer(this().toLong(), rhs())

@JvmName("eqIntByte") infix fun Int.eq(rhs: Byte) = IntEqBuffer(this.toLong(), rhs.toLong())

@JvmName("eqIntShort") infix fun Int.eq(rhs: Short) = IntEqBuffer(this.toLong(), rhs.toLong())

@JvmName("eqIntInt") infix fun Int.eq(rhs: Int) = IntEqBuffer(this.toLong(), rhs.toLong())

@JvmName("eqIntLong") infix fun Int.eq(rhs: Long) = IntEqBuffer(this.toLong(), rhs)

@JvmName("eqIntByteLambda")
infix fun Int.eq(rhs: (() -> Byte)) = IntEqBuffer(this.toLong(), rhs().toLong())

@JvmName("eqIntShortLambda")
infix fun Int.eq(rhs: (() -> Short)) = IntEqBuffer(this.toLong(), rhs().toLong())

@JvmName("eqIntIntLambda")
infix fun Int.eq(rhs: (() -> Int)) = IntEqBuffer(this.toLong(), rhs().toLong())

@JvmName("eqIntLongLambda") infix fun Int.eq(rhs: (() -> Long)) = IntEqBuffer(this.toLong(), rhs())

@JvmName("eqIntLambdaByte")
infix fun (() -> Int).eq(rhs: Byte) = IntEqBuffer(this().toLong(), rhs.toLong())

@JvmName("eqIntLambdaShort")
infix fun (() -> Int).eq(rhs: Short) = IntEqBuffer(this().toLong(), rhs.toLong())

@JvmName("eqIntLambdaInt")
infix fun (() -> Int).eq(rhs: Int) = IntEqBuffer(this().toLong(), rhs.toLong())

@JvmName("eqIntLambdaLong") infix fun (() -> Int).eq(rhs: Long) = IntEqBuffer(this().toLong(), rhs)

@JvmName("eqIntLambdaByteLambda")
infix fun (() -> Int).eq(rhs: (() -> Byte)) = IntEqBuffer(this().toLong(), rhs().toLong())

@JvmName("eqIntLambdaShortLambda")
infix fun (() -> Int).eq(rhs: (() -> Short)) = IntEqBuffer(this().toLong(), rhs().toLong())

@JvmName("eqIntLambdaIntLambda")
infix fun (() -> Int).eq(rhs: (() -> Int)) = IntEqBuffer(this().toLong(), rhs().toLong())

@JvmName("eqIntLambdaLongLambda")
infix fun (() -> Int).eq(rhs: (() -> Long)) = IntEqBuffer(this().toLong(), rhs())

@JvmName("eqLongByte") infix fun Long.eq(rhs: Byte) = IntEqBuffer(this.toLong(), rhs.toLong())

@JvmName("eqLongShort") infix fun Long.eq(rhs: Short) = IntEqBuffer(this.toLong(), rhs.toLong())

@JvmName("eqLongInt") infix fun Long.eq(rhs: Int) = IntEqBuffer(this.toLong(), rhs.toLong())

@JvmName("eqLongLong") infix fun Long.eq(rhs: Long) = IntEqBuffer(this.toLong(), rhs)

@JvmName("eqLongByteLambda")
infix fun Long.eq(rhs: (() -> Byte)) = IntEqBuffer(this.toLong(), rhs().toLong())

@JvmName("eqLongShortLambda")
infix fun Long.eq(rhs: (() -> Short)) = IntEqBuffer(this.toLong(), rhs().toLong())

@JvmName("eqLongIntLambda")
infix fun Long.eq(rhs: (() -> Int)) = IntEqBuffer(this.toLong(), rhs().toLong())

@JvmName("eqLongLongLambda")
infix fun Long.eq(rhs: (() -> Long)) = IntEqBuffer(this.toLong(), rhs())

@JvmName("eqLongLambdaByte")
infix fun (() -> Long).eq(rhs: Byte) = IntEqBuffer(this().toLong(), rhs.toLong())

@JvmName("eqLongLambdaShort")
infix fun (() -> Long).eq(rhs: Short) = IntEqBuffer(this().toLong(), rhs.toLong())

@JvmName("eqLongLambdaInt")
infix fun (() -> Long).eq(rhs: Int) = IntEqBuffer(this().toLong(), rhs.toLong())

@JvmName("eqLongLambdaLong")
infix fun (() -> Long).eq(rhs: Long) = IntEqBuffer(this().toLong(), rhs)

@JvmName("eqLongLambdaByteLambda")
infix fun (() -> Long).eq(rhs: (() -> Byte)) = IntEqBuffer(this().toLong(), rhs().toLong())

@JvmName("eqLongLambdaShortLambda")
infix fun (() -> Long).eq(rhs: (() -> Short)) = IntEqBuffer(this().toLong(), rhs().toLong())

@JvmName("eqLongLambdaIntLambda")
infix fun (() -> Long).eq(rhs: (() -> Int)) = IntEqBuffer(this().toLong(), rhs().toLong())

@JvmName("eqLongLambdaLongLambda")
infix fun (() -> Long).eq(rhs: (() -> Long)) = IntEqBuffer(this().toLong(), rhs())

/** Can later be converted to [Equals] of either [IntSort], [RealSort] or [FPSort]. */
class IntEqBuffer(lhs: Long, rhs: Long) {

  /** Store all arguments as Number, we can later convert all to Long with loss of information */
  private val buffer = mutableListOf<Number>(lhs, rhs)

  infix fun eq(rhs: Byte) = this.apply { buffer.add(rhs) }

  infix fun eq(rhs: Short) = this.apply { buffer.add(rhs) }

  infix fun eq(rhs: Int) = this.apply { buffer.add(rhs) }

  infix fun eq(rhs: Long) = this.apply { buffer.add(rhs) }

  @JvmName("eqBufferByteLambda") infix fun eq(rhs: (() -> Byte)) = this.apply { buffer.add(rhs()) }

  @JvmName("eqBufferShortLambda")
  infix fun eq(rhs: (() -> Short)) = this.apply { buffer.add(rhs()) }

  @JvmName("eqBufferIntLambda") infix fun eq(rhs: (() -> Int)) = this.apply { buffer.add(rhs()) }

  @JvmName("eqBufferLongLambda") infix fun eq(rhs: (() -> Long)) = this.apply { buffer.add(rhs()) }

  infix fun eq(expr: Expression<IntSort>) = Equals(buffer.map { IntLiteral(it.toLong()) } + expr)

  @JvmName("eqBufferFinalizeRealSort")
  infix fun eq(expr: Expression<RealSort>) = Equals(buffer.map { RealLiteral(it.toLong()) } + expr)

  /**
   * Note that conversion to float is only possible for [expr] of sort Float32 (_ FloatingPoint
   * 8 24) or Float64 (_ FloatingPoint 11 53).
   */
  @JvmName("eqBufferFinalizeFloatingPointSort")
  infix fun eq(expr: Expression<FPSort>) =
      Equals(
          buffer.map {
            if (expr.sort.exponentBits == 8 && expr.sort.significantBits == 24) {
              FPLiteral(it.toFloat())
            } else if (expr.sort.exponentBits == 11 && expr.sort.significantBits == 53) {
              FPLiteral(it.toDouble())
            } else {
              throw RuntimeException(
                  "Kotlin floating points can not be converted to sort ${expr.sort}, use (_ FloatingPoint 8 24) or (_ FloatingPoint 11 53)."
              )
            }
          } + expr
      )
}

@JvmName("eqFloatFloat")
infix fun Float.eq(rhs: Float) = RealEqBuffer(this.toDouble(), rhs.toDouble())

@JvmName("eqFloatFloatLambda")
infix fun Float.eq(rhs: (() -> Float)) = RealEqBuffer(this.toDouble(), rhs().toDouble())

@JvmName("eqFloatDouble") infix fun Float.eq(rhs: Double) = RealEqBuffer(this.toDouble(), rhs)

@JvmName("eqFloatDoubleLambda")
infix fun Float.eq(rhs: (() -> Double)) = RealEqBuffer(this.toDouble(), rhs())

@JvmName("eqFloatLambdaFloat")
infix fun (() -> Float).eq(rhs: Float) = RealEqBuffer(this().toDouble(), rhs.toDouble())

@JvmName("eqFloatLambdaFloatLambda")
infix fun (() -> Float).eq(rhs: (() -> Float)) = RealEqBuffer(this().toDouble(), rhs().toDouble())

@JvmName("eqFloatLambdaDouble")
infix fun (() -> Float).eq(rhs: Double) = RealEqBuffer(this().toDouble(), rhs)

@JvmName("eqFloatLambdaDoubleLambda")
infix fun (() -> Float).eq(rhs: (() -> Double)) = RealEqBuffer(this().toDouble(), rhs())

@JvmName("eqDoubleFloat") infix fun Double.eq(rhs: Float) = RealEqBuffer(this, rhs.toDouble())

@JvmName("eqDoubleFloatLambda")
infix fun Double.eq(rhs: (() -> Float)) = RealEqBuffer(this, rhs().toDouble())

@JvmName("eqDoubleDouble") infix fun Double.eq(rhs: Double) = RealEqBuffer(this, rhs)

@JvmName("eqDoubleDoubleLambda")
infix fun Double.eq(rhs: (() -> Double)) = RealEqBuffer(this, rhs())

@JvmName("eqDoubleLambdaFloat")
infix fun (() -> Double).eq(rhs: Float) = RealEqBuffer(this(), rhs.toDouble())

@JvmName("eqDoubleLambdaFloatLambda")
infix fun (() -> Double).eq(rhs: (() -> Float)) = RealEqBuffer(this(), rhs().toDouble())

@JvmName("eqDoubleLambdaDouble")
infix fun (() -> Double).eq(rhs: Double) = RealEqBuffer(this(), rhs)

@JvmName("eqDoubleLambdaDoubleLambda")
infix fun (() -> Double).eq(rhs: (() -> Double)) = RealEqBuffer(this(), rhs())

/** Can later be converted to [Equals] of either [RealSort] or [FPSort]. */
class RealEqBuffer(lhs: Double, rhs: Double) {

  /** Store all arguments as Number, we can later convert all to Double with loss of information */
  private val buffer = mutableListOf<Number>(lhs, rhs)

  infix fun eq(rhs: Number) = this.apply { buffer.add(rhs) }

  @JvmName("eqBufferNumberLambda")
  infix fun eq(rhs: (() -> Number)) = this.apply { buffer.add(rhs()) }

  @JvmName("eqBufferFinalizeRealSort")
  infix fun eq(expr: Expression<RealSort>) =
      Equals(buffer.map { RealLiteral(it.toDouble()) } + expr)

  /**
   * Note that conversion to float is only possible for [expr] of sort Float32 (_ FloatingPoint
   * 8 24) or Float64 (_ FloatingPoint 11 53).
   */
  @JvmName("eqBufferFinalizeFloatingPointSort")
  infix fun eq(expr: Expression<FPSort>) =
      Equals(
          buffer.map {
            if (expr.sort.exponentBits == 8 && expr.sort.significantBits == 24) {
              FPLiteral(it.toFloat())
            } else if (expr.sort.exponentBits == 11 && expr.sort.significantBits == 53) {
              FPLiteral(it.toDouble())
            } else {
              throw RuntimeException(
                  "Kotlin floating points can not be converted to sort ${expr.sort}, use (_ FloatingPoint 8 24) or (_ FloatingPoint 11 53)."
              )
            }
          } + expr
      )
}

fun main() {
  smt(QF_UF) {
    val expr = const(SMTInt)
    val temp = 1 eq 1 eq 1 eq expr

    assert { temp eq 1 }
  }
}

/** Creates a distinct: [this] distinct [other]. */
infix fun <T : Sort> Expression<T>.distinct(other: Expression<T>): Distinct<T> =
    Distinct(this, other)

/** Creates a distinct: [this] distinct [other]. */
infix fun <T : Sort> Distinct<T>.distinct(other: Expression<T>): Distinct<T> =
    Distinct(this.children + other)

private fun makeBoolOperator(
    init: Builder<BoolSort>.() -> Unit,
    op: (List<Expression<BoolSort>>) -> Expression<BoolSort>,
): Expression<BoolSort> {
  val builder = Builder<BoolSort>()
  builder.init()

  return op(builder.children)
}

/**
 * Lambda version of logical [And].
 *
 * Use [Builder.unaryPlus] inside [init] to add [Expression]s to the 'And' expression.
 */
fun and(init: Builder<BoolSort>.() -> Unit) = makeBoolOperator(init, ::And)

/**
 * Lambda version of logical [Or].
 *
 * Use [Builder.unaryPlus] inside [init] to add [Expression]s to the 'Or' expression.
 */
fun or(init: Builder<BoolSort>.() -> Unit) = makeBoolOperator(init, ::Or)

/**
 * Lambda version of logical [XOr].
 *
 * Use [Builder.unaryPlus] inside [init] to add [Expression]s to the 'XOr' expression.
 */
fun xor(init: Builder<BoolSort>.() -> Unit) = makeBoolOperator(init, ::XOr)

/**
 * Lambda version of logical [Equals].
 *
 * Use [Builder.unaryPlus] inside [init] to add [Expression]s to the 'Equals' expression.
 */
fun <T : Sort> eq(init: Builder<T>.() -> Unit): Equals<T> {
  val builder = Builder<T>()
  builder.init()

  return Equals(builder.children)
}

/**
 * Lambda version of logical [Distinct].
 *
 * Use [Builder.unaryPlus] inside [init] to add [Expression]s to the 'Distinct' expression.
 */
fun <T : Sort> distinct(init: Builder<T>.() -> Unit): Distinct<T> {
  val builder = Builder<T>()
  builder.init()

  return Distinct(builder.children)
}

/** Implements logical not operation. */
fun not(block: () -> Expression<BoolSort>): Not = Not(block())

/** Implements logical not operation. */
fun not(expr: Expression<BoolSort>): Not = Not(expr)

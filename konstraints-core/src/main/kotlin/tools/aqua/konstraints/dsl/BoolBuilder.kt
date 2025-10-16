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
import tools.aqua.konstraints.smt.Implies
import tools.aqua.konstraints.smt.IntLiteral
import tools.aqua.konstraints.smt.IntSort
import tools.aqua.konstraints.smt.Not
import tools.aqua.konstraints.smt.Or
import tools.aqua.konstraints.smt.RealLiteral
import tools.aqua.konstraints.smt.RealSort
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

// allow chaining of equals
/** Creates (eq [this] [other]). */
infix fun <T : Sort> Equals<T>.eq(other: Expression<T>) = Equals(children + other)

/** Creates (eq [this] [other]). */
infix fun <T : Sort> Expression<T>.eq(other: () -> Expression<T>) = this eq other()

/** Creates (eq [this] [other]). */
infix fun <T : Sort> (() -> Expression<T>).eq(other: Expression<T>) = this() eq other

/** Creates (eq [this] [other]). */
infix fun <T : Sort> (() -> Expression<T>).eq(other: () -> Expression<T>) = this() eq other()

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

/** Creates a distinct: [this] distinct [other]. */
infix fun <T : Sort> Expression<T>.distinct(other: Expression<T>): Distinct<T> =
    Distinct(this, other)

/** Creates a distinct: [this] distinct [other]. */
infix fun <T : Sort> Distinct<T>.distinct(other: Expression<T>): Distinct<T> =
    Distinct(this.children + other)

private fun makeBoolOperator(
    init: Builder<BoolSort>.() -> Unit,
    op: (List<Expression<BoolSort>>) -> Expression<BoolSort>
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

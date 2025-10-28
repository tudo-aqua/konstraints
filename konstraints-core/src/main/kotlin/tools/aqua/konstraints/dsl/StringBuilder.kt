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

import java.math.BigInteger
import tools.aqua.konstraints.smt.*

/** String concatenation. */
infix fun Expression<StringSort>.concat(rhs: Expression<StringSort>) =
    if (this is StrConcat) {
      StrConcat(this.children + rhs)
    } else {
      StrConcat(this, rhs)
    }

/**
 * String concatenation.
 * - [rhs] is converted to [StringLiteral] .
 */
@JvmName("concatStringSortString")
infix fun Expression<StringSort>.concat(rhs: String) = this concat StringLiteral(rhs)

/** String concatenation. */
@JvmName("concatStringSortStringSortLambda")
infix fun Expression<StringSort>.concat(rhs: (() -> Expression<StringSort>)) = this concat rhs()

/**
 * String concatenation.
 * - [rhs] is converted to [StringLiteral] .
 */
@JvmName("concatStringSortStringLambda")
infix fun Expression<StringSort>.concat(rhs: (() -> String)) = this concat StringLiteral(rhs())

/** String concatenation. */
@JvmName("concatStringSortLambdaStringSort")
infix fun (() -> Expression<StringSort>).concat(rhs: Expression<StringSort>) = this() concat rhs

/**
 * String concatenation.
 * - [rhs] is converted to [StringLiteral]
 */
@JvmName("concatStringSortLambdaString")
infix fun (() -> Expression<StringSort>).concat(rhs: String) = this() concat StringLiteral(rhs)

/** String concatenation. */
@JvmName("concatStringSortLambdaStringSortLambda")
infix fun (() -> Expression<StringSort>).concat(rhs: (() -> Expression<StringSort>)) =
    this() concat rhs()

/**
 * String concatenation.
 * - [rhs] is converted to [StringLiteral]
 */
@JvmName("concatStringSortLambdaStringLambda")
infix fun (() -> Expression<StringSort>).concat(rhs: (() -> String)) =
    this() concat StringLiteral(rhs())

/**
 * String concatenation.
 * - [String] is converted to [StringLiteral] .
 */
@JvmName("concatStringStringSort")
infix fun String.concat(rhs: Expression<StringSort>) = StringLiteral(this) concat rhs

/**
 * String concatenation.
 * - [String] is converted to [StringLiteral]
 * - [rhs] is converted to [StringLiteral] .
 */
@JvmName("concatStringString")
infix fun String.concat(rhs: String) = StringLiteral(this) concat StringLiteral(rhs)

/**
 * String concatenation.
 * - [String] is converted to [StringLiteral] .
 */
@JvmName("concatStringStringSortLambda")
infix fun String.concat(rhs: (() -> Expression<StringSort>)) = StringLiteral(this) concat rhs()

/**
 * String concatenation.
 * - [String] is converted to [StringLiteral]
 * - [rhs] is converted to [StringLiteral] .
 */
@JvmName("concatStringStringLambda")
infix fun String.concat(rhs: (() -> String)) = StringLiteral(this) concat StringLiteral(rhs())

/** String concatenation. */
@JvmName("concatStringLambdaStringSort")
infix fun (() -> String).concat(rhs: Expression<StringSort>) = StringLiteral(this()) concat rhs

/**
 * String concatenation.
 * - [rhs] is converted to [StringLiteral]
 */
@JvmName("concatStringLambdaString")
infix fun (() -> String).concat(rhs: String) = StringLiteral(this()) concat StringLiteral(rhs)

/** String concatenation. */
@JvmName("concatStringLambdaStringSortLambda")
infix fun (() -> String).concat(rhs: (() -> Expression<StringSort>)) =
    StringLiteral(this()) concat rhs()

/**
 * String concatenation.
 * - [rhs] is converted to [StringLiteral]
 */
@JvmName("concatStringLambdaStringLambda")
infix fun (() -> String).concat(rhs: (() -> String)) =
    StringLiteral(this()) concat StringLiteral(rhs())

/** String concatenation. */
infix operator fun Expression<StringSort>.plus(rhs: Expression<StringSort>) = this concat rhs

/**
 * String concatenation.
 * - [rhs] is converted to [StringLiteral]
 */
@JvmName("plusStringSortString")
infix operator fun Expression<StringSort>.plus(rhs: String) = this plus StringLiteral(rhs)

/** String concatenation. */
@JvmName("plusStringSortStringSortLambda")
infix operator fun Expression<StringSort>.plus(rhs: (() -> Expression<StringSort>)) =
    this plus rhs()

/**
 * String concatenation.
 * - [rhs] is converted to [StringLiteral]
 */
@JvmName("plusStringSortStringLambda")
infix operator fun Expression<StringSort>.plus(rhs: (() -> String)) = this plus StringLiteral(rhs())

/** String concatenation. */
@JvmName("plusStringSortLambdaStringSort")
infix operator fun (() -> Expression<StringSort>).plus(rhs: Expression<StringSort>) =
    this() plus rhs

/**
 * String concatenation.
 * - [rhs] is converted to [StringLiteral]
 */
@JvmName("plusStringSortLambdaString")
infix operator fun (() -> Expression<StringSort>).plus(rhs: String) = this() plus StringLiteral(rhs)

/** String concatenation. */
@JvmName("plusStringSortLambdaStringSortLambda")
infix operator fun (() -> Expression<StringSort>).plus(rhs: (() -> Expression<StringSort>)) =
    this() plus rhs()

/**
 * String concatenation.
 * - [rhs] is converted to [StringLiteral]
 */
@JvmName("plusStringSortLambdaStringLambda")
infix operator fun (() -> Expression<StringSort>).plus(rhs: (() -> String)) =
    this() plus StringLiteral(rhs())

/**
 * String concatenation.
 * - [String] is converted to [StringLiteral]
 */
@JvmName("plusStringStringSort")
infix operator fun String.plus(rhs: Expression<StringSort>) = StringLiteral(this) plus rhs

/**
 * String concatenation.
 * - [String] is converted to [StringLiteral]
 */
@JvmName("plusStringStringSortLambda")
infix operator fun String.plus(rhs: (() -> Expression<StringSort>)) = StringLiteral(this) plus rhs()

/** String concatenation. */
@JvmName("plusStringLambdaStringSort")
infix operator fun (() -> String).plus(rhs: Expression<StringSort>) = StringLiteral(this()) plus rhs

/** String concatenation. */
@JvmName("plusStringLambdaStringSortLambda")
infix operator fun (() -> String).plus(rhs: (() -> Expression<StringSort>)) =
    StringLiteral(this()) plus rhs()

/** String length. */
fun Expression<StringSort>.length() = StrLength(this)

/** String length. */
@JvmName("lengthStringSortLambda") fun (() -> Expression<StringSort>).length() = this().length()

/** Lexicographic ordering. */
infix fun Expression<StringSort>.lt(rhs: Expression<StringSort>) =
    if (this is StrLexOrder) {
      StrLexOrder(this.children + rhs)
    } else {
      StrLexOrder(this, rhs)
    }

/**
 * Lexicographic ordering.
 * - [rhs] is converted to [StringLiteral] .
 */
@JvmName("ltStringSortString")
infix fun Expression<StringSort>.lt(rhs: String) = this lt StringLiteral(rhs)

/** Lexicographic ordering. */
@JvmName("ltStringSortStringSortLambda")
infix fun Expression<StringSort>.lt(rhs: (() -> Expression<StringSort>)) = this lt rhs()

/**
 * Lexicographic ordering.
 * - [rhs] is converted to [StringLiteral] .
 */
@JvmName("ltStringSortStringLambda")
infix fun Expression<StringSort>.lt(rhs: (() -> String)) = this lt StringLiteral(rhs())

/** Lexicographic ordering. */
@JvmName("ltStringSortLambdaStringSort")
infix fun (() -> Expression<StringSort>).lt(rhs: Expression<StringSort>) = this() lt rhs

/**
 * Lexicographic ordering.
 * - [rhs] is converted to [StringLiteral]
 */
@JvmName("ltStringSortLambdaString")
infix fun (() -> Expression<StringSort>).lt(rhs: String) = this() lt StringLiteral(rhs)

/** Lexicographic ordering. */
@JvmName("ltStringSortLambdaStringSortLambda")
infix fun (() -> Expression<StringSort>).lt(rhs: (() -> Expression<StringSort>)) = this() lt rhs()

/**
 * Lexicographic ordering.
 * - [rhs] is converted to [StringLiteral]
 */
@JvmName("ltStringSortLambdaStringLambda")
infix fun (() -> Expression<StringSort>).lt(rhs: (() -> String)) = this() lt StringLiteral(rhs())

/**
 * Lexicographic ordering.
 * - [String] is converted to [StringLiteral] .
 */
@JvmName("ltStringStringSort")
infix fun String.lt(rhs: Expression<StringSort>) = StringLiteral(this) lt rhs

/**
 * Lexicographic ordering.
 * - [String] is converted to [StringLiteral]
 * - [rhs] is converted to [StringLiteral] .
 */
@JvmName("ltStringString")
infix fun String.lt(rhs: String) = StringLiteral(this) lt StringLiteral(rhs)

/**
 * Lexicographic ordering.
 * - [String] is converted to [StringLiteral] .
 */
@JvmName("ltStringStringSortLambda")
infix fun String.lt(rhs: (() -> Expression<StringSort>)) = StringLiteral(this) lt rhs()

/**
 * Lexicographic ordering.
 * - [String] is converted to [StringLiteral]
 * - [rhs] is converted to [StringLiteral] .
 */
@JvmName("ltStringStringLambda")
infix fun String.lt(rhs: (() -> String)) = StringLiteral(this) lt StringLiteral(rhs())

/** Lexicographic ordering. */
@JvmName("ltStringLambdaStringSort")
infix fun (() -> String).lt(rhs: Expression<StringSort>) = StringLiteral(this()) lt rhs

/**
 * Lexicographic ordering.
 * - [rhs] is converted to [StringLiteral]
 */
@JvmName("ltStringLambdaString")
infix fun (() -> String).lt(rhs: String) = StringLiteral(this()) lt StringLiteral(rhs)

/** Lexicographic ordering. */
@JvmName("ltStringLambdaStringSortLambda")
infix fun (() -> String).lt(rhs: (() -> Expression<StringSort>)) = StringLiteral(this()) lt rhs()

/**
 * Lexicographic ordering.
 * - [rhs] is converted to [StringLiteral]
 */
@JvmName("ltStringLambdaStringLambda")
infix fun (() -> String).lt(rhs: (() -> String)) = StringLiteral(this()) lt StringLiteral(rhs())

/** String to Regex injection. */
fun Expression<StringSort>.toRe() = StrToRe(this)

/**
 * String to Regex injection.
 * - [this] is converted to [StringLiteral]
 */
@JvmName("toReString") fun String.toRe() = StringLiteral(this).toRe()

/** String to Regex injection. */
@JvmName("toReStringSortLambda") fun (() -> Expression<StringSort>).toRe() = this().toRe()

/**
 * String to Regex injection.
 * - [this] is converted to [StringLiteral]
 */
@JvmName("toReStringLambda") fun (() -> String).toRe() = StringLiteral(this()).toRe()

/** Regex membership. */
infix fun Expression<StringSort>.in_re(regex: Expression<RegLanSort>) = StrInRe(this, regex)

/**
 * Regex membership.
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("in_reStringSortString")
infix fun Expression<StringSort>.in_re(regex: String) = this in_re StringLiteral(regex).toRe()

/** Regex membership. */
@JvmName("in_reStringSortRegLanSortLambda")
infix fun Expression<StringSort>.in_re(regex: (() -> Expression<RegLanSort>)) = this in_re regex()

/**
 * Regex membership.
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("in_reStringSortStringLambda")
infix fun Expression<StringSort>.in_re(regex: (() -> String)) =
    this in_re StringLiteral(regex()).toRe()

/** Regex membership. */
@JvmName("in_reStringSortLambdaRegLanSort")
infix fun (() -> Expression<StringSort>).in_re(regex: Expression<RegLanSort>) = this() in_re regex

/**
 * Regex membership.
 * - [regex] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("in_reStringSortLambdaString")
infix fun (() -> Expression<StringSort>).in_re(regex: String) =
    this() in_re StringLiteral(regex).toRe()

/** Regex membership. */
@JvmName("in_reStringSortLambdaRegLanSortLambda")
infix fun (() -> Expression<StringSort>).in_re(regex: (() -> Expression<RegLanSort>)) =
    this() in_re regex()

/**
 * Regex membership.
 * - [regex] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("in_reStringSortLambdaStringLambda")
infix fun (() -> Expression<StringSort>).in_re(regex: (() -> String)) =
    this() in_re StringLiteral(regex()).toRe()

/**
 * Regex membership.
 * - [String] is converted to [StringLiteral] .
 */
@JvmName("in_reStringRegLanSort")
infix fun String.in_re(regex: Expression<RegLanSort>) = StringLiteral(this) in_re regex

/**
 * Regex membership.
 * - [String] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("in_reStringString")
infix fun String.in_re(regex: String) = StringLiteral(this) in_re StringLiteral(regex).toRe()

/**
 * Regex membership.
 * - [String] is converted to [StringLiteral] .
 */
@JvmName("in_reStringRegLanSortLambda")
infix fun String.in_re(regex: (() -> Expression<RegLanSort>)) = StringLiteral(this) in_re regex()

/**
 * Regex membership.
 * - [String] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("in_reStringStringLambda")
infix fun String.in_re(regex: (() -> String)) =
    StringLiteral(this) in_re StringLiteral(regex()).toRe()

/** Regex membership. */
@JvmName("in_reStringLambdaRegLanSort")
infix fun (() -> String).in_re(regex: Expression<RegLanSort>) = StringLiteral(this()) in_re regex

/**
 * Regex membership.
 * - [regex] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("in_reStringLambdaString")
infix fun (() -> String).in_re(regex: String) =
    StringLiteral(this()) in_re StringLiteral(regex).toRe()

/** Regex membership. */
@JvmName("in_reStringLambdaRegLanSortLambda")
infix fun (() -> String).in_re(regex: (() -> Expression<RegLanSort>)) =
    StringLiteral(this()) in_re regex()

/**
 * Regex membership.
 * - [regex] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("in_reStringLambdaStringLambda")
infix fun (() -> String).in_re(regex: (() -> String)) =
    StringLiteral(this()) in_re StringLiteral(regex()).toRe()

/** Regex concatenation. */
infix fun Expression<RegLanSort>.concat(rhs: Expression<RegLanSort>) =
    if (this is RegexConcat) {
      RegexConcat(this.children + rhs)
    } else {
      RegexConcat(this, rhs)
    }

/**
 * Regex concatenation.
 * - [rhs] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("concatRegLanSortString")
infix fun Expression<RegLanSort>.concat(rhs: String) = this concat StringLiteral(rhs).toRe()

/** Regex concatenation. */
@JvmName("concatRegLanSortRegLanSortLambda")
infix fun Expression<RegLanSort>.concat(rhs: (() -> Expression<RegLanSort>)) = this concat rhs()

/**
 * Regex concatenation.
 * - [rhs] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("concatRegLanSortStringLambda")
infix fun Expression<RegLanSort>.concat(rhs: (() -> String)) =
    this concat StringLiteral(rhs()).toRe()

/** Regex concatenation. */
@JvmName("concatRegLanSortLambdaRegLanSort")
infix fun (() -> Expression<RegLanSort>).concat(rhs: Expression<RegLanSort>) = this() concat rhs

/**
 * Regex concatenation.
 * - [rhs] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("concatRegLanSortLambdaString")
infix fun (() -> Expression<RegLanSort>).concat(rhs: String) =
    this() concat StringLiteral(rhs).toRe()

/** Regex concatenation. */
@JvmName("concatRegLanSortLambdaRegLanSortLambda")
infix fun (() -> Expression<RegLanSort>).concat(rhs: (() -> Expression<RegLanSort>)) =
    this() concat rhs()

/**
 * Regex concatenation.
 * - [rhs] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("concatRegLanSortLambdaStringLambda")
infix fun (() -> Expression<RegLanSort>).concat(rhs: (() -> String)) =
    this() concat StringLiteral(rhs()).toRe()

/** Regex concatenation. */
infix operator fun Expression<RegLanSort>.times(rhs: Expression<RegLanSort>) = this concat rhs

/**
 * Regex concatenation.
 * - [rhs] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("timesRegLanSortString")
infix operator fun Expression<RegLanSort>.times(rhs: String) = this times StringLiteral(rhs).toRe()

/** Regex concatenation. */
@JvmName("timesRegLanSortRegLanSortLambda")
infix operator fun Expression<RegLanSort>.times(rhs: (() -> Expression<RegLanSort>)) =
    this times rhs()

/**
 * Regex concatenation.
 * - [rhs] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("timesRegLanSortStringLambda")
infix operator fun Expression<RegLanSort>.times(rhs: (() -> String)) =
    this times StringLiteral(rhs()).toRe()

/** Regex concatenation. */
@JvmName("timesRegLanSortLambdaRegLanSort")
infix operator fun (() -> Expression<RegLanSort>).times(rhs: Expression<RegLanSort>) =
    this() times rhs

/**
 * Regex concatenation.
 * - [rhs] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("timesRegLanSortLambdaString")
infix operator fun (() -> Expression<RegLanSort>).times(rhs: String) =
    this() times StringLiteral(rhs).toRe()

/** Regex concatenation. */
@JvmName("timesRegLanSortLambdaRegLanSortLambda")
infix operator fun (() -> Expression<RegLanSort>).times(rhs: (() -> Expression<RegLanSort>)) =
    this() times rhs()

/**
 * Regex concatenation.
 * - [rhs] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("timesRegLanSortLambdaStringLambda")
infix operator fun (() -> Expression<RegLanSort>).times(rhs: (() -> String)) =
    this() times StringLiteral(rhs()).toRe()

/**
 * Regex concatenation.
 * - [String] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("timesStringRegLanSort")
infix operator fun String.times(rhs: Expression<RegLanSort>) = StringLiteral(this).toRe() times rhs

/**
 * Regex concatenation.
 * - [String] is converted to [Expression] of type [RegLanSort]
 * - [rhs] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("timesStringString")
infix operator fun String.times(rhs: String) =
    StringLiteral(this).toRe() times StringLiteral(rhs).toRe()

/**
 * Regex concatenation.
 * - [String] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("timesStringRegLanSortLambda")
infix operator fun String.times(rhs: (() -> Expression<RegLanSort>)) =
    StringLiteral(this).toRe() times rhs()

/**
 * Regex concatenation.
 * - [String] is converted to [Expression] of type [RegLanSort]
 * - [rhs] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("timesStringStringLambda")
infix operator fun String.times(rhs: (() -> String)) =
    StringLiteral(this).toRe() times StringLiteral(rhs()).toRe()

/** Regex concatenation. */
@JvmName("timesStringLambdaRegLanSort")
infix operator fun (() -> String).times(rhs: Expression<RegLanSort>) =
    StringLiteral(this()).toRe() times rhs

/**
 * Regex concatenation.
 * - [rhs] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("timesStringLambdaString")
infix operator fun (() -> String).times(rhs: String) =
    StringLiteral(this()).toRe() times StringLiteral(rhs).toRe()

/** Regex concatenation. */
@JvmName("timesStringLambdaRegLanSortLambda")
infix operator fun (() -> String).times(rhs: (() -> Expression<RegLanSort>)) =
    StringLiteral(this()).toRe() times rhs()

/**
 * Regex concatenation.
 * - [rhs] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("timesStringLambdaStringLambda")
infix operator fun (() -> String).times(rhs: (() -> String)) =
    StringLiteral(this()).toRe() times StringLiteral(rhs()).toRe()

/** Regex union. */
infix fun Expression<RegLanSort>.union(rhs: Expression<RegLanSort>) =
    if (this is RegexUnion) {
      RegexUnion(this.children + rhs)
    } else {
      RegexUnion(this, rhs)
    }

/**
 * Regex union.
 * - [rhs] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("unionRegLanSortString")
infix fun Expression<RegLanSort>.union(rhs: String) = this union StringLiteral(rhs).toRe()

/** Regex union. */
@JvmName("unionRegLanSortRegLanSortLambda")
infix fun Expression<RegLanSort>.union(rhs: (() -> Expression<RegLanSort>)) = this union rhs()

/**
 * Regex union.
 * - [rhs] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("unionRegLanSortStringLambda")
infix fun Expression<RegLanSort>.union(rhs: (() -> String)) = this union StringLiteral(rhs()).toRe()

/** Regex union. */
@JvmName("unionRegLanSortLambdaRegLanSort")
infix fun (() -> Expression<RegLanSort>).union(rhs: Expression<RegLanSort>) = this() union rhs

/**
 * Regex union.
 * - [rhs] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("unionRegLanSortLambdaString")
infix fun (() -> Expression<RegLanSort>).union(rhs: String) = this() union StringLiteral(rhs).toRe()

/** Regex union. */
@JvmName("unionRegLanSortLambdaRegLanSortLambda")
infix fun (() -> Expression<RegLanSort>).union(rhs: (() -> Expression<RegLanSort>)) =
    this() union rhs()

/**
 * Regex union.
 * - [rhs] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("unionRegLanSortLambdaStringLambda")
infix fun (() -> Expression<RegLanSort>).union(rhs: (() -> String)) =
    this() union StringLiteral(rhs()).toRe()

/**
 * Regex union.
 * - [String] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("unionStringRegLanSort")
infix fun String.union(rhs: Expression<RegLanSort>) = StringLiteral(this).toRe() union rhs

/**
 * Regex union.
 * - [String] is converted to [Expression] of type [RegLanSort]
 * - [rhs] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("unionStringString")
infix fun String.union(rhs: String) = StringLiteral(this).toRe() union StringLiteral(rhs).toRe()

/**
 * Regex union.
 * - [String] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("unionStringRegLanSortLambda")
infix fun String.union(rhs: (() -> Expression<RegLanSort>)) = StringLiteral(this).toRe() union rhs()

/**
 * Regex union.
 * - [String] is converted to [Expression] of type [RegLanSort]
 * - [rhs] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("unionStringStringLambda")
infix fun String.union(rhs: (() -> String)) =
    StringLiteral(this).toRe() union StringLiteral(rhs()).toRe()

/** Regex union. */
@JvmName("unionStringLambdaRegLanSort")
infix fun (() -> String).union(rhs: Expression<RegLanSort>) = StringLiteral(this()).toRe() union rhs

/**
 * Regex union.
 * - [rhs] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("unionStringLambdaString")
infix fun (() -> String).union(rhs: String) =
    StringLiteral(this()).toRe() union StringLiteral(rhs).toRe()

/** Regex union. */
@JvmName("unionStringLambdaRegLanSortLambda")
infix fun (() -> String).union(rhs: (() -> Expression<RegLanSort>)) =
    StringLiteral(this()).toRe() union rhs()

/**
 * Regex union.
 * - [rhs] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("unionStringLambdaStringLambda")
infix fun (() -> String).union(rhs: (() -> String)) =
    StringLiteral(this()).toRe() union StringLiteral(rhs()).toRe()

/** Regex intersection. */
infix fun Expression<RegLanSort>.intersec(rhs: Expression<RegLanSort>) =
    if (this is RegexIntersec) {
      RegexIntersec(this.children + rhs)
    } else {
      RegexIntersec(this, rhs)
    }

/**
 * Regex intersection.
 * - [rhs] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("intersecRegLanSortString")
infix fun Expression<RegLanSort>.intersec(rhs: String) = this intersec StringLiteral(rhs).toRe()

/** Regex intersection. */
@JvmName("intersecRegLanSortRegLanSortLambda")
infix fun Expression<RegLanSort>.intersec(rhs: (() -> Expression<RegLanSort>)) = this intersec rhs()

/**
 * Regex intersection.
 * - [rhs] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("intersecRegLanSortStringLambda")
infix fun Expression<RegLanSort>.intersec(rhs: (() -> String)) =
    this intersec StringLiteral(rhs()).toRe()

/** Regex intersection. */
@JvmName("intersecRegLanSortLambdaRegLanSort")
infix fun (() -> Expression<RegLanSort>).intersec(rhs: Expression<RegLanSort>) = this() intersec rhs

/**
 * Regex intersection.
 * - [rhs] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("intersecRegLanSortLambdaString")
infix fun (() -> Expression<RegLanSort>).intersec(rhs: String) =
    this() intersec StringLiteral(rhs).toRe()

/** Regex intersection. */
@JvmName("intersecRegLanSortLambdaRegLanSortLambda")
infix fun (() -> Expression<RegLanSort>).intersec(rhs: (() -> Expression<RegLanSort>)) =
    this() intersec rhs()

/**
 * Regex intersection.
 * - [rhs] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("intersecRegLanSortLambdaStringLambda")
infix fun (() -> Expression<RegLanSort>).intersec(rhs: (() -> String)) =
    this() intersec StringLiteral(rhs()).toRe()

/**
 * Regex intersection.
 * - [String] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("intersecStringRegLanSort")
infix fun String.intersec(rhs: Expression<RegLanSort>) = StringLiteral(this).toRe() intersec rhs

/**
 * Regex intersection.
 * - [String] is converted to [Expression] of type [RegLanSort]
 * - [rhs] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("intersecStringString")
infix fun String.intersec(rhs: String) =
    StringLiteral(this).toRe() intersec StringLiteral(rhs).toRe()

/**
 * Regex intersection.
 * - [String] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("intersecStringRegLanSortLambda")
infix fun String.intersec(rhs: (() -> Expression<RegLanSort>)) =
    StringLiteral(this).toRe() intersec rhs()

/**
 * Regex intersection.
 * - [String] is converted to [Expression] of type [RegLanSort]
 * - [rhs] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("intersecStringStringLambda")
infix fun String.intersec(rhs: (() -> String)) =
    StringLiteral(this).toRe() intersec StringLiteral(rhs()).toRe()

/** Regex intersection. */
@JvmName("intersecStringLambdaRegLanSort")
infix fun (() -> String).intersec(rhs: Expression<RegLanSort>) =
    StringLiteral(this()).toRe() intersec rhs

/**
 * Regex intersection.
 * - [rhs] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("intersecStringLambdaString")
infix fun (() -> String).intersec(rhs: String) =
    StringLiteral(this()).toRe() intersec StringLiteral(rhs).toRe()

/** Regex intersection. */
@JvmName("intersecStringLambdaRegLanSortLambda")
infix fun (() -> String).intersec(rhs: (() -> Expression<RegLanSort>)) =
    StringLiteral(this()).toRe() intersec rhs()

/**
 * Regex intersection.
 * - [rhs] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("intersecStringLambdaStringLambda")
infix fun (() -> String).intersec(rhs: (() -> String)) =
    StringLiteral(this()).toRe() intersec StringLiteral(rhs()).toRe()

/** Kleene Closure. */
fun Expression<RegLanSort>.star() = RegexStar(this)

/**
 * Kleene Closure.
 * - [this] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("starString") fun String.star() = StringLiteral(this).toRe().star()

/** Kleene Closure. */
@JvmName("starRegLanSortLambda") fun (() -> Expression<RegLanSort>).star() = this().star()

/**
 * Kleene Closure.
 * - [this] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("starStringLambda") fun (() -> String).star() = StringLiteral(this()).toRe().star()

/** Reflexive closure of lexicographic ordering. */
infix fun Expression<StringSort>.leq(rhs: Expression<StringSort>) =
    if (this is StrRefLexOrder) {
      StrRefLexOrder(this.children + rhs)
    } else {
      StrRefLexOrder(this, rhs)
    }

/**
 * Reflexive closure of lexicographic ordering.
 * - [rhs] is converted to [StringLiteral] .
 */
@JvmName("leqStringSortString")
infix fun Expression<StringSort>.leq(rhs: String) = this leq StringLiteral(rhs)

/** Reflexive closure of lexicographic ordering. */
@JvmName("leqStringSortStringSortLambda")
infix fun Expression<StringSort>.leq(rhs: (() -> Expression<StringSort>)) = this leq rhs()

/**
 * Reflexive closure of lexicographic ordering.
 * - [rhs] is converted to [StringLiteral] .
 */
@JvmName("leqStringSortStringLambda")
infix fun Expression<StringSort>.leq(rhs: (() -> String)) = this leq StringLiteral(rhs())

/** Reflexive closure of lexicographic ordering. */
@JvmName("leqStringSortLambdaStringSort")
infix fun (() -> Expression<StringSort>).leq(rhs: Expression<StringSort>) = this() leq rhs

/**
 * Reflexive closure of lexicographic ordering.
 * - [rhs] is converted to [StringLiteral]
 */
@JvmName("leqStringSortLambdaString")
infix fun (() -> Expression<StringSort>).leq(rhs: String) = this() leq StringLiteral(rhs)

/** Reflexive closure of lexicographic ordering. */
@JvmName("leqStringSortLambdaStringSortLambda")
infix fun (() -> Expression<StringSort>).leq(rhs: (() -> Expression<StringSort>)) = this() leq rhs()

/**
 * Reflexive closure of lexicographic ordering.
 * - [rhs] is converted to [StringLiteral]
 */
@JvmName("leqStringSortLambdaStringLambda")
infix fun (() -> Expression<StringSort>).leq(rhs: (() -> String)) = this() leq StringLiteral(rhs())

/**
 * Reflexive closure of lexicographic ordering.
 * - [String] is converted to [StringLiteral] .
 */
@JvmName("leqStringStringSort")
infix fun String.leq(rhs: Expression<StringSort>) = StringLiteral(this) leq rhs

/**
 * Reflexive closure of lexicographic ordering.
 * - [String] is converted to [StringLiteral]
 * - [rhs] is converted to [StringLiteral] .
 */
@JvmName("leqStringString")
infix fun String.leq(rhs: String) = StringLiteral(this) leq StringLiteral(rhs)

/**
 * Reflexive closure of lexicographic ordering.
 * - [String] is converted to [StringLiteral] .
 */
@JvmName("leqStringStringSortLambda")
infix fun String.leq(rhs: (() -> Expression<StringSort>)) = StringLiteral(this) leq rhs()

/**
 * Reflexive closure of lexicographic ordering.
 * - [String] is converted to [StringLiteral]
 * - [rhs] is converted to [StringLiteral] .
 */
@JvmName("leqStringStringLambda")
infix fun String.leq(rhs: (() -> String)) = StringLiteral(this) leq StringLiteral(rhs())

/** Reflexive closure of lexicographic ordering. */
@JvmName("leqStringLambdaStringSort")
infix fun (() -> String).leq(rhs: Expression<StringSort>) = StringLiteral(this()) leq rhs

/**
 * Reflexive closure of lexicographic ordering.
 * - [rhs] is converted to [StringLiteral]
 */
@JvmName("leqStringLambdaString")
infix fun (() -> String).leq(rhs: String) = StringLiteral(this()) leq StringLiteral(rhs)

/** Reflexive closure of lexicographic ordering. */
@JvmName("leqStringLambdaStringSortLambda")
infix fun (() -> String).leq(rhs: (() -> Expression<StringSort>)) = StringLiteral(this()) leq rhs()

/**
 * Reflexive closure of lexicographic ordering.
 * - [rhs] is converted to [StringLiteral]
 */
@JvmName("leqStringLambdaStringLambda")
infix fun (() -> String).leq(rhs: (() -> String)) = StringLiteral(this()) leq StringLiteral(rhs())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 */
infix fun Expression<StringSort>.at(position: Expression<IntSort>) = StrAt(this, position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral] .
 */
@JvmName("atStringSortByte")
infix fun Expression<StringSort>.at(position: Byte) = this at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral] .
 */
@JvmName("atStringSortShort")
infix fun Expression<StringSort>.at(position: Short) = this at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral] .
 */
@JvmName("atStringSortInt")
infix fun Expression<StringSort>.at(position: Int) = this at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral] .
 */
@JvmName("atStringSortLong")
infix fun Expression<StringSort>.at(position: Long) = this at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral] .
 */
@JvmName("atStringSortBigInteger")
infix fun Expression<StringSort>.at(position: BigInteger) = this at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 */
@JvmName("atStringSortIntSortLambda")
infix fun Expression<StringSort>.at(position: (() -> Expression<IntSort>)) = this at position()

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral] .
 */
@JvmName("atStringSortByteLambda")
infix fun Expression<StringSort>.at(position: (() -> Byte)) = this at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral] .
 */
@JvmName("atStringSortShortLambda")
infix fun Expression<StringSort>.at(position: (() -> Short)) = this at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral] .
 */
@JvmName("atStringSortIntLambda")
infix fun Expression<StringSort>.at(position: (() -> Int)) = this at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral] .
 */
@JvmName("atStringSortLongLambda")
infix fun Expression<StringSort>.at(position: (() -> Long)) = this at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral] .
 */
@JvmName("atStringSortBigIntegerLambda")
infix fun Expression<StringSort>.at(position: (() -> BigInteger)) = this at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 */
@JvmName("atStringSortLambdaIntSort")
infix fun (() -> Expression<StringSort>).at(position: Expression<IntSort>) = this() at position

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral]
 */
@JvmName("atStringSortLambdaByte")
infix fun (() -> Expression<StringSort>).at(position: Byte) = this() at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral]
 */
@JvmName("atStringSortLambdaShort")
infix fun (() -> Expression<StringSort>).at(position: Short) = this() at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral]
 */
@JvmName("atStringSortLambdaInt")
infix fun (() -> Expression<StringSort>).at(position: Int) = this() at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral]
 */
@JvmName("atStringSortLambdaLong")
infix fun (() -> Expression<StringSort>).at(position: Long) = this() at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral]
 */
@JvmName("atStringSortLambdaBigInteger")
infix fun (() -> Expression<StringSort>).at(position: BigInteger) = this() at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 */
@JvmName("atStringSortLambdaIntSortLambda")
infix fun (() -> Expression<StringSort>).at(position: (() -> Expression<IntSort>)) =
    this() at position()

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral]
 */
@JvmName("atStringSortLambdaByteLambda")
infix fun (() -> Expression<StringSort>).at(position: (() -> Byte)) =
    this() at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral]
 */
@JvmName("atStringSortLambdaShortLambda")
infix fun (() -> Expression<StringSort>).at(position: (() -> Short)) =
    this() at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral]
 */
@JvmName("atStringSortLambdaIntLambda")
infix fun (() -> Expression<StringSort>).at(position: (() -> Int)) =
    this() at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral]
 */
@JvmName("atStringSortLambdaLongLambda")
infix fun (() -> Expression<StringSort>).at(position: (() -> Long)) =
    this() at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral]
 */
@JvmName("atStringSortLambdaBigIntegerLambda")
infix fun (() -> Expression<StringSort>).at(position: (() -> BigInteger)) =
    this() at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [String] is converted to [StringLiteral] .
 */
@JvmName("atStringIntSort")
infix fun String.at(position: Expression<IntSort>) = StringLiteral(this) at position

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [String] is converted to [StringLiteral]
 * - [position] is converted to [IntLiteral] .
 */
@JvmName("atStringByte")
infix fun String.at(position: Byte) = StringLiteral(this) at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [String] is converted to [StringLiteral]
 * - [position] is converted to [IntLiteral] .
 */
@JvmName("atStringShort")
infix fun String.at(position: Short) = StringLiteral(this) at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [String] is converted to [StringLiteral]
 * - [position] is converted to [IntLiteral] .
 */
@JvmName("atStringInt")
infix fun String.at(position: Int) = StringLiteral(this) at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [String] is converted to [StringLiteral]
 * - [position] is converted to [IntLiteral] .
 */
@JvmName("atStringLong")
infix fun String.at(position: Long) = StringLiteral(this) at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [String] is converted to [StringLiteral]
 * - [position] is converted to [IntLiteral] .
 */
@JvmName("atStringBigInteger")
infix fun String.at(position: BigInteger) = StringLiteral(this) at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [String] is converted to [StringLiteral] .
 */
@JvmName("atStringIntSortLambda")
infix fun String.at(position: (() -> Expression<IntSort>)) = StringLiteral(this) at position()

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [String] is converted to [StringLiteral]
 * - [position] is converted to [IntLiteral] .
 */
@JvmName("atStringByteLambda")
infix fun String.at(position: (() -> Byte)) = StringLiteral(this) at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [String] is converted to [StringLiteral]
 * - [position] is converted to [IntLiteral] .
 */
@JvmName("atStringShortLambda")
infix fun String.at(position: (() -> Short)) = StringLiteral(this) at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [String] is converted to [StringLiteral]
 * - [position] is converted to [IntLiteral] .
 */
@JvmName("atStringIntLambda")
infix fun String.at(position: (() -> Int)) = StringLiteral(this) at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [String] is converted to [StringLiteral]
 * - [position] is converted to [IntLiteral] .
 */
@JvmName("atStringLongLambda")
infix fun String.at(position: (() -> Long)) = StringLiteral(this) at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [String] is converted to [StringLiteral]
 * - [position] is converted to [IntLiteral] .
 */
@JvmName("atStringBigIntegerLambda")
infix fun String.at(position: (() -> BigInteger)) = StringLiteral(this) at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 */
@JvmName("atStringLambdaIntSort")
infix fun (() -> String).at(position: Expression<IntSort>) = StringLiteral(this()) at position

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral]
 */
@JvmName("atStringLambdaByte")
infix fun (() -> String).at(position: Byte) = StringLiteral(this()) at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral]
 */
@JvmName("atStringLambdaShort")
infix fun (() -> String).at(position: Short) = StringLiteral(this()) at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral]
 */
@JvmName("atStringLambdaInt")
infix fun (() -> String).at(position: Int) = StringLiteral(this()) at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral]
 */
@JvmName("atStringLambdaLong")
infix fun (() -> String).at(position: Long) = StringLiteral(this()) at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral]
 */
@JvmName("atStringLambdaBigInteger")
infix fun (() -> String).at(position: BigInteger) = StringLiteral(this()) at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 */
@JvmName("atStringLambdaIntSortLambda")
infix fun (() -> String).at(position: (() -> Expression<IntSort>)) =
    StringLiteral(this()) at position()

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral]
 */
@JvmName("atStringLambdaByteLambda")
infix fun (() -> String).at(position: (() -> Byte)) =
    StringLiteral(this()) at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral]
 */
@JvmName("atStringLambdaShortLambda")
infix fun (() -> String).at(position: (() -> Short)) =
    StringLiteral(this()) at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral]
 */
@JvmName("atStringLambdaIntLambda")
infix fun (() -> String).at(position: (() -> Int)) = StringLiteral(this()) at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral]
 */
@JvmName("atStringLambdaLongLambda")
infix fun (() -> String).at(position: (() -> Long)) =
    StringLiteral(this()) at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 * - [position] is converted to [IntLiteral]
 */
@JvmName("atStringLambdaBigIntegerLambda")
infix fun (() -> String).at(position: (() -> BigInteger)) =
    StringLiteral(this()) at IntLiteral(position())

/** Longest substring of [this] of at most [length] characters starting at [start]. */
fun Expression<StringSort>.substr(start: Expression<IntSort>, length: Expression<IntSort>) =
    StrSubstring(this, start, length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortIntSortByte")
fun Expression<StringSort>.substr(start: Expression<IntSort>, length: Byte) =
    this.substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortIntSortShort")
fun Expression<StringSort>.substr(start: Expression<IntSort>, length: Short) =
    this.substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortIntSortInt")
fun Expression<StringSort>.substr(start: Expression<IntSort>, length: Int) =
    this.substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortIntSortLong")
fun Expression<StringSort>.substr(start: Expression<IntSort>, length: Long) =
    this.substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortIntSortBigInteger")
fun Expression<StringSort>.substr(start: Expression<IntSort>, length: BigInteger) =
    this.substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortByteIntSort")
fun Expression<StringSort>.substr(start: Byte, length: Expression<IntSort>) =
    this.substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortByteByte")
fun Expression<StringSort>.substr(start: Byte, length: Byte) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortByteShort")
fun Expression<StringSort>.substr(start: Byte, length: Short) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortByteInt")
fun Expression<StringSort>.substr(start: Byte, length: Int) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortByteLong")
fun Expression<StringSort>.substr(start: Byte, length: Long) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortByteBigInteger")
fun Expression<StringSort>.substr(start: Byte, length: BigInteger) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortShortIntSort")
fun Expression<StringSort>.substr(start: Short, length: Expression<IntSort>) =
    this.substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortShortByte")
fun Expression<StringSort>.substr(start: Short, length: Byte) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortShortShort")
fun Expression<StringSort>.substr(start: Short, length: Short) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortShortInt")
fun Expression<StringSort>.substr(start: Short, length: Int) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortShortLong")
fun Expression<StringSort>.substr(start: Short, length: Long) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortShortBigInteger")
fun Expression<StringSort>.substr(start: Short, length: BigInteger) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortIntIntSort")
fun Expression<StringSort>.substr(start: Int, length: Expression<IntSort>) =
    this.substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortIntByte")
fun Expression<StringSort>.substr(start: Int, length: Byte) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortIntShort")
fun Expression<StringSort>.substr(start: Int, length: Short) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortIntInt")
fun Expression<StringSort>.substr(start: Int, length: Int) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortIntLong")
fun Expression<StringSort>.substr(start: Int, length: Long) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortIntBigInteger")
fun Expression<StringSort>.substr(start: Int, length: BigInteger) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortLongIntSort")
fun Expression<StringSort>.substr(start: Long, length: Expression<IntSort>) =
    this.substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLongByte")
fun Expression<StringSort>.substr(start: Long, length: Byte) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLongShort")
fun Expression<StringSort>.substr(start: Long, length: Short) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLongInt")
fun Expression<StringSort>.substr(start: Long, length: Int) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLongLong")
fun Expression<StringSort>.substr(start: Long, length: Long) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLongBigInteger")
fun Expression<StringSort>.substr(start: Long, length: BigInteger) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortBigIntegerIntSort")
fun Expression<StringSort>.substr(start: BigInteger, length: Expression<IntSort>) =
    this.substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortBigIntegerByte")
fun Expression<StringSort>.substr(start: BigInteger, length: Byte) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortBigIntegerShort")
fun Expression<StringSort>.substr(start: BigInteger, length: Short) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortBigIntegerInt")
fun Expression<StringSort>.substr(start: BigInteger, length: Int) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortBigIntegerLong")
fun Expression<StringSort>.substr(start: BigInteger, length: Long) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortBigIntegerBigInteger")
fun Expression<StringSort>.substr(start: BigInteger, length: BigInteger) =
    this.substr(IntLiteral(start), IntLiteral(length))

/** Longest substring of [this] of at most [length] characters starting at [start]. */
@JvmName("substrStringSortIntSortLambdaIntSort")
fun Expression<StringSort>.substr(start: (() -> Expression<IntSort>), length: Expression<IntSort>) =
    this.substr(start(), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortIntSortLambdaByte")
fun Expression<StringSort>.substr(start: (() -> Expression<IntSort>), length: Byte) =
    this.substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortIntSortLambdaShort")
fun Expression<StringSort>.substr(start: (() -> Expression<IntSort>), length: Short) =
    this.substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortIntSortLambdaInt")
fun Expression<StringSort>.substr(start: (() -> Expression<IntSort>), length: Int) =
    this.substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortIntSortLambdaLong")
fun Expression<StringSort>.substr(start: (() -> Expression<IntSort>), length: Long) =
    this.substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortIntSortLambdaBigInteger")
fun Expression<StringSort>.substr(start: (() -> Expression<IntSort>), length: BigInteger) =
    this.substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortByteLambdaIntSort")
fun Expression<StringSort>.substr(start: (() -> Byte), length: Expression<IntSort>) =
    this.substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortByteLambdaByte")
fun Expression<StringSort>.substr(start: (() -> Byte), length: Byte) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortByteLambdaShort")
fun Expression<StringSort>.substr(start: (() -> Byte), length: Short) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortByteLambdaInt")
fun Expression<StringSort>.substr(start: (() -> Byte), length: Int) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortByteLambdaLong")
fun Expression<StringSort>.substr(start: (() -> Byte), length: Long) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortByteLambdaBigInteger")
fun Expression<StringSort>.substr(start: (() -> Byte), length: BigInteger) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortShortLambdaIntSort")
fun Expression<StringSort>.substr(start: (() -> Short), length: Expression<IntSort>) =
    this.substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortShortLambdaByte")
fun Expression<StringSort>.substr(start: (() -> Short), length: Byte) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortShortLambdaShort")
fun Expression<StringSort>.substr(start: (() -> Short), length: Short) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortShortLambdaInt")
fun Expression<StringSort>.substr(start: (() -> Short), length: Int) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortShortLambdaLong")
fun Expression<StringSort>.substr(start: (() -> Short), length: Long) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortShortLambdaBigInteger")
fun Expression<StringSort>.substr(start: (() -> Short), length: BigInteger) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortIntLambdaIntSort")
fun Expression<StringSort>.substr(start: (() -> Int), length: Expression<IntSort>) =
    this.substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortIntLambdaByte")
fun Expression<StringSort>.substr(start: (() -> Int), length: Byte) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortIntLambdaShort")
fun Expression<StringSort>.substr(start: (() -> Int), length: Short) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortIntLambdaInt")
fun Expression<StringSort>.substr(start: (() -> Int), length: Int) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortIntLambdaLong")
fun Expression<StringSort>.substr(start: (() -> Int), length: Long) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortIntLambdaBigInteger")
fun Expression<StringSort>.substr(start: (() -> Int), length: BigInteger) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortLongLambdaIntSort")
fun Expression<StringSort>.substr(start: (() -> Long), length: Expression<IntSort>) =
    this.substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLongLambdaByte")
fun Expression<StringSort>.substr(start: (() -> Long), length: Byte) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLongLambdaShort")
fun Expression<StringSort>.substr(start: (() -> Long), length: Short) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLongLambdaInt")
fun Expression<StringSort>.substr(start: (() -> Long), length: Int) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLongLambdaLong")
fun Expression<StringSort>.substr(start: (() -> Long), length: Long) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLongLambdaBigInteger")
fun Expression<StringSort>.substr(start: (() -> Long), length: BigInteger) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortBigIntegerLambdaIntSort")
fun Expression<StringSort>.substr(start: (() -> BigInteger), length: Expression<IntSort>) =
    this.substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortBigIntegerLambdaByte")
fun Expression<StringSort>.substr(start: (() -> BigInteger), length: Byte) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortBigIntegerLambdaShort")
fun Expression<StringSort>.substr(start: (() -> BigInteger), length: Short) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortBigIntegerLambdaInt")
fun Expression<StringSort>.substr(start: (() -> BigInteger), length: Int) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortBigIntegerLambdaLong")
fun Expression<StringSort>.substr(start: (() -> BigInteger), length: Long) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortBigIntegerLambdaBigInteger")
fun Expression<StringSort>.substr(start: (() -> BigInteger), length: BigInteger) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/** Longest substring of [this] of at most [length] characters starting at [start]. */
@JvmName("substrStringSortIntSortIntSortLambda")
fun Expression<StringSort>.substr(start: Expression<IntSort>, length: (() -> Expression<IntSort>)) =
    this.substr(start, length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortIntSortByteLambda")
fun Expression<StringSort>.substr(start: Expression<IntSort>, length: (() -> Byte)) =
    this.substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortIntSortShortLambda")
fun Expression<StringSort>.substr(start: Expression<IntSort>, length: (() -> Short)) =
    this.substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortIntSortIntLambda")
fun Expression<StringSort>.substr(start: Expression<IntSort>, length: (() -> Int)) =
    this.substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortIntSortLongLambda")
fun Expression<StringSort>.substr(start: Expression<IntSort>, length: (() -> Long)) =
    this.substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortIntSortBigIntegerLambda")
fun Expression<StringSort>.substr(start: Expression<IntSort>, length: (() -> BigInteger)) =
    this.substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortByteIntSortLambda")
fun Expression<StringSort>.substr(start: Byte, length: (() -> Expression<IntSort>)) =
    this.substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortByteByteLambda")
fun Expression<StringSort>.substr(start: Byte, length: (() -> Byte)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortByteShortLambda")
fun Expression<StringSort>.substr(start: Byte, length: (() -> Short)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortByteIntLambda")
fun Expression<StringSort>.substr(start: Byte, length: (() -> Int)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortByteLongLambda")
fun Expression<StringSort>.substr(start: Byte, length: (() -> Long)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortByteBigIntegerLambda")
fun Expression<StringSort>.substr(start: Byte, length: (() -> BigInteger)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortShortIntSortLambda")
fun Expression<StringSort>.substr(start: Short, length: (() -> Expression<IntSort>)) =
    this.substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortShortByteLambda")
fun Expression<StringSort>.substr(start: Short, length: (() -> Byte)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortShortShortLambda")
fun Expression<StringSort>.substr(start: Short, length: (() -> Short)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortShortIntLambda")
fun Expression<StringSort>.substr(start: Short, length: (() -> Int)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortShortLongLambda")
fun Expression<StringSort>.substr(start: Short, length: (() -> Long)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortShortBigIntegerLambda")
fun Expression<StringSort>.substr(start: Short, length: (() -> BigInteger)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortIntIntSortLambda")
fun Expression<StringSort>.substr(start: Int, length: (() -> Expression<IntSort>)) =
    this.substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortIntByteLambda")
fun Expression<StringSort>.substr(start: Int, length: (() -> Byte)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortIntShortLambda")
fun Expression<StringSort>.substr(start: Int, length: (() -> Short)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortIntIntLambda")
fun Expression<StringSort>.substr(start: Int, length: (() -> Int)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortIntLongLambda")
fun Expression<StringSort>.substr(start: Int, length: (() -> Long)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortIntBigIntegerLambda")
fun Expression<StringSort>.substr(start: Int, length: (() -> BigInteger)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortLongIntSortLambda")
fun Expression<StringSort>.substr(start: Long, length: (() -> Expression<IntSort>)) =
    this.substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLongByteLambda")
fun Expression<StringSort>.substr(start: Long, length: (() -> Byte)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLongShortLambda")
fun Expression<StringSort>.substr(start: Long, length: (() -> Short)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLongIntLambda")
fun Expression<StringSort>.substr(start: Long, length: (() -> Int)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLongLongLambda")
fun Expression<StringSort>.substr(start: Long, length: (() -> Long)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLongBigIntegerLambda")
fun Expression<StringSort>.substr(start: Long, length: (() -> BigInteger)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortBigIntegerIntSortLambda")
fun Expression<StringSort>.substr(start: BigInteger, length: (() -> Expression<IntSort>)) =
    this.substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortBigIntegerByteLambda")
fun Expression<StringSort>.substr(start: BigInteger, length: (() -> Byte)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortBigIntegerShortLambda")
fun Expression<StringSort>.substr(start: BigInteger, length: (() -> Short)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortBigIntegerIntLambda")
fun Expression<StringSort>.substr(start: BigInteger, length: (() -> Int)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortBigIntegerLongLambda")
fun Expression<StringSort>.substr(start: BigInteger, length: (() -> Long)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortBigIntegerBigIntegerLambda")
fun Expression<StringSort>.substr(start: BigInteger, length: (() -> BigInteger)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/** Longest substring of [this] of at most [length] characters starting at [start]. */
@JvmName("substrStringSortIntSortLambdaIntSortLambda")
fun Expression<StringSort>.substr(
    start: (() -> Expression<IntSort>),
    length: (() -> Expression<IntSort>)
) = this.substr(start(), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortIntSortLambdaByteLambda")
fun Expression<StringSort>.substr(start: (() -> Expression<IntSort>), length: (() -> Byte)) =
    this.substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortIntSortLambdaShortLambda")
fun Expression<StringSort>.substr(start: (() -> Expression<IntSort>), length: (() -> Short)) =
    this.substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortIntSortLambdaIntLambda")
fun Expression<StringSort>.substr(start: (() -> Expression<IntSort>), length: (() -> Int)) =
    this.substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortIntSortLambdaLongLambda")
fun Expression<StringSort>.substr(start: (() -> Expression<IntSort>), length: (() -> Long)) =
    this.substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortIntSortLambdaBigIntegerLambda")
fun Expression<StringSort>.substr(start: (() -> Expression<IntSort>), length: (() -> BigInteger)) =
    this.substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortByteLambdaIntSortLambda")
fun Expression<StringSort>.substr(start: (() -> Byte), length: (() -> Expression<IntSort>)) =
    this.substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortByteLambdaByteLambda")
fun Expression<StringSort>.substr(start: (() -> Byte), length: (() -> Byte)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortByteLambdaShortLambda")
fun Expression<StringSort>.substr(start: (() -> Byte), length: (() -> Short)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortByteLambdaIntLambda")
fun Expression<StringSort>.substr(start: (() -> Byte), length: (() -> Int)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortByteLambdaLongLambda")
fun Expression<StringSort>.substr(start: (() -> Byte), length: (() -> Long)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortByteLambdaBigIntegerLambda")
fun Expression<StringSort>.substr(start: (() -> Byte), length: (() -> BigInteger)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortShortLambdaIntSortLambda")
fun Expression<StringSort>.substr(start: (() -> Short), length: (() -> Expression<IntSort>)) =
    this.substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortShortLambdaByteLambda")
fun Expression<StringSort>.substr(start: (() -> Short), length: (() -> Byte)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortShortLambdaShortLambda")
fun Expression<StringSort>.substr(start: (() -> Short), length: (() -> Short)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortShortLambdaIntLambda")
fun Expression<StringSort>.substr(start: (() -> Short), length: (() -> Int)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortShortLambdaLongLambda")
fun Expression<StringSort>.substr(start: (() -> Short), length: (() -> Long)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortShortLambdaBigIntegerLambda")
fun Expression<StringSort>.substr(start: (() -> Short), length: (() -> BigInteger)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortIntLambdaIntSortLambda")
fun Expression<StringSort>.substr(start: (() -> Int), length: (() -> Expression<IntSort>)) =
    this.substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortIntLambdaByteLambda")
fun Expression<StringSort>.substr(start: (() -> Int), length: (() -> Byte)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortIntLambdaShortLambda")
fun Expression<StringSort>.substr(start: (() -> Int), length: (() -> Short)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortIntLambdaIntLambda")
fun Expression<StringSort>.substr(start: (() -> Int), length: (() -> Int)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortIntLambdaLongLambda")
fun Expression<StringSort>.substr(start: (() -> Int), length: (() -> Long)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortIntLambdaBigIntegerLambda")
fun Expression<StringSort>.substr(start: (() -> Int), length: (() -> BigInteger)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortLongLambdaIntSortLambda")
fun Expression<StringSort>.substr(start: (() -> Long), length: (() -> Expression<IntSort>)) =
    this.substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLongLambdaByteLambda")
fun Expression<StringSort>.substr(start: (() -> Long), length: (() -> Byte)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLongLambdaShortLambda")
fun Expression<StringSort>.substr(start: (() -> Long), length: (() -> Short)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLongLambdaIntLambda")
fun Expression<StringSort>.substr(start: (() -> Long), length: (() -> Int)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLongLambdaLongLambda")
fun Expression<StringSort>.substr(start: (() -> Long), length: (() -> Long)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLongLambdaBigIntegerLambda")
fun Expression<StringSort>.substr(start: (() -> Long), length: (() -> BigInteger)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortBigIntegerLambdaIntSortLambda")
fun Expression<StringSort>.substr(start: (() -> BigInteger), length: (() -> Expression<IntSort>)) =
    this.substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortBigIntegerLambdaByteLambda")
fun Expression<StringSort>.substr(start: (() -> BigInteger), length: (() -> Byte)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortBigIntegerLambdaShortLambda")
fun Expression<StringSort>.substr(start: (() -> BigInteger), length: (() -> Short)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortBigIntegerLambdaIntLambda")
fun Expression<StringSort>.substr(start: (() -> BigInteger), length: (() -> Int)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortBigIntegerLambdaLongLambda")
fun Expression<StringSort>.substr(start: (() -> BigInteger), length: (() -> Long)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortBigIntegerLambdaBigIntegerLambda")
fun Expression<StringSort>.substr(start: (() -> BigInteger), length: (() -> BigInteger)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/** Longest substring of [this] of at most [length] characters starting at [start]. */
@JvmName("substrStringSortLambdaIntSortIntSort")
fun (() -> Expression<StringSort>).substr(start: Expression<IntSort>, length: Expression<IntSort>) =
    this().substr(start, length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntSortByte")
fun (() -> Expression<StringSort>).substr(start: Expression<IntSort>, length: Byte) =
    this().substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntSortShort")
fun (() -> Expression<StringSort>).substr(start: Expression<IntSort>, length: Short) =
    this().substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntSortInt")
fun (() -> Expression<StringSort>).substr(start: Expression<IntSort>, length: Int) =
    this().substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntSortLong")
fun (() -> Expression<StringSort>).substr(start: Expression<IntSort>, length: Long) =
    this().substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntSortBigInteger")
fun (() -> Expression<StringSort>).substr(start: Expression<IntSort>, length: BigInteger) =
    this().substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortLambdaByteIntSort")
fun (() -> Expression<StringSort>).substr(start: Byte, length: Expression<IntSort>) =
    this().substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaByteByte")
fun (() -> Expression<StringSort>).substr(start: Byte, length: Byte) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaByteShort")
fun (() -> Expression<StringSort>).substr(start: Byte, length: Short) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaByteInt")
fun (() -> Expression<StringSort>).substr(start: Byte, length: Int) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaByteLong")
fun (() -> Expression<StringSort>).substr(start: Byte, length: Long) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaByteBigInteger")
fun (() -> Expression<StringSort>).substr(start: Byte, length: BigInteger) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortLambdaShortIntSort")
fun (() -> Expression<StringSort>).substr(start: Short, length: Expression<IntSort>) =
    this().substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaShortByte")
fun (() -> Expression<StringSort>).substr(start: Short, length: Byte) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaShortShort")
fun (() -> Expression<StringSort>).substr(start: Short, length: Short) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaShortInt")
fun (() -> Expression<StringSort>).substr(start: Short, length: Int) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaShortLong")
fun (() -> Expression<StringSort>).substr(start: Short, length: Long) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaShortBigInteger")
fun (() -> Expression<StringSort>).substr(start: Short, length: BigInteger) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortLambdaIntIntSort")
fun (() -> Expression<StringSort>).substr(start: Int, length: Expression<IntSort>) =
    this().substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntByte")
fun (() -> Expression<StringSort>).substr(start: Int, length: Byte) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntShort")
fun (() -> Expression<StringSort>).substr(start: Int, length: Short) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntInt")
fun (() -> Expression<StringSort>).substr(start: Int, length: Int) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntLong")
fun (() -> Expression<StringSort>).substr(start: Int, length: Long) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntBigInteger")
fun (() -> Expression<StringSort>).substr(start: Int, length: BigInteger) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortLambdaLongIntSort")
fun (() -> Expression<StringSort>).substr(start: Long, length: Expression<IntSort>) =
    this().substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaLongByte")
fun (() -> Expression<StringSort>).substr(start: Long, length: Byte) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaLongShort")
fun (() -> Expression<StringSort>).substr(start: Long, length: Short) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaLongInt")
fun (() -> Expression<StringSort>).substr(start: Long, length: Int) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaLongLong")
fun (() -> Expression<StringSort>).substr(start: Long, length: Long) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaLongBigInteger")
fun (() -> Expression<StringSort>).substr(start: Long, length: BigInteger) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortLambdaBigIntegerIntSort")
fun (() -> Expression<StringSort>).substr(start: BigInteger, length: Expression<IntSort>) =
    this().substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaBigIntegerByte")
fun (() -> Expression<StringSort>).substr(start: BigInteger, length: Byte) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaBigIntegerShort")
fun (() -> Expression<StringSort>).substr(start: BigInteger, length: Short) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaBigIntegerInt")
fun (() -> Expression<StringSort>).substr(start: BigInteger, length: Int) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaBigIntegerLong")
fun (() -> Expression<StringSort>).substr(start: BigInteger, length: Long) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaBigIntegerBigInteger")
fun (() -> Expression<StringSort>).substr(start: BigInteger, length: BigInteger) =
    this().substr(IntLiteral(start), IntLiteral(length))

/** Longest substring of [this] of at most [length] characters starting at [start]. */
@JvmName("substrStringSortLambdaIntSortLambdaIntSort")
fun (() -> Expression<StringSort>).substr(
    start: (() -> Expression<IntSort>),
    length: Expression<IntSort>
) = this().substr(start(), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntSortLambdaByte")
fun (() -> Expression<StringSort>).substr(start: (() -> Expression<IntSort>), length: Byte) =
    this().substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntSortLambdaShort")
fun (() -> Expression<StringSort>).substr(start: (() -> Expression<IntSort>), length: Short) =
    this().substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntSortLambdaInt")
fun (() -> Expression<StringSort>).substr(start: (() -> Expression<IntSort>), length: Int) =
    this().substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntSortLambdaLong")
fun (() -> Expression<StringSort>).substr(start: (() -> Expression<IntSort>), length: Long) =
    this().substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntSortLambdaBigInteger")
fun (() -> Expression<StringSort>).substr(start: (() -> Expression<IntSort>), length: BigInteger) =
    this().substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortLambdaByteLambdaIntSort")
fun (() -> Expression<StringSort>).substr(start: (() -> Byte), length: Expression<IntSort>) =
    this().substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaByteLambdaByte")
fun (() -> Expression<StringSort>).substr(start: (() -> Byte), length: Byte) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaByteLambdaShort")
fun (() -> Expression<StringSort>).substr(start: (() -> Byte), length: Short) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaByteLambdaInt")
fun (() -> Expression<StringSort>).substr(start: (() -> Byte), length: Int) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaByteLambdaLong")
fun (() -> Expression<StringSort>).substr(start: (() -> Byte), length: Long) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaByteLambdaBigInteger")
fun (() -> Expression<StringSort>).substr(start: (() -> Byte), length: BigInteger) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortLambdaShortLambdaIntSort")
fun (() -> Expression<StringSort>).substr(start: (() -> Short), length: Expression<IntSort>) =
    this().substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaShortLambdaByte")
fun (() -> Expression<StringSort>).substr(start: (() -> Short), length: Byte) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaShortLambdaShort")
fun (() -> Expression<StringSort>).substr(start: (() -> Short), length: Short) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaShortLambdaInt")
fun (() -> Expression<StringSort>).substr(start: (() -> Short), length: Int) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaShortLambdaLong")
fun (() -> Expression<StringSort>).substr(start: (() -> Short), length: Long) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaShortLambdaBigInteger")
fun (() -> Expression<StringSort>).substr(start: (() -> Short), length: BigInteger) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortLambdaIntLambdaIntSort")
fun (() -> Expression<StringSort>).substr(start: (() -> Int), length: Expression<IntSort>) =
    this().substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntLambdaByte")
fun (() -> Expression<StringSort>).substr(start: (() -> Int), length: Byte) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntLambdaShort")
fun (() -> Expression<StringSort>).substr(start: (() -> Int), length: Short) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntLambdaInt")
fun (() -> Expression<StringSort>).substr(start: (() -> Int), length: Int) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntLambdaLong")
fun (() -> Expression<StringSort>).substr(start: (() -> Int), length: Long) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntLambdaBigInteger")
fun (() -> Expression<StringSort>).substr(start: (() -> Int), length: BigInteger) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortLambdaLongLambdaIntSort")
fun (() -> Expression<StringSort>).substr(start: (() -> Long), length: Expression<IntSort>) =
    this().substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaLongLambdaByte")
fun (() -> Expression<StringSort>).substr(start: (() -> Long), length: Byte) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaLongLambdaShort")
fun (() -> Expression<StringSort>).substr(start: (() -> Long), length: Short) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaLongLambdaInt")
fun (() -> Expression<StringSort>).substr(start: (() -> Long), length: Int) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaLongLambdaLong")
fun (() -> Expression<StringSort>).substr(start: (() -> Long), length: Long) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaLongLambdaBigInteger")
fun (() -> Expression<StringSort>).substr(start: (() -> Long), length: BigInteger) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortLambdaBigIntegerLambdaIntSort")
fun (() -> Expression<StringSort>).substr(start: (() -> BigInteger), length: Expression<IntSort>) =
    this().substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaBigIntegerLambdaByte")
fun (() -> Expression<StringSort>).substr(start: (() -> BigInteger), length: Byte) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaBigIntegerLambdaShort")
fun (() -> Expression<StringSort>).substr(start: (() -> BigInteger), length: Short) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaBigIntegerLambdaInt")
fun (() -> Expression<StringSort>).substr(start: (() -> BigInteger), length: Int) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaBigIntegerLambdaLong")
fun (() -> Expression<StringSort>).substr(start: (() -> BigInteger), length: Long) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaBigIntegerLambdaBigInteger")
fun (() -> Expression<StringSort>).substr(start: (() -> BigInteger), length: BigInteger) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/** Longest substring of [this] of at most [length] characters starting at [start]. */
@JvmName("substrStringSortLambdaIntSortIntSortLambda")
fun (() -> Expression<StringSort>).substr(
    start: Expression<IntSort>,
    length: (() -> Expression<IntSort>)
) = this().substr(start, length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntSortByteLambda")
fun (() -> Expression<StringSort>).substr(start: Expression<IntSort>, length: (() -> Byte)) =
    this().substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntSortShortLambda")
fun (() -> Expression<StringSort>).substr(start: Expression<IntSort>, length: (() -> Short)) =
    this().substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntSortIntLambda")
fun (() -> Expression<StringSort>).substr(start: Expression<IntSort>, length: (() -> Int)) =
    this().substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntSortLongLambda")
fun (() -> Expression<StringSort>).substr(start: Expression<IntSort>, length: (() -> Long)) =
    this().substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntSortBigIntegerLambda")
fun (() -> Expression<StringSort>).substr(start: Expression<IntSort>, length: (() -> BigInteger)) =
    this().substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortLambdaByteIntSortLambda")
fun (() -> Expression<StringSort>).substr(start: Byte, length: (() -> Expression<IntSort>)) =
    this().substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaByteByteLambda")
fun (() -> Expression<StringSort>).substr(start: Byte, length: (() -> Byte)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaByteShortLambda")
fun (() -> Expression<StringSort>).substr(start: Byte, length: (() -> Short)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaByteIntLambda")
fun (() -> Expression<StringSort>).substr(start: Byte, length: (() -> Int)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaByteLongLambda")
fun (() -> Expression<StringSort>).substr(start: Byte, length: (() -> Long)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaByteBigIntegerLambda")
fun (() -> Expression<StringSort>).substr(start: Byte, length: (() -> BigInteger)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortLambdaShortIntSortLambda")
fun (() -> Expression<StringSort>).substr(start: Short, length: (() -> Expression<IntSort>)) =
    this().substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaShortByteLambda")
fun (() -> Expression<StringSort>).substr(start: Short, length: (() -> Byte)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaShortShortLambda")
fun (() -> Expression<StringSort>).substr(start: Short, length: (() -> Short)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaShortIntLambda")
fun (() -> Expression<StringSort>).substr(start: Short, length: (() -> Int)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaShortLongLambda")
fun (() -> Expression<StringSort>).substr(start: Short, length: (() -> Long)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaShortBigIntegerLambda")
fun (() -> Expression<StringSort>).substr(start: Short, length: (() -> BigInteger)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortLambdaIntIntSortLambda")
fun (() -> Expression<StringSort>).substr(start: Int, length: (() -> Expression<IntSort>)) =
    this().substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntByteLambda")
fun (() -> Expression<StringSort>).substr(start: Int, length: (() -> Byte)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntShortLambda")
fun (() -> Expression<StringSort>).substr(start: Int, length: (() -> Short)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntIntLambda")
fun (() -> Expression<StringSort>).substr(start: Int, length: (() -> Int)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntLongLambda")
fun (() -> Expression<StringSort>).substr(start: Int, length: (() -> Long)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntBigIntegerLambda")
fun (() -> Expression<StringSort>).substr(start: Int, length: (() -> BigInteger)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortLambdaLongIntSortLambda")
fun (() -> Expression<StringSort>).substr(start: Long, length: (() -> Expression<IntSort>)) =
    this().substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaLongByteLambda")
fun (() -> Expression<StringSort>).substr(start: Long, length: (() -> Byte)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaLongShortLambda")
fun (() -> Expression<StringSort>).substr(start: Long, length: (() -> Short)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaLongIntLambda")
fun (() -> Expression<StringSort>).substr(start: Long, length: (() -> Int)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaLongLongLambda")
fun (() -> Expression<StringSort>).substr(start: Long, length: (() -> Long)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaLongBigIntegerLambda")
fun (() -> Expression<StringSort>).substr(start: Long, length: (() -> BigInteger)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortLambdaBigIntegerIntSortLambda")
fun (() -> Expression<StringSort>).substr(start: BigInteger, length: (() -> Expression<IntSort>)) =
    this().substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaBigIntegerByteLambda")
fun (() -> Expression<StringSort>).substr(start: BigInteger, length: (() -> Byte)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaBigIntegerShortLambda")
fun (() -> Expression<StringSort>).substr(start: BigInteger, length: (() -> Short)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaBigIntegerIntLambda")
fun (() -> Expression<StringSort>).substr(start: BigInteger, length: (() -> Int)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaBigIntegerLongLambda")
fun (() -> Expression<StringSort>).substr(start: BigInteger, length: (() -> Long)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaBigIntegerBigIntegerLambda")
fun (() -> Expression<StringSort>).substr(start: BigInteger, length: (() -> BigInteger)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/** Longest substring of [this] of at most [length] characters starting at [start]. */
@JvmName("substrStringSortLambdaIntSortLambdaIntSortLambda")
fun (() -> Expression<StringSort>).substr(
    start: (() -> Expression<IntSort>),
    length: (() -> Expression<IntSort>)
) = this().substr(start(), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntSortLambdaByteLambda")
fun (() -> Expression<StringSort>).substr(
    start: (() -> Expression<IntSort>),
    length: (() -> Byte)
) = this().substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntSortLambdaShortLambda")
fun (() -> Expression<StringSort>).substr(
    start: (() -> Expression<IntSort>),
    length: (() -> Short)
) = this().substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntSortLambdaIntLambda")
fun (() -> Expression<StringSort>).substr(start: (() -> Expression<IntSort>), length: (() -> Int)) =
    this().substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntSortLambdaLongLambda")
fun (() -> Expression<StringSort>).substr(
    start: (() -> Expression<IntSort>),
    length: (() -> Long)
) = this().substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].* - [length] is
 * converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntSortLambdaBigIntegerLambda")
fun (() -> Expression<StringSort>).substr(
    start: (() -> Expression<IntSort>),
    length: (() -> BigInteger)
) = this().substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortLambdaByteLambdaIntSortLambda")
fun (() -> Expression<StringSort>).substr(
    start: (() -> Byte),
    length: (() -> Expression<IntSort>)
) = this().substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaByteLambdaByteLambda")
fun (() -> Expression<StringSort>).substr(start: (() -> Byte), length: (() -> Byte)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaByteLambdaShortLambda")
fun (() -> Expression<StringSort>).substr(start: (() -> Byte), length: (() -> Short)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaByteLambdaIntLambda")
fun (() -> Expression<StringSort>).substr(start: (() -> Byte), length: (() -> Int)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaByteLambdaLongLambda")
fun (() -> Expression<StringSort>).substr(start: (() -> Byte), length: (() -> Long)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaByteLambdaBigIntegerLambda")
fun (() -> Expression<StringSort>).substr(start: (() -> Byte), length: (() -> BigInteger)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortLambdaShortLambdaIntSortLambda")
fun (() -> Expression<StringSort>).substr(
    start: (() -> Short),
    length: (() -> Expression<IntSort>)
) = this().substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaShortLambdaByteLambda")
fun (() -> Expression<StringSort>).substr(start: (() -> Short), length: (() -> Byte)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaShortLambdaShortLambda")
fun (() -> Expression<StringSort>).substr(start: (() -> Short), length: (() -> Short)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaShortLambdaIntLambda")
fun (() -> Expression<StringSort>).substr(start: (() -> Short), length: (() -> Int)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaShortLambdaLongLambda")
fun (() -> Expression<StringSort>).substr(start: (() -> Short), length: (() -> Long)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaShortLambdaBigIntegerLambda")
fun (() -> Expression<StringSort>).substr(start: (() -> Short), length: (() -> BigInteger)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortLambdaIntLambdaIntSortLambda")
fun (() -> Expression<StringSort>).substr(start: (() -> Int), length: (() -> Expression<IntSort>)) =
    this().substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntLambdaByteLambda")
fun (() -> Expression<StringSort>).substr(start: (() -> Int), length: (() -> Byte)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntLambdaShortLambda")
fun (() -> Expression<StringSort>).substr(start: (() -> Int), length: (() -> Short)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntLambdaIntLambda")
fun (() -> Expression<StringSort>).substr(start: (() -> Int), length: (() -> Int)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntLambdaLongLambda")
fun (() -> Expression<StringSort>).substr(start: (() -> Int), length: (() -> Long)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaIntLambdaBigIntegerLambda")
fun (() -> Expression<StringSort>).substr(start: (() -> Int), length: (() -> BigInteger)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortLambdaLongLambdaIntSortLambda")
fun (() -> Expression<StringSort>).substr(
    start: (() -> Long),
    length: (() -> Expression<IntSort>)
) = this().substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaLongLambdaByteLambda")
fun (() -> Expression<StringSort>).substr(start: (() -> Long), length: (() -> Byte)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaLongLambdaShortLambda")
fun (() -> Expression<StringSort>).substr(start: (() -> Long), length: (() -> Short)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaLongLambdaIntLambda")
fun (() -> Expression<StringSort>).substr(start: (() -> Long), length: (() -> Int)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaLongLambdaLongLambda")
fun (() -> Expression<StringSort>).substr(start: (() -> Long), length: (() -> Long)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaLongLambdaBigIntegerLambda")
fun (() -> Expression<StringSort>).substr(start: (() -> Long), length: (() -> BigInteger)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringSortLambdaBigIntegerLambdaIntSortLambda")
fun (() -> Expression<StringSort>).substr(
    start: (() -> BigInteger),
    length: (() -> Expression<IntSort>)
) = this().substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaBigIntegerLambdaByteLambda")
fun (() -> Expression<StringSort>).substr(start: (() -> BigInteger), length: (() -> Byte)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaBigIntegerLambdaShortLambda")
fun (() -> Expression<StringSort>).substr(start: (() -> BigInteger), length: (() -> Short)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaBigIntegerLambdaIntLambda")
fun (() -> Expression<StringSort>).substr(start: (() -> BigInteger), length: (() -> Int)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaBigIntegerLambdaLongLambda")
fun (() -> Expression<StringSort>).substr(start: (() -> BigInteger), length: (() -> Long)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringSortLambdaBigIntegerLambdaBigIntegerLambda")
fun (() -> Expression<StringSort>).substr(start: (() -> BigInteger), length: (() -> BigInteger)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("substrStringIntSortIntSort")
fun String.substr(start: Expression<IntSort>, length: Expression<IntSort>) =
    StringLiteral(this).substr(start, length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntSortByte")
fun String.substr(start: Expression<IntSort>, length: Byte) =
    StringLiteral(this).substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntSortShort")
fun String.substr(start: Expression<IntSort>, length: Short) =
    StringLiteral(this).substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntSortInt")
fun String.substr(start: Expression<IntSort>, length: Int) =
    StringLiteral(this).substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntSortLong")
fun String.substr(start: Expression<IntSort>, length: Long) =
    StringLiteral(this).substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntSortBigInteger")
fun String.substr(start: Expression<IntSort>, length: BigInteger) =
    StringLiteral(this).substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringByteIntSort")
fun String.substr(start: Byte, length: Expression<IntSort>) =
    StringLiteral(this).substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringByteByte")
fun String.substr(start: Byte, length: Byte) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringByteShort")
fun String.substr(start: Byte, length: Short) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringByteInt")
fun String.substr(start: Byte, length: Int) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringByteLong")
fun String.substr(start: Byte, length: Long) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringByteBigInteger")
fun String.substr(start: Byte, length: BigInteger) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringShortIntSort")
fun String.substr(start: Short, length: Expression<IntSort>) =
    StringLiteral(this).substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringShortByte")
fun String.substr(start: Short, length: Byte) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringShortShort")
fun String.substr(start: Short, length: Short) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringShortInt")
fun String.substr(start: Short, length: Int) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringShortLong")
fun String.substr(start: Short, length: Long) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringShortBigInteger")
fun String.substr(start: Short, length: BigInteger) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringIntIntSort")
fun String.substr(start: Int, length: Expression<IntSort>) =
    StringLiteral(this).substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntByte")
fun String.substr(start: Int, length: Byte) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntShort")
fun String.substr(start: Int, length: Short) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntInt")
fun String.substr(start: Int, length: Int) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntLong")
fun String.substr(start: Int, length: Long) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntBigInteger")
fun String.substr(start: Int, length: BigInteger) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringLongIntSort")
fun String.substr(start: Long, length: Expression<IntSort>) =
    StringLiteral(this).substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLongByte")
fun String.substr(start: Long, length: Byte) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLongShort")
fun String.substr(start: Long, length: Short) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLongInt")
fun String.substr(start: Long, length: Int) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLongLong")
fun String.substr(start: Long, length: Long) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLongBigInteger")
fun String.substr(start: Long, length: BigInteger) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringBigIntegerIntSort")
fun String.substr(start: BigInteger, length: Expression<IntSort>) =
    StringLiteral(this).substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringBigIntegerByte")
fun String.substr(start: BigInteger, length: Byte) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringBigIntegerShort")
fun String.substr(start: BigInteger, length: Short) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringBigIntegerInt")
fun String.substr(start: BigInteger, length: Int) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringBigIntegerLong")
fun String.substr(start: BigInteger, length: Long) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringBigIntegerBigInteger")
fun String.substr(start: BigInteger, length: BigInteger) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("substrStringIntSortLambdaIntSort")
fun String.substr(start: (() -> Expression<IntSort>), length: Expression<IntSort>) =
    StringLiteral(this).substr(start(), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntSortLambdaByte")
fun String.substr(start: (() -> Expression<IntSort>), length: Byte) =
    StringLiteral(this).substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntSortLambdaShort")
fun String.substr(start: (() -> Expression<IntSort>), length: Short) =
    StringLiteral(this).substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntSortLambdaInt")
fun String.substr(start: (() -> Expression<IntSort>), length: Int) =
    StringLiteral(this).substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntSortLambdaLong")
fun String.substr(start: (() -> Expression<IntSort>), length: Long) =
    StringLiteral(this).substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntSortLambdaBigInteger")
fun String.substr(start: (() -> Expression<IntSort>), length: BigInteger) =
    StringLiteral(this).substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringByteLambdaIntSort")
fun String.substr(start: (() -> Byte), length: Expression<IntSort>) =
    StringLiteral(this).substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringByteLambdaByte")
fun String.substr(start: (() -> Byte), length: Byte) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringByteLambdaShort")
fun String.substr(start: (() -> Byte), length: Short) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringByteLambdaInt")
fun String.substr(start: (() -> Byte), length: Int) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringByteLambdaLong")
fun String.substr(start: (() -> Byte), length: Long) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringByteLambdaBigInteger")
fun String.substr(start: (() -> Byte), length: BigInteger) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringShortLambdaIntSort")
fun String.substr(start: (() -> Short), length: Expression<IntSort>) =
    StringLiteral(this).substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringShortLambdaByte")
fun String.substr(start: (() -> Short), length: Byte) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringShortLambdaShort")
fun String.substr(start: (() -> Short), length: Short) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringShortLambdaInt")
fun String.substr(start: (() -> Short), length: Int) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringShortLambdaLong")
fun String.substr(start: (() -> Short), length: Long) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringShortLambdaBigInteger")
fun String.substr(start: (() -> Short), length: BigInteger) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringIntLambdaIntSort")
fun String.substr(start: (() -> Int), length: Expression<IntSort>) =
    StringLiteral(this).substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntLambdaByte")
fun String.substr(start: (() -> Int), length: Byte) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntLambdaShort")
fun String.substr(start: (() -> Int), length: Short) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntLambdaInt")
fun String.substr(start: (() -> Int), length: Int) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntLambdaLong")
fun String.substr(start: (() -> Int), length: Long) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntLambdaBigInteger")
fun String.substr(start: (() -> Int), length: BigInteger) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringLongLambdaIntSort")
fun String.substr(start: (() -> Long), length: Expression<IntSort>) =
    StringLiteral(this).substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLongLambdaByte")
fun String.substr(start: (() -> Long), length: Byte) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLongLambdaShort")
fun String.substr(start: (() -> Long), length: Short) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLongLambdaInt")
fun String.substr(start: (() -> Long), length: Int) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLongLambdaLong")
fun String.substr(start: (() -> Long), length: Long) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLongLambdaBigInteger")
fun String.substr(start: (() -> Long), length: BigInteger) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringBigIntegerLambdaIntSort")
fun String.substr(start: (() -> BigInteger), length: Expression<IntSort>) =
    StringLiteral(this).substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringBigIntegerLambdaByte")
fun String.substr(start: (() -> BigInteger), length: Byte) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringBigIntegerLambdaShort")
fun String.substr(start: (() -> BigInteger), length: Short) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringBigIntegerLambdaInt")
fun String.substr(start: (() -> BigInteger), length: Int) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringBigIntegerLambdaLong")
fun String.substr(start: (() -> BigInteger), length: Long) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringBigIntegerLambdaBigInteger")
fun String.substr(start: (() -> BigInteger), length: BigInteger) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("substrStringIntSortIntSortLambda")
fun String.substr(start: Expression<IntSort>, length: (() -> Expression<IntSort>)) =
    StringLiteral(this).substr(start, length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntSortByteLambda")
fun String.substr(start: Expression<IntSort>, length: (() -> Byte)) =
    StringLiteral(this).substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntSortShortLambda")
fun String.substr(start: Expression<IntSort>, length: (() -> Short)) =
    StringLiteral(this).substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntSortIntLambda")
fun String.substr(start: Expression<IntSort>, length: (() -> Int)) =
    StringLiteral(this).substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntSortLongLambda")
fun String.substr(start: Expression<IntSort>, length: (() -> Long)) =
    StringLiteral(this).substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntSortBigIntegerLambda")
fun String.substr(start: Expression<IntSort>, length: (() -> BigInteger)) =
    StringLiteral(this).substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringByteIntSortLambda")
fun String.substr(start: Byte, length: (() -> Expression<IntSort>)) =
    StringLiteral(this).substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringByteByteLambda")
fun String.substr(start: Byte, length: (() -> Byte)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringByteShortLambda")
fun String.substr(start: Byte, length: (() -> Short)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringByteIntLambda")
fun String.substr(start: Byte, length: (() -> Int)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringByteLongLambda")
fun String.substr(start: Byte, length: (() -> Long)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringByteBigIntegerLambda")
fun String.substr(start: Byte, length: (() -> BigInteger)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringShortIntSortLambda")
fun String.substr(start: Short, length: (() -> Expression<IntSort>)) =
    StringLiteral(this).substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringShortByteLambda")
fun String.substr(start: Short, length: (() -> Byte)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringShortShortLambda")
fun String.substr(start: Short, length: (() -> Short)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringShortIntLambda")
fun String.substr(start: Short, length: (() -> Int)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringShortLongLambda")
fun String.substr(start: Short, length: (() -> Long)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringShortBigIntegerLambda")
fun String.substr(start: Short, length: (() -> BigInteger)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringIntIntSortLambda")
fun String.substr(start: Int, length: (() -> Expression<IntSort>)) =
    StringLiteral(this).substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntByteLambda")
fun String.substr(start: Int, length: (() -> Byte)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntShortLambda")
fun String.substr(start: Int, length: (() -> Short)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntIntLambda")
fun String.substr(start: Int, length: (() -> Int)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntLongLambda")
fun String.substr(start: Int, length: (() -> Long)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntBigIntegerLambda")
fun String.substr(start: Int, length: (() -> BigInteger)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringLongIntSortLambda")
fun String.substr(start: Long, length: (() -> Expression<IntSort>)) =
    StringLiteral(this).substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLongByteLambda")
fun String.substr(start: Long, length: (() -> Byte)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLongShortLambda")
fun String.substr(start: Long, length: (() -> Short)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLongIntLambda")
fun String.substr(start: Long, length: (() -> Int)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLongLongLambda")
fun String.substr(start: Long, length: (() -> Long)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLongBigIntegerLambda")
fun String.substr(start: Long, length: (() -> BigInteger)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringBigIntegerIntSortLambda")
fun String.substr(start: BigInteger, length: (() -> Expression<IntSort>)) =
    StringLiteral(this).substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringBigIntegerByteLambda")
fun String.substr(start: BigInteger, length: (() -> Byte)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringBigIntegerShortLambda")
fun String.substr(start: BigInteger, length: (() -> Short)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringBigIntegerIntLambda")
fun String.substr(start: BigInteger, length: (() -> Int)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringBigIntegerLongLambda")
fun String.substr(start: BigInteger, length: (() -> Long)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringBigIntegerBigIntegerLambda")
fun String.substr(start: BigInteger, length: (() -> BigInteger)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("substrStringIntSortLambdaIntSortLambda")
fun String.substr(start: (() -> Expression<IntSort>), length: (() -> Expression<IntSort>)) =
    StringLiteral(this).substr(start(), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntSortLambdaByteLambda")
fun String.substr(start: (() -> Expression<IntSort>), length: (() -> Byte)) =
    StringLiteral(this).substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntSortLambdaShortLambda")
fun String.substr(start: (() -> Expression<IntSort>), length: (() -> Short)) =
    StringLiteral(this).substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntSortLambdaIntLambda")
fun String.substr(start: (() -> Expression<IntSort>), length: (() -> Int)) =
    StringLiteral(this).substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntSortLambdaLongLambda")
fun String.substr(start: (() -> Expression<IntSort>), length: (() -> Long)) =
    StringLiteral(this).substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntSortLambdaBigIntegerLambda")
fun String.substr(start: (() -> Expression<IntSort>), length: (() -> BigInteger)) =
    StringLiteral(this).substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringByteLambdaIntSortLambda")
fun String.substr(start: (() -> Byte), length: (() -> Expression<IntSort>)) =
    StringLiteral(this).substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringByteLambdaByteLambda")
fun String.substr(start: (() -> Byte), length: (() -> Byte)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringByteLambdaShortLambda")
fun String.substr(start: (() -> Byte), length: (() -> Short)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringByteLambdaIntLambda")
fun String.substr(start: (() -> Byte), length: (() -> Int)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringByteLambdaLongLambda")
fun String.substr(start: (() -> Byte), length: (() -> Long)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringByteLambdaBigIntegerLambda")
fun String.substr(start: (() -> Byte), length: (() -> BigInteger)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringShortLambdaIntSortLambda")
fun String.substr(start: (() -> Short), length: (() -> Expression<IntSort>)) =
    StringLiteral(this).substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringShortLambdaByteLambda")
fun String.substr(start: (() -> Short), length: (() -> Byte)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringShortLambdaShortLambda")
fun String.substr(start: (() -> Short), length: (() -> Short)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringShortLambdaIntLambda")
fun String.substr(start: (() -> Short), length: (() -> Int)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringShortLambdaLongLambda")
fun String.substr(start: (() -> Short), length: (() -> Long)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringShortLambdaBigIntegerLambda")
fun String.substr(start: (() -> Short), length: (() -> BigInteger)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringIntLambdaIntSortLambda")
fun String.substr(start: (() -> Int), length: (() -> Expression<IntSort>)) =
    StringLiteral(this).substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntLambdaByteLambda")
fun String.substr(start: (() -> Int), length: (() -> Byte)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntLambdaShortLambda")
fun String.substr(start: (() -> Int), length: (() -> Short)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntLambdaIntLambda")
fun String.substr(start: (() -> Int), length: (() -> Int)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntLambdaLongLambda")
fun String.substr(start: (() -> Int), length: (() -> Long)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringIntLambdaBigIntegerLambda")
fun String.substr(start: (() -> Int), length: (() -> BigInteger)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringLongLambdaIntSortLambda")
fun String.substr(start: (() -> Long), length: (() -> Expression<IntSort>)) =
    StringLiteral(this).substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLongLambdaByteLambda")
fun String.substr(start: (() -> Long), length: (() -> Byte)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLongLambdaShortLambda")
fun String.substr(start: (() -> Long), length: (() -> Short)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLongLambdaIntLambda")
fun String.substr(start: (() -> Long), length: (() -> Int)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLongLambdaLongLambda")
fun String.substr(start: (() -> Long), length: (() -> Long)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLongLambdaBigIntegerLambda")
fun String.substr(start: (() -> Long), length: (() -> BigInteger)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringBigIntegerLambdaIntSortLambda")
fun String.substr(start: (() -> BigInteger), length: (() -> Expression<IntSort>)) =
    StringLiteral(this).substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringBigIntegerLambdaByteLambda")
fun String.substr(start: (() -> BigInteger), length: (() -> Byte)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringBigIntegerLambdaShortLambda")
fun String.substr(start: (() -> BigInteger), length: (() -> Short)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringBigIntegerLambdaIntLambda")
fun String.substr(start: (() -> BigInteger), length: (() -> Int)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringBigIntegerLambdaLongLambda")
fun String.substr(start: (() -> BigInteger), length: (() -> Long)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringBigIntegerLambdaBigIntegerLambda")
fun String.substr(start: (() -> BigInteger), length: (() -> BigInteger)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("substrStringLambdaIntSortIntSort")
fun (() -> String).substr(start: Expression<IntSort>, length: Expression<IntSort>) =
    StringLiteral(this()).substr(start, length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntSortByte")
fun (() -> String).substr(start: Expression<IntSort>, length: Byte) =
    StringLiteral(this()).substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntSortShort")
fun (() -> String).substr(start: Expression<IntSort>, length: Short) =
    StringLiteral(this()).substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntSortInt")
fun (() -> String).substr(start: Expression<IntSort>, length: Int) =
    StringLiteral(this()).substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntSortLong")
fun (() -> String).substr(start: Expression<IntSort>, length: Long) =
    StringLiteral(this()).substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntSortBigInteger")
fun (() -> String).substr(start: Expression<IntSort>, length: BigInteger) =
    StringLiteral(this()).substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringLambdaByteIntSort")
fun (() -> String).substr(start: Byte, length: Expression<IntSort>) =
    StringLiteral(this()).substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaByteByte")
fun (() -> String).substr(start: Byte, length: Byte) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaByteShort")
fun (() -> String).substr(start: Byte, length: Short) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaByteInt")
fun (() -> String).substr(start: Byte, length: Int) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaByteLong")
fun (() -> String).substr(start: Byte, length: Long) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaByteBigInteger")
fun (() -> String).substr(start: Byte, length: BigInteger) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringLambdaShortIntSort")
fun (() -> String).substr(start: Short, length: Expression<IntSort>) =
    StringLiteral(this()).substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaShortByte")
fun (() -> String).substr(start: Short, length: Byte) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaShortShort")
fun (() -> String).substr(start: Short, length: Short) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaShortInt")
fun (() -> String).substr(start: Short, length: Int) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaShortLong")
fun (() -> String).substr(start: Short, length: Long) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaShortBigInteger")
fun (() -> String).substr(start: Short, length: BigInteger) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringLambdaIntIntSort")
fun (() -> String).substr(start: Int, length: Expression<IntSort>) =
    StringLiteral(this()).substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntByte")
fun (() -> String).substr(start: Int, length: Byte) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntShort")
fun (() -> String).substr(start: Int, length: Short) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntInt")
fun (() -> String).substr(start: Int, length: Int) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntLong")
fun (() -> String).substr(start: Int, length: Long) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntBigInteger")
fun (() -> String).substr(start: Int, length: BigInteger) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringLambdaLongIntSort")
fun (() -> String).substr(start: Long, length: Expression<IntSort>) =
    StringLiteral(this()).substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaLongByte")
fun (() -> String).substr(start: Long, length: Byte) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaLongShort")
fun (() -> String).substr(start: Long, length: Short) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaLongInt")
fun (() -> String).substr(start: Long, length: Int) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaLongLong")
fun (() -> String).substr(start: Long, length: Long) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaLongBigInteger")
fun (() -> String).substr(start: Long, length: BigInteger) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringLambdaBigIntegerIntSort")
fun (() -> String).substr(start: BigInteger, length: Expression<IntSort>) =
    StringLiteral(this()).substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaBigIntegerByte")
fun (() -> String).substr(start: BigInteger, length: Byte) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaBigIntegerShort")
fun (() -> String).substr(start: BigInteger, length: Short) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaBigIntegerInt")
fun (() -> String).substr(start: BigInteger, length: Int) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaBigIntegerLong")
fun (() -> String).substr(start: BigInteger, length: Long) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaBigIntegerBigInteger")
fun (() -> String).substr(start: BigInteger, length: BigInteger) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("substrStringLambdaIntSortLambdaIntSort")
fun (() -> String).substr(start: (() -> Expression<IntSort>), length: Expression<IntSort>) =
    StringLiteral(this()).substr(start(), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntSortLambdaByte")
fun (() -> String).substr(start: (() -> Expression<IntSort>), length: Byte) =
    StringLiteral(this()).substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntSortLambdaShort")
fun (() -> String).substr(start: (() -> Expression<IntSort>), length: Short) =
    StringLiteral(this()).substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntSortLambdaInt")
fun (() -> String).substr(start: (() -> Expression<IntSort>), length: Int) =
    StringLiteral(this()).substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntSortLambdaLong")
fun (() -> String).substr(start: (() -> Expression<IntSort>), length: Long) =
    StringLiteral(this()).substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntSortLambdaBigInteger")
fun (() -> String).substr(start: (() -> Expression<IntSort>), length: BigInteger) =
    StringLiteral(this()).substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringLambdaByteLambdaIntSort")
fun (() -> String).substr(start: (() -> Byte), length: Expression<IntSort>) =
    StringLiteral(this()).substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaByteLambdaByte")
fun (() -> String).substr(start: (() -> Byte), length: Byte) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaByteLambdaShort")
fun (() -> String).substr(start: (() -> Byte), length: Short) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaByteLambdaInt")
fun (() -> String).substr(start: (() -> Byte), length: Int) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaByteLambdaLong")
fun (() -> String).substr(start: (() -> Byte), length: Long) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaByteLambdaBigInteger")
fun (() -> String).substr(start: (() -> Byte), length: BigInteger) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringLambdaShortLambdaIntSort")
fun (() -> String).substr(start: (() -> Short), length: Expression<IntSort>) =
    StringLiteral(this()).substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaShortLambdaByte")
fun (() -> String).substr(start: (() -> Short), length: Byte) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaShortLambdaShort")
fun (() -> String).substr(start: (() -> Short), length: Short) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaShortLambdaInt")
fun (() -> String).substr(start: (() -> Short), length: Int) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaShortLambdaLong")
fun (() -> String).substr(start: (() -> Short), length: Long) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaShortLambdaBigInteger")
fun (() -> String).substr(start: (() -> Short), length: BigInteger) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringLambdaIntLambdaIntSort")
fun (() -> String).substr(start: (() -> Int), length: Expression<IntSort>) =
    StringLiteral(this()).substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntLambdaByte")
fun (() -> String).substr(start: (() -> Int), length: Byte) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntLambdaShort")
fun (() -> String).substr(start: (() -> Int), length: Short) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntLambdaInt")
fun (() -> String).substr(start: (() -> Int), length: Int) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntLambdaLong")
fun (() -> String).substr(start: (() -> Int), length: Long) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntLambdaBigInteger")
fun (() -> String).substr(start: (() -> Int), length: BigInteger) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringLambdaLongLambdaIntSort")
fun (() -> String).substr(start: (() -> Long), length: Expression<IntSort>) =
    StringLiteral(this()).substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaLongLambdaByte")
fun (() -> String).substr(start: (() -> Long), length: Byte) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaLongLambdaShort")
fun (() -> String).substr(start: (() -> Long), length: Short) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaLongLambdaInt")
fun (() -> String).substr(start: (() -> Long), length: Int) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaLongLambdaLong")
fun (() -> String).substr(start: (() -> Long), length: Long) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaLongLambdaBigInteger")
fun (() -> String).substr(start: (() -> Long), length: BigInteger) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringLambdaBigIntegerLambdaIntSort")
fun (() -> String).substr(start: (() -> BigInteger), length: Expression<IntSort>) =
    StringLiteral(this()).substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaBigIntegerLambdaByte")
fun (() -> String).substr(start: (() -> BigInteger), length: Byte) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaBigIntegerLambdaShort")
fun (() -> String).substr(start: (() -> BigInteger), length: Short) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaBigIntegerLambdaInt")
fun (() -> String).substr(start: (() -> BigInteger), length: Int) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaBigIntegerLambdaLong")
fun (() -> String).substr(start: (() -> BigInteger), length: Long) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaBigIntegerLambdaBigInteger")
fun (() -> String).substr(start: (() -> BigInteger), length: BigInteger) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("substrStringLambdaIntSortIntSortLambda")
fun (() -> String).substr(start: Expression<IntSort>, length: (() -> Expression<IntSort>)) =
    StringLiteral(this()).substr(start, length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntSortByteLambda")
fun (() -> String).substr(start: Expression<IntSort>, length: (() -> Byte)) =
    StringLiteral(this()).substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntSortShortLambda")
fun (() -> String).substr(start: Expression<IntSort>, length: (() -> Short)) =
    StringLiteral(this()).substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntSortIntLambda")
fun (() -> String).substr(start: Expression<IntSort>, length: (() -> Int)) =
    StringLiteral(this()).substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntSortLongLambda")
fun (() -> String).substr(start: Expression<IntSort>, length: (() -> Long)) =
    StringLiteral(this()).substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntSortBigIntegerLambda")
fun (() -> String).substr(start: Expression<IntSort>, length: (() -> BigInteger)) =
    StringLiteral(this()).substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringLambdaByteIntSortLambda")
fun (() -> String).substr(start: Byte, length: (() -> Expression<IntSort>)) =
    StringLiteral(this()).substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaByteByteLambda")
fun (() -> String).substr(start: Byte, length: (() -> Byte)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaByteShortLambda")
fun (() -> String).substr(start: Byte, length: (() -> Short)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaByteIntLambda")
fun (() -> String).substr(start: Byte, length: (() -> Int)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaByteLongLambda")
fun (() -> String).substr(start: Byte, length: (() -> Long)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaByteBigIntegerLambda")
fun (() -> String).substr(start: Byte, length: (() -> BigInteger)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringLambdaShortIntSortLambda")
fun (() -> String).substr(start: Short, length: (() -> Expression<IntSort>)) =
    StringLiteral(this()).substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaShortByteLambda")
fun (() -> String).substr(start: Short, length: (() -> Byte)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaShortShortLambda")
fun (() -> String).substr(start: Short, length: (() -> Short)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaShortIntLambda")
fun (() -> String).substr(start: Short, length: (() -> Int)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaShortLongLambda")
fun (() -> String).substr(start: Short, length: (() -> Long)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaShortBigIntegerLambda")
fun (() -> String).substr(start: Short, length: (() -> BigInteger)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringLambdaIntIntSortLambda")
fun (() -> String).substr(start: Int, length: (() -> Expression<IntSort>)) =
    StringLiteral(this()).substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntByteLambda")
fun (() -> String).substr(start: Int, length: (() -> Byte)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntShortLambda")
fun (() -> String).substr(start: Int, length: (() -> Short)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntIntLambda")
fun (() -> String).substr(start: Int, length: (() -> Int)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntLongLambda")
fun (() -> String).substr(start: Int, length: (() -> Long)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntBigIntegerLambda")
fun (() -> String).substr(start: Int, length: (() -> BigInteger)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringLambdaLongIntSortLambda")
fun (() -> String).substr(start: Long, length: (() -> Expression<IntSort>)) =
    StringLiteral(this()).substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaLongByteLambda")
fun (() -> String).substr(start: Long, length: (() -> Byte)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaLongShortLambda")
fun (() -> String).substr(start: Long, length: (() -> Short)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaLongIntLambda")
fun (() -> String).substr(start: Long, length: (() -> Int)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaLongLongLambda")
fun (() -> String).substr(start: Long, length: (() -> Long)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaLongBigIntegerLambda")
fun (() -> String).substr(start: Long, length: (() -> BigInteger)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringLambdaBigIntegerIntSortLambda")
fun (() -> String).substr(start: BigInteger, length: (() -> Expression<IntSort>)) =
    StringLiteral(this()).substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaBigIntegerByteLambda")
fun (() -> String).substr(start: BigInteger, length: (() -> Byte)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaBigIntegerShortLambda")
fun (() -> String).substr(start: BigInteger, length: (() -> Short)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaBigIntegerIntLambda")
fun (() -> String).substr(start: BigInteger, length: (() -> Int)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaBigIntegerLongLambda")
fun (() -> String).substr(start: BigInteger, length: (() -> Long)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaBigIntegerBigIntegerLambda")
fun (() -> String).substr(start: BigInteger, length: (() -> BigInteger)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("substrStringLambdaIntSortLambdaIntSortLambda")
fun (() -> String).substr(start: (() -> Expression<IntSort>), length: (() -> Expression<IntSort>)) =
    StringLiteral(this()).substr(start(), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntSortLambdaByteLambda")
fun (() -> String).substr(start: (() -> Expression<IntSort>), length: (() -> Byte)) =
    StringLiteral(this()).substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntSortLambdaShortLambda")
fun (() -> String).substr(start: (() -> Expression<IntSort>), length: (() -> Short)) =
    StringLiteral(this()).substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntSortLambdaIntLambda")
fun (() -> String).substr(start: (() -> Expression<IntSort>), length: (() -> Int)) =
    StringLiteral(this()).substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntSortLambdaLongLambda")
fun (() -> String).substr(start: (() -> Expression<IntSort>), length: (() -> Long)) =
    StringLiteral(this()).substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntSortLambdaBigIntegerLambda")
fun (() -> String).substr(start: (() -> Expression<IntSort>), length: (() -> BigInteger)) =
    StringLiteral(this()).substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringLambdaByteLambdaIntSortLambda")
fun (() -> String).substr(start: (() -> Byte), length: (() -> Expression<IntSort>)) =
    StringLiteral(this()).substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaByteLambdaByteLambda")
fun (() -> String).substr(start: (() -> Byte), length: (() -> Byte)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaByteLambdaShortLambda")
fun (() -> String).substr(start: (() -> Byte), length: (() -> Short)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaByteLambdaIntLambda")
fun (() -> String).substr(start: (() -> Byte), length: (() -> Int)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaByteLambdaLongLambda")
fun (() -> String).substr(start: (() -> Byte), length: (() -> Long)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaByteLambdaBigIntegerLambda")
fun (() -> String).substr(start: (() -> Byte), length: (() -> BigInteger)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringLambdaShortLambdaIntSortLambda")
fun (() -> String).substr(start: (() -> Short), length: (() -> Expression<IntSort>)) =
    StringLiteral(this()).substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaShortLambdaByteLambda")
fun (() -> String).substr(start: (() -> Short), length: (() -> Byte)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaShortLambdaShortLambda")
fun (() -> String).substr(start: (() -> Short), length: (() -> Short)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaShortLambdaIntLambda")
fun (() -> String).substr(start: (() -> Short), length: (() -> Int)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaShortLambdaLongLambda")
fun (() -> String).substr(start: (() -> Short), length: (() -> Long)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaShortLambdaBigIntegerLambda")
fun (() -> String).substr(start: (() -> Short), length: (() -> BigInteger)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringLambdaIntLambdaIntSortLambda")
fun (() -> String).substr(start: (() -> Int), length: (() -> Expression<IntSort>)) =
    StringLiteral(this()).substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntLambdaByteLambda")
fun (() -> String).substr(start: (() -> Int), length: (() -> Byte)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntLambdaShortLambda")
fun (() -> String).substr(start: (() -> Int), length: (() -> Short)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntLambdaIntLambda")
fun (() -> String).substr(start: (() -> Int), length: (() -> Int)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntLambdaLongLambda")
fun (() -> String).substr(start: (() -> Int), length: (() -> Long)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaIntLambdaBigIntegerLambda")
fun (() -> String).substr(start: (() -> Int), length: (() -> BigInteger)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringLambdaLongLambdaIntSortLambda")
fun (() -> String).substr(start: (() -> Long), length: (() -> Expression<IntSort>)) =
    StringLiteral(this()).substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaLongLambdaByteLambda")
fun (() -> String).substr(start: (() -> Long), length: (() -> Byte)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaLongLambdaShortLambda")
fun (() -> String).substr(start: (() -> Long), length: (() -> Short)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaLongLambdaIntLambda")
fun (() -> String).substr(start: (() -> Long), length: (() -> Int)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaLongLambdaLongLambda")
fun (() -> String).substr(start: (() -> Long), length: (() -> Long)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaLongLambdaBigIntegerLambda")
fun (() -> String).substr(start: (() -> Long), length: (() -> BigInteger)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .
 */
@JvmName("substrStringLambdaBigIntegerLambdaIntSortLambda")
fun (() -> String).substr(start: (() -> BigInteger), length: (() -> Expression<IntSort>)) =
    StringLiteral(this()).substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaBigIntegerLambdaByteLambda")
fun (() -> String).substr(start: (() -> BigInteger), length: (() -> Byte)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaBigIntegerLambdaShortLambda")
fun (() -> String).substr(start: (() -> BigInteger), length: (() -> Short)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaBigIntegerLambdaIntLambda")
fun (() -> String).substr(start: (() -> BigInteger), length: (() -> Int)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaBigIntegerLambdaLongLambda")
fun (() -> String).substr(start: (() -> BigInteger), length: (() -> Long)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [start] is converted to [IntLiteral] .* - [length] is converted to [IntLiteral]
 */
@JvmName("substrStringLambdaBigIntegerLambdaBigIntegerLambda")
fun (() -> String).substr(start: (() -> BigInteger), length: (() -> BigInteger)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/** Check if [this] is a prefix of [rhs]. */
infix fun Expression<StringSort>.prefixof(rhs: Expression<StringSort>) = StrPrefixOf(this, rhs)

/**
 * Check if [this] is a prefix of [rhs].
 * - [rhs] is converted to [StringLiteral] .
 */
@JvmName("prefixofStringSortString")
infix fun Expression<StringSort>.prefixof(rhs: String) = this prefixof StringLiteral(rhs)

/** Check if [this] is a prefix of [rhs]. */
@JvmName("prefixofStringSortStringSortLambda")
infix fun Expression<StringSort>.prefixof(rhs: (() -> Expression<StringSort>)) = this prefixof rhs()

/**
 * Check if [this] is a prefix of [rhs].
 * - [rhs] is converted to [StringLiteral] .
 */
@JvmName("prefixofStringSortStringLambda")
infix fun Expression<StringSort>.prefixof(rhs: (() -> String)) = this prefixof StringLiteral(rhs())

/** Check if [this] is a prefix of [rhs]. */
@JvmName("prefixofStringSortLambdaStringSort")
infix fun (() -> Expression<StringSort>).prefixof(rhs: Expression<StringSort>) = this() prefixof rhs

/**
 * Check if [this] is a prefix of [rhs].
 * - [rhs] is converted to [StringLiteral]
 */
@JvmName("prefixofStringSortLambdaString")
infix fun (() -> Expression<StringSort>).prefixof(rhs: String) = this() prefixof StringLiteral(rhs)

/** Check if [this] is a prefix of [rhs]. */
@JvmName("prefixofStringSortLambdaStringSortLambda")
infix fun (() -> Expression<StringSort>).prefixof(rhs: (() -> Expression<StringSort>)) =
    this() prefixof rhs()

/**
 * Check if [this] is a prefix of [rhs].
 * - [rhs] is converted to [StringLiteral]
 */
@JvmName("prefixofStringSortLambdaStringLambda")
infix fun (() -> Expression<StringSort>).prefixof(rhs: (() -> String)) =
    this() prefixof StringLiteral(rhs())

/**
 * Check if [this] is a prefix of [rhs].
 * - [String] is converted to [StringLiteral] .
 */
@JvmName("prefixofStringStringSort")
infix fun String.prefixof(rhs: Expression<StringSort>) = StringLiteral(this) prefixof rhs

/**
 * Check if [this] is a prefix of [rhs].
 * - [String] is converted to [StringLiteral]
 * - [rhs] is converted to [StringLiteral] .
 */
@JvmName("prefixofStringString")
infix fun String.prefixof(rhs: String) = StringLiteral(this) prefixof StringLiteral(rhs)

/**
 * Check if [this] is a prefix of [rhs].
 * - [String] is converted to [StringLiteral] .
 */
@JvmName("prefixofStringStringSortLambda")
infix fun String.prefixof(rhs: (() -> Expression<StringSort>)) = StringLiteral(this) prefixof rhs()

/**
 * Check if [this] is a prefix of [rhs].
 * - [String] is converted to [StringLiteral]
 * - [rhs] is converted to [StringLiteral] .
 */
@JvmName("prefixofStringStringLambda")
infix fun String.prefixof(rhs: (() -> String)) = StringLiteral(this) prefixof StringLiteral(rhs())

/** Check if [this] is a prefix of [rhs]. */
@JvmName("prefixofStringLambdaStringSort")
infix fun (() -> String).prefixof(rhs: Expression<StringSort>) = StringLiteral(this()) prefixof rhs

/**
 * Check if [this] is a prefix of [rhs].
 * - [rhs] is converted to [StringLiteral]
 */
@JvmName("prefixofStringLambdaString")
infix fun (() -> String).prefixof(rhs: String) = StringLiteral(this()) prefixof StringLiteral(rhs)

/** Check if [this] is a prefix of [rhs]. */
@JvmName("prefixofStringLambdaStringSortLambda")
infix fun (() -> String).prefixof(rhs: (() -> Expression<StringSort>)) =
    StringLiteral(this()) prefixof rhs()

/**
 * Check if [this] is a prefix of [rhs].
 * - [rhs] is converted to [StringLiteral]
 */
@JvmName("prefixofStringLambdaStringLambda")
infix fun (() -> String).prefixof(rhs: (() -> String)) =
    StringLiteral(this()) prefixof StringLiteral(rhs())

/** Check if [this] is a suffix of [rhs]. */
infix fun Expression<StringSort>.suffixof(rhs: Expression<StringSort>) = StrSuffixOf(this, rhs)

/**
 * Check if [this] is a suffix of [rhs].
 * - [rhs] is converted to [StringLiteral] .
 */
@JvmName("suffixofStringSortString")
infix fun Expression<StringSort>.suffixof(rhs: String) = this suffixof StringLiteral(rhs)

/** Check if [this] is a suffix of [rhs]. */
@JvmName("suffixofStringSortStringSortLambda")
infix fun Expression<StringSort>.suffixof(rhs: (() -> Expression<StringSort>)) = this suffixof rhs()

/**
 * Check if [this] is a suffix of [rhs].
 * - [rhs] is converted to [StringLiteral] .
 */
@JvmName("suffixofStringSortStringLambda")
infix fun Expression<StringSort>.suffixof(rhs: (() -> String)) = this suffixof StringLiteral(rhs())

/** Check if [this] is a suffix of [rhs]. */
@JvmName("suffixofStringSortLambdaStringSort")
infix fun (() -> Expression<StringSort>).suffixof(rhs: Expression<StringSort>) = this() suffixof rhs

/**
 * Check if [this] is a suffix of [rhs].
 * - [rhs] is converted to [StringLiteral]
 */
@JvmName("suffixofStringSortLambdaString")
infix fun (() -> Expression<StringSort>).suffixof(rhs: String) = this() suffixof StringLiteral(rhs)

/** Check if [this] is a suffix of [rhs]. */
@JvmName("suffixofStringSortLambdaStringSortLambda")
infix fun (() -> Expression<StringSort>).suffixof(rhs: (() -> Expression<StringSort>)) =
    this() suffixof rhs()

/**
 * Check if [this] is a suffix of [rhs].
 * - [rhs] is converted to [StringLiteral]
 */
@JvmName("suffixofStringSortLambdaStringLambda")
infix fun (() -> Expression<StringSort>).suffixof(rhs: (() -> String)) =
    this() suffixof StringLiteral(rhs())

/**
 * Check if [this] is a suffix of [rhs].
 * - [String] is converted to [StringLiteral] .
 */
@JvmName("suffixofStringStringSort")
infix fun String.suffixof(rhs: Expression<StringSort>) = StringLiteral(this) suffixof rhs

/**
 * Check if [this] is a suffix of [rhs].
 * - [String] is converted to [StringLiteral]
 * - [rhs] is converted to [StringLiteral] .
 */
@JvmName("suffixofStringString")
infix fun String.suffixof(rhs: String) = StringLiteral(this) suffixof StringLiteral(rhs)

/**
 * Check if [this] is a suffix of [rhs].
 * - [String] is converted to [StringLiteral] .
 */
@JvmName("suffixofStringStringSortLambda")
infix fun String.suffixof(rhs: (() -> Expression<StringSort>)) = StringLiteral(this) suffixof rhs()

/**
 * Check if [this] is a suffix of [rhs].
 * - [String] is converted to [StringLiteral]
 * - [rhs] is converted to [StringLiteral] .
 */
@JvmName("suffixofStringStringLambda")
infix fun String.suffixof(rhs: (() -> String)) = StringLiteral(this) suffixof StringLiteral(rhs())

/** Check if [this] is a suffix of [rhs]. */
@JvmName("suffixofStringLambdaStringSort")
infix fun (() -> String).suffixof(rhs: Expression<StringSort>) = StringLiteral(this()) suffixof rhs

/**
 * Check if [this] is a suffix of [rhs].
 * - [rhs] is converted to [StringLiteral]
 */
@JvmName("suffixofStringLambdaString")
infix fun (() -> String).suffixof(rhs: String) = StringLiteral(this()) suffixof StringLiteral(rhs)

/** Check if [this] is a suffix of [rhs]. */
@JvmName("suffixofStringLambdaStringSortLambda")
infix fun (() -> String).suffixof(rhs: (() -> Expression<StringSort>)) =
    StringLiteral(this()) suffixof rhs()

/**
 * Check if [this] is a suffix of [rhs].
 * - [rhs] is converted to [StringLiteral]
 */
@JvmName("suffixofStringLambdaStringLambda")
infix fun (() -> String).suffixof(rhs: (() -> String)) =
    StringLiteral(this()) suffixof StringLiteral(rhs())

/** Check if [this] contains [rhs] as substring. */
infix fun Expression<StringSort>.contains(rhs: Expression<StringSort>) = StrContains(this, rhs)

/**
 * Check if [this] contains [rhs] as substring.
 * - [rhs] is converted to [StringLiteral] .
 */
@JvmName("containsStringSortString")
infix fun Expression<StringSort>.contains(rhs: String) = this contains StringLiteral(rhs)

/** Check if [this] contains [rhs] as substring. */
@JvmName("containsStringSortStringSortLambda")
infix fun Expression<StringSort>.contains(rhs: (() -> Expression<StringSort>)) = this contains rhs()

/**
 * Check if [this] contains [rhs] as substring.
 * - [rhs] is converted to [StringLiteral] .
 */
@JvmName("containsStringSortStringLambda")
infix fun Expression<StringSort>.contains(rhs: (() -> String)) = this contains StringLiteral(rhs())

/** Check if [this] contains [rhs] as substring. */
@JvmName("containsStringSortLambdaStringSort")
infix fun (() -> Expression<StringSort>).contains(rhs: Expression<StringSort>) = this() contains rhs

/**
 * Check if [this] contains [rhs] as substring.
 * - [rhs] is converted to [StringLiteral]
 */
@JvmName("containsStringSortLambdaString")
infix fun (() -> Expression<StringSort>).contains(rhs: String) = this() contains StringLiteral(rhs)

/** Check if [this] contains [rhs] as substring. */
@JvmName("containsStringSortLambdaStringSortLambda")
infix fun (() -> Expression<StringSort>).contains(rhs: (() -> Expression<StringSort>)) =
    this() contains rhs()

/**
 * Check if [this] contains [rhs] as substring.
 * - [rhs] is converted to [StringLiteral]
 */
@JvmName("containsStringSortLambdaStringLambda")
infix fun (() -> Expression<StringSort>).contains(rhs: (() -> String)) =
    this() contains StringLiteral(rhs())

/**
 * Check if [this] contains [rhs] as substring.
 * - [String] is converted to [StringLiteral] .
 */
@JvmName("containsStringStringSort")
infix fun String.contains(rhs: Expression<StringSort>) = StringLiteral(this) contains rhs

/**
 * Check if [this] contains [rhs] as substring.
 * - [String] is converted to [StringLiteral]
 * - [rhs] is converted to [StringLiteral] .
 */
@JvmName("containsStringString")
infix fun String.contains(rhs: String) = StringLiteral(this) contains StringLiteral(rhs)

/**
 * Check if [this] contains [rhs] as substring.
 * - [String] is converted to [StringLiteral] .
 */
@JvmName("containsStringStringSortLambda")
infix fun String.contains(rhs: (() -> Expression<StringSort>)) = StringLiteral(this) contains rhs()

/**
 * Check if [this] contains [rhs] as substring.
 * - [String] is converted to [StringLiteral]
 * - [rhs] is converted to [StringLiteral] .
 */
@JvmName("containsStringStringLambda")
infix fun String.contains(rhs: (() -> String)) = StringLiteral(this) contains StringLiteral(rhs())

/** Check if [this] contains [rhs] as substring. */
@JvmName("containsStringLambdaStringSort")
infix fun (() -> String).contains(rhs: Expression<StringSort>) = StringLiteral(this()) contains rhs

/**
 * Check if [this] contains [rhs] as substring.
 * - [rhs] is converted to [StringLiteral]
 */
@JvmName("containsStringLambdaString")
infix fun (() -> String).contains(rhs: String) = StringLiteral(this()) contains StringLiteral(rhs)

/** Check if [this] contains [rhs] as substring. */
@JvmName("containsStringLambdaStringSortLambda")
infix fun (() -> String).contains(rhs: (() -> Expression<StringSort>)) =
    StringLiteral(this()) contains rhs()

/**
 * Check if [this] contains [rhs] as substring.
 * - [rhs] is converted to [StringLiteral]
 */
@JvmName("containsStringLambdaStringLambda")
infix fun (() -> String).contains(rhs: (() -> String)) =
    StringLiteral(this()) contains StringLiteral(rhs())

/** Index of first occurrence of [substring] in [this] starting at [start]. */
fun Expression<StringSort>.indexof(substring: Expression<StringSort>, start: Expression<IntSort>) =
    StrIndexOf(this, substring, start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortStringSortByte")
fun Expression<StringSort>.indexof(substring: Expression<StringSort>, start: Byte) =
    this.indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortStringSortShort")
fun Expression<StringSort>.indexof(substring: Expression<StringSort>, start: Short) =
    this.indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortStringSortInt")
fun Expression<StringSort>.indexof(substring: Expression<StringSort>, start: Int) =
    this.indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortStringSortLong")
fun Expression<StringSort>.indexof(substring: Expression<StringSort>, start: Long) =
    this.indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortStringSortBigInteger")
fun Expression<StringSort>.indexof(substring: Expression<StringSort>, start: BigInteger) =
    this.indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .
 */
@JvmName("indexofStringSortStringIntSort")
fun Expression<StringSort>.indexof(substring: String, start: Expression<IntSort>) =
    this.indexof(StringLiteral(substring), start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortStringByte")
fun Expression<StringSort>.indexof(substring: String, start: Byte) =
    this.indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortStringShort")
fun Expression<StringSort>.indexof(substring: String, start: Short) =
    this.indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortStringInt")
fun Expression<StringSort>.indexof(substring: String, start: Int) =
    this.indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortStringLong")
fun Expression<StringSort>.indexof(substring: String, start: Long) =
    this.indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortStringBigInteger")
fun Expression<StringSort>.indexof(substring: String, start: BigInteger) =
    this.indexof(StringLiteral(substring), IntLiteral(start))

/** Index of first occurrence of [substring] in [this] starting at [start]. */
@JvmName("indexofStringSortStringSortLambdaIntSort")
fun Expression<StringSort>.indexof(
    substring: (() -> Expression<StringSort>),
    start: Expression<IntSort>
) = this.indexof(substring(), start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortStringSortLambdaByte")
fun Expression<StringSort>.indexof(substring: (() -> Expression<StringSort>), start: Byte) =
    this.indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortStringSortLambdaShort")
fun Expression<StringSort>.indexof(substring: (() -> Expression<StringSort>), start: Short) =
    this.indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortStringSortLambdaInt")
fun Expression<StringSort>.indexof(substring: (() -> Expression<StringSort>), start: Int) =
    this.indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortStringSortLambdaLong")
fun Expression<StringSort>.indexof(substring: (() -> Expression<StringSort>), start: Long) =
    this.indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortStringSortLambdaBigInteger")
fun Expression<StringSort>.indexof(substring: (() -> Expression<StringSort>), start: BigInteger) =
    this.indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .
 */
@JvmName("indexofStringSortStringLambdaIntSort")
fun Expression<StringSort>.indexof(substring: (() -> String), start: Expression<IntSort>) =
    this.indexof(StringLiteral(substring()), start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortStringLambdaByte")
fun Expression<StringSort>.indexof(substring: (() -> String), start: Byte) =
    this.indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortStringLambdaShort")
fun Expression<StringSort>.indexof(substring: (() -> String), start: Short) =
    this.indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortStringLambdaInt")
fun Expression<StringSort>.indexof(substring: (() -> String), start: Int) =
    this.indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortStringLambdaLong")
fun Expression<StringSort>.indexof(substring: (() -> String), start: Long) =
    this.indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortStringLambdaBigInteger")
fun Expression<StringSort>.indexof(substring: (() -> String), start: BigInteger) =
    this.indexof(StringLiteral(substring()), IntLiteral(start))

/** Index of first occurrence of [substring] in [this] starting at [start]. */
@JvmName("indexofStringSortStringSortIntSortLambda")
fun Expression<StringSort>.indexof(
    substring: Expression<StringSort>,
    start: (() -> Expression<IntSort>)
) = this.indexof(substring, start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortStringSortByteLambda")
fun Expression<StringSort>.indexof(substring: Expression<StringSort>, start: (() -> Byte)) =
    this.indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortStringSortShortLambda")
fun Expression<StringSort>.indexof(substring: Expression<StringSort>, start: (() -> Short)) =
    this.indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortStringSortIntLambda")
fun Expression<StringSort>.indexof(substring: Expression<StringSort>, start: (() -> Int)) =
    this.indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortStringSortLongLambda")
fun Expression<StringSort>.indexof(substring: Expression<StringSort>, start: (() -> Long)) =
    this.indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortStringSortBigIntegerLambda")
fun Expression<StringSort>.indexof(substring: Expression<StringSort>, start: (() -> BigInteger)) =
    this.indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .
 */
@JvmName("indexofStringSortStringIntSortLambda")
fun Expression<StringSort>.indexof(substring: String, start: (() -> Expression<IntSort>)) =
    this.indexof(StringLiteral(substring), start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortStringByteLambda")
fun Expression<StringSort>.indexof(substring: String, start: (() -> Byte)) =
    this.indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortStringShortLambda")
fun Expression<StringSort>.indexof(substring: String, start: (() -> Short)) =
    this.indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortStringIntLambda")
fun Expression<StringSort>.indexof(substring: String, start: (() -> Int)) =
    this.indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortStringLongLambda")
fun Expression<StringSort>.indexof(substring: String, start: (() -> Long)) =
    this.indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortStringBigIntegerLambda")
fun Expression<StringSort>.indexof(substring: String, start: (() -> BigInteger)) =
    this.indexof(StringLiteral(substring), IntLiteral(start()))

/** Index of first occurrence of [substring] in [this] starting at [start]. */
@JvmName("indexofStringSortStringSortLambdaIntSortLambda")
fun Expression<StringSort>.indexof(
    substring: (() -> Expression<StringSort>),
    start: (() -> Expression<IntSort>)
) = this.indexof(substring(), start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortStringSortLambdaByteLambda")
fun Expression<StringSort>.indexof(substring: (() -> Expression<StringSort>), start: (() -> Byte)) =
    this.indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortStringSortLambdaShortLambda")
fun Expression<StringSort>.indexof(
    substring: (() -> Expression<StringSort>),
    start: (() -> Short)
) = this.indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortStringSortLambdaIntLambda")
fun Expression<StringSort>.indexof(substring: (() -> Expression<StringSort>), start: (() -> Int)) =
    this.indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortStringSortLambdaLongLambda")
fun Expression<StringSort>.indexof(substring: (() -> Expression<StringSort>), start: (() -> Long)) =
    this.indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortStringSortLambdaBigIntegerLambda")
fun Expression<StringSort>.indexof(
    substring: (() -> Expression<StringSort>),
    start: (() -> BigInteger)
) = this.indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .
 */
@JvmName("indexofStringSortStringLambdaIntSortLambda")
fun Expression<StringSort>.indexof(substring: (() -> String), start: (() -> Expression<IntSort>)) =
    this.indexof(StringLiteral(substring()), start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortStringLambdaByteLambda")
fun Expression<StringSort>.indexof(substring: (() -> String), start: (() -> Byte)) =
    this.indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortStringLambdaShortLambda")
fun Expression<StringSort>.indexof(substring: (() -> String), start: (() -> Short)) =
    this.indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortStringLambdaIntLambda")
fun Expression<StringSort>.indexof(substring: (() -> String), start: (() -> Int)) =
    this.indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortStringLambdaLongLambda")
fun Expression<StringSort>.indexof(substring: (() -> String), start: (() -> Long)) =
    this.indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortStringLambdaBigIntegerLambda")
fun Expression<StringSort>.indexof(substring: (() -> String), start: (() -> BigInteger)) =
    this.indexof(StringLiteral(substring()), IntLiteral(start()))

/** Index of first occurrence of [substring] in [this] starting at [start]. */
@JvmName("indexofStringSortLambdaStringSortIntSort")
fun (() -> Expression<StringSort>).indexof(
    substring: Expression<StringSort>,
    start: Expression<IntSort>
) = this().indexof(substring, start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringSortByte")
fun (() -> Expression<StringSort>).indexof(substring: Expression<StringSort>, start: Byte) =
    this().indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringSortShort")
fun (() -> Expression<StringSort>).indexof(substring: Expression<StringSort>, start: Short) =
    this().indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringSortInt")
fun (() -> Expression<StringSort>).indexof(substring: Expression<StringSort>, start: Int) =
    this().indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringSortLong")
fun (() -> Expression<StringSort>).indexof(substring: Expression<StringSort>, start: Long) =
    this().indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringSortBigInteger")
fun (() -> Expression<StringSort>).indexof(substring: Expression<StringSort>, start: BigInteger) =
    this().indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .
 */
@JvmName("indexofStringSortLambdaStringIntSort")
fun (() -> Expression<StringSort>).indexof(substring: String, start: Expression<IntSort>) =
    this().indexof(StringLiteral(substring), start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringByte")
fun (() -> Expression<StringSort>).indexof(substring: String, start: Byte) =
    this().indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringShort")
fun (() -> Expression<StringSort>).indexof(substring: String, start: Short) =
    this().indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringInt")
fun (() -> Expression<StringSort>).indexof(substring: String, start: Int) =
    this().indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringLong")
fun (() -> Expression<StringSort>).indexof(substring: String, start: Long) =
    this().indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringBigInteger")
fun (() -> Expression<StringSort>).indexof(substring: String, start: BigInteger) =
    this().indexof(StringLiteral(substring), IntLiteral(start))

/** Index of first occurrence of [substring] in [this] starting at [start]. */
@JvmName("indexofStringSortLambdaStringSortLambdaIntSort")
fun (() -> Expression<StringSort>).indexof(
    substring: (() -> Expression<StringSort>),
    start: Expression<IntSort>
) = this().indexof(substring(), start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringSortLambdaByte")
fun (() -> Expression<StringSort>).indexof(substring: (() -> Expression<StringSort>), start: Byte) =
    this().indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringSortLambdaShort")
fun (() -> Expression<StringSort>).indexof(
    substring: (() -> Expression<StringSort>),
    start: Short
) = this().indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringSortLambdaInt")
fun (() -> Expression<StringSort>).indexof(substring: (() -> Expression<StringSort>), start: Int) =
    this().indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringSortLambdaLong")
fun (() -> Expression<StringSort>).indexof(substring: (() -> Expression<StringSort>), start: Long) =
    this().indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringSortLambdaBigInteger")
fun (() -> Expression<StringSort>).indexof(
    substring: (() -> Expression<StringSort>),
    start: BigInteger
) = this().indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .
 */
@JvmName("indexofStringSortLambdaStringLambdaIntSort")
fun (() -> Expression<StringSort>).indexof(substring: (() -> String), start: Expression<IntSort>) =
    this().indexof(StringLiteral(substring()), start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringLambdaByte")
fun (() -> Expression<StringSort>).indexof(substring: (() -> String), start: Byte) =
    this().indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringLambdaShort")
fun (() -> Expression<StringSort>).indexof(substring: (() -> String), start: Short) =
    this().indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringLambdaInt")
fun (() -> Expression<StringSort>).indexof(substring: (() -> String), start: Int) =
    this().indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringLambdaLong")
fun (() -> Expression<StringSort>).indexof(substring: (() -> String), start: Long) =
    this().indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringLambdaBigInteger")
fun (() -> Expression<StringSort>).indexof(substring: (() -> String), start: BigInteger) =
    this().indexof(StringLiteral(substring()), IntLiteral(start))

/** Index of first occurrence of [substring] in [this] starting at [start]. */
@JvmName("indexofStringSortLambdaStringSortIntSortLambda")
fun (() -> Expression<StringSort>).indexof(
    substring: Expression<StringSort>,
    start: (() -> Expression<IntSort>)
) = this().indexof(substring, start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringSortByteLambda")
fun (() -> Expression<StringSort>).indexof(substring: Expression<StringSort>, start: (() -> Byte)) =
    this().indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringSortShortLambda")
fun (() -> Expression<StringSort>).indexof(
    substring: Expression<StringSort>,
    start: (() -> Short)
) = this().indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringSortIntLambda")
fun (() -> Expression<StringSort>).indexof(substring: Expression<StringSort>, start: (() -> Int)) =
    this().indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringSortLongLambda")
fun (() -> Expression<StringSort>).indexof(substring: Expression<StringSort>, start: (() -> Long)) =
    this().indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringSortBigIntegerLambda")
fun (() -> Expression<StringSort>).indexof(
    substring: Expression<StringSort>,
    start: (() -> BigInteger)
) = this().indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .
 */
@JvmName("indexofStringSortLambdaStringIntSortLambda")
fun (() -> Expression<StringSort>).indexof(substring: String, start: (() -> Expression<IntSort>)) =
    this().indexof(StringLiteral(substring), start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringByteLambda")
fun (() -> Expression<StringSort>).indexof(substring: String, start: (() -> Byte)) =
    this().indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringShortLambda")
fun (() -> Expression<StringSort>).indexof(substring: String, start: (() -> Short)) =
    this().indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringIntLambda")
fun (() -> Expression<StringSort>).indexof(substring: String, start: (() -> Int)) =
    this().indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringLongLambda")
fun (() -> Expression<StringSort>).indexof(substring: String, start: (() -> Long)) =
    this().indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringBigIntegerLambda")
fun (() -> Expression<StringSort>).indexof(substring: String, start: (() -> BigInteger)) =
    this().indexof(StringLiteral(substring), IntLiteral(start()))

/** Index of first occurrence of [substring] in [this] starting at [start]. */
@JvmName("indexofStringSortLambdaStringSortLambdaIntSortLambda")
fun (() -> Expression<StringSort>).indexof(
    substring: (() -> Expression<StringSort>),
    start: (() -> Expression<IntSort>)
) = this().indexof(substring(), start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringSortLambdaByteLambda")
fun (() -> Expression<StringSort>).indexof(
    substring: (() -> Expression<StringSort>),
    start: (() -> Byte)
) = this().indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringSortLambdaShortLambda")
fun (() -> Expression<StringSort>).indexof(
    substring: (() -> Expression<StringSort>),
    start: (() -> Short)
) = this().indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringSortLambdaIntLambda")
fun (() -> Expression<StringSort>).indexof(
    substring: (() -> Expression<StringSort>),
    start: (() -> Int)
) = this().indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringSortLambdaLongLambda")
fun (() -> Expression<StringSort>).indexof(
    substring: (() -> Expression<StringSort>),
    start: (() -> Long)
) = this().indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].* - [start] is converted
 * to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringSortLambdaBigIntegerLambda")
fun (() -> Expression<StringSort>).indexof(
    substring: (() -> Expression<StringSort>),
    start: (() -> BigInteger)
) = this().indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .
 */
@JvmName("indexofStringSortLambdaStringLambdaIntSortLambda")
fun (() -> Expression<StringSort>).indexof(
    substring: (() -> String),
    start: (() -> Expression<IntSort>)
) = this().indexof(StringLiteral(substring()), start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringLambdaByteLambda")
fun (() -> Expression<StringSort>).indexof(substring: (() -> String), start: (() -> Byte)) =
    this().indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringLambdaShortLambda")
fun (() -> Expression<StringSort>).indexof(substring: (() -> String), start: (() -> Short)) =
    this().indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringLambdaIntLambda")
fun (() -> Expression<StringSort>).indexof(substring: (() -> String), start: (() -> Int)) =
    this().indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringLambdaLongLambda")
fun (() -> Expression<StringSort>).indexof(substring: (() -> String), start: (() -> Long)) =
    this().indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringSortLambdaStringLambdaBigIntegerLambda")
fun (() -> Expression<StringSort>).indexof(substring: (() -> String), start: (() -> BigInteger)) =
    this().indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("indexofStringStringSortIntSort")
fun String.indexof(substring: Expression<StringSort>, start: Expression<IntSort>) =
    StringLiteral(this).indexof(substring, start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringSortByte")
fun String.indexof(substring: Expression<StringSort>, start: Byte) =
    StringLiteral(this).indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringSortShort")
fun String.indexof(substring: Expression<StringSort>, start: Short) =
    StringLiteral(this).indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringSortInt")
fun String.indexof(substring: Expression<StringSort>, start: Int) =
    StringLiteral(this).indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringSortLong")
fun String.indexof(substring: Expression<StringSort>, start: Long) =
    StringLiteral(this).indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringSortBigInteger")
fun String.indexof(substring: Expression<StringSort>, start: BigInteger) =
    StringLiteral(this).indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .
 */
@JvmName("indexofStringStringIntSort")
fun String.indexof(substring: String, start: Expression<IntSort>) =
    StringLiteral(this).indexof(StringLiteral(substring), start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringByte")
fun String.indexof(substring: String, start: Byte) =
    StringLiteral(this).indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringShort")
fun String.indexof(substring: String, start: Short) =
    StringLiteral(this).indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringInt")
fun String.indexof(substring: String, start: Int) =
    StringLiteral(this).indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringLong")
fun String.indexof(substring: String, start: Long) =
    StringLiteral(this).indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringBigInteger")
fun String.indexof(substring: String, start: BigInteger) =
    StringLiteral(this).indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("indexofStringStringSortLambdaIntSort")
fun String.indexof(substring: (() -> Expression<StringSort>), start: Expression<IntSort>) =
    StringLiteral(this).indexof(substring(), start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringSortLambdaByte")
fun String.indexof(substring: (() -> Expression<StringSort>), start: Byte) =
    StringLiteral(this).indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringSortLambdaShort")
fun String.indexof(substring: (() -> Expression<StringSort>), start: Short) =
    StringLiteral(this).indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringSortLambdaInt")
fun String.indexof(substring: (() -> Expression<StringSort>), start: Int) =
    StringLiteral(this).indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringSortLambdaLong")
fun String.indexof(substring: (() -> Expression<StringSort>), start: Long) =
    StringLiteral(this).indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringSortLambdaBigInteger")
fun String.indexof(substring: (() -> Expression<StringSort>), start: BigInteger) =
    StringLiteral(this).indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .
 */
@JvmName("indexofStringStringLambdaIntSort")
fun String.indexof(substring: (() -> String), start: Expression<IntSort>) =
    StringLiteral(this).indexof(StringLiteral(substring()), start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringLambdaByte")
fun String.indexof(substring: (() -> String), start: Byte) =
    StringLiteral(this).indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringLambdaShort")
fun String.indexof(substring: (() -> String), start: Short) =
    StringLiteral(this).indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringLambdaInt")
fun String.indexof(substring: (() -> String), start: Int) =
    StringLiteral(this).indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringLambdaLong")
fun String.indexof(substring: (() -> String), start: Long) =
    StringLiteral(this).indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringLambdaBigInteger")
fun String.indexof(substring: (() -> String), start: BigInteger) =
    StringLiteral(this).indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("indexofStringStringSortIntSortLambda")
fun String.indexof(substring: Expression<StringSort>, start: (() -> Expression<IntSort>)) =
    StringLiteral(this).indexof(substring, start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringSortByteLambda")
fun String.indexof(substring: Expression<StringSort>, start: (() -> Byte)) =
    StringLiteral(this).indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringSortShortLambda")
fun String.indexof(substring: Expression<StringSort>, start: (() -> Short)) =
    StringLiteral(this).indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringSortIntLambda")
fun String.indexof(substring: Expression<StringSort>, start: (() -> Int)) =
    StringLiteral(this).indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringSortLongLambda")
fun String.indexof(substring: Expression<StringSort>, start: (() -> Long)) =
    StringLiteral(this).indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringSortBigIntegerLambda")
fun String.indexof(substring: Expression<StringSort>, start: (() -> BigInteger)) =
    StringLiteral(this).indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .
 */
@JvmName("indexofStringStringIntSortLambda")
fun String.indexof(substring: String, start: (() -> Expression<IntSort>)) =
    StringLiteral(this).indexof(StringLiteral(substring), start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringByteLambda")
fun String.indexof(substring: String, start: (() -> Byte)) =
    StringLiteral(this).indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringShortLambda")
fun String.indexof(substring: String, start: (() -> Short)) =
    StringLiteral(this).indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringIntLambda")
fun String.indexof(substring: String, start: (() -> Int)) =
    StringLiteral(this).indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringLongLambda")
fun String.indexof(substring: String, start: (() -> Long)) =
    StringLiteral(this).indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringBigIntegerLambda")
fun String.indexof(substring: String, start: (() -> BigInteger)) =
    StringLiteral(this).indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("indexofStringStringSortLambdaIntSortLambda")
fun String.indexof(substring: (() -> Expression<StringSort>), start: (() -> Expression<IntSort>)) =
    StringLiteral(this).indexof(substring(), start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringSortLambdaByteLambda")
fun String.indexof(substring: (() -> Expression<StringSort>), start: (() -> Byte)) =
    StringLiteral(this).indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringSortLambdaShortLambda")
fun String.indexof(substring: (() -> Expression<StringSort>), start: (() -> Short)) =
    StringLiteral(this).indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringSortLambdaIntLambda")
fun String.indexof(substring: (() -> Expression<StringSort>), start: (() -> Int)) =
    StringLiteral(this).indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringSortLambdaLongLambda")
fun String.indexof(substring: (() -> Expression<StringSort>), start: (() -> Long)) =
    StringLiteral(this).indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringSortLambdaBigIntegerLambda")
fun String.indexof(substring: (() -> Expression<StringSort>), start: (() -> BigInteger)) =
    StringLiteral(this).indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .
 */
@JvmName("indexofStringStringLambdaIntSortLambda")
fun String.indexof(substring: (() -> String), start: (() -> Expression<IntSort>)) =
    StringLiteral(this).indexof(StringLiteral(substring()), start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringLambdaByteLambda")
fun String.indexof(substring: (() -> String), start: (() -> Byte)) =
    StringLiteral(this).indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringLambdaShortLambda")
fun String.indexof(substring: (() -> String), start: (() -> Short)) =
    StringLiteral(this).indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringLambdaIntLambda")
fun String.indexof(substring: (() -> String), start: (() -> Int)) =
    StringLiteral(this).indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringLambdaLongLambda")
fun String.indexof(substring: (() -> String), start: (() -> Long)) =
    StringLiteral(this).indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringStringLambdaBigIntegerLambda")
fun String.indexof(substring: (() -> String), start: (() -> BigInteger)) =
    StringLiteral(this).indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("indexofStringLambdaStringSortIntSort")
fun (() -> String).indexof(substring: Expression<StringSort>, start: Expression<IntSort>) =
    StringLiteral(this()).indexof(substring, start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringSortByte")
fun (() -> String).indexof(substring: Expression<StringSort>, start: Byte) =
    StringLiteral(this()).indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringSortShort")
fun (() -> String).indexof(substring: Expression<StringSort>, start: Short) =
    StringLiteral(this()).indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringSortInt")
fun (() -> String).indexof(substring: Expression<StringSort>, start: Int) =
    StringLiteral(this()).indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringSortLong")
fun (() -> String).indexof(substring: Expression<StringSort>, start: Long) =
    StringLiteral(this()).indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringSortBigInteger")
fun (() -> String).indexof(substring: Expression<StringSort>, start: BigInteger) =
    StringLiteral(this()).indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .
 */
@JvmName("indexofStringLambdaStringIntSort")
fun (() -> String).indexof(substring: String, start: Expression<IntSort>) =
    StringLiteral(this()).indexof(StringLiteral(substring), start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringByte")
fun (() -> String).indexof(substring: String, start: Byte) =
    StringLiteral(this()).indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringShort")
fun (() -> String).indexof(substring: String, start: Short) =
    StringLiteral(this()).indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringInt")
fun (() -> String).indexof(substring: String, start: Int) =
    StringLiteral(this()).indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringLong")
fun (() -> String).indexof(substring: String, start: Long) =
    StringLiteral(this()).indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringBigInteger")
fun (() -> String).indexof(substring: String, start: BigInteger) =
    StringLiteral(this()).indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("indexofStringLambdaStringSortLambdaIntSort")
fun (() -> String).indexof(substring: (() -> Expression<StringSort>), start: Expression<IntSort>) =
    StringLiteral(this()).indexof(substring(), start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringSortLambdaByte")
fun (() -> String).indexof(substring: (() -> Expression<StringSort>), start: Byte) =
    StringLiteral(this()).indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringSortLambdaShort")
fun (() -> String).indexof(substring: (() -> Expression<StringSort>), start: Short) =
    StringLiteral(this()).indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringSortLambdaInt")
fun (() -> String).indexof(substring: (() -> Expression<StringSort>), start: Int) =
    StringLiteral(this()).indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringSortLambdaLong")
fun (() -> String).indexof(substring: (() -> Expression<StringSort>), start: Long) =
    StringLiteral(this()).indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringSortLambdaBigInteger")
fun (() -> String).indexof(substring: (() -> Expression<StringSort>), start: BigInteger) =
    StringLiteral(this()).indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .
 */
@JvmName("indexofStringLambdaStringLambdaIntSort")
fun (() -> String).indexof(substring: (() -> String), start: Expression<IntSort>) =
    StringLiteral(this()).indexof(StringLiteral(substring()), start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringLambdaByte")
fun (() -> String).indexof(substring: (() -> String), start: Byte) =
    StringLiteral(this()).indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringLambdaShort")
fun (() -> String).indexof(substring: (() -> String), start: Short) =
    StringLiteral(this()).indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringLambdaInt")
fun (() -> String).indexof(substring: (() -> String), start: Int) =
    StringLiteral(this()).indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringLambdaLong")
fun (() -> String).indexof(substring: (() -> String), start: Long) =
    StringLiteral(this()).indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringLambdaBigInteger")
fun (() -> String).indexof(substring: (() -> String), start: BigInteger) =
    StringLiteral(this()).indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("indexofStringLambdaStringSortIntSortLambda")
fun (() -> String).indexof(substring: Expression<StringSort>, start: (() -> Expression<IntSort>)) =
    StringLiteral(this()).indexof(substring, start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringSortByteLambda")
fun (() -> String).indexof(substring: Expression<StringSort>, start: (() -> Byte)) =
    StringLiteral(this()).indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringSortShortLambda")
fun (() -> String).indexof(substring: Expression<StringSort>, start: (() -> Short)) =
    StringLiteral(this()).indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringSortIntLambda")
fun (() -> String).indexof(substring: Expression<StringSort>, start: (() -> Int)) =
    StringLiteral(this()).indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringSortLongLambda")
fun (() -> String).indexof(substring: Expression<StringSort>, start: (() -> Long)) =
    StringLiteral(this()).indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringSortBigIntegerLambda")
fun (() -> String).indexof(substring: Expression<StringSort>, start: (() -> BigInteger)) =
    StringLiteral(this()).indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .
 */
@JvmName("indexofStringLambdaStringIntSortLambda")
fun (() -> String).indexof(substring: String, start: (() -> Expression<IntSort>)) =
    StringLiteral(this()).indexof(StringLiteral(substring), start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringByteLambda")
fun (() -> String).indexof(substring: String, start: (() -> Byte)) =
    StringLiteral(this()).indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringShortLambda")
fun (() -> String).indexof(substring: String, start: (() -> Short)) =
    StringLiteral(this()).indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringIntLambda")
fun (() -> String).indexof(substring: String, start: (() -> Int)) =
    StringLiteral(this()).indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringLongLambda")
fun (() -> String).indexof(substring: String, start: (() -> Long)) =
    StringLiteral(this()).indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringBigIntegerLambda")
fun (() -> String).indexof(substring: String, start: (() -> BigInteger)) =
    StringLiteral(this()).indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("indexofStringLambdaStringSortLambdaIntSortLambda")
fun (() -> String).indexof(
    substring: (() -> Expression<StringSort>),
    start: (() -> Expression<IntSort>)
) = StringLiteral(this()).indexof(substring(), start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringSortLambdaByteLambda")
fun (() -> String).indexof(substring: (() -> Expression<StringSort>), start: (() -> Byte)) =
    StringLiteral(this()).indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringSortLambdaShortLambda")
fun (() -> String).indexof(substring: (() -> Expression<StringSort>), start: (() -> Short)) =
    StringLiteral(this()).indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringSortLambdaIntLambda")
fun (() -> String).indexof(substring: (() -> Expression<StringSort>), start: (() -> Int)) =
    StringLiteral(this()).indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringSortLambdaLongLambda")
fun (() -> String).indexof(substring: (() -> Expression<StringSort>), start: (() -> Long)) =
    StringLiteral(this()).indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringSortLambdaBigIntegerLambda")
fun (() -> String).indexof(substring: (() -> Expression<StringSort>), start: (() -> BigInteger)) =
    StringLiteral(this()).indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .
 */
@JvmName("indexofStringLambdaStringLambdaIntSortLambda")
fun (() -> String).indexof(substring: (() -> String), start: (() -> Expression<IntSort>)) =
    StringLiteral(this()).indexof(StringLiteral(substring()), start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringLambdaByteLambda")
fun (() -> String).indexof(substring: (() -> String), start: (() -> Byte)) =
    StringLiteral(this()).indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringLambdaShortLambda")
fun (() -> String).indexof(substring: (() -> String), start: (() -> Short)) =
    StringLiteral(this()).indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringLambdaIntLambda")
fun (() -> String).indexof(substring: (() -> String), start: (() -> Int)) =
    StringLiteral(this()).indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringLambdaLongLambda")
fun (() -> String).indexof(substring: (() -> String), start: (() -> Long)) =
    StringLiteral(this()).indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start].
 * - [this] is converted to [StringLiteral]
 * - [substring] is converted to [StringLiteral] .* - [start] is converted to [IntLiteral]
 */
@JvmName("indexofStringLambdaStringLambdaBigIntegerLambda")
fun (() -> String).indexof(substring: (() -> String), start: (() -> BigInteger)) =
    StringLiteral(this()).indexof(StringLiteral(substring()), IntLiteral(start()))

/** Replace the first occurrence of [oldValue] in [this] with [newValue]. */
fun Expression<StringSort>.replace(
    oldValue: Expression<StringSort>,
    newValue: Expression<StringSort>
) = StrReplace(this, oldValue, newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].* - [newValue] is converted
 * to [StringLiteral]
 */
@JvmName("replaceStringSortStringSortString")
fun Expression<StringSort>.replace(oldValue: Expression<StringSort>, newValue: String) =
    this.replace(oldValue, StringLiteral(newValue))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replaceStringSortStringStringSort")
fun Expression<StringSort>.replace(oldValue: String, newValue: Expression<StringSort>) =
    this.replace(StringLiteral(oldValue), newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replaceStringSortStringString")
fun Expression<StringSort>.replace(oldValue: String, newValue: String) =
    this.replace(StringLiteral(oldValue), StringLiteral(newValue))

/** Replace the first occurrence of [oldValue] in [this] with [newValue]. */
@JvmName("replaceStringSortStringSortLambdaStringSort")
fun Expression<StringSort>.replace(
    oldValue: (() -> Expression<StringSort>),
    newValue: Expression<StringSort>
) = this.replace(oldValue(), newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].* - [newValue] is converted
 * to [StringLiteral]
 */
@JvmName("replaceStringSortStringSortLambdaString")
fun Expression<StringSort>.replace(oldValue: (() -> Expression<StringSort>), newValue: String) =
    this.replace(oldValue(), StringLiteral(newValue))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replaceStringSortStringLambdaStringSort")
fun Expression<StringSort>.replace(oldValue: (() -> String), newValue: Expression<StringSort>) =
    this.replace(StringLiteral(oldValue()), newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replaceStringSortStringLambdaString")
fun Expression<StringSort>.replace(oldValue: (() -> String), newValue: String) =
    this.replace(StringLiteral(oldValue()), StringLiteral(newValue))

/** Replace the first occurrence of [oldValue] in [this] with [newValue]. */
@JvmName("replaceStringSortStringSortStringSortLambda")
fun Expression<StringSort>.replace(
    oldValue: Expression<StringSort>,
    newValue: (() -> Expression<StringSort>)
) = this.replace(oldValue, newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].* - [newValue] is converted
 * to [StringLiteral]
 */
@JvmName("replaceStringSortStringSortStringLambda")
fun Expression<StringSort>.replace(oldValue: Expression<StringSort>, newValue: (() -> String)) =
    this.replace(oldValue, StringLiteral(newValue()))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replaceStringSortStringStringSortLambda")
fun Expression<StringSort>.replace(oldValue: String, newValue: (() -> Expression<StringSort>)) =
    this.replace(StringLiteral(oldValue), newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replaceStringSortStringStringLambda")
fun Expression<StringSort>.replace(oldValue: String, newValue: (() -> String)) =
    this.replace(StringLiteral(oldValue), StringLiteral(newValue()))

/** Replace the first occurrence of [oldValue] in [this] with [newValue]. */
@JvmName("replaceStringSortStringSortLambdaStringSortLambda")
fun Expression<StringSort>.replace(
    oldValue: (() -> Expression<StringSort>),
    newValue: (() -> Expression<StringSort>)
) = this.replace(oldValue(), newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].* - [newValue] is converted
 * to [StringLiteral]
 */
@JvmName("replaceStringSortStringSortLambdaStringLambda")
fun Expression<StringSort>.replace(
    oldValue: (() -> Expression<StringSort>),
    newValue: (() -> String)
) = this.replace(oldValue(), StringLiteral(newValue()))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replaceStringSortStringLambdaStringSortLambda")
fun Expression<StringSort>.replace(
    oldValue: (() -> String),
    newValue: (() -> Expression<StringSort>)
) = this.replace(StringLiteral(oldValue()), newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replaceStringSortStringLambdaStringLambda")
fun Expression<StringSort>.replace(oldValue: (() -> String), newValue: (() -> String)) =
    this.replace(StringLiteral(oldValue()), StringLiteral(newValue()))

/** Replace the first occurrence of [oldValue] in [this] with [newValue]. */
@JvmName("replaceStringSortLambdaStringSortStringSort")
fun (() -> Expression<StringSort>).replace(
    oldValue: Expression<StringSort>,
    newValue: Expression<StringSort>
) = this().replace(oldValue, newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].* - [newValue] is converted
 * to [StringLiteral]
 */
@JvmName("replaceStringSortLambdaStringSortString")
fun (() -> Expression<StringSort>).replace(oldValue: Expression<StringSort>, newValue: String) =
    this().replace(oldValue, StringLiteral(newValue))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replaceStringSortLambdaStringStringSort")
fun (() -> Expression<StringSort>).replace(oldValue: String, newValue: Expression<StringSort>) =
    this().replace(StringLiteral(oldValue), newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replaceStringSortLambdaStringString")
fun (() -> Expression<StringSort>).replace(oldValue: String, newValue: String) =
    this().replace(StringLiteral(oldValue), StringLiteral(newValue))

/** Replace the first occurrence of [oldValue] in [this] with [newValue]. */
@JvmName("replaceStringSortLambdaStringSortLambdaStringSort")
fun (() -> Expression<StringSort>).replace(
    oldValue: (() -> Expression<StringSort>),
    newValue: Expression<StringSort>
) = this().replace(oldValue(), newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].* - [newValue] is converted
 * to [StringLiteral]
 */
@JvmName("replaceStringSortLambdaStringSortLambdaString")
fun (() -> Expression<StringSort>).replace(
    oldValue: (() -> Expression<StringSort>),
    newValue: String
) = this().replace(oldValue(), StringLiteral(newValue))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replaceStringSortLambdaStringLambdaStringSort")
fun (() -> Expression<StringSort>).replace(
    oldValue: (() -> String),
    newValue: Expression<StringSort>
) = this().replace(StringLiteral(oldValue()), newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replaceStringSortLambdaStringLambdaString")
fun (() -> Expression<StringSort>).replace(oldValue: (() -> String), newValue: String) =
    this().replace(StringLiteral(oldValue()), StringLiteral(newValue))

/** Replace the first occurrence of [oldValue] in [this] with [newValue]. */
@JvmName("replaceStringSortLambdaStringSortStringSortLambda")
fun (() -> Expression<StringSort>).replace(
    oldValue: Expression<StringSort>,
    newValue: (() -> Expression<StringSort>)
) = this().replace(oldValue, newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].* - [newValue] is converted
 * to [StringLiteral]
 */
@JvmName("replaceStringSortLambdaStringSortStringLambda")
fun (() -> Expression<StringSort>).replace(
    oldValue: Expression<StringSort>,
    newValue: (() -> String)
) = this().replace(oldValue, StringLiteral(newValue()))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replaceStringSortLambdaStringStringSortLambda")
fun (() -> Expression<StringSort>).replace(
    oldValue: String,
    newValue: (() -> Expression<StringSort>)
) = this().replace(StringLiteral(oldValue), newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replaceStringSortLambdaStringStringLambda")
fun (() -> Expression<StringSort>).replace(oldValue: String, newValue: (() -> String)) =
    this().replace(StringLiteral(oldValue), StringLiteral(newValue()))

/** Replace the first occurrence of [oldValue] in [this] with [newValue]. */
@JvmName("replaceStringSortLambdaStringSortLambdaStringSortLambda")
fun (() -> Expression<StringSort>).replace(
    oldValue: (() -> Expression<StringSort>),
    newValue: (() -> Expression<StringSort>)
) = this().replace(oldValue(), newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].* - [newValue] is converted
 * to [StringLiteral]
 */
@JvmName("replaceStringSortLambdaStringSortLambdaStringLambda")
fun (() -> Expression<StringSort>).replace(
    oldValue: (() -> Expression<StringSort>),
    newValue: (() -> String)
) = this().replace(oldValue(), StringLiteral(newValue()))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replaceStringSortLambdaStringLambdaStringSortLambda")
fun (() -> Expression<StringSort>).replace(
    oldValue: (() -> String),
    newValue: (() -> Expression<StringSort>)
) = this().replace(StringLiteral(oldValue()), newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replaceStringSortLambdaStringLambdaStringLambda")
fun (() -> Expression<StringSort>).replace(oldValue: (() -> String), newValue: (() -> String)) =
    this().replace(StringLiteral(oldValue()), StringLiteral(newValue()))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replaceStringStringSortStringSort")
fun String.replace(oldValue: Expression<StringSort>, newValue: Expression<StringSort>) =
    StringLiteral(this).replace(oldValue, newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replaceStringStringSortString")
fun String.replace(oldValue: Expression<StringSort>, newValue: String) =
    StringLiteral(this).replace(oldValue, StringLiteral(newValue))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replaceStringStringStringSort")
fun String.replace(oldValue: String, newValue: Expression<StringSort>) =
    StringLiteral(this).replace(StringLiteral(oldValue), newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replaceStringStringString")
fun String.replace(oldValue: String, newValue: String) =
    StringLiteral(this).replace(StringLiteral(oldValue), StringLiteral(newValue))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replaceStringStringSortLambdaStringSort")
fun String.replace(oldValue: (() -> Expression<StringSort>), newValue: Expression<StringSort>) =
    StringLiteral(this).replace(oldValue(), newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replaceStringStringSortLambdaString")
fun String.replace(oldValue: (() -> Expression<StringSort>), newValue: String) =
    StringLiteral(this).replace(oldValue(), StringLiteral(newValue))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replaceStringStringLambdaStringSort")
fun String.replace(oldValue: (() -> String), newValue: Expression<StringSort>) =
    StringLiteral(this).replace(StringLiteral(oldValue()), newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replaceStringStringLambdaString")
fun String.replace(oldValue: (() -> String), newValue: String) =
    StringLiteral(this).replace(StringLiteral(oldValue()), StringLiteral(newValue))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replaceStringStringSortStringSortLambda")
fun String.replace(oldValue: Expression<StringSort>, newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this).replace(oldValue, newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replaceStringStringSortStringLambda")
fun String.replace(oldValue: Expression<StringSort>, newValue: (() -> String)) =
    StringLiteral(this).replace(oldValue, StringLiteral(newValue()))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replaceStringStringStringSortLambda")
fun String.replace(oldValue: String, newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this).replace(StringLiteral(oldValue), newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replaceStringStringStringLambda")
fun String.replace(oldValue: String, newValue: (() -> String)) =
    StringLiteral(this).replace(StringLiteral(oldValue), StringLiteral(newValue()))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replaceStringStringSortLambdaStringSortLambda")
fun String.replace(
    oldValue: (() -> Expression<StringSort>),
    newValue: (() -> Expression<StringSort>)
) = StringLiteral(this).replace(oldValue(), newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replaceStringStringSortLambdaStringLambda")
fun String.replace(oldValue: (() -> Expression<StringSort>), newValue: (() -> String)) =
    StringLiteral(this).replace(oldValue(), StringLiteral(newValue()))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replaceStringStringLambdaStringSortLambda")
fun String.replace(oldValue: (() -> String), newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this).replace(StringLiteral(oldValue()), newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replaceStringStringLambdaStringLambda")
fun String.replace(oldValue: (() -> String), newValue: (() -> String)) =
    StringLiteral(this).replace(StringLiteral(oldValue()), StringLiteral(newValue()))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replaceStringLambdaStringSortStringSort")
fun (() -> String).replace(oldValue: Expression<StringSort>, newValue: Expression<StringSort>) =
    StringLiteral(this()).replace(oldValue, newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replaceStringLambdaStringSortString")
fun (() -> String).replace(oldValue: Expression<StringSort>, newValue: String) =
    StringLiteral(this()).replace(oldValue, StringLiteral(newValue))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replaceStringLambdaStringStringSort")
fun (() -> String).replace(oldValue: String, newValue: Expression<StringSort>) =
    StringLiteral(this()).replace(StringLiteral(oldValue), newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replaceStringLambdaStringString")
fun (() -> String).replace(oldValue: String, newValue: String) =
    StringLiteral(this()).replace(StringLiteral(oldValue), StringLiteral(newValue))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replaceStringLambdaStringSortLambdaStringSort")
fun (() -> String).replace(
    oldValue: (() -> Expression<StringSort>),
    newValue: Expression<StringSort>
) = StringLiteral(this()).replace(oldValue(), newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replaceStringLambdaStringSortLambdaString")
fun (() -> String).replace(oldValue: (() -> Expression<StringSort>), newValue: String) =
    StringLiteral(this()).replace(oldValue(), StringLiteral(newValue))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replaceStringLambdaStringLambdaStringSort")
fun (() -> String).replace(oldValue: (() -> String), newValue: Expression<StringSort>) =
    StringLiteral(this()).replace(StringLiteral(oldValue()), newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replaceStringLambdaStringLambdaString")
fun (() -> String).replace(oldValue: (() -> String), newValue: String) =
    StringLiteral(this()).replace(StringLiteral(oldValue()), StringLiteral(newValue))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replaceStringLambdaStringSortStringSortLambda")
fun (() -> String).replace(
    oldValue: Expression<StringSort>,
    newValue: (() -> Expression<StringSort>)
) = StringLiteral(this()).replace(oldValue, newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replaceStringLambdaStringSortStringLambda")
fun (() -> String).replace(oldValue: Expression<StringSort>, newValue: (() -> String)) =
    StringLiteral(this()).replace(oldValue, StringLiteral(newValue()))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replaceStringLambdaStringStringSortLambda")
fun (() -> String).replace(oldValue: String, newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this()).replace(StringLiteral(oldValue), newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replaceStringLambdaStringStringLambda")
fun (() -> String).replace(oldValue: String, newValue: (() -> String)) =
    StringLiteral(this()).replace(StringLiteral(oldValue), StringLiteral(newValue()))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replaceStringLambdaStringSortLambdaStringSortLambda")
fun (() -> String).replace(
    oldValue: (() -> Expression<StringSort>),
    newValue: (() -> Expression<StringSort>)
) = StringLiteral(this()).replace(oldValue(), newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replaceStringLambdaStringSortLambdaStringLambda")
fun (() -> String).replace(oldValue: (() -> Expression<StringSort>), newValue: (() -> String)) =
    StringLiteral(this()).replace(oldValue(), StringLiteral(newValue()))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replaceStringLambdaStringLambdaStringSortLambda")
fun (() -> String).replace(oldValue: (() -> String), newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this()).replace(StringLiteral(oldValue()), newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replaceStringLambdaStringLambdaStringLambda")
fun (() -> String).replace(oldValue: (() -> String), newValue: (() -> String)) =
    StringLiteral(this()).replace(StringLiteral(oldValue()), StringLiteral(newValue()))

/** Replace all occurrence of [oldValue] in [this] with [newValue]. */
fun Expression<StringSort>.replace_all(
    oldValue: Expression<StringSort>,
    newValue: Expression<StringSort>
) = StrReplaceAll(this, oldValue, newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].* - [newValue] is converted to
 * [StringLiteral]
 */
@JvmName("replace_allStringSortStringSortString")
fun Expression<StringSort>.replace_all(oldValue: Expression<StringSort>, newValue: String) =
    this.replace_all(oldValue, StringLiteral(newValue))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replace_allStringSortStringStringSort")
fun Expression<StringSort>.replace_all(oldValue: String, newValue: Expression<StringSort>) =
    this.replace_all(StringLiteral(oldValue), newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_allStringSortStringString")
fun Expression<StringSort>.replace_all(oldValue: String, newValue: String) =
    this.replace_all(StringLiteral(oldValue), StringLiteral(newValue))

/** Replace all occurrence of [oldValue] in [this] with [newValue]. */
@JvmName("replace_allStringSortStringSortLambdaStringSort")
fun Expression<StringSort>.replace_all(
    oldValue: (() -> Expression<StringSort>),
    newValue: Expression<StringSort>
) = this.replace_all(oldValue(), newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].* - [newValue] is converted to
 * [StringLiteral]
 */
@JvmName("replace_allStringSortStringSortLambdaString")
fun Expression<StringSort>.replace_all(oldValue: (() -> Expression<StringSort>), newValue: String) =
    this.replace_all(oldValue(), StringLiteral(newValue))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replace_allStringSortStringLambdaStringSort")
fun Expression<StringSort>.replace_all(oldValue: (() -> String), newValue: Expression<StringSort>) =
    this.replace_all(StringLiteral(oldValue()), newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_allStringSortStringLambdaString")
fun Expression<StringSort>.replace_all(oldValue: (() -> String), newValue: String) =
    this.replace_all(StringLiteral(oldValue()), StringLiteral(newValue))

/** Replace all occurrence of [oldValue] in [this] with [newValue]. */
@JvmName("replace_allStringSortStringSortStringSortLambda")
fun Expression<StringSort>.replace_all(
    oldValue: Expression<StringSort>,
    newValue: (() -> Expression<StringSort>)
) = this.replace_all(oldValue, newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].* - [newValue] is converted to
 * [StringLiteral]
 */
@JvmName("replace_allStringSortStringSortStringLambda")
fun Expression<StringSort>.replace_all(oldValue: Expression<StringSort>, newValue: (() -> String)) =
    this.replace_all(oldValue, StringLiteral(newValue()))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replace_allStringSortStringStringSortLambda")
fun Expression<StringSort>.replace_all(oldValue: String, newValue: (() -> Expression<StringSort>)) =
    this.replace_all(StringLiteral(oldValue), newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_allStringSortStringStringLambda")
fun Expression<StringSort>.replace_all(oldValue: String, newValue: (() -> String)) =
    this.replace_all(StringLiteral(oldValue), StringLiteral(newValue()))

/** Replace all occurrence of [oldValue] in [this] with [newValue]. */
@JvmName("replace_allStringSortStringSortLambdaStringSortLambda")
fun Expression<StringSort>.replace_all(
    oldValue: (() -> Expression<StringSort>),
    newValue: (() -> Expression<StringSort>)
) = this.replace_all(oldValue(), newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].* - [newValue] is converted to
 * [StringLiteral]
 */
@JvmName("replace_allStringSortStringSortLambdaStringLambda")
fun Expression<StringSort>.replace_all(
    oldValue: (() -> Expression<StringSort>),
    newValue: (() -> String)
) = this.replace_all(oldValue(), StringLiteral(newValue()))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replace_allStringSortStringLambdaStringSortLambda")
fun Expression<StringSort>.replace_all(
    oldValue: (() -> String),
    newValue: (() -> Expression<StringSort>)
) = this.replace_all(StringLiteral(oldValue()), newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_allStringSortStringLambdaStringLambda")
fun Expression<StringSort>.replace_all(oldValue: (() -> String), newValue: (() -> String)) =
    this.replace_all(StringLiteral(oldValue()), StringLiteral(newValue()))

/** Replace all occurrence of [oldValue] in [this] with [newValue]. */
@JvmName("replace_allStringSortLambdaStringSortStringSort")
fun (() -> Expression<StringSort>).replace_all(
    oldValue: Expression<StringSort>,
    newValue: Expression<StringSort>
) = this().replace_all(oldValue, newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].* - [newValue] is converted to
 * [StringLiteral]
 */
@JvmName("replace_allStringSortLambdaStringSortString")
fun (() -> Expression<StringSort>).replace_all(oldValue: Expression<StringSort>, newValue: String) =
    this().replace_all(oldValue, StringLiteral(newValue))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replace_allStringSortLambdaStringStringSort")
fun (() -> Expression<StringSort>).replace_all(oldValue: String, newValue: Expression<StringSort>) =
    this().replace_all(StringLiteral(oldValue), newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_allStringSortLambdaStringString")
fun (() -> Expression<StringSort>).replace_all(oldValue: String, newValue: String) =
    this().replace_all(StringLiteral(oldValue), StringLiteral(newValue))

/** Replace all occurrence of [oldValue] in [this] with [newValue]. */
@JvmName("replace_allStringSortLambdaStringSortLambdaStringSort")
fun (() -> Expression<StringSort>).replace_all(
    oldValue: (() -> Expression<StringSort>),
    newValue: Expression<StringSort>
) = this().replace_all(oldValue(), newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].* - [newValue] is converted to
 * [StringLiteral]
 */
@JvmName("replace_allStringSortLambdaStringSortLambdaString")
fun (() -> Expression<StringSort>).replace_all(
    oldValue: (() -> Expression<StringSort>),
    newValue: String
) = this().replace_all(oldValue(), StringLiteral(newValue))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replace_allStringSortLambdaStringLambdaStringSort")
fun (() -> Expression<StringSort>).replace_all(
    oldValue: (() -> String),
    newValue: Expression<StringSort>
) = this().replace_all(StringLiteral(oldValue()), newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_allStringSortLambdaStringLambdaString")
fun (() -> Expression<StringSort>).replace_all(oldValue: (() -> String), newValue: String) =
    this().replace_all(StringLiteral(oldValue()), StringLiteral(newValue))

/** Replace all occurrence of [oldValue] in [this] with [newValue]. */
@JvmName("replace_allStringSortLambdaStringSortStringSortLambda")
fun (() -> Expression<StringSort>).replace_all(
    oldValue: Expression<StringSort>,
    newValue: (() -> Expression<StringSort>)
) = this().replace_all(oldValue, newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].* - [newValue] is converted to
 * [StringLiteral]
 */
@JvmName("replace_allStringSortLambdaStringSortStringLambda")
fun (() -> Expression<StringSort>).replace_all(
    oldValue: Expression<StringSort>,
    newValue: (() -> String)
) = this().replace_all(oldValue, StringLiteral(newValue()))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replace_allStringSortLambdaStringStringSortLambda")
fun (() -> Expression<StringSort>).replace_all(
    oldValue: String,
    newValue: (() -> Expression<StringSort>)
) = this().replace_all(StringLiteral(oldValue), newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_allStringSortLambdaStringStringLambda")
fun (() -> Expression<StringSort>).replace_all(oldValue: String, newValue: (() -> String)) =
    this().replace_all(StringLiteral(oldValue), StringLiteral(newValue()))

/** Replace all occurrence of [oldValue] in [this] with [newValue]. */
@JvmName("replace_allStringSortLambdaStringSortLambdaStringSortLambda")
fun (() -> Expression<StringSort>).replace_all(
    oldValue: (() -> Expression<StringSort>),
    newValue: (() -> Expression<StringSort>)
) = this().replace_all(oldValue(), newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].* - [newValue] is converted to
 * [StringLiteral]
 */
@JvmName("replace_allStringSortLambdaStringSortLambdaStringLambda")
fun (() -> Expression<StringSort>).replace_all(
    oldValue: (() -> Expression<StringSort>),
    newValue: (() -> String)
) = this().replace_all(oldValue(), StringLiteral(newValue()))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replace_allStringSortLambdaStringLambdaStringSortLambda")
fun (() -> Expression<StringSort>).replace_all(
    oldValue: (() -> String),
    newValue: (() -> Expression<StringSort>)
) = this().replace_all(StringLiteral(oldValue()), newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_allStringSortLambdaStringLambdaStringLambda")
fun (() -> Expression<StringSort>).replace_all(oldValue: (() -> String), newValue: (() -> String)) =
    this().replace_all(StringLiteral(oldValue()), StringLiteral(newValue()))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replace_allStringStringSortStringSort")
fun String.replace_all(oldValue: Expression<StringSort>, newValue: Expression<StringSort>) =
    StringLiteral(this).replace_all(oldValue, newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_allStringStringSortString")
fun String.replace_all(oldValue: Expression<StringSort>, newValue: String) =
    StringLiteral(this).replace_all(oldValue, StringLiteral(newValue))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replace_allStringStringStringSort")
fun String.replace_all(oldValue: String, newValue: Expression<StringSort>) =
    StringLiteral(this).replace_all(StringLiteral(oldValue), newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_allStringStringString")
fun String.replace_all(oldValue: String, newValue: String) =
    StringLiteral(this).replace_all(StringLiteral(oldValue), StringLiteral(newValue))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replace_allStringStringSortLambdaStringSort")
fun String.replace_all(oldValue: (() -> Expression<StringSort>), newValue: Expression<StringSort>) =
    StringLiteral(this).replace_all(oldValue(), newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_allStringStringSortLambdaString")
fun String.replace_all(oldValue: (() -> Expression<StringSort>), newValue: String) =
    StringLiteral(this).replace_all(oldValue(), StringLiteral(newValue))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replace_allStringStringLambdaStringSort")
fun String.replace_all(oldValue: (() -> String), newValue: Expression<StringSort>) =
    StringLiteral(this).replace_all(StringLiteral(oldValue()), newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_allStringStringLambdaString")
fun String.replace_all(oldValue: (() -> String), newValue: String) =
    StringLiteral(this).replace_all(StringLiteral(oldValue()), StringLiteral(newValue))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replace_allStringStringSortStringSortLambda")
fun String.replace_all(oldValue: Expression<StringSort>, newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this).replace_all(oldValue, newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_allStringStringSortStringLambda")
fun String.replace_all(oldValue: Expression<StringSort>, newValue: (() -> String)) =
    StringLiteral(this).replace_all(oldValue, StringLiteral(newValue()))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replace_allStringStringStringSortLambda")
fun String.replace_all(oldValue: String, newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this).replace_all(StringLiteral(oldValue), newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_allStringStringStringLambda")
fun String.replace_all(oldValue: String, newValue: (() -> String)) =
    StringLiteral(this).replace_all(StringLiteral(oldValue), StringLiteral(newValue()))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replace_allStringStringSortLambdaStringSortLambda")
fun String.replace_all(
    oldValue: (() -> Expression<StringSort>),
    newValue: (() -> Expression<StringSort>)
) = StringLiteral(this).replace_all(oldValue(), newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_allStringStringSortLambdaStringLambda")
fun String.replace_all(oldValue: (() -> Expression<StringSort>), newValue: (() -> String)) =
    StringLiteral(this).replace_all(oldValue(), StringLiteral(newValue()))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replace_allStringStringLambdaStringSortLambda")
fun String.replace_all(oldValue: (() -> String), newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this).replace_all(StringLiteral(oldValue()), newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_allStringStringLambdaStringLambda")
fun String.replace_all(oldValue: (() -> String), newValue: (() -> String)) =
    StringLiteral(this).replace_all(StringLiteral(oldValue()), StringLiteral(newValue()))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replace_allStringLambdaStringSortStringSort")
fun (() -> String).replace_all(oldValue: Expression<StringSort>, newValue: Expression<StringSort>) =
    StringLiteral(this()).replace_all(oldValue, newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_allStringLambdaStringSortString")
fun (() -> String).replace_all(oldValue: Expression<StringSort>, newValue: String) =
    StringLiteral(this()).replace_all(oldValue, StringLiteral(newValue))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replace_allStringLambdaStringStringSort")
fun (() -> String).replace_all(oldValue: String, newValue: Expression<StringSort>) =
    StringLiteral(this()).replace_all(StringLiteral(oldValue), newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_allStringLambdaStringString")
fun (() -> String).replace_all(oldValue: String, newValue: String) =
    StringLiteral(this()).replace_all(StringLiteral(oldValue), StringLiteral(newValue))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replace_allStringLambdaStringSortLambdaStringSort")
fun (() -> String).replace_all(
    oldValue: (() -> Expression<StringSort>),
    newValue: Expression<StringSort>
) = StringLiteral(this()).replace_all(oldValue(), newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_allStringLambdaStringSortLambdaString")
fun (() -> String).replace_all(oldValue: (() -> Expression<StringSort>), newValue: String) =
    StringLiteral(this()).replace_all(oldValue(), StringLiteral(newValue))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replace_allStringLambdaStringLambdaStringSort")
fun (() -> String).replace_all(oldValue: (() -> String), newValue: Expression<StringSort>) =
    StringLiteral(this()).replace_all(StringLiteral(oldValue()), newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_allStringLambdaStringLambdaString")
fun (() -> String).replace_all(oldValue: (() -> String), newValue: String) =
    StringLiteral(this()).replace_all(StringLiteral(oldValue()), StringLiteral(newValue))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replace_allStringLambdaStringSortStringSortLambda")
fun (() -> String).replace_all(
    oldValue: Expression<StringSort>,
    newValue: (() -> Expression<StringSort>)
) = StringLiteral(this()).replace_all(oldValue, newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_allStringLambdaStringSortStringLambda")
fun (() -> String).replace_all(oldValue: Expression<StringSort>, newValue: (() -> String)) =
    StringLiteral(this()).replace_all(oldValue, StringLiteral(newValue()))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replace_allStringLambdaStringStringSortLambda")
fun (() -> String).replace_all(oldValue: String, newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this()).replace_all(StringLiteral(oldValue), newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_allStringLambdaStringStringLambda")
fun (() -> String).replace_all(oldValue: String, newValue: (() -> String)) =
    StringLiteral(this()).replace_all(StringLiteral(oldValue), StringLiteral(newValue()))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replace_allStringLambdaStringSortLambdaStringSortLambda")
fun (() -> String).replace_all(
    oldValue: (() -> Expression<StringSort>),
    newValue: (() -> Expression<StringSort>)
) = StringLiteral(this()).replace_all(oldValue(), newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_allStringLambdaStringSortLambdaStringLambda")
fun (() -> String).replace_all(oldValue: (() -> Expression<StringSort>), newValue: (() -> String)) =
    StringLiteral(this()).replace_all(oldValue(), StringLiteral(newValue()))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .
 */
@JvmName("replace_allStringLambdaStringLambdaStringSortLambda")
fun (() -> String).replace_all(oldValue: (() -> String), newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this()).replace_all(StringLiteral(oldValue()), newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [oldValue] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_allStringLambdaStringLambdaStringLambda")
fun (() -> String).replace_all(oldValue: (() -> String), newValue: (() -> String)) =
    StringLiteral(this()).replace_all(StringLiteral(oldValue()), StringLiteral(newValue()))

/** Replace the shortest leftmost match of [regex] in [this] with [newValue]. */
fun Expression<StringSort>.replace_re(
    regex: Expression<RegLanSort>,
    newValue: Expression<StringSort>
) = StrReplaceRegex(this, regex, newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].* - [newValue] is
 * converted to [StringLiteral]
 */
@JvmName("replace_reStringSortRegLanSortString")
fun Expression<StringSort>.replace_re(regex: Expression<RegLanSort>, newValue: String) =
    this.replace_re(regex, StringLiteral(newValue))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_reStringSortStringStringSort")
fun Expression<StringSort>.replace_re(regex: String, newValue: Expression<StringSort>) =
    this.replace_re(StringLiteral(regex).toRe(), newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_reStringSortStringString")
fun Expression<StringSort>.replace_re(regex: String, newValue: String) =
    this.replace_re(StringLiteral(regex).toRe(), StringLiteral(newValue))

/** Replace the shortest leftmost match of [regex] in [this] with [newValue]. */
@JvmName("replace_reStringSortRegLanSortLambdaStringSort")
fun Expression<StringSort>.replace_re(
    regex: (() -> Expression<RegLanSort>),
    newValue: Expression<StringSort>
) = this.replace_re(regex(), newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].* - [newValue] is
 * converted to [StringLiteral]
 */
@JvmName("replace_reStringSortRegLanSortLambdaString")
fun Expression<StringSort>.replace_re(regex: (() -> Expression<RegLanSort>), newValue: String) =
    this.replace_re(regex(), StringLiteral(newValue))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_reStringSortStringLambdaStringSort")
fun Expression<StringSort>.replace_re(regex: (() -> String), newValue: Expression<StringSort>) =
    this.replace_re(StringLiteral(regex()).toRe(), newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_reStringSortStringLambdaString")
fun Expression<StringSort>.replace_re(regex: (() -> String), newValue: String) =
    this.replace_re(StringLiteral(regex()).toRe(), StringLiteral(newValue))

/** Replace the shortest leftmost match of [regex] in [this] with [newValue]. */
@JvmName("replace_reStringSortRegLanSortStringSortLambda")
fun Expression<StringSort>.replace_re(
    regex: Expression<RegLanSort>,
    newValue: (() -> Expression<StringSort>)
) = this.replace_re(regex, newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].* - [newValue] is
 * converted to [StringLiteral]
 */
@JvmName("replace_reStringSortRegLanSortStringLambda")
fun Expression<StringSort>.replace_re(regex: Expression<RegLanSort>, newValue: (() -> String)) =
    this.replace_re(regex, StringLiteral(newValue()))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_reStringSortStringStringSortLambda")
fun Expression<StringSort>.replace_re(regex: String, newValue: (() -> Expression<StringSort>)) =
    this.replace_re(StringLiteral(regex).toRe(), newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_reStringSortStringStringLambda")
fun Expression<StringSort>.replace_re(regex: String, newValue: (() -> String)) =
    this.replace_re(StringLiteral(regex).toRe(), StringLiteral(newValue()))

/** Replace the shortest leftmost match of [regex] in [this] with [newValue]. */
@JvmName("replace_reStringSortRegLanSortLambdaStringSortLambda")
fun Expression<StringSort>.replace_re(
    regex: (() -> Expression<RegLanSort>),
    newValue: (() -> Expression<StringSort>)
) = this.replace_re(regex(), newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].* - [newValue] is
 * converted to [StringLiteral]
 */
@JvmName("replace_reStringSortRegLanSortLambdaStringLambda")
fun Expression<StringSort>.replace_re(
    regex: (() -> Expression<RegLanSort>),
    newValue: (() -> String)
) = this.replace_re(regex(), StringLiteral(newValue()))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_reStringSortStringLambdaStringSortLambda")
fun Expression<StringSort>.replace_re(
    regex: (() -> String),
    newValue: (() -> Expression<StringSort>)
) = this.replace_re(StringLiteral(regex()).toRe(), newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_reStringSortStringLambdaStringLambda")
fun Expression<StringSort>.replace_re(regex: (() -> String), newValue: (() -> String)) =
    this.replace_re(StringLiteral(regex()).toRe(), StringLiteral(newValue()))

/** Replace the shortest leftmost match of [regex] in [this] with [newValue]. */
@JvmName("replace_reStringSortLambdaRegLanSortStringSort")
fun (() -> Expression<StringSort>).replace_re(
    regex: Expression<RegLanSort>,
    newValue: Expression<StringSort>
) = this().replace_re(regex, newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].* - [newValue] is
 * converted to [StringLiteral]
 */
@JvmName("replace_reStringSortLambdaRegLanSortString")
fun (() -> Expression<StringSort>).replace_re(regex: Expression<RegLanSort>, newValue: String) =
    this().replace_re(regex, StringLiteral(newValue))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_reStringSortLambdaStringStringSort")
fun (() -> Expression<StringSort>).replace_re(regex: String, newValue: Expression<StringSort>) =
    this().replace_re(StringLiteral(regex).toRe(), newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_reStringSortLambdaStringString")
fun (() -> Expression<StringSort>).replace_re(regex: String, newValue: String) =
    this().replace_re(StringLiteral(regex).toRe(), StringLiteral(newValue))

/** Replace the shortest leftmost match of [regex] in [this] with [newValue]. */
@JvmName("replace_reStringSortLambdaRegLanSortLambdaStringSort")
fun (() -> Expression<StringSort>).replace_re(
    regex: (() -> Expression<RegLanSort>),
    newValue: Expression<StringSort>
) = this().replace_re(regex(), newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].* - [newValue] is
 * converted to [StringLiteral]
 */
@JvmName("replace_reStringSortLambdaRegLanSortLambdaString")
fun (() -> Expression<StringSort>).replace_re(
    regex: (() -> Expression<RegLanSort>),
    newValue: String
) = this().replace_re(regex(), StringLiteral(newValue))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_reStringSortLambdaStringLambdaStringSort")
fun (() -> Expression<StringSort>).replace_re(
    regex: (() -> String),
    newValue: Expression<StringSort>
) = this().replace_re(StringLiteral(regex()).toRe(), newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_reStringSortLambdaStringLambdaString")
fun (() -> Expression<StringSort>).replace_re(regex: (() -> String), newValue: String) =
    this().replace_re(StringLiteral(regex()).toRe(), StringLiteral(newValue))

/** Replace the shortest leftmost match of [regex] in [this] with [newValue]. */
@JvmName("replace_reStringSortLambdaRegLanSortStringSortLambda")
fun (() -> Expression<StringSort>).replace_re(
    regex: Expression<RegLanSort>,
    newValue: (() -> Expression<StringSort>)
) = this().replace_re(regex, newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].* - [newValue] is
 * converted to [StringLiteral]
 */
@JvmName("replace_reStringSortLambdaRegLanSortStringLambda")
fun (() -> Expression<StringSort>).replace_re(
    regex: Expression<RegLanSort>,
    newValue: (() -> String)
) = this().replace_re(regex, StringLiteral(newValue()))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_reStringSortLambdaStringStringSortLambda")
fun (() -> Expression<StringSort>).replace_re(
    regex: String,
    newValue: (() -> Expression<StringSort>)
) = this().replace_re(StringLiteral(regex).toRe(), newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_reStringSortLambdaStringStringLambda")
fun (() -> Expression<StringSort>).replace_re(regex: String, newValue: (() -> String)) =
    this().replace_re(StringLiteral(regex).toRe(), StringLiteral(newValue()))

/** Replace the shortest leftmost match of [regex] in [this] with [newValue]. */
@JvmName("replace_reStringSortLambdaRegLanSortLambdaStringSortLambda")
fun (() -> Expression<StringSort>).replace_re(
    regex: (() -> Expression<RegLanSort>),
    newValue: (() -> Expression<StringSort>)
) = this().replace_re(regex(), newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].* - [newValue] is
 * converted to [StringLiteral]
 */
@JvmName("replace_reStringSortLambdaRegLanSortLambdaStringLambda")
fun (() -> Expression<StringSort>).replace_re(
    regex: (() -> Expression<RegLanSort>),
    newValue: (() -> String)
) = this().replace_re(regex(), StringLiteral(newValue()))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_reStringSortLambdaStringLambdaStringSortLambda")
fun (() -> Expression<StringSort>).replace_re(
    regex: (() -> String),
    newValue: (() -> Expression<StringSort>)
) = this().replace_re(StringLiteral(regex()).toRe(), newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_reStringSortLambdaStringLambdaStringLambda")
fun (() -> Expression<StringSort>).replace_re(regex: (() -> String), newValue: (() -> String)) =
    this().replace_re(StringLiteral(regex()).toRe(), StringLiteral(newValue()))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replace_reStringRegLanSortStringSort")
fun String.replace_re(regex: Expression<RegLanSort>, newValue: Expression<StringSort>) =
    StringLiteral(this).replace_re(regex, newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_reStringRegLanSortString")
fun String.replace_re(regex: Expression<RegLanSort>, newValue: String) =
    StringLiteral(this).replace_re(regex, StringLiteral(newValue))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_reStringStringStringSort")
fun String.replace_re(regex: String, newValue: Expression<StringSort>) =
    StringLiteral(this).replace_re(StringLiteral(regex).toRe(), newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_reStringStringString")
fun String.replace_re(regex: String, newValue: String) =
    StringLiteral(this).replace_re(StringLiteral(regex).toRe(), StringLiteral(newValue))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replace_reStringRegLanSortLambdaStringSort")
fun String.replace_re(regex: (() -> Expression<RegLanSort>), newValue: Expression<StringSort>) =
    StringLiteral(this).replace_re(regex(), newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_reStringRegLanSortLambdaString")
fun String.replace_re(regex: (() -> Expression<RegLanSort>), newValue: String) =
    StringLiteral(this).replace_re(regex(), StringLiteral(newValue))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_reStringStringLambdaStringSort")
fun String.replace_re(regex: (() -> String), newValue: Expression<StringSort>) =
    StringLiteral(this).replace_re(StringLiteral(regex()).toRe(), newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_reStringStringLambdaString")
fun String.replace_re(regex: (() -> String), newValue: String) =
    StringLiteral(this).replace_re(StringLiteral(regex()).toRe(), StringLiteral(newValue))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replace_reStringRegLanSortStringSortLambda")
fun String.replace_re(regex: Expression<RegLanSort>, newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this).replace_re(regex, newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_reStringRegLanSortStringLambda")
fun String.replace_re(regex: Expression<RegLanSort>, newValue: (() -> String)) =
    StringLiteral(this).replace_re(regex, StringLiteral(newValue()))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_reStringStringStringSortLambda")
fun String.replace_re(regex: String, newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this).replace_re(StringLiteral(regex).toRe(), newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_reStringStringStringLambda")
fun String.replace_re(regex: String, newValue: (() -> String)) =
    StringLiteral(this).replace_re(StringLiteral(regex).toRe(), StringLiteral(newValue()))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replace_reStringRegLanSortLambdaStringSortLambda")
fun String.replace_re(
    regex: (() -> Expression<RegLanSort>),
    newValue: (() -> Expression<StringSort>)
) = StringLiteral(this).replace_re(regex(), newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_reStringRegLanSortLambdaStringLambda")
fun String.replace_re(regex: (() -> Expression<RegLanSort>), newValue: (() -> String)) =
    StringLiteral(this).replace_re(regex(), StringLiteral(newValue()))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_reStringStringLambdaStringSortLambda")
fun String.replace_re(regex: (() -> String), newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this).replace_re(StringLiteral(regex()).toRe(), newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_reStringStringLambdaStringLambda")
fun String.replace_re(regex: (() -> String), newValue: (() -> String)) =
    StringLiteral(this).replace_re(StringLiteral(regex()).toRe(), StringLiteral(newValue()))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replace_reStringLambdaRegLanSortStringSort")
fun (() -> String).replace_re(regex: Expression<RegLanSort>, newValue: Expression<StringSort>) =
    StringLiteral(this()).replace_re(regex, newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_reStringLambdaRegLanSortString")
fun (() -> String).replace_re(regex: Expression<RegLanSort>, newValue: String) =
    StringLiteral(this()).replace_re(regex, StringLiteral(newValue))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_reStringLambdaStringStringSort")
fun (() -> String).replace_re(regex: String, newValue: Expression<StringSort>) =
    StringLiteral(this()).replace_re(StringLiteral(regex).toRe(), newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_reStringLambdaStringString")
fun (() -> String).replace_re(regex: String, newValue: String) =
    StringLiteral(this()).replace_re(StringLiteral(regex).toRe(), StringLiteral(newValue))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replace_reStringLambdaRegLanSortLambdaStringSort")
fun (() -> String).replace_re(
    regex: (() -> Expression<RegLanSort>),
    newValue: Expression<StringSort>
) = StringLiteral(this()).replace_re(regex(), newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_reStringLambdaRegLanSortLambdaString")
fun (() -> String).replace_re(regex: (() -> Expression<RegLanSort>), newValue: String) =
    StringLiteral(this()).replace_re(regex(), StringLiteral(newValue))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_reStringLambdaStringLambdaStringSort")
fun (() -> String).replace_re(regex: (() -> String), newValue: Expression<StringSort>) =
    StringLiteral(this()).replace_re(StringLiteral(regex()).toRe(), newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_reStringLambdaStringLambdaString")
fun (() -> String).replace_re(regex: (() -> String), newValue: String) =
    StringLiteral(this()).replace_re(StringLiteral(regex()).toRe(), StringLiteral(newValue))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replace_reStringLambdaRegLanSortStringSortLambda")
fun (() -> String).replace_re(
    regex: Expression<RegLanSort>,
    newValue: (() -> Expression<StringSort>)
) = StringLiteral(this()).replace_re(regex, newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_reStringLambdaRegLanSortStringLambda")
fun (() -> String).replace_re(regex: Expression<RegLanSort>, newValue: (() -> String)) =
    StringLiteral(this()).replace_re(regex, StringLiteral(newValue()))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_reStringLambdaStringStringSortLambda")
fun (() -> String).replace_re(regex: String, newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this()).replace_re(StringLiteral(regex).toRe(), newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_reStringLambdaStringStringLambda")
fun (() -> String).replace_re(regex: String, newValue: (() -> String)) =
    StringLiteral(this()).replace_re(StringLiteral(regex).toRe(), StringLiteral(newValue()))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replace_reStringLambdaRegLanSortLambdaStringSortLambda")
fun (() -> String).replace_re(
    regex: (() -> Expression<RegLanSort>),
    newValue: (() -> Expression<StringSort>)
) = StringLiteral(this()).replace_re(regex(), newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_reStringLambdaRegLanSortLambdaStringLambda")
fun (() -> String).replace_re(regex: (() -> Expression<RegLanSort>), newValue: (() -> String)) =
    StringLiteral(this()).replace_re(regex(), StringLiteral(newValue()))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_reStringLambdaStringLambdaStringSortLambda")
fun (() -> String).replace_re(regex: (() -> String), newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this()).replace_re(StringLiteral(regex()).toRe(), newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_reStringLambdaStringLambdaStringLambda")
fun (() -> String).replace_re(regex: (() -> String), newValue: (() -> String)) =
    StringLiteral(this()).replace_re(StringLiteral(regex()).toRe(), StringLiteral(newValue()))

/** Replace all matchs of [regex] in [this] with [newValue]. */
fun Expression<StringSort>.replace_re_all(
    regex: Expression<RegLanSort>,
    newValue: Expression<StringSort>
) = StrReplaceAllRegex(this, regex, newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue].* - [newValue] is converted to
 * [StringLiteral]
 */
@JvmName("replace_re_allStringSortRegLanSortString")
fun Expression<StringSort>.replace_re_all(regex: Expression<RegLanSort>, newValue: String) =
    this.replace_re_all(regex, StringLiteral(newValue))

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_re_allStringSortStringStringSort")
fun Expression<StringSort>.replace_re_all(regex: String, newValue: Expression<StringSort>) =
    this.replace_re_all(StringLiteral(regex).toRe(), newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_re_allStringSortStringString")
fun Expression<StringSort>.replace_re_all(regex: String, newValue: String) =
    this.replace_re_all(StringLiteral(regex).toRe(), StringLiteral(newValue))

/** Replace all matchs of [regex] in [this] with [newValue]. */
@JvmName("replace_re_allStringSortRegLanSortLambdaStringSort")
fun Expression<StringSort>.replace_re_all(
    regex: (() -> Expression<RegLanSort>),
    newValue: Expression<StringSort>
) = this.replace_re_all(regex(), newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue].* - [newValue] is converted to
 * [StringLiteral]
 */
@JvmName("replace_re_allStringSortRegLanSortLambdaString")
fun Expression<StringSort>.replace_re_all(regex: (() -> Expression<RegLanSort>), newValue: String) =
    this.replace_re_all(regex(), StringLiteral(newValue))

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_re_allStringSortStringLambdaStringSort")
fun Expression<StringSort>.replace_re_all(regex: (() -> String), newValue: Expression<StringSort>) =
    this.replace_re_all(StringLiteral(regex()).toRe(), newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_re_allStringSortStringLambdaString")
fun Expression<StringSort>.replace_re_all(regex: (() -> String), newValue: String) =
    this.replace_re_all(StringLiteral(regex()).toRe(), StringLiteral(newValue))

/** Replace all matchs of [regex] in [this] with [newValue]. */
@JvmName("replace_re_allStringSortRegLanSortStringSortLambda")
fun Expression<StringSort>.replace_re_all(
    regex: Expression<RegLanSort>,
    newValue: (() -> Expression<StringSort>)
) = this.replace_re_all(regex, newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue].* - [newValue] is converted to
 * [StringLiteral]
 */
@JvmName("replace_re_allStringSortRegLanSortStringLambda")
fun Expression<StringSort>.replace_re_all(regex: Expression<RegLanSort>, newValue: (() -> String)) =
    this.replace_re_all(regex, StringLiteral(newValue()))

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_re_allStringSortStringStringSortLambda")
fun Expression<StringSort>.replace_re_all(regex: String, newValue: (() -> Expression<StringSort>)) =
    this.replace_re_all(StringLiteral(regex).toRe(), newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_re_allStringSortStringStringLambda")
fun Expression<StringSort>.replace_re_all(regex: String, newValue: (() -> String)) =
    this.replace_re_all(StringLiteral(regex).toRe(), StringLiteral(newValue()))

/** Replace all matchs of [regex] in [this] with [newValue]. */
@JvmName("replace_re_allStringSortRegLanSortLambdaStringSortLambda")
fun Expression<StringSort>.replace_re_all(
    regex: (() -> Expression<RegLanSort>),
    newValue: (() -> Expression<StringSort>)
) = this.replace_re_all(regex(), newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue].* - [newValue] is converted to
 * [StringLiteral]
 */
@JvmName("replace_re_allStringSortRegLanSortLambdaStringLambda")
fun Expression<StringSort>.replace_re_all(
    regex: (() -> Expression<RegLanSort>),
    newValue: (() -> String)
) = this.replace_re_all(regex(), StringLiteral(newValue()))

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_re_allStringSortStringLambdaStringSortLambda")
fun Expression<StringSort>.replace_re_all(
    regex: (() -> String),
    newValue: (() -> Expression<StringSort>)
) = this.replace_re_all(StringLiteral(regex()).toRe(), newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_re_allStringSortStringLambdaStringLambda")
fun Expression<StringSort>.replace_re_all(regex: (() -> String), newValue: (() -> String)) =
    this.replace_re_all(StringLiteral(regex()).toRe(), StringLiteral(newValue()))

/** Replace all matchs of [regex] in [this] with [newValue]. */
@JvmName("replace_re_allStringSortLambdaRegLanSortStringSort")
fun (() -> Expression<StringSort>).replace_re_all(
    regex: Expression<RegLanSort>,
    newValue: Expression<StringSort>
) = this().replace_re_all(regex, newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue].* - [newValue] is converted to
 * [StringLiteral]
 */
@JvmName("replace_re_allStringSortLambdaRegLanSortString")
fun (() -> Expression<StringSort>).replace_re_all(regex: Expression<RegLanSort>, newValue: String) =
    this().replace_re_all(regex, StringLiteral(newValue))

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_re_allStringSortLambdaStringStringSort")
fun (() -> Expression<StringSort>).replace_re_all(regex: String, newValue: Expression<StringSort>) =
    this().replace_re_all(StringLiteral(regex).toRe(), newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_re_allStringSortLambdaStringString")
fun (() -> Expression<StringSort>).replace_re_all(regex: String, newValue: String) =
    this().replace_re_all(StringLiteral(regex).toRe(), StringLiteral(newValue))

/** Replace all matchs of [regex] in [this] with [newValue]. */
@JvmName("replace_re_allStringSortLambdaRegLanSortLambdaStringSort")
fun (() -> Expression<StringSort>).replace_re_all(
    regex: (() -> Expression<RegLanSort>),
    newValue: Expression<StringSort>
) = this().replace_re_all(regex(), newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue].* - [newValue] is converted to
 * [StringLiteral]
 */
@JvmName("replace_re_allStringSortLambdaRegLanSortLambdaString")
fun (() -> Expression<StringSort>).replace_re_all(
    regex: (() -> Expression<RegLanSort>),
    newValue: String
) = this().replace_re_all(regex(), StringLiteral(newValue))

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_re_allStringSortLambdaStringLambdaStringSort")
fun (() -> Expression<StringSort>).replace_re_all(
    regex: (() -> String),
    newValue: Expression<StringSort>
) = this().replace_re_all(StringLiteral(regex()).toRe(), newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_re_allStringSortLambdaStringLambdaString")
fun (() -> Expression<StringSort>).replace_re_all(regex: (() -> String), newValue: String) =
    this().replace_re_all(StringLiteral(regex()).toRe(), StringLiteral(newValue))

/** Replace all matchs of [regex] in [this] with [newValue]. */
@JvmName("replace_re_allStringSortLambdaRegLanSortStringSortLambda")
fun (() -> Expression<StringSort>).replace_re_all(
    regex: Expression<RegLanSort>,
    newValue: (() -> Expression<StringSort>)
) = this().replace_re_all(regex, newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue].* - [newValue] is converted to
 * [StringLiteral]
 */
@JvmName("replace_re_allStringSortLambdaRegLanSortStringLambda")
fun (() -> Expression<StringSort>).replace_re_all(
    regex: Expression<RegLanSort>,
    newValue: (() -> String)
) = this().replace_re_all(regex, StringLiteral(newValue()))

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_re_allStringSortLambdaStringStringSortLambda")
fun (() -> Expression<StringSort>).replace_re_all(
    regex: String,
    newValue: (() -> Expression<StringSort>)
) = this().replace_re_all(StringLiteral(regex).toRe(), newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_re_allStringSortLambdaStringStringLambda")
fun (() -> Expression<StringSort>).replace_re_all(regex: String, newValue: (() -> String)) =
    this().replace_re_all(StringLiteral(regex).toRe(), StringLiteral(newValue()))

/** Replace all matchs of [regex] in [this] with [newValue]. */
@JvmName("replace_re_allStringSortLambdaRegLanSortLambdaStringSortLambda")
fun (() -> Expression<StringSort>).replace_re_all(
    regex: (() -> Expression<RegLanSort>),
    newValue: (() -> Expression<StringSort>)
) = this().replace_re_all(regex(), newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue].* - [newValue] is converted to
 * [StringLiteral]
 */
@JvmName("replace_re_allStringSortLambdaRegLanSortLambdaStringLambda")
fun (() -> Expression<StringSort>).replace_re_all(
    regex: (() -> Expression<RegLanSort>),
    newValue: (() -> String)
) = this().replace_re_all(regex(), StringLiteral(newValue()))

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_re_allStringSortLambdaStringLambdaStringSortLambda")
fun (() -> Expression<StringSort>).replace_re_all(
    regex: (() -> String),
    newValue: (() -> Expression<StringSort>)
) = this().replace_re_all(StringLiteral(regex()).toRe(), newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_re_allStringSortLambdaStringLambdaStringLambda")
fun (() -> Expression<StringSort>).replace_re_all(regex: (() -> String), newValue: (() -> String)) =
    this().replace_re_all(StringLiteral(regex()).toRe(), StringLiteral(newValue()))

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replace_re_allStringRegLanSortStringSort")
fun String.replace_re_all(regex: Expression<RegLanSort>, newValue: Expression<StringSort>) =
    StringLiteral(this).replace_re_all(regex, newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_re_allStringRegLanSortString")
fun String.replace_re_all(regex: Expression<RegLanSort>, newValue: String) =
    StringLiteral(this).replace_re_all(regex, StringLiteral(newValue))

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_re_allStringStringStringSort")
fun String.replace_re_all(regex: String, newValue: Expression<StringSort>) =
    StringLiteral(this).replace_re_all(StringLiteral(regex).toRe(), newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_re_allStringStringString")
fun String.replace_re_all(regex: String, newValue: String) =
    StringLiteral(this).replace_re_all(StringLiteral(regex).toRe(), StringLiteral(newValue))

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replace_re_allStringRegLanSortLambdaStringSort")
fun String.replace_re_all(regex: (() -> Expression<RegLanSort>), newValue: Expression<StringSort>) =
    StringLiteral(this).replace_re_all(regex(), newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_re_allStringRegLanSortLambdaString")
fun String.replace_re_all(regex: (() -> Expression<RegLanSort>), newValue: String) =
    StringLiteral(this).replace_re_all(regex(), StringLiteral(newValue))

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_re_allStringStringLambdaStringSort")
fun String.replace_re_all(regex: (() -> String), newValue: Expression<StringSort>) =
    StringLiteral(this).replace_re_all(StringLiteral(regex()).toRe(), newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_re_allStringStringLambdaString")
fun String.replace_re_all(regex: (() -> String), newValue: String) =
    StringLiteral(this).replace_re_all(StringLiteral(regex()).toRe(), StringLiteral(newValue))

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replace_re_allStringRegLanSortStringSortLambda")
fun String.replace_re_all(regex: Expression<RegLanSort>, newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this).replace_re_all(regex, newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_re_allStringRegLanSortStringLambda")
fun String.replace_re_all(regex: Expression<RegLanSort>, newValue: (() -> String)) =
    StringLiteral(this).replace_re_all(regex, StringLiteral(newValue()))

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_re_allStringStringStringSortLambda")
fun String.replace_re_all(regex: String, newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this).replace_re_all(StringLiteral(regex).toRe(), newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_re_allStringStringStringLambda")
fun String.replace_re_all(regex: String, newValue: (() -> String)) =
    StringLiteral(this).replace_re_all(StringLiteral(regex).toRe(), StringLiteral(newValue()))

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replace_re_allStringRegLanSortLambdaStringSortLambda")
fun String.replace_re_all(
    regex: (() -> Expression<RegLanSort>),
    newValue: (() -> Expression<StringSort>)
) = StringLiteral(this).replace_re_all(regex(), newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_re_allStringRegLanSortLambdaStringLambda")
fun String.replace_re_all(regex: (() -> Expression<RegLanSort>), newValue: (() -> String)) =
    StringLiteral(this).replace_re_all(regex(), StringLiteral(newValue()))

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_re_allStringStringLambdaStringSortLambda")
fun String.replace_re_all(regex: (() -> String), newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this).replace_re_all(StringLiteral(regex()).toRe(), newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_re_allStringStringLambdaStringLambda")
fun String.replace_re_all(regex: (() -> String), newValue: (() -> String)) =
    StringLiteral(this).replace_re_all(StringLiteral(regex()).toRe(), StringLiteral(newValue()))

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replace_re_allStringLambdaRegLanSortStringSort")
fun (() -> String).replace_re_all(regex: Expression<RegLanSort>, newValue: Expression<StringSort>) =
    StringLiteral(this()).replace_re_all(regex, newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_re_allStringLambdaRegLanSortString")
fun (() -> String).replace_re_all(regex: Expression<RegLanSort>, newValue: String) =
    StringLiteral(this()).replace_re_all(regex, StringLiteral(newValue))

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_re_allStringLambdaStringStringSort")
fun (() -> String).replace_re_all(regex: String, newValue: Expression<StringSort>) =
    StringLiteral(this()).replace_re_all(StringLiteral(regex).toRe(), newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_re_allStringLambdaStringString")
fun (() -> String).replace_re_all(regex: String, newValue: String) =
    StringLiteral(this()).replace_re_all(StringLiteral(regex).toRe(), StringLiteral(newValue))

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replace_re_allStringLambdaRegLanSortLambdaStringSort")
fun (() -> String).replace_re_all(
    regex: (() -> Expression<RegLanSort>),
    newValue: Expression<StringSort>
) = StringLiteral(this()).replace_re_all(regex(), newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_re_allStringLambdaRegLanSortLambdaString")
fun (() -> String).replace_re_all(regex: (() -> Expression<RegLanSort>), newValue: String) =
    StringLiteral(this()).replace_re_all(regex(), StringLiteral(newValue))

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_re_allStringLambdaStringLambdaStringSort")
fun (() -> String).replace_re_all(regex: (() -> String), newValue: Expression<StringSort>) =
    StringLiteral(this()).replace_re_all(StringLiteral(regex()).toRe(), newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_re_allStringLambdaStringLambdaString")
fun (() -> String).replace_re_all(regex: (() -> String), newValue: String) =
    StringLiteral(this()).replace_re_all(StringLiteral(regex()).toRe(), StringLiteral(newValue))

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replace_re_allStringLambdaRegLanSortStringSortLambda")
fun (() -> String).replace_re_all(
    regex: Expression<RegLanSort>,
    newValue: (() -> Expression<StringSort>)
) = StringLiteral(this()).replace_re_all(regex, newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_re_allStringLambdaRegLanSortStringLambda")
fun (() -> String).replace_re_all(regex: Expression<RegLanSort>, newValue: (() -> String)) =
    StringLiteral(this()).replace_re_all(regex, StringLiteral(newValue()))

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_re_allStringLambdaStringStringSortLambda")
fun (() -> String).replace_re_all(regex: String, newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this()).replace_re_all(StringLiteral(regex).toRe(), newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_re_allStringLambdaStringStringLambda")
fun (() -> String).replace_re_all(regex: String, newValue: (() -> String)) =
    StringLiteral(this()).replace_re_all(StringLiteral(regex).toRe(), StringLiteral(newValue()))

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .
 */
@JvmName("replace_re_allStringLambdaRegLanSortLambdaStringSortLambda")
fun (() -> String).replace_re_all(
    regex: (() -> Expression<RegLanSort>),
    newValue: (() -> Expression<StringSort>)
) = StringLiteral(this()).replace_re_all(regex(), newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral] .* - [newValue] is converted to [StringLiteral]
 */
@JvmName("replace_re_allStringLambdaRegLanSortLambdaStringLambda")
fun (() -> String).replace_re_all(regex: (() -> Expression<RegLanSort>), newValue: (() -> String)) =
    StringLiteral(this()).replace_re_all(regex(), StringLiteral(newValue()))

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("replace_re_allStringLambdaStringLambdaStringSortLambda")
fun (() -> String).replace_re_all(regex: (() -> String), newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this()).replace_re_all(StringLiteral(regex()).toRe(), newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue].
 * - [this] is converted to [StringLiteral]
 * - [regex] is converted to [Expression] of type [RegLanSort] .* - [newValue] is converted to
 *   [StringLiteral]
 */
@JvmName("replace_re_allStringLambdaStringLambdaStringLambda")
fun (() -> String).replace_re_all(regex: (() -> String), newValue: (() -> String)) =
    StringLiteral(this()).replace_re_all(StringLiteral(regex()).toRe(), StringLiteral(newValue()))

/** Regex complement. */
fun Expression<RegLanSort>.comp() = RegexComp(this)

/**
 * Regex complement.
 * - [this] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("compString") fun String.comp() = StringLiteral(this).toRe().comp()

/** Regex complement. */
@JvmName("compRegLanSortLambda") fun (() -> Expression<RegLanSort>).comp() = this().comp()

/**
 * Regex complement.
 * - [this] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("compStringLambda") fun (() -> String).comp() = StringLiteral(this()).toRe().comp()

/** Regex difference. */
infix fun Expression<RegLanSort>.diff(rhs: Expression<RegLanSort>) =
    if (this is RegexDiff) {
      RegexDiff(this.children + rhs)
    } else {
      RegexDiff(this, rhs)
    }

/**
 * Regex difference.
 * - [rhs] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("diffRegLanSortString")
infix fun Expression<RegLanSort>.diff(rhs: String) = this diff StringLiteral(rhs).toRe()

/** Regex difference. */
@JvmName("diffRegLanSortRegLanSortLambda")
infix fun Expression<RegLanSort>.diff(rhs: (() -> Expression<RegLanSort>)) = this diff rhs()

/**
 * Regex difference.
 * - [rhs] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("diffRegLanSortStringLambda")
infix fun Expression<RegLanSort>.diff(rhs: (() -> String)) = this diff StringLiteral(rhs()).toRe()

/** Regex difference. */
@JvmName("diffRegLanSortLambdaRegLanSort")
infix fun (() -> Expression<RegLanSort>).diff(rhs: Expression<RegLanSort>) = this() diff rhs

/**
 * Regex difference.
 * - [rhs] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("diffRegLanSortLambdaString")
infix fun (() -> Expression<RegLanSort>).diff(rhs: String) = this() diff StringLiteral(rhs).toRe()

/** Regex difference. */
@JvmName("diffRegLanSortLambdaRegLanSortLambda")
infix fun (() -> Expression<RegLanSort>).diff(rhs: (() -> Expression<RegLanSort>)) =
    this() diff rhs()

/**
 * Regex difference.
 * - [rhs] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("diffRegLanSortLambdaStringLambda")
infix fun (() -> Expression<RegLanSort>).diff(rhs: (() -> String)) =
    this() diff StringLiteral(rhs()).toRe()

/**
 * Regex difference.
 * - [String] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("diffStringRegLanSort")
infix fun String.diff(rhs: Expression<RegLanSort>) = StringLiteral(this).toRe() diff rhs

/**
 * Regex difference.
 * - [String] is converted to [Expression] of type [RegLanSort]
 * - [rhs] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("diffStringString")
infix fun String.diff(rhs: String) = StringLiteral(this).toRe() diff StringLiteral(rhs).toRe()

/**
 * Regex difference.
 * - [String] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("diffStringRegLanSortLambda")
infix fun String.diff(rhs: (() -> Expression<RegLanSort>)) = StringLiteral(this).toRe() diff rhs()

/**
 * Regex difference.
 * - [String] is converted to [Expression] of type [RegLanSort]
 * - [rhs] is converted to [Expression] of type [RegLanSort] .
 */
@JvmName("diffStringStringLambda")
infix fun String.diff(rhs: (() -> String)) =
    StringLiteral(this).toRe() diff StringLiteral(rhs()).toRe()

/** Regex difference. */
@JvmName("diffStringLambdaRegLanSort")
infix fun (() -> String).diff(rhs: Expression<RegLanSort>) = StringLiteral(this()).toRe() diff rhs

/**
 * Regex difference.
 * - [rhs] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("diffStringLambdaString")
infix fun (() -> String).diff(rhs: String) =
    StringLiteral(this()).toRe() diff StringLiteral(rhs).toRe()

/** Regex difference. */
@JvmName("diffStringLambdaRegLanSortLambda")
infix fun (() -> String).diff(rhs: (() -> Expression<RegLanSort>)) =
    StringLiteral(this()).toRe() diff rhs()

/**
 * Regex difference.
 * - [rhs] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("diffStringLambdaStringLambda")
infix fun (() -> String).diff(rhs: (() -> String)) =
    StringLiteral(this()).toRe() diff StringLiteral(rhs()).toRe()

/** Regex Kleene cross. */
fun Expression<RegLanSort>.plus() = RegexPlus(this)

/**
 * Regex Kleene cross.
 * - [this] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("plusString") fun String.plus() = StringLiteral(this).toRe().plus()

/** Regex Kleene cross. */
@JvmName("plusRegLanSortLambda") fun (() -> Expression<RegLanSort>).plus() = this().plus()

/**
 * Regex Kleene cross.
 * - [this] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("plusStringLambda") fun (() -> String).plus() = StringLiteral(this()).toRe().plus()

/** Regex option. */
fun Expression<RegLanSort>.opt() = RegexOption(this)

/**
 * Regex option.
 * - [this] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("optString") fun String.opt() = StringLiteral(this).toRe().opt()

/** Regex option. */
@JvmName("optRegLanSortLambda") fun (() -> Expression<RegLanSort>).opt() = this().opt()

/**
 * Regex option.
 * - [this] is converted to [Expression] of type [RegLanSort]
 */
@JvmName("optStringLambda") fun (() -> String).opt() = StringLiteral(this()).toRe().opt()

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language.
 */
infix fun Expression<StringSort>.range(end: Expression<StringSort>) = RegexRange(this, end)

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language.
 * - [end] is converted to [StringLiteral] .
 */
@JvmName("rangeStringSortString")
infix fun Expression<StringSort>.range(end: String) = this range StringLiteral(end)

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language.
 */
@JvmName("rangeStringSortStringSortLambda")
infix fun Expression<StringSort>.range(end: (() -> Expression<StringSort>)) = this range end()

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language.
 * - [end] is converted to [StringLiteral] .
 */
@JvmName("rangeStringSortStringLambda")
infix fun Expression<StringSort>.range(end: (() -> String)) = this range StringLiteral(end())

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language.
 */
@JvmName("rangeStringSortLambdaStringSort")
infix fun (() -> Expression<StringSort>).range(end: Expression<StringSort>) = this() range end

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language.
 * - [end] is converted to [StringLiteral]
 */
@JvmName("rangeStringSortLambdaString")
infix fun (() -> Expression<StringSort>).range(end: String) = this() range StringLiteral(end)

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language.
 */
@JvmName("rangeStringSortLambdaStringSortLambda")
infix fun (() -> Expression<StringSort>).range(end: (() -> Expression<StringSort>)) =
    this() range end()

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language.
 * - [end] is converted to [StringLiteral]
 */
@JvmName("rangeStringSortLambdaStringLambda")
infix fun (() -> Expression<StringSort>).range(end: (() -> String)) =
    this() range StringLiteral(end())

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language.
 * - [String] is converted to [StringLiteral] .
 */
@JvmName("rangeStringStringSort")
infix fun String.range(end: Expression<StringSort>) = StringLiteral(this) range end

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language.
 * - [String] is converted to [StringLiteral]
 * - [end] is converted to [StringLiteral] .
 */
@JvmName("rangeStringString")
infix fun String.range(end: String) = StringLiteral(this) range StringLiteral(end)

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language.
 * - [String] is converted to [StringLiteral] .
 */
@JvmName("rangeStringStringSortLambda")
infix fun String.range(end: (() -> Expression<StringSort>)) = StringLiteral(this) range end()

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language.
 * - [String] is converted to [StringLiteral]
 * - [end] is converted to [StringLiteral] .
 */
@JvmName("rangeStringStringLambda")
infix fun String.range(end: (() -> String)) = StringLiteral(this) range StringLiteral(end())

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language.
 */
@JvmName("rangeStringLambdaStringSort")
infix fun (() -> String).range(end: Expression<StringSort>) = StringLiteral(this()) range end

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language.
 * - [end] is converted to [StringLiteral]
 */
@JvmName("rangeStringLambdaString")
infix fun (() -> String).range(end: String) = StringLiteral(this()) range StringLiteral(end)

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language.
 */
@JvmName("rangeStringLambdaStringSortLambda")
infix fun (() -> String).range(end: (() -> Expression<StringSort>)) =
    StringLiteral(this()) range end()

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language.
 * - [end] is converted to [StringLiteral]
 */
@JvmName("rangeStringLambdaStringLambda")
infix fun (() -> String).range(end: (() -> String)) =
    StringLiteral(this()) range StringLiteral(end())

/** Regex power. */
fun Expression<RegLanSort>.power(n: Int) = RegexPower(this, n)

/** Regex power. */
@JvmName("powerRegLanLambdaInt")
fun (() -> Expression<RegLanSort>).power(n: Int) = RegexPower(this(), n)

/** Regex power. */
fun String.power(n: Int) = RegexPower(StringLiteral(this).toRe(), n)

/** Regex power. */
@JvmName("powerStringLambdaInt")
fun (() -> String).power(n: Int) = RegexPower(StringLiteral(this()).toRe(), n)

/** Regex loop. */
fun Expression<RegLanSort>.loop(n: Int, m: Int) = RegexLoop(this, n, m)

/** Regex loop. */
@JvmName("loopRegLanLambdaInt")
fun (() -> Expression<RegLanSort>).loop(n: Int, m: Int) = RegexLoop(this(), n, m)

/** Regex loop. */
fun String.loop(n: Int, m: Int) = RegexLoop(StringLiteral(this).toRe(), n, m)

/** Regex loop. */
@JvmName("loopStringLambdaInt")
fun (() -> String).loop(n: Int, m: Int) = RegexLoop(StringLiteral(this()).toRe(), n, m)

/**
 * Digit check. Evaluates to true iff [this] consists of a single character which is a decimal
 * digit.
 */
fun Expression<StringSort>.isDigit() = StrIsDigit(this)

/**
 * Digit check. Evaluates to true iff [this] consists of a single character which is a decimal
 * digit.
 * - [this] is converted to [StringLiteral]
 */
@JvmName("isDigitString") fun String.isDigit() = StringLiteral(this).isDigit()

/**
 * Digit check. Evaluates to true iff [this] consists of a single character which is a decimal
 * digit.
 */
@JvmName("isDigitStringSortLambda") fun (() -> Expression<StringSort>).isDigit() = this().isDigit()

/**
 * Digit check. Evaluates to true iff [this] consists of a single character which is a decimal
 * digit.
 * - [this] is converted to [StringLiteral]
 */
@JvmName("isDigitStringLambda") fun (() -> String).isDigit() = StringLiteral(this()).isDigit()

/**
 * Evaluates to the code point of [this], iff [this] is a singleton string, otherwise evaluates to
 * -1.
 */
fun Expression<StringSort>.toCode() = StrToCode(this)

/**
 * Evaluates to the code point of [this], iff [this] is a singleton string, otherwise evaluates to
 * -1.
 * - [this] is converted to [StringLiteral]
 */
@JvmName("toCodeString") fun String.toCode() = StringLiteral(this).toCode()

/**
 * Evaluates to the code point of [this], iff [this] is a singleton string, otherwise evaluates to
 * -1.
 */
@JvmName("toCodeStringSortLambda") fun (() -> Expression<StringSort>).toCode() = this().toCode()

/**
 * Evaluates to the code point of [this], iff [this] is a singleton string, otherwise evaluates to
 * -1.
 * - [this] is converted to [StringLiteral]
 */
@JvmName("toCodeStringLambda") fun (() -> String).toCode() = StringLiteral(this()).toCode()

/** Conversion from code point. */
fun Expression<IntSort>.fromCode() = StrFromCode(this)

/**
 * Conversion from code point.
 * - [this] is converted to [IntLiteral]
 */
@JvmName("fromCodeByte") fun Byte.fromCode() = IntLiteral(this).fromCode()

/**
 * Conversion from code point.
 * - [this] is converted to [IntLiteral]
 */
@JvmName("fromCodeShort") fun Short.fromCode() = IntLiteral(this).fromCode()

/**
 * Conversion from code point.
 * - [this] is converted to [IntLiteral]
 */
@JvmName("fromCodeInt") fun Int.fromCode() = IntLiteral(this).fromCode()

/**
 * Conversion from code point.
 * - [this] is converted to [IntLiteral]
 */
@JvmName("fromCodeLong") fun Long.fromCode() = IntLiteral(this).fromCode()

/**
 * Conversion from code point.
 * - [this] is converted to [IntLiteral]
 */
@JvmName("fromCodeBigInteger") fun BigInteger.fromCode() = IntLiteral(this).fromCode()

/** Conversion from code point. */
@JvmName("fromCodeIntSortLambda") fun (() -> Expression<IntSort>).fromCode() = this().fromCode()

/**
 * Conversion from code point.
 * - [this] is converted to [IntLiteral]
 */
@JvmName("fromCodeByteLambda") fun (() -> Byte).fromCode() = IntLiteral(this()).fromCode()

/**
 * Conversion from code point.
 * - [this] is converted to [IntLiteral]
 */
@JvmName("fromCodeShortLambda") fun (() -> Short).fromCode() = IntLiteral(this()).fromCode()

/**
 * Conversion from code point.
 * - [this] is converted to [IntLiteral]
 */
@JvmName("fromCodeIntLambda") fun (() -> Int).fromCode() = IntLiteral(this()).fromCode()

/**
 * Conversion from code point.
 * - [this] is converted to [IntLiteral]
 */
@JvmName("fromCodeLongLambda") fun (() -> Long).fromCode() = IntLiteral(this()).fromCode()

/**
 * Conversion from code point.
 * - [this] is converted to [IntLiteral]
 */
@JvmName("fromCodeBigIntegerLambda")
fun (() -> BigInteger).fromCode() = IntLiteral(this()).fromCode()

/** Conversion to integers. */
fun Expression<StringSort>.toSMTInt() = StrToInt(this)

/**
 * Conversion to integers.
 * - [this] is converted to [StringLiteral]
 */
@JvmName("toSMTIntString") fun String.toSMTInt() = StringLiteral(this).toSMTInt()

/** Conversion to integers. */
@JvmName("toSMTIntStringSortLambda")
fun (() -> Expression<StringSort>).toSMTInt() = this().toSMTInt()

/**
 * Conversion to integers.
 * - [this] is converted to [StringLiteral]
 */
@JvmName("toSMTIntStringLambda") fun (() -> String).toSMTInt() = StringLiteral(this()).toSMTInt()

/** Conversion from integers. */
fun Expression<IntSort>.fromInt() = StrFromInt(this)

/**
 * Conversion from integers.
 * - [this] is converted to [IntLiteral]
 */
@JvmName("fromIntByte") fun Byte.fromInt() = IntLiteral(this).fromInt()

/**
 * Conversion from integers.
 * - [this] is converted to [IntLiteral]
 */
@JvmName("fromIntShort") fun Short.fromInt() = IntLiteral(this).fromInt()

/**
 * Conversion from integers.
 * - [this] is converted to [IntLiteral]
 */
@JvmName("fromIntInt") fun Int.fromInt() = IntLiteral(this).fromInt()

/**
 * Conversion from integers.
 * - [this] is converted to [IntLiteral]
 */
@JvmName("fromIntLong") fun Long.fromInt() = IntLiteral(this).fromInt()

/**
 * Conversion from integers.
 * - [this] is converted to [IntLiteral]
 */
@JvmName("fromIntBigInteger") fun BigInteger.fromInt() = IntLiteral(this).fromInt()

/** Conversion from integers. */
@JvmName("fromIntIntSortLambda") fun (() -> Expression<IntSort>).fromInt() = this().fromInt()

/**
 * Conversion from integers.
 * - [this] is converted to [IntLiteral]
 */
@JvmName("fromIntByteLambda") fun (() -> Byte).fromInt() = IntLiteral(this()).fromInt()

/**
 * Conversion from integers.
 * - [this] is converted to [IntLiteral]
 */
@JvmName("fromIntShortLambda") fun (() -> Short).fromInt() = IntLiteral(this()).fromInt()

/**
 * Conversion from integers.
 * - [this] is converted to [IntLiteral]
 */
@JvmName("fromIntIntLambda") fun (() -> Int).fromInt() = IntLiteral(this()).fromInt()

/**
 * Conversion from integers.
 * - [this] is converted to [IntLiteral]
 */
@JvmName("fromIntLongLambda") fun (() -> Long).fromInt() = IntLiteral(this()).fromInt()

/**
 * Conversion from integers.
 * - [this] is converted to [IntLiteral]
 */
@JvmName("fromIntBigIntegerLambda") fun (() -> BigInteger).fromInt() = IntLiteral(this()).fromInt()

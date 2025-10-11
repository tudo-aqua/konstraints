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

/** String concatenation. [rhs] is converted to [StringLiteral] . */
infix fun Expression<StringSort>.concat(rhs: String) = this concat StringLiteral(rhs)

/** String concatenation. . */
infix fun Expression<StringSort>.concat(rhs: (() -> Expression<StringSort>)) = this concat rhs()

/** String concatenation. [rhs] is converted to [StringLiteral] . */
infix fun Expression<StringSort>.concat(rhs: (() -> String)) = this concat StringLiteral(rhs())

/** String concatenation. */
infix fun (() -> Expression<StringSort>).concat(rhs: Expression<StringSort>) = this() concat rhs

/** String concatenation. [rhs] is converted to [StringLiteral] */
infix fun (() -> Expression<StringSort>).concat(rhs: String) = this() concat StringLiteral(rhs)

/** String concatenation. */
infix fun (() -> Expression<StringSort>).concat(rhs: (() -> Expression<StringSort>)) =
    this() concat rhs()

/** String concatenation. [rhs] is converted to [StringLiteral] */
infix fun (() -> Expression<StringSort>).concat(rhs: (() -> String)) =
    this() concat StringLiteral(rhs())

/** String concatenation. [String] is converted to [StringLiteral] . */
infix fun String.concat(rhs: Expression<StringSort>) = StringLiteral(this) concat rhs

/**
 * String concatenation. [String] is converted to [StringLiteral] [rhs] is converted to
 * [StringLiteral] .
 */
infix fun String.concat(rhs: String) = StringLiteral(this) concat StringLiteral(rhs)

/** String concatenation. [String] is converted to [StringLiteral] . */
infix fun String.concat(rhs: (() -> Expression<StringSort>)) = StringLiteral(this) concat rhs()

/**
 * String concatenation. [String] is converted to [StringLiteral] [rhs] is converted to
 * [StringLiteral] .
 */
infix fun String.concat(rhs: (() -> String)) = StringLiteral(this) concat StringLiteral(rhs())

/** String concatenation. */
infix fun (() -> String).concat(rhs: Expression<StringSort>) = StringLiteral(this()) concat rhs

/** String concatenation. [rhs] is converted to [StringLiteral] */
infix fun (() -> String).concat(rhs: String) = StringLiteral(this()) concat StringLiteral(rhs)

/** String concatenation. */
infix fun (() -> String).concat(rhs: (() -> Expression<StringSort>)) =
    StringLiteral(this()) concat rhs()

/** String concatenation. [rhs] is converted to [StringLiteral] */
infix fun (() -> String).concat(rhs: (() -> String)) =
    StringLiteral(this()) concat StringLiteral(rhs())

/** String concatenation. */
infix operator fun Expression<StringSort>.plus(rhs: Expression<StringSort>) = this concat rhs

/** String concatenation. [rhs] is converted to [StringLiteral] */
infix operator fun Expression<StringSort>.plus(rhs: String) = this plus StringLiteral(rhs)

/** String concatenation. */
infix operator fun Expression<StringSort>.plus(rhs: (() -> Expression<StringSort>)) =
    this plus rhs()

/** String concatenation. [rhs] is converted to [StringLiteral] */
infix operator fun Expression<StringSort>.plus(rhs: (() -> String)) = this plus StringLiteral(rhs())

/** String concatenation. */
infix operator fun (() -> Expression<StringSort>).plus(rhs: Expression<StringSort>) =
    this() plus rhs

/** String concatenation. [rhs] is converted to [StringLiteral] */
infix operator fun (() -> Expression<StringSort>).plus(rhs: String) = this() plus StringLiteral(rhs)

/** String concatenation. */
infix operator fun (() -> Expression<StringSort>).plus(rhs: (() -> Expression<StringSort>)) =
    this() plus rhs()

/** String concatenation. [rhs] is converted to [StringLiteral] */
infix operator fun (() -> Expression<StringSort>).plus(rhs: (() -> String)) =
    this() plus StringLiteral(rhs())

/** String concatenation. [String] is converted to [StringLiteral] */
infix operator fun String.plus(rhs: Expression<StringSort>) = StringLiteral(this) plus rhs

/**
 * String concatenation. [String] is converted to [StringLiteral] [rhs] is converted to
 * [StringLiteral]
 */
infix operator fun String.plus(rhs: String) = StringLiteral(this) plus StringLiteral(rhs)

/** String concatenation. [String] is converted to [StringLiteral] */
infix operator fun String.plus(rhs: (() -> Expression<StringSort>)) = StringLiteral(this) plus rhs()

/**
 * String concatenation. [String] is converted to [StringLiteral] [rhs] is converted to
 * [StringLiteral]
 */
infix operator fun String.plus(rhs: (() -> String)) = StringLiteral(this) plus StringLiteral(rhs())

/** String concatenation. */
infix operator fun (() -> String).plus(rhs: Expression<StringSort>) = StringLiteral(this()) plus rhs

/** String concatenation. [rhs] is converted to [StringLiteral] */
infix operator fun (() -> String).plus(rhs: String) = StringLiteral(this()) plus StringLiteral(rhs)

/** String concatenation. */
infix operator fun (() -> String).plus(rhs: (() -> Expression<StringSort>)) =
    StringLiteral(this()) plus rhs()

/** String concatenation. [rhs] is converted to [StringLiteral] */
infix operator fun (() -> String).plus(rhs: (() -> String)) =
    StringLiteral(this()) plus StringLiteral(rhs())

/** String length. */
fun Expression<StringSort>.length() = StrLength(this)

/** String length. */
fun (() -> Expression<StringSort>).length() = this().length()

/** Lexicographic ordering. */
infix fun Expression<StringSort>.lt(rhs: Expression<StringSort>) =
    if (this is StrLexOrder) {
      StrLexOrder(this.children + rhs)
    } else {
      StrLexOrder(this, rhs)
    }

/** Lexicographic ordering. [rhs] is converted to [StringLiteral] . */
infix fun Expression<StringSort>.lt(rhs: String) = this lt StringLiteral(rhs)

/** Lexicographic ordering. . */
infix fun Expression<StringSort>.lt(rhs: (() -> Expression<StringSort>)) = this lt rhs()

/** Lexicographic ordering. [rhs] is converted to [StringLiteral] . */
infix fun Expression<StringSort>.lt(rhs: (() -> String)) = this lt StringLiteral(rhs())

/** Lexicographic ordering. */
infix fun (() -> Expression<StringSort>).lt(rhs: Expression<StringSort>) = this() lt rhs

/** Lexicographic ordering. [rhs] is converted to [StringLiteral] */
infix fun (() -> Expression<StringSort>).lt(rhs: String) = this() lt StringLiteral(rhs)

/** Lexicographic ordering. */
infix fun (() -> Expression<StringSort>).lt(rhs: (() -> Expression<StringSort>)) = this() lt rhs()

/** Lexicographic ordering. [rhs] is converted to [StringLiteral] */
infix fun (() -> Expression<StringSort>).lt(rhs: (() -> String)) = this() lt StringLiteral(rhs())

/** Lexicographic ordering. [String] is converted to [StringLiteral] . */
infix fun String.lt(rhs: Expression<StringSort>) = StringLiteral(this) lt rhs

/**
 * Lexicographic ordering. [String] is converted to [StringLiteral] [rhs] is converted to
 * [StringLiteral] .
 */
infix fun String.lt(rhs: String) = StringLiteral(this) lt StringLiteral(rhs)

/** Lexicographic ordering. [String] is converted to [StringLiteral] . */
infix fun String.lt(rhs: (() -> Expression<StringSort>)) = StringLiteral(this) lt rhs()

/**
 * Lexicographic ordering. [String] is converted to [StringLiteral] [rhs] is converted to
 * [StringLiteral] .
 */
infix fun String.lt(rhs: (() -> String)) = StringLiteral(this) lt StringLiteral(rhs())

/** Lexicographic ordering. */
infix fun (() -> String).lt(rhs: Expression<StringSort>) = StringLiteral(this()) lt rhs

/** Lexicographic ordering. [rhs] is converted to [StringLiteral] */
infix fun (() -> String).lt(rhs: String) = StringLiteral(this()) lt StringLiteral(rhs)

/** Lexicographic ordering. */
infix fun (() -> String).lt(rhs: (() -> Expression<StringSort>)) = StringLiteral(this()) lt rhs()

/** Lexicographic ordering. [rhs] is converted to [StringLiteral] */
infix fun (() -> String).lt(rhs: (() -> String)) = StringLiteral(this()) lt StringLiteral(rhs())

/** String to Regex injection. */
fun Expression<StringSort>.toRe() = StrToRe(this)

/** String to Regex injection. [this] is converted to [StringLiteral] */
fun String.toRe() = StringLiteral(this).toRe()

/** String to Regex injection. */
fun (() -> Expression<StringSort>).toRe() = this().toRe()

/** String to Regex injection. [this] is converted to [StringLiteral] */
fun (() -> String).toRe() = StringLiteral(this()).toRe()

/** Regex membership. */
infix fun Expression<StringSort>.in_re(regex: Expression<RegLanSort>) = StrInRe(this, regex)

/** Regex membership. [regex] is converted to [Expression] of type [RegLanSort] */
infix fun Expression<StringSort>.in_re(regex: String) = this in_re StringLiteral(regex).toRe()

/** Regex membership. . */
infix fun Expression<StringSort>.in_re(regex: (() -> Expression<RegLanSort>)) = this in_re regex()

/** Regex membership. [regex] is converted to [Expression] of type [RegLanSort] */
infix fun Expression<StringSort>.in_re(regex: (() -> String)) =
    this in_re StringLiteral(regex()).toRe()

/** Regex membership. */
infix fun (() -> Expression<StringSort>).in_re(regex: Expression<RegLanSort>) = this() in_re regex

/** Regex membership. [regex] is converted to [Expression] of type [RegLanSort] */
infix fun (() -> Expression<StringSort>).in_re(regex: String) =
    this() in_re StringLiteral(regex).toRe()

/** Regex membership. */
infix fun (() -> Expression<StringSort>).in_re(regex: (() -> Expression<RegLanSort>)) =
    this() in_re regex()

/** Regex membership. [regex] is converted to [Expression] of type [RegLanSort] */
infix fun (() -> Expression<StringSort>).in_re(regex: (() -> String)) =
    this() in_re StringLiteral(regex()).toRe()

/** Regex membership. [String] is converted to [StringLiteral] . */
infix fun String.in_re(regex: Expression<RegLanSort>) = StringLiteral(this) in_re regex

/**
 * Regex membership. [String] is converted to [StringLiteral] [regex] is converted to [Expression]
 * of type [RegLanSort] .
 */
infix fun String.in_re(regex: String) = StringLiteral(this) in_re StringLiteral(regex).toRe()

/** Regex membership. [String] is converted to [StringLiteral] . */
infix fun String.in_re(regex: (() -> Expression<RegLanSort>)) = StringLiteral(this) in_re regex()

/**
 * Regex membership. [String] is converted to [StringLiteral] [regex] is converted to [Expression]
 * of type [RegLanSort] .
 */
infix fun String.in_re(regex: (() -> String)) =
    StringLiteral(this) in_re StringLiteral(regex()).toRe()

/** Regex membership. */
infix fun (() -> String).in_re(regex: Expression<RegLanSort>) = StringLiteral(this()) in_re regex

/** Regex membership. [regex] is converted to [Expression] of type [RegLanSort] */
infix fun (() -> String).in_re(regex: String) =
    StringLiteral(this()) in_re StringLiteral(regex).toRe()

/** Regex membership. */
infix fun (() -> String).in_re(regex: (() -> Expression<RegLanSort>)) =
    StringLiteral(this()) in_re regex()

/** Regex membership. [regex] is converted to [Expression] of type [RegLanSort] */
infix fun (() -> String).in_re(regex: (() -> String)) =
    StringLiteral(this()) in_re StringLiteral(regex()).toRe()

/** Regex concatenation. */
infix fun Expression<RegLanSort>.concat(rhs: Expression<RegLanSort>) =
    if (this is RegexConcat) {
      RegexConcat(this.children + rhs)
    } else {
      RegexConcat(this, rhs)
    }

/** Regex concatenation. [rhs] is converted to [Expression] of type [RegLanSort] . */
infix fun Expression<RegLanSort>.concat(rhs: String) = this concat StringLiteral(rhs).toRe()

/** Regex concatenation. . */
infix fun Expression<RegLanSort>.concat(rhs: (() -> Expression<RegLanSort>)) = this concat rhs()

/** Regex concatenation. [rhs] is converted to [Expression] of type [RegLanSort] . */
infix fun Expression<RegLanSort>.concat(rhs: (() -> String)) =
    this concat StringLiteral(rhs()).toRe()

/** Regex concatenation. */
infix fun (() -> Expression<RegLanSort>).concat(rhs: Expression<RegLanSort>) = this() concat rhs

/** Regex concatenation. [rhs] is converted to [Expression] of type [RegLanSort] */
infix fun (() -> Expression<RegLanSort>).concat(rhs: String) =
    this() concat StringLiteral(rhs).toRe()

/** Regex concatenation. */
infix fun (() -> Expression<RegLanSort>).concat(rhs: (() -> Expression<RegLanSort>)) =
    this() concat rhs()

/** Regex concatenation. [rhs] is converted to [Expression] of type [RegLanSort] */
infix fun (() -> Expression<RegLanSort>).concat(rhs: (() -> String)) =
    this() concat StringLiteral(rhs()).toRe()

/** Regex concatenation. */
infix operator fun Expression<RegLanSort>.times(rhs: Expression<RegLanSort>) = this concat rhs

/** Regex concatenation. [rhs] is converted to [Expression] of type [RegLanSort] */
infix operator fun Expression<RegLanSort>.times(rhs: String) = this times StringLiteral(rhs).toRe()

/** Regex concatenation. */
infix operator fun Expression<RegLanSort>.times(rhs: (() -> Expression<RegLanSort>)) =
    this times rhs()

/** Regex concatenation. [rhs] is converted to [Expression] of type [RegLanSort] */
infix operator fun Expression<RegLanSort>.times(rhs: (() -> String)) =
    this times StringLiteral(rhs()).toRe()

/** Regex concatenation. */
infix operator fun (() -> Expression<RegLanSort>).times(rhs: Expression<RegLanSort>) =
    this() times rhs

/** Regex concatenation. [rhs] is converted to [Expression] of type [RegLanSort] */
infix operator fun (() -> Expression<RegLanSort>).times(rhs: String) =
    this() times StringLiteral(rhs).toRe()

/** Regex concatenation. */
infix operator fun (() -> Expression<RegLanSort>).times(rhs: (() -> Expression<RegLanSort>)) =
    this() times rhs()

/** Regex concatenation. [rhs] is converted to [Expression] of type [RegLanSort] */
infix operator fun (() -> Expression<RegLanSort>).times(rhs: (() -> String)) =
    this() times StringLiteral(rhs()).toRe()

/** Regex concatenation. [String] is converted to [Expression] of type [RegLanSort] */
infix operator fun String.times(rhs: Expression<RegLanSort>) = StringLiteral(this).toRe() times rhs

/**
 * Regex concatenation. [String] is converted to [Expression] of type [RegLanSort] [rhs] is
 * converted to [Expression] of type [RegLanSort]
 */
infix operator fun String.times(rhs: String) =
    StringLiteral(this).toRe() times StringLiteral(rhs).toRe()

/** Regex concatenation. [String] is converted to [Expression] of type [RegLanSort] */
infix operator fun String.times(rhs: (() -> Expression<RegLanSort>)) =
    StringLiteral(this).toRe() times rhs()

/**
 * Regex concatenation. [String] is converted to [Expression] of type [RegLanSort] [rhs] is
 * converted to [Expression] of type [RegLanSort]
 */
infix operator fun String.times(rhs: (() -> String)) =
    StringLiteral(this).toRe() times StringLiteral(rhs()).toRe()

/** Regex concatenation. */
infix operator fun (() -> String).times(rhs: Expression<RegLanSort>) =
    StringLiteral(this()).toRe() times rhs

/** Regex concatenation. [rhs] is converted to [Expression] of type [RegLanSort] */
infix operator fun (() -> String).times(rhs: String) =
    StringLiteral(this()).toRe() times StringLiteral(rhs).toRe()

/** Regex concatenation. */
infix operator fun (() -> String).times(rhs: (() -> Expression<RegLanSort>)) =
    StringLiteral(this()).toRe() times rhs()

/** Regex concatenation. [rhs] is converted to [Expression] of type [RegLanSort] */
infix operator fun (() -> String).times(rhs: (() -> String)) =
    StringLiteral(this()).toRe() times StringLiteral(rhs()).toRe()

/** Regex union. */
infix fun Expression<RegLanSort>.union(rhs: Expression<RegLanSort>) =
    if (this is RegexUnion) {
      RegexUnion(this.children + rhs)
    } else {
      RegexUnion(this, rhs)
    }

/** Regex union. [rhs] is converted to [Expression] of type [RegLanSort] . */
infix fun Expression<RegLanSort>.union(rhs: String) = this union StringLiteral(rhs).toRe()

/** Regex union. . */
infix fun Expression<RegLanSort>.union(rhs: (() -> Expression<RegLanSort>)) = this union rhs()

/** Regex union. [rhs] is converted to [Expression] of type [RegLanSort] . */
infix fun Expression<RegLanSort>.union(rhs: (() -> String)) = this union StringLiteral(rhs()).toRe()

/** Regex union. */
infix fun (() -> Expression<RegLanSort>).union(rhs: Expression<RegLanSort>) = this() union rhs

/** Regex union. [rhs] is converted to [Expression] of type [RegLanSort] */
infix fun (() -> Expression<RegLanSort>).union(rhs: String) = this() union StringLiteral(rhs).toRe()

/** Regex union. */
infix fun (() -> Expression<RegLanSort>).union(rhs: (() -> Expression<RegLanSort>)) =
    this() union rhs()

/** Regex union. [rhs] is converted to [Expression] of type [RegLanSort] */
infix fun (() -> Expression<RegLanSort>).union(rhs: (() -> String)) =
    this() union StringLiteral(rhs()).toRe()

/** Regex union. [String] is converted to [Expression] of type [RegLanSort] . */
infix fun String.union(rhs: Expression<RegLanSort>) = StringLiteral(this).toRe() union rhs

/**
 * Regex union. [String] is converted to [Expression] of type [RegLanSort] [rhs] is converted to
 * [Expression] of type [RegLanSort] .
 */
infix fun String.union(rhs: String) = StringLiteral(this).toRe() union StringLiteral(rhs).toRe()

/** Regex union. [String] is converted to [Expression] of type [RegLanSort] . */
infix fun String.union(rhs: (() -> Expression<RegLanSort>)) = StringLiteral(this).toRe() union rhs()

/**
 * Regex union. [String] is converted to [Expression] of type [RegLanSort] [rhs] is converted to
 * [Expression] of type [RegLanSort] .
 */
infix fun String.union(rhs: (() -> String)) =
    StringLiteral(this).toRe() union StringLiteral(rhs()).toRe()

/** Regex union. */
infix fun (() -> String).union(rhs: Expression<RegLanSort>) = StringLiteral(this()).toRe() union rhs

/** Regex union. [rhs] is converted to [Expression] of type [RegLanSort] */
infix fun (() -> String).union(rhs: String) =
    StringLiteral(this()).toRe() union StringLiteral(rhs).toRe()

/** Regex union. */
infix fun (() -> String).union(rhs: (() -> Expression<RegLanSort>)) =
    StringLiteral(this()).toRe() union rhs()

/** Regex union. [rhs] is converted to [Expression] of type [RegLanSort] */
infix fun (() -> String).union(rhs: (() -> String)) =
    StringLiteral(this()).toRe() union StringLiteral(rhs()).toRe()

/** Regex intersection. */
infix fun Expression<RegLanSort>.intersec(rhs: Expression<RegLanSort>) =
    if (this is RegexIntersec) {
      RegexIntersec(this.children + rhs)
    } else {
      RegexIntersec(this, rhs)
    }

/** Regex intersection. [rhs] is converted to [Expression] of type [RegLanSort] . */
infix fun Expression<RegLanSort>.intersec(rhs: String) = this intersec StringLiteral(rhs).toRe()

/** Regex intersection. . */
infix fun Expression<RegLanSort>.intersec(rhs: (() -> Expression<RegLanSort>)) = this intersec rhs()

/** Regex intersection. [rhs] is converted to [Expression] of type [RegLanSort] . */
infix fun Expression<RegLanSort>.intersec(rhs: (() -> String)) =
    this intersec StringLiteral(rhs()).toRe()

/** Regex intersection. */
infix fun (() -> Expression<RegLanSort>).intersec(rhs: Expression<RegLanSort>) = this() intersec rhs

/** Regex intersection. [rhs] is converted to [Expression] of type [RegLanSort] */
infix fun (() -> Expression<RegLanSort>).intersec(rhs: String) =
    this() intersec StringLiteral(rhs).toRe()

/** Regex intersection. */
infix fun (() -> Expression<RegLanSort>).intersec(rhs: (() -> Expression<RegLanSort>)) =
    this() intersec rhs()

/** Regex intersection. [rhs] is converted to [Expression] of type [RegLanSort] */
infix fun (() -> Expression<RegLanSort>).intersec(rhs: (() -> String)) =
    this() intersec StringLiteral(rhs()).toRe()

/** Regex intersection. [String] is converted to [Expression] of type [RegLanSort] . */
infix fun String.intersec(rhs: Expression<RegLanSort>) = StringLiteral(this).toRe() intersec rhs

/**
 * Regex intersection. [String] is converted to [Expression] of type [RegLanSort] [rhs] is converted
 * to [Expression] of type [RegLanSort] .
 */
infix fun String.intersec(rhs: String) =
    StringLiteral(this).toRe() intersec StringLiteral(rhs).toRe()

/** Regex intersection. [String] is converted to [Expression] of type [RegLanSort] . */
infix fun String.intersec(rhs: (() -> Expression<RegLanSort>)) =
    StringLiteral(this).toRe() intersec rhs()

/**
 * Regex intersection. [String] is converted to [Expression] of type [RegLanSort] [rhs] is converted
 * to [Expression] of type [RegLanSort] .
 */
infix fun String.intersec(rhs: (() -> String)) =
    StringLiteral(this).toRe() intersec StringLiteral(rhs()).toRe()

/** Regex intersection. */
infix fun (() -> String).intersec(rhs: Expression<RegLanSort>) =
    StringLiteral(this()).toRe() intersec rhs

/** Regex intersection. [rhs] is converted to [Expression] of type [RegLanSort] */
infix fun (() -> String).intersec(rhs: String) =
    StringLiteral(this()).toRe() intersec StringLiteral(rhs).toRe()

/** Regex intersection. */
infix fun (() -> String).intersec(rhs: (() -> Expression<RegLanSort>)) =
    StringLiteral(this()).toRe() intersec rhs()

/** Regex intersection. [rhs] is converted to [Expression] of type [RegLanSort] */
infix fun (() -> String).intersec(rhs: (() -> String)) =
    StringLiteral(this()).toRe() intersec StringLiteral(rhs()).toRe()

/** Kleene Closure. */
fun Expression<RegLanSort>.star() = RegexStar(this)

/** Kleene Closure. [this] is converted to [Expression] of type [RegLanSort] */
fun String.star() = StringLiteral(this).toRe().star()

/** Kleene Closure. */
fun (() -> Expression<RegLanSort>).star() = this().star()

/** Kleene Closure. [this] is converted to [Expression] of type [RegLanSort] */
fun (() -> String).star() = StringLiteral(this()).toRe().star()

/** Reflexive closure of lexicographic ordering. */
infix fun Expression<StringSort>.leq(rhs: Expression<StringSort>) =
    if (this is StrRefLexOrder) {
      StrRefLexOrder(this.children + rhs)
    } else {
      StrRefLexOrder(this, rhs)
    }

/** Reflexive closure of lexicographic ordering. [rhs] is converted to [StringLiteral] . */
infix fun Expression<StringSort>.leq(rhs: String) = this leq StringLiteral(rhs)

/** Reflexive closure of lexicographic ordering. . */
infix fun Expression<StringSort>.leq(rhs: (() -> Expression<StringSort>)) = this leq rhs()

/** Reflexive closure of lexicographic ordering. [rhs] is converted to [StringLiteral] . */
infix fun Expression<StringSort>.leq(rhs: (() -> String)) = this leq StringLiteral(rhs())

/** Reflexive closure of lexicographic ordering. */
infix fun (() -> Expression<StringSort>).leq(rhs: Expression<StringSort>) = this() leq rhs

/** Reflexive closure of lexicographic ordering. [rhs] is converted to [StringLiteral] */
infix fun (() -> Expression<StringSort>).leq(rhs: String) = this() leq StringLiteral(rhs)

/** Reflexive closure of lexicographic ordering. */
infix fun (() -> Expression<StringSort>).leq(rhs: (() -> Expression<StringSort>)) = this() leq rhs()

/** Reflexive closure of lexicographic ordering. [rhs] is converted to [StringLiteral] */
infix fun (() -> Expression<StringSort>).leq(rhs: (() -> String)) = this() leq StringLiteral(rhs())

/** Reflexive closure of lexicographic ordering. [String] is converted to [StringLiteral] . */
infix fun String.leq(rhs: Expression<StringSort>) = StringLiteral(this) leq rhs

/**
 * Reflexive closure of lexicographic ordering. [String] is converted to [StringLiteral] [rhs] is
 * converted to [StringLiteral] .
 */
infix fun String.leq(rhs: String) = StringLiteral(this) leq StringLiteral(rhs)

/** Reflexive closure of lexicographic ordering. [String] is converted to [StringLiteral] . */
infix fun String.leq(rhs: (() -> Expression<StringSort>)) = StringLiteral(this) leq rhs()

/**
 * Reflexive closure of lexicographic ordering. [String] is converted to [StringLiteral] [rhs] is
 * converted to [StringLiteral] .
 */
infix fun String.leq(rhs: (() -> String)) = StringLiteral(this) leq StringLiteral(rhs())

/** Reflexive closure of lexicographic ordering. */
infix fun (() -> String).leq(rhs: Expression<StringSort>) = StringLiteral(this()) leq rhs

/** Reflexive closure of lexicographic ordering. [rhs] is converted to [StringLiteral] */
infix fun (() -> String).leq(rhs: String) = StringLiteral(this()) leq StringLiteral(rhs)

/** Reflexive closure of lexicographic ordering. */
infix fun (() -> String).leq(rhs: (() -> Expression<StringSort>)) = StringLiteral(this()) leq rhs()

/** Reflexive closure of lexicographic ordering. [rhs] is converted to [StringLiteral] */
infix fun (() -> String).leq(rhs: (() -> String)) = StringLiteral(this()) leq StringLiteral(rhs())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 */
infix fun Expression<StringSort>.at(position: Expression<IntSort>) = StrAt(this, position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral] .
 */
infix fun Expression<StringSort>.at(position: Byte) = this at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral] .
 */
infix fun Expression<StringSort>.at(position: Short) = this at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral] .
 */
infix fun Expression<StringSort>.at(position: Int) = this at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral] .
 */
infix fun Expression<StringSort>.at(position: Long) = this at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral] .
 */
infix fun Expression<StringSort>.at(position: BigInteger) = this at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. .
 */
infix fun Expression<StringSort>.at(position: (() -> Expression<IntSort>)) = this at position()

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral] .
 */
infix fun Expression<StringSort>.at(position: (() -> Byte)) = this at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral] .
 */
infix fun Expression<StringSort>.at(position: (() -> Short)) = this at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral] .
 */
infix fun Expression<StringSort>.at(position: (() -> Int)) = this at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral] .
 */
infix fun Expression<StringSort>.at(position: (() -> Long)) = this at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral] .
 */
infix fun Expression<StringSort>.at(position: (() -> BigInteger)) = this at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 */
infix fun (() -> Expression<StringSort>).at(position: Expression<IntSort>) = this() at position

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral]
 */
infix fun (() -> Expression<StringSort>).at(position: Byte) = this() at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral]
 */
infix fun (() -> Expression<StringSort>).at(position: Short) = this() at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral]
 */
infix fun (() -> Expression<StringSort>).at(position: Int) = this() at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral]
 */
infix fun (() -> Expression<StringSort>).at(position: Long) = this() at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral]
 */
infix fun (() -> Expression<StringSort>).at(position: BigInteger) = this() at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 */
infix fun (() -> Expression<StringSort>).at(position: (() -> Expression<IntSort>)) =
    this() at position()

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral]
 */
infix fun (() -> Expression<StringSort>).at(position: (() -> Byte)) =
    this() at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral]
 */
infix fun (() -> Expression<StringSort>).at(position: (() -> Short)) =
    this() at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral]
 */
infix fun (() -> Expression<StringSort>).at(position: (() -> Int)) =
    this() at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral]
 */
infix fun (() -> Expression<StringSort>).at(position: (() -> Long)) =
    this() at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral]
 */
infix fun (() -> Expression<StringSort>).at(position: (() -> BigInteger)) =
    this() at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [String] is converted to [StringLiteral] .
 */
infix fun String.at(position: Expression<IntSort>) = StringLiteral(this) at position

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [String] is converted to [StringLiteral] [position] is
 * converted to [IntLiteral] .
 */
infix fun String.at(position: Byte) = StringLiteral(this) at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [String] is converted to [StringLiteral] [position] is
 * converted to [IntLiteral] .
 */
infix fun String.at(position: Short) = StringLiteral(this) at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [String] is converted to [StringLiteral] [position] is
 * converted to [IntLiteral] .
 */
infix fun String.at(position: Int) = StringLiteral(this) at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [String] is converted to [StringLiteral] [position] is
 * converted to [IntLiteral] .
 */
infix fun String.at(position: Long) = StringLiteral(this) at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [String] is converted to [StringLiteral] [position] is
 * converted to [IntLiteral] .
 */
infix fun String.at(position: BigInteger) = StringLiteral(this) at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [String] is converted to [StringLiteral] .
 */
infix fun String.at(position: (() -> Expression<IntSort>)) = StringLiteral(this) at position()

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [String] is converted to [StringLiteral] [position] is
 * converted to [IntLiteral] .
 */
infix fun String.at(position: (() -> Byte)) = StringLiteral(this) at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [String] is converted to [StringLiteral] [position] is
 * converted to [IntLiteral] .
 */
infix fun String.at(position: (() -> Short)) = StringLiteral(this) at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [String] is converted to [StringLiteral] [position] is
 * converted to [IntLiteral] .
 */
infix fun String.at(position: (() -> Int)) = StringLiteral(this) at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [String] is converted to [StringLiteral] [position] is
 * converted to [IntLiteral] .
 */
infix fun String.at(position: (() -> Long)) = StringLiteral(this) at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [String] is converted to [StringLiteral] [position] is
 * converted to [IntLiteral] .
 */
infix fun String.at(position: (() -> BigInteger)) = StringLiteral(this) at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 */
infix fun (() -> String).at(position: Expression<IntSort>) = StringLiteral(this()) at position

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral]
 */
infix fun (() -> String).at(position: Byte) = StringLiteral(this()) at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral]
 */
infix fun (() -> String).at(position: Short) = StringLiteral(this()) at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral]
 */
infix fun (() -> String).at(position: Int) = StringLiteral(this()) at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral]
 */
infix fun (() -> String).at(position: Long) = StringLiteral(this()) at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral]
 */
infix fun (() -> String).at(position: BigInteger) = StringLiteral(this()) at IntLiteral(position)

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0.
 */
infix fun (() -> String).at(position: (() -> Expression<IntSort>)) =
    StringLiteral(this()) at position()

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral]
 */
infix fun (() -> String).at(position: (() -> Byte)) =
    StringLiteral(this()) at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral]
 */
infix fun (() -> String).at(position: (() -> Short)) =
    StringLiteral(this()) at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral]
 */
infix fun (() -> String).at(position: (() -> Int)) = StringLiteral(this()) at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral]
 */
infix fun (() -> String).at(position: (() -> Long)) =
    StringLiteral(this()) at IntLiteral(position())

/**
 * Singleton string containing character at [position] or empty string when [position] is out of
 * range. The leftmost position is 0. [position] is converted to [IntLiteral]
 */
infix fun (() -> String).at(position: (() -> BigInteger)) =
    StringLiteral(this()) at IntLiteral(position())

/** Longest substring of [this] of at most [length] characters starting at [start]. */
fun Expression<StringSort>.substr(start: Expression<IntSort>, length: Expression<IntSort>) =
    StrSubstring(this, start, length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Expression<IntSort>, length: Byte) =
    this.substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Expression<IntSort>, length: Short) =
    this.substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Expression<IntSort>, length: Int) =
    this.substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Expression<IntSort>, length: Long) =
    this.substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Expression<IntSort>, length: BigInteger) =
    this.substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun Expression<StringSort>.substr(start: Byte, length: Expression<IntSort>) =
    this.substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Byte, length: Byte) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Byte, length: Short) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Byte, length: Int) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Byte, length: Long) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Byte, length: BigInteger) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun Expression<StringSort>.substr(start: Short, length: Expression<IntSort>) =
    this.substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Short, length: Byte) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Short, length: Short) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Short, length: Int) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Short, length: Long) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Short, length: BigInteger) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun Expression<StringSort>.substr(start: Int, length: Expression<IntSort>) =
    this.substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Int, length: Byte) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Int, length: Short) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Int, length: Int) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Int, length: Long) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Int, length: BigInteger) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun Expression<StringSort>.substr(start: Long, length: Expression<IntSort>) =
    this.substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Long, length: Byte) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Long, length: Short) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Long, length: Int) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Long, length: Long) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Long, length: BigInteger) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun Expression<StringSort>.substr(start: BigInteger, length: Expression<IntSort>) =
    this.substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: BigInteger, length: Byte) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: BigInteger, length: Short) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: BigInteger, length: Int) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: BigInteger, length: Long) =
    this.substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: BigInteger, length: BigInteger) =
    this.substr(IntLiteral(start), IntLiteral(length))

/** Longest substring of [this] of at most [length] characters starting at [start]. . */
fun Expression<StringSort>.substr(start: (() -> Expression<IntSort>), length: Expression<IntSort>) =
    this.substr(start(), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Expression<IntSort>), length: Byte) =
    this.substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Expression<IntSort>), length: Short) =
    this.substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Expression<IntSort>), length: Int) =
    this.substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Expression<IntSort>), length: Long) =
    this.substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Expression<IntSort>), length: BigInteger) =
    this.substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun Expression<StringSort>.substr(start: (() -> Byte), length: Expression<IntSort>) =
    this.substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Byte), length: Byte) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Byte), length: Short) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Byte), length: Int) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Byte), length: Long) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Byte), length: BigInteger) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun Expression<StringSort>.substr(start: (() -> Short), length: Expression<IntSort>) =
    this.substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Short), length: Byte) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Short), length: Short) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Short), length: Int) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Short), length: Long) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Short), length: BigInteger) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun Expression<StringSort>.substr(start: (() -> Int), length: Expression<IntSort>) =
    this.substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Int), length: Byte) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Int), length: Short) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Int), length: Int) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Int), length: Long) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Int), length: BigInteger) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun Expression<StringSort>.substr(start: (() -> Long), length: Expression<IntSort>) =
    this.substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Long), length: Byte) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Long), length: Short) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Long), length: Int) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Long), length: Long) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Long), length: BigInteger) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun Expression<StringSort>.substr(start: (() -> BigInteger), length: Expression<IntSort>) =
    this.substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> BigInteger), length: Byte) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> BigInteger), length: Short) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> BigInteger), length: Int) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> BigInteger), length: Long) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> BigInteger), length: BigInteger) =
    this.substr(IntLiteral(start()), IntLiteral(length))

/** Longest substring of [this] of at most [length] characters starting at [start]. . */
fun Expression<StringSort>.substr(start: Expression<IntSort>, length: (() -> Expression<IntSort>)) =
    this.substr(start, length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Expression<IntSort>, length: (() -> Byte)) =
    this.substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Expression<IntSort>, length: (() -> Short)) =
    this.substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Expression<IntSort>, length: (() -> Int)) =
    this.substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Expression<IntSort>, length: (() -> Long)) =
    this.substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Expression<IntSort>, length: (() -> BigInteger)) =
    this.substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun Expression<StringSort>.substr(start: Byte, length: (() -> Expression<IntSort>)) =
    this.substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Byte, length: (() -> Byte)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Byte, length: (() -> Short)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Byte, length: (() -> Int)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Byte, length: (() -> Long)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Byte, length: (() -> BigInteger)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun Expression<StringSort>.substr(start: Short, length: (() -> Expression<IntSort>)) =
    this.substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Short, length: (() -> Byte)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Short, length: (() -> Short)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Short, length: (() -> Int)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Short, length: (() -> Long)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Short, length: (() -> BigInteger)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun Expression<StringSort>.substr(start: Int, length: (() -> Expression<IntSort>)) =
    this.substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Int, length: (() -> Byte)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Int, length: (() -> Short)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Int, length: (() -> Int)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Int, length: (() -> Long)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Int, length: (() -> BigInteger)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun Expression<StringSort>.substr(start: Long, length: (() -> Expression<IntSort>)) =
    this.substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Long, length: (() -> Byte)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Long, length: (() -> Short)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Long, length: (() -> Int)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Long, length: (() -> Long)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: Long, length: (() -> BigInteger)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun Expression<StringSort>.substr(start: BigInteger, length: (() -> Expression<IntSort>)) =
    this.substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: BigInteger, length: (() -> Byte)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: BigInteger, length: (() -> Short)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: BigInteger, length: (() -> Int)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: BigInteger, length: (() -> Long)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: BigInteger, length: (() -> BigInteger)) =
    this.substr(IntLiteral(start), IntLiteral(length()))

/** Longest substring of [this] of at most [length] characters starting at [start]. . */
fun Expression<StringSort>.substr(
    start: (() -> Expression<IntSort>),
    length: (() -> Expression<IntSort>)
) = this.substr(start(), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Expression<IntSort>), length: (() -> Byte)) =
    this.substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Expression<IntSort>), length: (() -> Short)) =
    this.substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Expression<IntSort>), length: (() -> Int)) =
    this.substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Expression<IntSort>), length: (() -> Long)) =
    this.substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Expression<IntSort>), length: (() -> BigInteger)) =
    this.substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun Expression<StringSort>.substr(start: (() -> Byte), length: (() -> Expression<IntSort>)) =
    this.substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Byte), length: (() -> Byte)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Byte), length: (() -> Short)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Byte), length: (() -> Int)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Byte), length: (() -> Long)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Byte), length: (() -> BigInteger)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun Expression<StringSort>.substr(start: (() -> Short), length: (() -> Expression<IntSort>)) =
    this.substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Short), length: (() -> Byte)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Short), length: (() -> Short)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Short), length: (() -> Int)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Short), length: (() -> Long)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Short), length: (() -> BigInteger)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun Expression<StringSort>.substr(start: (() -> Int), length: (() -> Expression<IntSort>)) =
    this.substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Int), length: (() -> Byte)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Int), length: (() -> Short)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Int), length: (() -> Int)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Int), length: (() -> Long)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Int), length: (() -> BigInteger)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun Expression<StringSort>.substr(start: (() -> Long), length: (() -> Expression<IntSort>)) =
    this.substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Long), length: (() -> Byte)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Long), length: (() -> Short)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Long), length: (() -> Int)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Long), length: (() -> Long)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> Long), length: (() -> BigInteger)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun Expression<StringSort>.substr(start: (() -> BigInteger), length: (() -> Expression<IntSort>)) =
    this.substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> BigInteger), length: (() -> Byte)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> BigInteger), length: (() -> Short)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> BigInteger), length: (() -> Int)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> BigInteger), length: (() -> Long)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun Expression<StringSort>.substr(start: (() -> BigInteger), length: (() -> BigInteger)) =
    this.substr(IntLiteral(start()), IntLiteral(length()))

/** Longest substring of [this] of at most [length] characters starting at [start]. . */
fun (() -> Expression<StringSort>).substr(start: Expression<IntSort>, length: Expression<IntSort>) =
    this().substr(start, length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Expression<IntSort>, length: Byte) =
    this().substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Expression<IntSort>, length: Short) =
    this().substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Expression<IntSort>, length: Int) =
    this().substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Expression<IntSort>, length: Long) =
    this().substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Expression<IntSort>, length: BigInteger) =
    this().substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun (() -> Expression<StringSort>).substr(start: Byte, length: Expression<IntSort>) =
    this().substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Byte, length: Byte) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Byte, length: Short) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Byte, length: Int) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Byte, length: Long) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Byte, length: BigInteger) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun (() -> Expression<StringSort>).substr(start: Short, length: Expression<IntSort>) =
    this().substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Short, length: Byte) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Short, length: Short) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Short, length: Int) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Short, length: Long) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Short, length: BigInteger) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun (() -> Expression<StringSort>).substr(start: Int, length: Expression<IntSort>) =
    this().substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Int, length: Byte) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Int, length: Short) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Int, length: Int) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Int, length: Long) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Int, length: BigInteger) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun (() -> Expression<StringSort>).substr(start: Long, length: Expression<IntSort>) =
    this().substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Long, length: Byte) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Long, length: Short) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Long, length: Int) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Long, length: Long) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Long, length: BigInteger) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun (() -> Expression<StringSort>).substr(start: BigInteger, length: Expression<IntSort>) =
    this().substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: BigInteger, length: Byte) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: BigInteger, length: Short) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: BigInteger, length: Int) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: BigInteger, length: Long) =
    this().substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: BigInteger, length: BigInteger) =
    this().substr(IntLiteral(start), IntLiteral(length))

/** Longest substring of [this] of at most [length] characters starting at [start]. . */
fun (() -> Expression<StringSort>).substr(
    start: (() -> Expression<IntSort>),
    length: Expression<IntSort>
) = this().substr(start(), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Expression<IntSort>), length: Byte) =
    this().substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Expression<IntSort>), length: Short) =
    this().substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Expression<IntSort>), length: Int) =
    this().substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Expression<IntSort>), length: Long) =
    this().substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Expression<IntSort>), length: BigInteger) =
    this().substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Byte), length: Expression<IntSort>) =
    this().substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Byte), length: Byte) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Byte), length: Short) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Byte), length: Int) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Byte), length: Long) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Byte), length: BigInteger) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Short), length: Expression<IntSort>) =
    this().substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Short), length: Byte) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Short), length: Short) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Short), length: Int) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Short), length: Long) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Short), length: BigInteger) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Int), length: Expression<IntSort>) =
    this().substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Int), length: Byte) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Int), length: Short) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Int), length: Int) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Int), length: Long) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Int), length: BigInteger) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Long), length: Expression<IntSort>) =
    this().substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Long), length: Byte) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Long), length: Short) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Long), length: Int) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Long), length: Long) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Long), length: BigInteger) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun (() -> Expression<StringSort>).substr(start: (() -> BigInteger), length: Expression<IntSort>) =
    this().substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> BigInteger), length: Byte) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> BigInteger), length: Short) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> BigInteger), length: Int) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> BigInteger), length: Long) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> BigInteger), length: BigInteger) =
    this().substr(IntLiteral(start()), IntLiteral(length))

/** Longest substring of [this] of at most [length] characters starting at [start]. . */
fun (() -> Expression<StringSort>).substr(
    start: Expression<IntSort>,
    length: (() -> Expression<IntSort>)
) = this().substr(start, length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Expression<IntSort>, length: (() -> Byte)) =
    this().substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Expression<IntSort>, length: (() -> Short)) =
    this().substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Expression<IntSort>, length: (() -> Int)) =
    this().substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Expression<IntSort>, length: (() -> Long)) =
    this().substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Expression<IntSort>, length: (() -> BigInteger)) =
    this().substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun (() -> Expression<StringSort>).substr(start: Byte, length: (() -> Expression<IntSort>)) =
    this().substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Byte, length: (() -> Byte)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Byte, length: (() -> Short)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Byte, length: (() -> Int)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Byte, length: (() -> Long)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Byte, length: (() -> BigInteger)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun (() -> Expression<StringSort>).substr(start: Short, length: (() -> Expression<IntSort>)) =
    this().substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Short, length: (() -> Byte)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Short, length: (() -> Short)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Short, length: (() -> Int)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Short, length: (() -> Long)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Short, length: (() -> BigInteger)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun (() -> Expression<StringSort>).substr(start: Int, length: (() -> Expression<IntSort>)) =
    this().substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Int, length: (() -> Byte)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Int, length: (() -> Short)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Int, length: (() -> Int)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Int, length: (() -> Long)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Int, length: (() -> BigInteger)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun (() -> Expression<StringSort>).substr(start: Long, length: (() -> Expression<IntSort>)) =
    this().substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Long, length: (() -> Byte)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Long, length: (() -> Short)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Long, length: (() -> Int)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Long, length: (() -> Long)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: Long, length: (() -> BigInteger)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun (() -> Expression<StringSort>).substr(start: BigInteger, length: (() -> Expression<IntSort>)) =
    this().substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: BigInteger, length: (() -> Byte)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: BigInteger, length: (() -> Short)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: BigInteger, length: (() -> Int)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: BigInteger, length: (() -> Long)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: BigInteger, length: (() -> BigInteger)) =
    this().substr(IntLiteral(start), IntLiteral(length()))

/** Longest substring of [this] of at most [length] characters starting at [start]. . */
fun (() -> Expression<StringSort>).substr(
    start: (() -> Expression<IntSort>),
    length: (() -> Expression<IntSort>)
) = this().substr(start(), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(
    start: (() -> Expression<IntSort>),
    length: (() -> Byte)
) = this().substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(
    start: (() -> Expression<IntSort>),
    length: (() -> Short)
) = this().substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Expression<IntSort>), length: (() -> Int)) =
    this().substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(
    start: (() -> Expression<IntSort>),
    length: (() -> Long)
) = this().substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. .[length] is
 * converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(
    start: (() -> Expression<IntSort>),
    length: (() -> BigInteger)
) = this().substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun (() -> Expression<StringSort>).substr(
    start: (() -> Byte),
    length: (() -> Expression<IntSort>)
) = this().substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Byte), length: (() -> Byte)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Byte), length: (() -> Short)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Byte), length: (() -> Int)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Byte), length: (() -> Long)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Byte), length: (() -> BigInteger)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun (() -> Expression<StringSort>).substr(
    start: (() -> Short),
    length: (() -> Expression<IntSort>)
) = this().substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Short), length: (() -> Byte)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Short), length: (() -> Short)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Short), length: (() -> Int)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Short), length: (() -> Long)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Short), length: (() -> BigInteger)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Int), length: (() -> Expression<IntSort>)) =
    this().substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Int), length: (() -> Byte)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Int), length: (() -> Short)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Int), length: (() -> Int)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Int), length: (() -> Long)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Int), length: (() -> BigInteger)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun (() -> Expression<StringSort>).substr(
    start: (() -> Long),
    length: (() -> Expression<IntSort>)
) = this().substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Long), length: (() -> Byte)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Long), length: (() -> Short)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Long), length: (() -> Int)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Long), length: (() -> Long)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> Long), length: (() -> BigInteger)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .
 */
fun (() -> Expression<StringSort>).substr(
    start: (() -> BigInteger),
    length: (() -> Expression<IntSort>)
) = this().substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> BigInteger), length: (() -> Byte)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> BigInteger), length: (() -> Short)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> BigInteger), length: (() -> Int)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> BigInteger), length: (() -> Long)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [start] is
 * converted to [IntLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).substr(start: (() -> BigInteger), length: (() -> BigInteger)) =
    this().substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .
 */
fun String.substr(start: Expression<IntSort>, length: Expression<IntSort>) =
    StringLiteral(this).substr(start, length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun String.substr(start: Expression<IntSort>, length: Byte) =
    StringLiteral(this).substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun String.substr(start: Expression<IntSort>, length: Short) =
    StringLiteral(this).substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun String.substr(start: Expression<IntSort>, length: Int) =
    StringLiteral(this).substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun String.substr(start: Expression<IntSort>, length: Long) =
    StringLiteral(this).substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun String.substr(start: Expression<IntSort>, length: BigInteger) =
    StringLiteral(this).substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun String.substr(start: Byte, length: Expression<IntSort>) =
    StringLiteral(this).substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Byte, length: Byte) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Byte, length: Short) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Byte, length: Int) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Byte, length: Long) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Byte, length: BigInteger) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun String.substr(start: Short, length: Expression<IntSort>) =
    StringLiteral(this).substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Short, length: Byte) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Short, length: Short) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Short, length: Int) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Short, length: Long) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Short, length: BigInteger) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun String.substr(start: Int, length: Expression<IntSort>) =
    StringLiteral(this).substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Int, length: Byte) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Int, length: Short) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Int, length: Int) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Int, length: Long) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Int, length: BigInteger) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun String.substr(start: Long, length: Expression<IntSort>) =
    StringLiteral(this).substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Long, length: Byte) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Long, length: Short) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Long, length: Int) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Long, length: Long) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Long, length: BigInteger) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun String.substr(start: BigInteger, length: Expression<IntSort>) =
    StringLiteral(this).substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: BigInteger, length: Byte) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: BigInteger, length: Short) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: BigInteger, length: Int) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: BigInteger, length: Long) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: BigInteger, length: BigInteger) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .
 */
fun String.substr(start: (() -> Expression<IntSort>), length: Expression<IntSort>) =
    StringLiteral(this).substr(start(), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun String.substr(start: (() -> Expression<IntSort>), length: Byte) =
    StringLiteral(this).substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun String.substr(start: (() -> Expression<IntSort>), length: Short) =
    StringLiteral(this).substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun String.substr(start: (() -> Expression<IntSort>), length: Int) =
    StringLiteral(this).substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun String.substr(start: (() -> Expression<IntSort>), length: Long) =
    StringLiteral(this).substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun String.substr(start: (() -> Expression<IntSort>), length: BigInteger) =
    StringLiteral(this).substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun String.substr(start: (() -> Byte), length: Expression<IntSort>) =
    StringLiteral(this).substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Byte), length: Byte) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Byte), length: Short) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Byte), length: Int) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Byte), length: Long) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Byte), length: BigInteger) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun String.substr(start: (() -> Short), length: Expression<IntSort>) =
    StringLiteral(this).substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Short), length: Byte) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Short), length: Short) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Short), length: Int) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Short), length: Long) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Short), length: BigInteger) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun String.substr(start: (() -> Int), length: Expression<IntSort>) =
    StringLiteral(this).substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Int), length: Byte) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Int), length: Short) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Int), length: Int) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Int), length: Long) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Int), length: BigInteger) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun String.substr(start: (() -> Long), length: Expression<IntSort>) =
    StringLiteral(this).substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Long), length: Byte) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Long), length: Short) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Long), length: Int) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Long), length: Long) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Long), length: BigInteger) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun String.substr(start: (() -> BigInteger), length: Expression<IntSort>) =
    StringLiteral(this).substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> BigInteger), length: Byte) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> BigInteger), length: Short) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> BigInteger), length: Int) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> BigInteger), length: Long) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> BigInteger), length: BigInteger) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .
 */
fun String.substr(start: Expression<IntSort>, length: (() -> Expression<IntSort>)) =
    StringLiteral(this).substr(start, length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun String.substr(start: Expression<IntSort>, length: (() -> Byte)) =
    StringLiteral(this).substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun String.substr(start: Expression<IntSort>, length: (() -> Short)) =
    StringLiteral(this).substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun String.substr(start: Expression<IntSort>, length: (() -> Int)) =
    StringLiteral(this).substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun String.substr(start: Expression<IntSort>, length: (() -> Long)) =
    StringLiteral(this).substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun String.substr(start: Expression<IntSort>, length: (() -> BigInteger)) =
    StringLiteral(this).substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun String.substr(start: Byte, length: (() -> Expression<IntSort>)) =
    StringLiteral(this).substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Byte, length: (() -> Byte)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Byte, length: (() -> Short)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Byte, length: (() -> Int)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Byte, length: (() -> Long)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Byte, length: (() -> BigInteger)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun String.substr(start: Short, length: (() -> Expression<IntSort>)) =
    StringLiteral(this).substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Short, length: (() -> Byte)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Short, length: (() -> Short)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Short, length: (() -> Int)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Short, length: (() -> Long)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Short, length: (() -> BigInteger)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun String.substr(start: Int, length: (() -> Expression<IntSort>)) =
    StringLiteral(this).substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Int, length: (() -> Byte)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Int, length: (() -> Short)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Int, length: (() -> Int)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Int, length: (() -> Long)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Int, length: (() -> BigInteger)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun String.substr(start: Long, length: (() -> Expression<IntSort>)) =
    StringLiteral(this).substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Long, length: (() -> Byte)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Long, length: (() -> Short)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Long, length: (() -> Int)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Long, length: (() -> Long)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: Long, length: (() -> BigInteger)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun String.substr(start: BigInteger, length: (() -> Expression<IntSort>)) =
    StringLiteral(this).substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: BigInteger, length: (() -> Byte)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: BigInteger, length: (() -> Short)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: BigInteger, length: (() -> Int)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: BigInteger, length: (() -> Long)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: BigInteger, length: (() -> BigInteger)) =
    StringLiteral(this).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .
 */
fun String.substr(start: (() -> Expression<IntSort>), length: (() -> Expression<IntSort>)) =
    StringLiteral(this).substr(start(), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun String.substr(start: (() -> Expression<IntSort>), length: (() -> Byte)) =
    StringLiteral(this).substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun String.substr(start: (() -> Expression<IntSort>), length: (() -> Short)) =
    StringLiteral(this).substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun String.substr(start: (() -> Expression<IntSort>), length: (() -> Int)) =
    StringLiteral(this).substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun String.substr(start: (() -> Expression<IntSort>), length: (() -> Long)) =
    StringLiteral(this).substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun String.substr(start: (() -> Expression<IntSort>), length: (() -> BigInteger)) =
    StringLiteral(this).substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun String.substr(start: (() -> Byte), length: (() -> Expression<IntSort>)) =
    StringLiteral(this).substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Byte), length: (() -> Byte)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Byte), length: (() -> Short)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Byte), length: (() -> Int)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Byte), length: (() -> Long)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Byte), length: (() -> BigInteger)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun String.substr(start: (() -> Short), length: (() -> Expression<IntSort>)) =
    StringLiteral(this).substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Short), length: (() -> Byte)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Short), length: (() -> Short)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Short), length: (() -> Int)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Short), length: (() -> Long)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Short), length: (() -> BigInteger)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun String.substr(start: (() -> Int), length: (() -> Expression<IntSort>)) =
    StringLiteral(this).substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Int), length: (() -> Byte)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Int), length: (() -> Short)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Int), length: (() -> Int)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Int), length: (() -> Long)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Int), length: (() -> BigInteger)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun String.substr(start: (() -> Long), length: (() -> Expression<IntSort>)) =
    StringLiteral(this).substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Long), length: (() -> Byte)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Long), length: (() -> Short)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Long), length: (() -> Int)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Long), length: (() -> Long)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> Long), length: (() -> BigInteger)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun String.substr(start: (() -> BigInteger), length: (() -> Expression<IntSort>)) =
    StringLiteral(this).substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> BigInteger), length: (() -> Byte)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> BigInteger), length: (() -> Short)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> BigInteger), length: (() -> Int)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> BigInteger), length: (() -> Long)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun String.substr(start: (() -> BigInteger), length: (() -> BigInteger)) =
    StringLiteral(this).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .
 */
fun (() -> String).substr(start: Expression<IntSort>, length: Expression<IntSort>) =
    StringLiteral(this()).substr(start, length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> String).substr(start: Expression<IntSort>, length: Byte) =
    StringLiteral(this()).substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> String).substr(start: Expression<IntSort>, length: Short) =
    StringLiteral(this()).substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> String).substr(start: Expression<IntSort>, length: Int) =
    StringLiteral(this()).substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> String).substr(start: Expression<IntSort>, length: Long) =
    StringLiteral(this()).substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> String).substr(start: Expression<IntSort>, length: BigInteger) =
    StringLiteral(this()).substr(start, IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun (() -> String).substr(start: Byte, length: Expression<IntSort>) =
    StringLiteral(this()).substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Byte, length: Byte) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Byte, length: Short) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Byte, length: Int) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Byte, length: Long) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Byte, length: BigInteger) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun (() -> String).substr(start: Short, length: Expression<IntSort>) =
    StringLiteral(this()).substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Short, length: Byte) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Short, length: Short) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Short, length: Int) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Short, length: Long) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Short, length: BigInteger) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun (() -> String).substr(start: Int, length: Expression<IntSort>) =
    StringLiteral(this()).substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Int, length: Byte) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Int, length: Short) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Int, length: Int) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Int, length: Long) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Int, length: BigInteger) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun (() -> String).substr(start: Long, length: Expression<IntSort>) =
    StringLiteral(this()).substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Long, length: Byte) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Long, length: Short) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Long, length: Int) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Long, length: Long) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Long, length: BigInteger) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun (() -> String).substr(start: BigInteger, length: Expression<IntSort>) =
    StringLiteral(this()).substr(IntLiteral(start), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: BigInteger, length: Byte) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: BigInteger, length: Short) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: BigInteger, length: Int) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: BigInteger, length: Long) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: BigInteger, length: BigInteger) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .
 */
fun (() -> String).substr(start: (() -> Expression<IntSort>), length: Expression<IntSort>) =
    StringLiteral(this()).substr(start(), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Expression<IntSort>), length: Byte) =
    StringLiteral(this()).substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Expression<IntSort>), length: Short) =
    StringLiteral(this()).substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Expression<IntSort>), length: Int) =
    StringLiteral(this()).substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Expression<IntSort>), length: Long) =
    StringLiteral(this()).substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Expression<IntSort>), length: BigInteger) =
    StringLiteral(this()).substr(start(), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun (() -> String).substr(start: (() -> Byte), length: Expression<IntSort>) =
    StringLiteral(this()).substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Byte), length: Byte) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Byte), length: Short) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Byte), length: Int) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Byte), length: Long) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Byte), length: BigInteger) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun (() -> String).substr(start: (() -> Short), length: Expression<IntSort>) =
    StringLiteral(this()).substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Short), length: Byte) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Short), length: Short) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Short), length: Int) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Short), length: Long) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Short), length: BigInteger) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun (() -> String).substr(start: (() -> Int), length: Expression<IntSort>) =
    StringLiteral(this()).substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Int), length: Byte) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Int), length: Short) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Int), length: Int) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Int), length: Long) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Int), length: BigInteger) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun (() -> String).substr(start: (() -> Long), length: Expression<IntSort>) =
    StringLiteral(this()).substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Long), length: Byte) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Long), length: Short) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Long), length: Int) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Long), length: Long) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Long), length: BigInteger) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun (() -> String).substr(start: (() -> BigInteger), length: Expression<IntSort>) =
    StringLiteral(this()).substr(IntLiteral(start()), length)

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> BigInteger), length: Byte) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> BigInteger), length: Short) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> BigInteger), length: Int) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> BigInteger), length: Long) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> BigInteger), length: BigInteger) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .
 */
fun (() -> String).substr(start: Expression<IntSort>, length: (() -> Expression<IntSort>)) =
    StringLiteral(this()).substr(start, length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> String).substr(start: Expression<IntSort>, length: (() -> Byte)) =
    StringLiteral(this()).substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> String).substr(start: Expression<IntSort>, length: (() -> Short)) =
    StringLiteral(this()).substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> String).substr(start: Expression<IntSort>, length: (() -> Int)) =
    StringLiteral(this()).substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> String).substr(start: Expression<IntSort>, length: (() -> Long)) =
    StringLiteral(this()).substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> String).substr(start: Expression<IntSort>, length: (() -> BigInteger)) =
    StringLiteral(this()).substr(start, IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun (() -> String).substr(start: Byte, length: (() -> Expression<IntSort>)) =
    StringLiteral(this()).substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Byte, length: (() -> Byte)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Byte, length: (() -> Short)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Byte, length: (() -> Int)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Byte, length: (() -> Long)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Byte, length: (() -> BigInteger)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun (() -> String).substr(start: Short, length: (() -> Expression<IntSort>)) =
    StringLiteral(this()).substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Short, length: (() -> Byte)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Short, length: (() -> Short)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Short, length: (() -> Int)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Short, length: (() -> Long)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Short, length: (() -> BigInteger)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun (() -> String).substr(start: Int, length: (() -> Expression<IntSort>)) =
    StringLiteral(this()).substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Int, length: (() -> Byte)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Int, length: (() -> Short)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Int, length: (() -> Int)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Int, length: (() -> Long)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Int, length: (() -> BigInteger)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun (() -> String).substr(start: Long, length: (() -> Expression<IntSort>)) =
    StringLiteral(this()).substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Long, length: (() -> Byte)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Long, length: (() -> Short)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Long, length: (() -> Int)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Long, length: (() -> Long)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: Long, length: (() -> BigInteger)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun (() -> String).substr(start: BigInteger, length: (() -> Expression<IntSort>)) =
    StringLiteral(this()).substr(IntLiteral(start), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: BigInteger, length: (() -> Byte)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: BigInteger, length: (() -> Short)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: BigInteger, length: (() -> Int)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: BigInteger, length: (() -> Long)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: BigInteger, length: (() -> BigInteger)) =
    StringLiteral(this()).substr(IntLiteral(start), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .
 */
fun (() -> String).substr(start: (() -> Expression<IntSort>), length: (() -> Expression<IntSort>)) =
    StringLiteral(this()).substr(start(), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Expression<IntSort>), length: (() -> Byte)) =
    StringLiteral(this()).substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Expression<IntSort>), length: (() -> Short)) =
    StringLiteral(this()).substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Expression<IntSort>), length: (() -> Int)) =
    StringLiteral(this()).substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Expression<IntSort>), length: (() -> Long)) =
    StringLiteral(this()).substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] .[length] is converted to [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Expression<IntSort>), length: (() -> BigInteger)) =
    StringLiteral(this()).substr(start(), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun (() -> String).substr(start: (() -> Byte), length: (() -> Expression<IntSort>)) =
    StringLiteral(this()).substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Byte), length: (() -> Byte)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Byte), length: (() -> Short)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Byte), length: (() -> Int)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Byte), length: (() -> Long)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Byte), length: (() -> BigInteger)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun (() -> String).substr(start: (() -> Short), length: (() -> Expression<IntSort>)) =
    StringLiteral(this()).substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Short), length: (() -> Byte)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Short), length: (() -> Short)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Short), length: (() -> Int)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Short), length: (() -> Long)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Short), length: (() -> BigInteger)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun (() -> String).substr(start: (() -> Int), length: (() -> Expression<IntSort>)) =
    StringLiteral(this()).substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Int), length: (() -> Byte)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Int), length: (() -> Short)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Int), length: (() -> Int)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Int), length: (() -> Long)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Int), length: (() -> BigInteger)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun (() -> String).substr(start: (() -> Long), length: (() -> Expression<IntSort>)) =
    StringLiteral(this()).substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Long), length: (() -> Byte)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Long), length: (() -> Short)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Long), length: (() -> Int)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Long), length: (() -> Long)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> Long), length: (() -> BigInteger)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .
 */
fun (() -> String).substr(start: (() -> BigInteger), length: (() -> Expression<IntSort>)) =
    StringLiteral(this()).substr(IntLiteral(start()), length())

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> BigInteger), length: (() -> Byte)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> BigInteger), length: (() -> Short)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> BigInteger), length: (() -> Int)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> BigInteger), length: (() -> Long)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/**
 * Longest substring of [this] of at most [length] characters starting at [start]. [this] is
 * converted to [StringLiteral] [start] is converted to [IntLiteral] .[length] is converted to
 * [IntLiteral]
 */
fun (() -> String).substr(start: (() -> BigInteger), length: (() -> BigInteger)) =
    StringLiteral(this()).substr(IntLiteral(start()), IntLiteral(length()))

/** Check if [this] is a prefix of [rhs]. */
infix fun Expression<StringSort>.prefixof(rhs: Expression<StringSort>) = StrPrefixOf(this, rhs)

/** Check if [this] is a prefix of [rhs]. [rhs] is converted to [StringLiteral] . */
infix fun Expression<StringSort>.prefixof(rhs: String) = this prefixof StringLiteral(rhs)

/** Check if [this] is a prefix of [rhs]. . */
infix fun Expression<StringSort>.prefixof(rhs: (() -> Expression<StringSort>)) = this prefixof rhs()

/** Check if [this] is a prefix of [rhs]. [rhs] is converted to [StringLiteral] . */
infix fun Expression<StringSort>.prefixof(rhs: (() -> String)) = this prefixof StringLiteral(rhs())

/** Check if [this] is a prefix of [rhs]. */
infix fun (() -> Expression<StringSort>).prefixof(rhs: Expression<StringSort>) = this() prefixof rhs

/** Check if [this] is a prefix of [rhs]. [rhs] is converted to [StringLiteral] */
infix fun (() -> Expression<StringSort>).prefixof(rhs: String) = this() prefixof StringLiteral(rhs)

/** Check if [this] is a prefix of [rhs]. */
infix fun (() -> Expression<StringSort>).prefixof(rhs: (() -> Expression<StringSort>)) =
    this() prefixof rhs()

/** Check if [this] is a prefix of [rhs]. [rhs] is converted to [StringLiteral] */
infix fun (() -> Expression<StringSort>).prefixof(rhs: (() -> String)) =
    this() prefixof StringLiteral(rhs())

/** Check if [this] is a prefix of [rhs]. [String] is converted to [StringLiteral] . */
infix fun String.prefixof(rhs: Expression<StringSort>) = StringLiteral(this) prefixof rhs

/**
 * Check if [this] is a prefix of [rhs]. [String] is converted to [StringLiteral] [rhs] is converted
 * to [StringLiteral] .
 */
infix fun String.prefixof(rhs: String) = StringLiteral(this) prefixof StringLiteral(rhs)

/** Check if [this] is a prefix of [rhs]. [String] is converted to [StringLiteral] . */
infix fun String.prefixof(rhs: (() -> Expression<StringSort>)) = StringLiteral(this) prefixof rhs()

/**
 * Check if [this] is a prefix of [rhs]. [String] is converted to [StringLiteral] [rhs] is converted
 * to [StringLiteral] .
 */
infix fun String.prefixof(rhs: (() -> String)) = StringLiteral(this) prefixof StringLiteral(rhs())

/** Check if [this] is a prefix of [rhs]. */
infix fun (() -> String).prefixof(rhs: Expression<StringSort>) = StringLiteral(this()) prefixof rhs

/** Check if [this] is a prefix of [rhs]. [rhs] is converted to [StringLiteral] */
infix fun (() -> String).prefixof(rhs: String) = StringLiteral(this()) prefixof StringLiteral(rhs)

/** Check if [this] is a prefix of [rhs]. */
infix fun (() -> String).prefixof(rhs: (() -> Expression<StringSort>)) =
    StringLiteral(this()) prefixof rhs()

/** Check if [this] is a prefix of [rhs]. [rhs] is converted to [StringLiteral] */
infix fun (() -> String).prefixof(rhs: (() -> String)) =
    StringLiteral(this()) prefixof StringLiteral(rhs())

/** Check if [this] is a suffix of [rhs]. */
infix fun Expression<StringSort>.suffixof(rhs: Expression<StringSort>) = StrSuffixOf(this, rhs)

/** Check if [this] is a suffix of [rhs]. [rhs] is converted to [StringLiteral] . */
infix fun Expression<StringSort>.suffixof(rhs: String) = this suffixof StringLiteral(rhs)

/** Check if [this] is a suffix of [rhs]. . */
infix fun Expression<StringSort>.suffixof(rhs: (() -> Expression<StringSort>)) = this suffixof rhs()

/** Check if [this] is a suffix of [rhs]. [rhs] is converted to [StringLiteral] . */
infix fun Expression<StringSort>.suffixof(rhs: (() -> String)) = this suffixof StringLiteral(rhs())

/** Check if [this] is a suffix of [rhs]. */
infix fun (() -> Expression<StringSort>).suffixof(rhs: Expression<StringSort>) = this() suffixof rhs

/** Check if [this] is a suffix of [rhs]. [rhs] is converted to [StringLiteral] */
infix fun (() -> Expression<StringSort>).suffixof(rhs: String) = this() suffixof StringLiteral(rhs)

/** Check if [this] is a suffix of [rhs]. */
infix fun (() -> Expression<StringSort>).suffixof(rhs: (() -> Expression<StringSort>)) =
    this() suffixof rhs()

/** Check if [this] is a suffix of [rhs]. [rhs] is converted to [StringLiteral] */
infix fun (() -> Expression<StringSort>).suffixof(rhs: (() -> String)) =
    this() suffixof StringLiteral(rhs())

/** Check if [this] is a suffix of [rhs]. [String] is converted to [StringLiteral] . */
infix fun String.suffixof(rhs: Expression<StringSort>) = StringLiteral(this) suffixof rhs

/**
 * Check if [this] is a suffix of [rhs]. [String] is converted to [StringLiteral] [rhs] is converted
 * to [StringLiteral] .
 */
infix fun String.suffixof(rhs: String) = StringLiteral(this) suffixof StringLiteral(rhs)

/** Check if [this] is a suffix of [rhs]. [String] is converted to [StringLiteral] . */
infix fun String.suffixof(rhs: (() -> Expression<StringSort>)) = StringLiteral(this) suffixof rhs()

/**
 * Check if [this] is a suffix of [rhs]. [String] is converted to [StringLiteral] [rhs] is converted
 * to [StringLiteral] .
 */
infix fun String.suffixof(rhs: (() -> String)) = StringLiteral(this) suffixof StringLiteral(rhs())

/** Check if [this] is a suffix of [rhs]. */
infix fun (() -> String).suffixof(rhs: Expression<StringSort>) = StringLiteral(this()) suffixof rhs

/** Check if [this] is a suffix of [rhs]. [rhs] is converted to [StringLiteral] */
infix fun (() -> String).suffixof(rhs: String) = StringLiteral(this()) suffixof StringLiteral(rhs)

/** Check if [this] is a suffix of [rhs]. */
infix fun (() -> String).suffixof(rhs: (() -> Expression<StringSort>)) =
    StringLiteral(this()) suffixof rhs()

/** Check if [this] is a suffix of [rhs]. [rhs] is converted to [StringLiteral] */
infix fun (() -> String).suffixof(rhs: (() -> String)) =
    StringLiteral(this()) suffixof StringLiteral(rhs())

/** Check if [this] contains [rhs] as substring. */
infix fun Expression<StringSort>.contains(rhs: Expression<StringSort>) = StrContains(this, rhs)

/** Check if [this] contains [rhs] as substring. [rhs] is converted to [StringLiteral] . */
infix fun Expression<StringSort>.contains(rhs: String) = this contains StringLiteral(rhs)

/** Check if [this] contains [rhs] as substring. . */
infix fun Expression<StringSort>.contains(rhs: (() -> Expression<StringSort>)) = this contains rhs()

/** Check if [this] contains [rhs] as substring. [rhs] is converted to [StringLiteral] . */
infix fun Expression<StringSort>.contains(rhs: (() -> String)) = this contains StringLiteral(rhs())

/** Check if [this] contains [rhs] as substring. */
infix fun (() -> Expression<StringSort>).contains(rhs: Expression<StringSort>) = this() contains rhs

/** Check if [this] contains [rhs] as substring. [rhs] is converted to [StringLiteral] */
infix fun (() -> Expression<StringSort>).contains(rhs: String) = this() contains StringLiteral(rhs)

/** Check if [this] contains [rhs] as substring. */
infix fun (() -> Expression<StringSort>).contains(rhs: (() -> Expression<StringSort>)) =
    this() contains rhs()

/** Check if [this] contains [rhs] as substring. [rhs] is converted to [StringLiteral] */
infix fun (() -> Expression<StringSort>).contains(rhs: (() -> String)) =
    this() contains StringLiteral(rhs())

/** Check if [this] contains [rhs] as substring. [String] is converted to [StringLiteral] . */
infix fun String.contains(rhs: Expression<StringSort>) = StringLiteral(this) contains rhs

/**
 * Check if [this] contains [rhs] as substring. [String] is converted to [StringLiteral] [rhs] is
 * converted to [StringLiteral] .
 */
infix fun String.contains(rhs: String) = StringLiteral(this) contains StringLiteral(rhs)

/** Check if [this] contains [rhs] as substring. [String] is converted to [StringLiteral] . */
infix fun String.contains(rhs: (() -> Expression<StringSort>)) = StringLiteral(this) contains rhs()

/**
 * Check if [this] contains [rhs] as substring. [String] is converted to [StringLiteral] [rhs] is
 * converted to [StringLiteral] .
 */
infix fun String.contains(rhs: (() -> String)) = StringLiteral(this) contains StringLiteral(rhs())

/** Check if [this] contains [rhs] as substring. */
infix fun (() -> String).contains(rhs: Expression<StringSort>) = StringLiteral(this()) contains rhs

/** Check if [this] contains [rhs] as substring. [rhs] is converted to [StringLiteral] */
infix fun (() -> String).contains(rhs: String) = StringLiteral(this()) contains StringLiteral(rhs)

/** Check if [this] contains [rhs] as substring. */
infix fun (() -> String).contains(rhs: (() -> Expression<StringSort>)) =
    StringLiteral(this()) contains rhs()

/** Check if [this] contains [rhs] as substring. [rhs] is converted to [StringLiteral] */
infix fun (() -> String).contains(rhs: (() -> String)) =
    StringLiteral(this()) contains StringLiteral(rhs())

/** Index of first occurrence of [substring] in [this] starting at [start]. */
fun Expression<StringSort>.indexof(substring: Expression<StringSort>, start: Expression<IntSort>) =
    StrIndexOf(this, substring, start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: Expression<StringSort>, start: Byte) =
    this.indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: Expression<StringSort>, start: Short) =
    this.indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: Expression<StringSort>, start: Int) =
    this.indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: Expression<StringSort>, start: Long) =
    this.indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: Expression<StringSort>, start: BigInteger) =
    this.indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .
 */
fun Expression<StringSort>.indexof(substring: String, start: Expression<IntSort>) =
    this.indexof(StringLiteral(substring), start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: String, start: Byte) =
    this.indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: String, start: Short) =
    this.indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: String, start: Int) =
    this.indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: String, start: Long) =
    this.indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: String, start: BigInteger) =
    this.indexof(StringLiteral(substring), IntLiteral(start))

/** Index of first occurrence of [substring] in [this] starting at [start]. . */
fun Expression<StringSort>.indexof(
    substring: (() -> Expression<StringSort>),
    start: Expression<IntSort>
) = this.indexof(substring(), start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: (() -> Expression<StringSort>), start: Byte) =
    this.indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: (() -> Expression<StringSort>), start: Short) =
    this.indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: (() -> Expression<StringSort>), start: Int) =
    this.indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: (() -> Expression<StringSort>), start: Long) =
    this.indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: (() -> Expression<StringSort>), start: BigInteger) =
    this.indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .
 */
fun Expression<StringSort>.indexof(substring: (() -> String), start: Expression<IntSort>) =
    this.indexof(StringLiteral(substring()), start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: (() -> String), start: Byte) =
    this.indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: (() -> String), start: Short) =
    this.indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: (() -> String), start: Int) =
    this.indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: (() -> String), start: Long) =
    this.indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: (() -> String), start: BigInteger) =
    this.indexof(StringLiteral(substring()), IntLiteral(start))

/** Index of first occurrence of [substring] in [this] starting at [start]. . */
fun Expression<StringSort>.indexof(
    substring: Expression<StringSort>,
    start: (() -> Expression<IntSort>)
) = this.indexof(substring, start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: Expression<StringSort>, start: (() -> Byte)) =
    this.indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: Expression<StringSort>, start: (() -> Short)) =
    this.indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: Expression<StringSort>, start: (() -> Int)) =
    this.indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: Expression<StringSort>, start: (() -> Long)) =
    this.indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: Expression<StringSort>, start: (() -> BigInteger)) =
    this.indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .
 */
fun Expression<StringSort>.indexof(substring: String, start: (() -> Expression<IntSort>)) =
    this.indexof(StringLiteral(substring), start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: String, start: (() -> Byte)) =
    this.indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: String, start: (() -> Short)) =
    this.indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: String, start: (() -> Int)) =
    this.indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: String, start: (() -> Long)) =
    this.indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: String, start: (() -> BigInteger)) =
    this.indexof(StringLiteral(substring), IntLiteral(start()))

/** Index of first occurrence of [substring] in [this] starting at [start]. . */
fun Expression<StringSort>.indexof(
    substring: (() -> Expression<StringSort>),
    start: (() -> Expression<IntSort>)
) = this.indexof(substring(), start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: (() -> Expression<StringSort>), start: (() -> Byte)) =
    this.indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun Expression<StringSort>.indexof(
    substring: (() -> Expression<StringSort>),
    start: (() -> Short)
) = this.indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: (() -> Expression<StringSort>), start: (() -> Int)) =
    this.indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: (() -> Expression<StringSort>), start: (() -> Long)) =
    this.indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun Expression<StringSort>.indexof(
    substring: (() -> Expression<StringSort>),
    start: (() -> BigInteger)
) = this.indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .
 */
fun Expression<StringSort>.indexof(substring: (() -> String), start: (() -> Expression<IntSort>)) =
    this.indexof(StringLiteral(substring()), start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: (() -> String), start: (() -> Byte)) =
    this.indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: (() -> String), start: (() -> Short)) =
    this.indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: (() -> String), start: (() -> Int)) =
    this.indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: (() -> String), start: (() -> Long)) =
    this.indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun Expression<StringSort>.indexof(substring: (() -> String), start: (() -> BigInteger)) =
    this.indexof(StringLiteral(substring()), IntLiteral(start()))

/** Index of first occurrence of [substring] in [this] starting at [start]. . */
fun (() -> Expression<StringSort>).indexof(
    substring: Expression<StringSort>,
    start: Expression<IntSort>
) = this().indexof(substring, start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: Expression<StringSort>, start: Byte) =
    this().indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: Expression<StringSort>, start: Short) =
    this().indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: Expression<StringSort>, start: Int) =
    this().indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: Expression<StringSort>, start: Long) =
    this().indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: Expression<StringSort>, start: BigInteger) =
    this().indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .
 */
fun (() -> Expression<StringSort>).indexof(substring: String, start: Expression<IntSort>) =
    this().indexof(StringLiteral(substring), start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: String, start: Byte) =
    this().indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: String, start: Short) =
    this().indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: String, start: Int) =
    this().indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: String, start: Long) =
    this().indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: String, start: BigInteger) =
    this().indexof(StringLiteral(substring), IntLiteral(start))

/** Index of first occurrence of [substring] in [this] starting at [start]. . */
fun (() -> Expression<StringSort>).indexof(
    substring: (() -> Expression<StringSort>),
    start: Expression<IntSort>
) = this().indexof(substring(), start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: (() -> Expression<StringSort>), start: Byte) =
    this().indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(
    substring: (() -> Expression<StringSort>),
    start: Short
) = this().indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: (() -> Expression<StringSort>), start: Int) =
    this().indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: (() -> Expression<StringSort>), start: Long) =
    this().indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(
    substring: (() -> Expression<StringSort>),
    start: BigInteger
) = this().indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .
 */
fun (() -> Expression<StringSort>).indexof(substring: (() -> String), start: Expression<IntSort>) =
    this().indexof(StringLiteral(substring()), start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: (() -> String), start: Byte) =
    this().indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: (() -> String), start: Short) =
    this().indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: (() -> String), start: Int) =
    this().indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: (() -> String), start: Long) =
    this().indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: (() -> String), start: BigInteger) =
    this().indexof(StringLiteral(substring()), IntLiteral(start))

/** Index of first occurrence of [substring] in [this] starting at [start]. . */
fun (() -> Expression<StringSort>).indexof(
    substring: Expression<StringSort>,
    start: (() -> Expression<IntSort>)
) = this().indexof(substring, start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: Expression<StringSort>, start: (() -> Byte)) =
    this().indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(
    substring: Expression<StringSort>,
    start: (() -> Short)
) = this().indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: Expression<StringSort>, start: (() -> Int)) =
    this().indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: Expression<StringSort>, start: (() -> Long)) =
    this().indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(
    substring: Expression<StringSort>,
    start: (() -> BigInteger)
) = this().indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .
 */
fun (() -> Expression<StringSort>).indexof(substring: String, start: (() -> Expression<IntSort>)) =
    this().indexof(StringLiteral(substring), start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: String, start: (() -> Byte)) =
    this().indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: String, start: (() -> Short)) =
    this().indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: String, start: (() -> Int)) =
    this().indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: String, start: (() -> Long)) =
    this().indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: String, start: (() -> BigInteger)) =
    this().indexof(StringLiteral(substring), IntLiteral(start()))

/** Index of first occurrence of [substring] in [this] starting at [start]. . */
fun (() -> Expression<StringSort>).indexof(
    substring: (() -> Expression<StringSort>),
    start: (() -> Expression<IntSort>)
) = this().indexof(substring(), start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(
    substring: (() -> Expression<StringSort>),
    start: (() -> Byte)
) = this().indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(
    substring: (() -> Expression<StringSort>),
    start: (() -> Short)
) = this().indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(
    substring: (() -> Expression<StringSort>),
    start: (() -> Int)
) = this().indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(
    substring: (() -> Expression<StringSort>),
    start: (() -> Long)
) = this().indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. .[start] is converted to
 * [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(
    substring: (() -> Expression<StringSort>),
    start: (() -> BigInteger)
) = this().indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .
 */
fun (() -> Expression<StringSort>).indexof(
    substring: (() -> String),
    start: (() -> Expression<IntSort>)
) = this().indexof(StringLiteral(substring()), start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: (() -> String), start: (() -> Byte)) =
    this().indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: (() -> String), start: (() -> Short)) =
    this().indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: (() -> String), start: (() -> Int)) =
    this().indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: (() -> String), start: (() -> Long)) =
    this().indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [substring] is converted
 * to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> Expression<StringSort>).indexof(substring: (() -> String), start: (() -> BigInteger)) =
    this().indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .
 */
fun String.indexof(substring: Expression<StringSort>, start: Expression<IntSort>) =
    StringLiteral(this).indexof(substring, start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: Expression<StringSort>, start: Byte) =
    StringLiteral(this).indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: Expression<StringSort>, start: Short) =
    StringLiteral(this).indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: Expression<StringSort>, start: Int) =
    StringLiteral(this).indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: Expression<StringSort>, start: Long) =
    StringLiteral(this).indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: Expression<StringSort>, start: BigInteger) =
    StringLiteral(this).indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .
 */
fun String.indexof(substring: String, start: Expression<IntSort>) =
    StringLiteral(this).indexof(StringLiteral(substring), start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: String, start: Byte) =
    StringLiteral(this).indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: String, start: Short) =
    StringLiteral(this).indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: String, start: Int) =
    StringLiteral(this).indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: String, start: Long) =
    StringLiteral(this).indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: String, start: BigInteger) =
    StringLiteral(this).indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .
 */
fun String.indexof(substring: (() -> Expression<StringSort>), start: Expression<IntSort>) =
    StringLiteral(this).indexof(substring(), start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: (() -> Expression<StringSort>), start: Byte) =
    StringLiteral(this).indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: (() -> Expression<StringSort>), start: Short) =
    StringLiteral(this).indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: (() -> Expression<StringSort>), start: Int) =
    StringLiteral(this).indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: (() -> Expression<StringSort>), start: Long) =
    StringLiteral(this).indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: (() -> Expression<StringSort>), start: BigInteger) =
    StringLiteral(this).indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .
 */
fun String.indexof(substring: (() -> String), start: Expression<IntSort>) =
    StringLiteral(this).indexof(StringLiteral(substring()), start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: (() -> String), start: Byte) =
    StringLiteral(this).indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: (() -> String), start: Short) =
    StringLiteral(this).indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: (() -> String), start: Int) =
    StringLiteral(this).indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: (() -> String), start: Long) =
    StringLiteral(this).indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: (() -> String), start: BigInteger) =
    StringLiteral(this).indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .
 */
fun String.indexof(substring: Expression<StringSort>, start: (() -> Expression<IntSort>)) =
    StringLiteral(this).indexof(substring, start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: Expression<StringSort>, start: (() -> Byte)) =
    StringLiteral(this).indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: Expression<StringSort>, start: (() -> Short)) =
    StringLiteral(this).indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: Expression<StringSort>, start: (() -> Int)) =
    StringLiteral(this).indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: Expression<StringSort>, start: (() -> Long)) =
    StringLiteral(this).indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: Expression<StringSort>, start: (() -> BigInteger)) =
    StringLiteral(this).indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .
 */
fun String.indexof(substring: String, start: (() -> Expression<IntSort>)) =
    StringLiteral(this).indexof(StringLiteral(substring), start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: String, start: (() -> Byte)) =
    StringLiteral(this).indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: String, start: (() -> Short)) =
    StringLiteral(this).indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: String, start: (() -> Int)) =
    StringLiteral(this).indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: String, start: (() -> Long)) =
    StringLiteral(this).indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: String, start: (() -> BigInteger)) =
    StringLiteral(this).indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .
 */
fun String.indexof(substring: (() -> Expression<StringSort>), start: (() -> Expression<IntSort>)) =
    StringLiteral(this).indexof(substring(), start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: (() -> Expression<StringSort>), start: (() -> Byte)) =
    StringLiteral(this).indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: (() -> Expression<StringSort>), start: (() -> Short)) =
    StringLiteral(this).indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: (() -> Expression<StringSort>), start: (() -> Int)) =
    StringLiteral(this).indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: (() -> Expression<StringSort>), start: (() -> Long)) =
    StringLiteral(this).indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: (() -> Expression<StringSort>), start: (() -> BigInteger)) =
    StringLiteral(this).indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .
 */
fun String.indexof(substring: (() -> String), start: (() -> Expression<IntSort>)) =
    StringLiteral(this).indexof(StringLiteral(substring()), start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: (() -> String), start: (() -> Byte)) =
    StringLiteral(this).indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: (() -> String), start: (() -> Short)) =
    StringLiteral(this).indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: (() -> String), start: (() -> Int)) =
    StringLiteral(this).indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: (() -> String), start: (() -> Long)) =
    StringLiteral(this).indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun String.indexof(substring: (() -> String), start: (() -> BigInteger)) =
    StringLiteral(this).indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .
 */
fun (() -> String).indexof(substring: Expression<StringSort>, start: Expression<IntSort>) =
    StringLiteral(this()).indexof(substring, start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: Expression<StringSort>, start: Byte) =
    StringLiteral(this()).indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: Expression<StringSort>, start: Short) =
    StringLiteral(this()).indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: Expression<StringSort>, start: Int) =
    StringLiteral(this()).indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: Expression<StringSort>, start: Long) =
    StringLiteral(this()).indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: Expression<StringSort>, start: BigInteger) =
    StringLiteral(this()).indexof(substring, IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .
 */
fun (() -> String).indexof(substring: String, start: Expression<IntSort>) =
    StringLiteral(this()).indexof(StringLiteral(substring), start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: String, start: Byte) =
    StringLiteral(this()).indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: String, start: Short) =
    StringLiteral(this()).indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: String, start: Int) =
    StringLiteral(this()).indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: String, start: Long) =
    StringLiteral(this()).indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: String, start: BigInteger) =
    StringLiteral(this()).indexof(StringLiteral(substring), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .
 */
fun (() -> String).indexof(substring: (() -> Expression<StringSort>), start: Expression<IntSort>) =
    StringLiteral(this()).indexof(substring(), start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: (() -> Expression<StringSort>), start: Byte) =
    StringLiteral(this()).indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: (() -> Expression<StringSort>), start: Short) =
    StringLiteral(this()).indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: (() -> Expression<StringSort>), start: Int) =
    StringLiteral(this()).indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: (() -> Expression<StringSort>), start: Long) =
    StringLiteral(this()).indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: (() -> Expression<StringSort>), start: BigInteger) =
    StringLiteral(this()).indexof(substring(), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .
 */
fun (() -> String).indexof(substring: (() -> String), start: Expression<IntSort>) =
    StringLiteral(this()).indexof(StringLiteral(substring()), start)

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: (() -> String), start: Byte) =
    StringLiteral(this()).indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: (() -> String), start: Short) =
    StringLiteral(this()).indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: (() -> String), start: Int) =
    StringLiteral(this()).indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: (() -> String), start: Long) =
    StringLiteral(this()).indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: (() -> String), start: BigInteger) =
    StringLiteral(this()).indexof(StringLiteral(substring()), IntLiteral(start))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .
 */
fun (() -> String).indexof(substring: Expression<StringSort>, start: (() -> Expression<IntSort>)) =
    StringLiteral(this()).indexof(substring, start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: Expression<StringSort>, start: (() -> Byte)) =
    StringLiteral(this()).indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: Expression<StringSort>, start: (() -> Short)) =
    StringLiteral(this()).indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: Expression<StringSort>, start: (() -> Int)) =
    StringLiteral(this()).indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: Expression<StringSort>, start: (() -> Long)) =
    StringLiteral(this()).indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: Expression<StringSort>, start: (() -> BigInteger)) =
    StringLiteral(this()).indexof(substring, IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .
 */
fun (() -> String).indexof(substring: String, start: (() -> Expression<IntSort>)) =
    StringLiteral(this()).indexof(StringLiteral(substring), start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: String, start: (() -> Byte)) =
    StringLiteral(this()).indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: String, start: (() -> Short)) =
    StringLiteral(this()).indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: String, start: (() -> Int)) =
    StringLiteral(this()).indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: String, start: (() -> Long)) =
    StringLiteral(this()).indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: String, start: (() -> BigInteger)) =
    StringLiteral(this()).indexof(StringLiteral(substring), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .
 */
fun (() -> String).indexof(
    substring: (() -> Expression<StringSort>),
    start: (() -> Expression<IntSort>)
) = StringLiteral(this()).indexof(substring(), start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: (() -> Expression<StringSort>), start: (() -> Byte)) =
    StringLiteral(this()).indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: (() -> Expression<StringSort>), start: (() -> Short)) =
    StringLiteral(this()).indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: (() -> Expression<StringSort>), start: (() -> Int)) =
    StringLiteral(this()).indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: (() -> Expression<StringSort>), start: (() -> Long)) =
    StringLiteral(this()).indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: (() -> Expression<StringSort>), start: (() -> BigInteger)) =
    StringLiteral(this()).indexof(substring(), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .
 */
fun (() -> String).indexof(substring: (() -> String), start: (() -> Expression<IntSort>)) =
    StringLiteral(this()).indexof(StringLiteral(substring()), start())

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: (() -> String), start: (() -> Byte)) =
    StringLiteral(this()).indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: (() -> String), start: (() -> Short)) =
    StringLiteral(this()).indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: (() -> String), start: (() -> Int)) =
    StringLiteral(this()).indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: (() -> String), start: (() -> Long)) =
    StringLiteral(this()).indexof(StringLiteral(substring()), IntLiteral(start()))

/**
 * Index of first occurrence of [substring] in [this] starting at [start]. [this] is converted to
 * [StringLiteral] [substring] is converted to [StringLiteral] .[start] is converted to [IntLiteral]
 */
fun (() -> String).indexof(substring: (() -> String), start: (() -> BigInteger)) =
    StringLiteral(this()).indexof(StringLiteral(substring()), IntLiteral(start()))

/** Replace the first occurrence of [oldValue] in [this] with [newValue]. */
fun Expression<StringSort>.replace(
    oldValue: Expression<StringSort>,
    newValue: Expression<StringSort>
) = StrReplace(this, oldValue, newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. .[newValue] is converted to
 * [StringLiteral]
 */
fun Expression<StringSort>.replace(oldValue: Expression<StringSort>, newValue: String) =
    this.replace(oldValue, StringLiteral(newValue))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .
 */
fun Expression<StringSort>.replace(oldValue: String, newValue: Expression<StringSort>) =
    this.replace(StringLiteral(oldValue), newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun Expression<StringSort>.replace(oldValue: String, newValue: String) =
    this.replace(StringLiteral(oldValue), StringLiteral(newValue))

/** Replace the first occurrence of [oldValue] in [this] with [newValue]. . */
fun Expression<StringSort>.replace(
    oldValue: (() -> Expression<StringSort>),
    newValue: Expression<StringSort>
) = this.replace(oldValue(), newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. .[newValue] is converted to
 * [StringLiteral]
 */
fun Expression<StringSort>.replace(oldValue: (() -> Expression<StringSort>), newValue: String) =
    this.replace(oldValue(), StringLiteral(newValue))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .
 */
fun Expression<StringSort>.replace(oldValue: (() -> String), newValue: Expression<StringSort>) =
    this.replace(StringLiteral(oldValue()), newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun Expression<StringSort>.replace(oldValue: (() -> String), newValue: String) =
    this.replace(StringLiteral(oldValue()), StringLiteral(newValue))

/** Replace the first occurrence of [oldValue] in [this] with [newValue]. . */
fun Expression<StringSort>.replace(
    oldValue: Expression<StringSort>,
    newValue: (() -> Expression<StringSort>)
) = this.replace(oldValue, newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. .[newValue] is converted to
 * [StringLiteral]
 */
fun Expression<StringSort>.replace(oldValue: Expression<StringSort>, newValue: (() -> String)) =
    this.replace(oldValue, StringLiteral(newValue()))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .
 */
fun Expression<StringSort>.replace(oldValue: String, newValue: (() -> Expression<StringSort>)) =
    this.replace(StringLiteral(oldValue), newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun Expression<StringSort>.replace(oldValue: String, newValue: (() -> String)) =
    this.replace(StringLiteral(oldValue), StringLiteral(newValue()))

/** Replace the first occurrence of [oldValue] in [this] with [newValue]. . */
fun Expression<StringSort>.replace(
    oldValue: (() -> Expression<StringSort>),
    newValue: (() -> Expression<StringSort>)
) = this.replace(oldValue(), newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. .[newValue] is converted to
 * [StringLiteral]
 */
fun Expression<StringSort>.replace(
    oldValue: (() -> Expression<StringSort>),
    newValue: (() -> String)
) = this.replace(oldValue(), StringLiteral(newValue()))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .
 */
fun Expression<StringSort>.replace(
    oldValue: (() -> String),
    newValue: (() -> Expression<StringSort>)
) = this.replace(StringLiteral(oldValue()), newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun Expression<StringSort>.replace(oldValue: (() -> String), newValue: (() -> String)) =
    this.replace(StringLiteral(oldValue()), StringLiteral(newValue()))

/** Replace the first occurrence of [oldValue] in [this] with [newValue]. . */
fun (() -> Expression<StringSort>).replace(
    oldValue: Expression<StringSort>,
    newValue: Expression<StringSort>
) = this().replace(oldValue, newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. .[newValue] is converted to
 * [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace(oldValue: Expression<StringSort>, newValue: String) =
    this().replace(oldValue, StringLiteral(newValue))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .
 */
fun (() -> Expression<StringSort>).replace(oldValue: String, newValue: Expression<StringSort>) =
    this().replace(StringLiteral(oldValue), newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace(oldValue: String, newValue: String) =
    this().replace(StringLiteral(oldValue), StringLiteral(newValue))

/** Replace the first occurrence of [oldValue] in [this] with [newValue]. . */
fun (() -> Expression<StringSort>).replace(
    oldValue: (() -> Expression<StringSort>),
    newValue: Expression<StringSort>
) = this().replace(oldValue(), newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. .[newValue] is converted to
 * [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace(
    oldValue: (() -> Expression<StringSort>),
    newValue: String
) = this().replace(oldValue(), StringLiteral(newValue))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .
 */
fun (() -> Expression<StringSort>).replace(
    oldValue: (() -> String),
    newValue: Expression<StringSort>
) = this().replace(StringLiteral(oldValue()), newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace(oldValue: (() -> String), newValue: String) =
    this().replace(StringLiteral(oldValue()), StringLiteral(newValue))

/** Replace the first occurrence of [oldValue] in [this] with [newValue]. . */
fun (() -> Expression<StringSort>).replace(
    oldValue: Expression<StringSort>,
    newValue: (() -> Expression<StringSort>)
) = this().replace(oldValue, newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. .[newValue] is converted to
 * [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace(
    oldValue: Expression<StringSort>,
    newValue: (() -> String)
) = this().replace(oldValue, StringLiteral(newValue()))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .
 */
fun (() -> Expression<StringSort>).replace(
    oldValue: String,
    newValue: (() -> Expression<StringSort>)
) = this().replace(StringLiteral(oldValue), newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace(oldValue: String, newValue: (() -> String)) =
    this().replace(StringLiteral(oldValue), StringLiteral(newValue()))

/** Replace the first occurrence of [oldValue] in [this] with [newValue]. . */
fun (() -> Expression<StringSort>).replace(
    oldValue: (() -> Expression<StringSort>),
    newValue: (() -> Expression<StringSort>)
) = this().replace(oldValue(), newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. .[newValue] is converted to
 * [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace(
    oldValue: (() -> Expression<StringSort>),
    newValue: (() -> String)
) = this().replace(oldValue(), StringLiteral(newValue()))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .
 */
fun (() -> Expression<StringSort>).replace(
    oldValue: (() -> String),
    newValue: (() -> Expression<StringSort>)
) = this().replace(StringLiteral(oldValue()), newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace(oldValue: (() -> String), newValue: (() -> String)) =
    this().replace(StringLiteral(oldValue()), StringLiteral(newValue()))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .
 */
fun String.replace(oldValue: Expression<StringSort>, newValue: Expression<StringSort>) =
    StringLiteral(this).replace(oldValue, newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun String.replace(oldValue: Expression<StringSort>, newValue: String) =
    StringLiteral(this).replace(oldValue, StringLiteral(newValue))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .
 */
fun String.replace(oldValue: String, newValue: Expression<StringSort>) =
    StringLiteral(this).replace(StringLiteral(oldValue), newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .[newValue] is converted to
 * [StringLiteral]
 */
fun String.replace(oldValue: String, newValue: String) =
    StringLiteral(this).replace(StringLiteral(oldValue), StringLiteral(newValue))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .
 */
fun String.replace(oldValue: (() -> Expression<StringSort>), newValue: Expression<StringSort>) =
    StringLiteral(this).replace(oldValue(), newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun String.replace(oldValue: (() -> Expression<StringSort>), newValue: String) =
    StringLiteral(this).replace(oldValue(), StringLiteral(newValue))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .
 */
fun String.replace(oldValue: (() -> String), newValue: Expression<StringSort>) =
    StringLiteral(this).replace(StringLiteral(oldValue()), newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .[newValue] is converted to
 * [StringLiteral]
 */
fun String.replace(oldValue: (() -> String), newValue: String) =
    StringLiteral(this).replace(StringLiteral(oldValue()), StringLiteral(newValue))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .
 */
fun String.replace(oldValue: Expression<StringSort>, newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this).replace(oldValue, newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun String.replace(oldValue: Expression<StringSort>, newValue: (() -> String)) =
    StringLiteral(this).replace(oldValue, StringLiteral(newValue()))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .
 */
fun String.replace(oldValue: String, newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this).replace(StringLiteral(oldValue), newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .[newValue] is converted to
 * [StringLiteral]
 */
fun String.replace(oldValue: String, newValue: (() -> String)) =
    StringLiteral(this).replace(StringLiteral(oldValue), StringLiteral(newValue()))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .
 */
fun String.replace(
    oldValue: (() -> Expression<StringSort>),
    newValue: (() -> Expression<StringSort>)
) = StringLiteral(this).replace(oldValue(), newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun String.replace(oldValue: (() -> Expression<StringSort>), newValue: (() -> String)) =
    StringLiteral(this).replace(oldValue(), StringLiteral(newValue()))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .
 */
fun String.replace(oldValue: (() -> String), newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this).replace(StringLiteral(oldValue()), newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .[newValue] is converted to
 * [StringLiteral]
 */
fun String.replace(oldValue: (() -> String), newValue: (() -> String)) =
    StringLiteral(this).replace(StringLiteral(oldValue()), StringLiteral(newValue()))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .
 */
fun (() -> String).replace(oldValue: Expression<StringSort>, newValue: Expression<StringSort>) =
    StringLiteral(this()).replace(oldValue, newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun (() -> String).replace(oldValue: Expression<StringSort>, newValue: String) =
    StringLiteral(this()).replace(oldValue, StringLiteral(newValue))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .
 */
fun (() -> String).replace(oldValue: String, newValue: Expression<StringSort>) =
    StringLiteral(this()).replace(StringLiteral(oldValue), newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .[newValue] is converted to
 * [StringLiteral]
 */
fun (() -> String).replace(oldValue: String, newValue: String) =
    StringLiteral(this()).replace(StringLiteral(oldValue), StringLiteral(newValue))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .
 */
fun (() -> String).replace(
    oldValue: (() -> Expression<StringSort>),
    newValue: Expression<StringSort>
) = StringLiteral(this()).replace(oldValue(), newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun (() -> String).replace(oldValue: (() -> Expression<StringSort>), newValue: String) =
    StringLiteral(this()).replace(oldValue(), StringLiteral(newValue))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .
 */
fun (() -> String).replace(oldValue: (() -> String), newValue: Expression<StringSort>) =
    StringLiteral(this()).replace(StringLiteral(oldValue()), newValue)

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .[newValue] is converted to
 * [StringLiteral]
 */
fun (() -> String).replace(oldValue: (() -> String), newValue: String) =
    StringLiteral(this()).replace(StringLiteral(oldValue()), StringLiteral(newValue))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .
 */
fun (() -> String).replace(
    oldValue: Expression<StringSort>,
    newValue: (() -> Expression<StringSort>)
) = StringLiteral(this()).replace(oldValue, newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun (() -> String).replace(oldValue: Expression<StringSort>, newValue: (() -> String)) =
    StringLiteral(this()).replace(oldValue, StringLiteral(newValue()))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .
 */
fun (() -> String).replace(oldValue: String, newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this()).replace(StringLiteral(oldValue), newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .[newValue] is converted to
 * [StringLiteral]
 */
fun (() -> String).replace(oldValue: String, newValue: (() -> String)) =
    StringLiteral(this()).replace(StringLiteral(oldValue), StringLiteral(newValue()))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .
 */
fun (() -> String).replace(
    oldValue: (() -> Expression<StringSort>),
    newValue: (() -> Expression<StringSort>)
) = StringLiteral(this()).replace(oldValue(), newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun (() -> String).replace(oldValue: (() -> Expression<StringSort>), newValue: (() -> String)) =
    StringLiteral(this()).replace(oldValue(), StringLiteral(newValue()))

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .
 */
fun (() -> String).replace(oldValue: (() -> String), newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this()).replace(StringLiteral(oldValue()), newValue())

/**
 * Replace the first occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .[newValue] is converted to
 * [StringLiteral]
 */
fun (() -> String).replace(oldValue: (() -> String), newValue: (() -> String)) =
    StringLiteral(this()).replace(StringLiteral(oldValue()), StringLiteral(newValue()))

/** Replace all occurrence of [oldValue] in [this] with [newValue]. */
fun Expression<StringSort>.replace_all(
    oldValue: Expression<StringSort>,
    newValue: Expression<StringSort>
) = StrReplaceAll(this, oldValue, newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. .[newValue] is converted to
 * [StringLiteral]
 */
fun Expression<StringSort>.replace_all(oldValue: Expression<StringSort>, newValue: String) =
    this.replace_all(oldValue, StringLiteral(newValue))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .
 */
fun Expression<StringSort>.replace_all(oldValue: String, newValue: Expression<StringSort>) =
    this.replace_all(StringLiteral(oldValue), newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun Expression<StringSort>.replace_all(oldValue: String, newValue: String) =
    this.replace_all(StringLiteral(oldValue), StringLiteral(newValue))

/** Replace all occurrence of [oldValue] in [this] with [newValue]. . */
fun Expression<StringSort>.replace_all(
    oldValue: (() -> Expression<StringSort>),
    newValue: Expression<StringSort>
) = this.replace_all(oldValue(), newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. .[newValue] is converted to
 * [StringLiteral]
 */
fun Expression<StringSort>.replace_all(oldValue: (() -> Expression<StringSort>), newValue: String) =
    this.replace_all(oldValue(), StringLiteral(newValue))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .
 */
fun Expression<StringSort>.replace_all(oldValue: (() -> String), newValue: Expression<StringSort>) =
    this.replace_all(StringLiteral(oldValue()), newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun Expression<StringSort>.replace_all(oldValue: (() -> String), newValue: String) =
    this.replace_all(StringLiteral(oldValue()), StringLiteral(newValue))

/** Replace all occurrence of [oldValue] in [this] with [newValue]. . */
fun Expression<StringSort>.replace_all(
    oldValue: Expression<StringSort>,
    newValue: (() -> Expression<StringSort>)
) = this.replace_all(oldValue, newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. .[newValue] is converted to
 * [StringLiteral]
 */
fun Expression<StringSort>.replace_all(oldValue: Expression<StringSort>, newValue: (() -> String)) =
    this.replace_all(oldValue, StringLiteral(newValue()))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .
 */
fun Expression<StringSort>.replace_all(oldValue: String, newValue: (() -> Expression<StringSort>)) =
    this.replace_all(StringLiteral(oldValue), newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun Expression<StringSort>.replace_all(oldValue: String, newValue: (() -> String)) =
    this.replace_all(StringLiteral(oldValue), StringLiteral(newValue()))

/** Replace all occurrence of [oldValue] in [this] with [newValue]. . */
fun Expression<StringSort>.replace_all(
    oldValue: (() -> Expression<StringSort>),
    newValue: (() -> Expression<StringSort>)
) = this.replace_all(oldValue(), newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. .[newValue] is converted to
 * [StringLiteral]
 */
fun Expression<StringSort>.replace_all(
    oldValue: (() -> Expression<StringSort>),
    newValue: (() -> String)
) = this.replace_all(oldValue(), StringLiteral(newValue()))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .
 */
fun Expression<StringSort>.replace_all(
    oldValue: (() -> String),
    newValue: (() -> Expression<StringSort>)
) = this.replace_all(StringLiteral(oldValue()), newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun Expression<StringSort>.replace_all(oldValue: (() -> String), newValue: (() -> String)) =
    this.replace_all(StringLiteral(oldValue()), StringLiteral(newValue()))

/** Replace all occurrence of [oldValue] in [this] with [newValue]. . */
fun (() -> Expression<StringSort>).replace_all(
    oldValue: Expression<StringSort>,
    newValue: Expression<StringSort>
) = this().replace_all(oldValue, newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. .[newValue] is converted to
 * [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace_all(oldValue: Expression<StringSort>, newValue: String) =
    this().replace_all(oldValue, StringLiteral(newValue))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .
 */
fun (() -> Expression<StringSort>).replace_all(oldValue: String, newValue: Expression<StringSort>) =
    this().replace_all(StringLiteral(oldValue), newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace_all(oldValue: String, newValue: String) =
    this().replace_all(StringLiteral(oldValue), StringLiteral(newValue))

/** Replace all occurrence of [oldValue] in [this] with [newValue]. . */
fun (() -> Expression<StringSort>).replace_all(
    oldValue: (() -> Expression<StringSort>),
    newValue: Expression<StringSort>
) = this().replace_all(oldValue(), newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. .[newValue] is converted to
 * [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace_all(
    oldValue: (() -> Expression<StringSort>),
    newValue: String
) = this().replace_all(oldValue(), StringLiteral(newValue))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .
 */
fun (() -> Expression<StringSort>).replace_all(
    oldValue: (() -> String),
    newValue: Expression<StringSort>
) = this().replace_all(StringLiteral(oldValue()), newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace_all(oldValue: (() -> String), newValue: String) =
    this().replace_all(StringLiteral(oldValue()), StringLiteral(newValue))

/** Replace all occurrence of [oldValue] in [this] with [newValue]. . */
fun (() -> Expression<StringSort>).replace_all(
    oldValue: Expression<StringSort>,
    newValue: (() -> Expression<StringSort>)
) = this().replace_all(oldValue, newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. .[newValue] is converted to
 * [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace_all(
    oldValue: Expression<StringSort>,
    newValue: (() -> String)
) = this().replace_all(oldValue, StringLiteral(newValue()))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .
 */
fun (() -> Expression<StringSort>).replace_all(
    oldValue: String,
    newValue: (() -> Expression<StringSort>)
) = this().replace_all(StringLiteral(oldValue), newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace_all(oldValue: String, newValue: (() -> String)) =
    this().replace_all(StringLiteral(oldValue), StringLiteral(newValue()))

/** Replace all occurrence of [oldValue] in [this] with [newValue]. . */
fun (() -> Expression<StringSort>).replace_all(
    oldValue: (() -> Expression<StringSort>),
    newValue: (() -> Expression<StringSort>)
) = this().replace_all(oldValue(), newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. .[newValue] is converted to
 * [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace_all(
    oldValue: (() -> Expression<StringSort>),
    newValue: (() -> String)
) = this().replace_all(oldValue(), StringLiteral(newValue()))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .
 */
fun (() -> Expression<StringSort>).replace_all(
    oldValue: (() -> String),
    newValue: (() -> Expression<StringSort>)
) = this().replace_all(StringLiteral(oldValue()), newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [oldValue] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace_all(oldValue: (() -> String), newValue: (() -> String)) =
    this().replace_all(StringLiteral(oldValue()), StringLiteral(newValue()))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .
 */
fun String.replace_all(oldValue: Expression<StringSort>, newValue: Expression<StringSort>) =
    StringLiteral(this).replace_all(oldValue, newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun String.replace_all(oldValue: Expression<StringSort>, newValue: String) =
    StringLiteral(this).replace_all(oldValue, StringLiteral(newValue))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .
 */
fun String.replace_all(oldValue: String, newValue: Expression<StringSort>) =
    StringLiteral(this).replace_all(StringLiteral(oldValue), newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .[newValue] is converted to
 * [StringLiteral]
 */
fun String.replace_all(oldValue: String, newValue: String) =
    StringLiteral(this).replace_all(StringLiteral(oldValue), StringLiteral(newValue))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .
 */
fun String.replace_all(oldValue: (() -> Expression<StringSort>), newValue: Expression<StringSort>) =
    StringLiteral(this).replace_all(oldValue(), newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun String.replace_all(oldValue: (() -> Expression<StringSort>), newValue: String) =
    StringLiteral(this).replace_all(oldValue(), StringLiteral(newValue))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .
 */
fun String.replace_all(oldValue: (() -> String), newValue: Expression<StringSort>) =
    StringLiteral(this).replace_all(StringLiteral(oldValue()), newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .[newValue] is converted to
 * [StringLiteral]
 */
fun String.replace_all(oldValue: (() -> String), newValue: String) =
    StringLiteral(this).replace_all(StringLiteral(oldValue()), StringLiteral(newValue))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .
 */
fun String.replace_all(oldValue: Expression<StringSort>, newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this).replace_all(oldValue, newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun String.replace_all(oldValue: Expression<StringSort>, newValue: (() -> String)) =
    StringLiteral(this).replace_all(oldValue, StringLiteral(newValue()))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .
 */
fun String.replace_all(oldValue: String, newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this).replace_all(StringLiteral(oldValue), newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .[newValue] is converted to
 * [StringLiteral]
 */
fun String.replace_all(oldValue: String, newValue: (() -> String)) =
    StringLiteral(this).replace_all(StringLiteral(oldValue), StringLiteral(newValue()))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .
 */
fun String.replace_all(
    oldValue: (() -> Expression<StringSort>),
    newValue: (() -> Expression<StringSort>)
) = StringLiteral(this).replace_all(oldValue(), newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun String.replace_all(oldValue: (() -> Expression<StringSort>), newValue: (() -> String)) =
    StringLiteral(this).replace_all(oldValue(), StringLiteral(newValue()))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .
 */
fun String.replace_all(oldValue: (() -> String), newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this).replace_all(StringLiteral(oldValue()), newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .[newValue] is converted to
 * [StringLiteral]
 */
fun String.replace_all(oldValue: (() -> String), newValue: (() -> String)) =
    StringLiteral(this).replace_all(StringLiteral(oldValue()), StringLiteral(newValue()))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .
 */
fun (() -> String).replace_all(oldValue: Expression<StringSort>, newValue: Expression<StringSort>) =
    StringLiteral(this()).replace_all(oldValue, newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun (() -> String).replace_all(oldValue: Expression<StringSort>, newValue: String) =
    StringLiteral(this()).replace_all(oldValue, StringLiteral(newValue))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .
 */
fun (() -> String).replace_all(oldValue: String, newValue: Expression<StringSort>) =
    StringLiteral(this()).replace_all(StringLiteral(oldValue), newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .[newValue] is converted to
 * [StringLiteral]
 */
fun (() -> String).replace_all(oldValue: String, newValue: String) =
    StringLiteral(this()).replace_all(StringLiteral(oldValue), StringLiteral(newValue))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .
 */
fun (() -> String).replace_all(
    oldValue: (() -> Expression<StringSort>),
    newValue: Expression<StringSort>
) = StringLiteral(this()).replace_all(oldValue(), newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun (() -> String).replace_all(oldValue: (() -> Expression<StringSort>), newValue: String) =
    StringLiteral(this()).replace_all(oldValue(), StringLiteral(newValue))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .
 */
fun (() -> String).replace_all(oldValue: (() -> String), newValue: Expression<StringSort>) =
    StringLiteral(this()).replace_all(StringLiteral(oldValue()), newValue)

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .[newValue] is converted to
 * [StringLiteral]
 */
fun (() -> String).replace_all(oldValue: (() -> String), newValue: String) =
    StringLiteral(this()).replace_all(StringLiteral(oldValue()), StringLiteral(newValue))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .
 */
fun (() -> String).replace_all(
    oldValue: Expression<StringSort>,
    newValue: (() -> Expression<StringSort>)
) = StringLiteral(this()).replace_all(oldValue, newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun (() -> String).replace_all(oldValue: Expression<StringSort>, newValue: (() -> String)) =
    StringLiteral(this()).replace_all(oldValue, StringLiteral(newValue()))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .
 */
fun (() -> String).replace_all(oldValue: String, newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this()).replace_all(StringLiteral(oldValue), newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .[newValue] is converted to
 * [StringLiteral]
 */
fun (() -> String).replace_all(oldValue: String, newValue: (() -> String)) =
    StringLiteral(this()).replace_all(StringLiteral(oldValue), StringLiteral(newValue()))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .
 */
fun (() -> String).replace_all(
    oldValue: (() -> Expression<StringSort>),
    newValue: (() -> Expression<StringSort>)
) = StringLiteral(this()).replace_all(oldValue(), newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun (() -> String).replace_all(oldValue: (() -> Expression<StringSort>), newValue: (() -> String)) =
    StringLiteral(this()).replace_all(oldValue(), StringLiteral(newValue()))

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .
 */
fun (() -> String).replace_all(oldValue: (() -> String), newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this()).replace_all(StringLiteral(oldValue()), newValue())

/**
 * Replace all occurrence of [oldValue] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [oldValue] is converted to [StringLiteral] .[newValue] is converted to
 * [StringLiteral]
 */
fun (() -> String).replace_all(oldValue: (() -> String), newValue: (() -> String)) =
    StringLiteral(this()).replace_all(StringLiteral(oldValue()), StringLiteral(newValue()))

/** Replace the shortest leftmost match of [regex] in [this] with [newValue]. */
fun Expression<StringSort>.replace_re(
    regex: Expression<RegLanSort>,
    newValue: Expression<StringSort>
) = StrReplaceRegex(this, regex, newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. .[newValue] is
 * converted to [StringLiteral]
 */
fun Expression<StringSort>.replace_re(regex: Expression<RegLanSort>, newValue: String) =
    this.replace_re(regex, StringLiteral(newValue))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [regex] is converted to
 * [Expression] of type [RegLanSort] .
 */
fun Expression<StringSort>.replace_re(regex: String, newValue: Expression<StringSort>) =
    this.replace_re(StringLiteral(regex).toRe(), newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [regex] is converted to
 * [Expression] of type [RegLanSort] .[newValue] is converted to [StringLiteral]
 */
fun Expression<StringSort>.replace_re(regex: String, newValue: String) =
    this.replace_re(StringLiteral(regex).toRe(), StringLiteral(newValue))

/** Replace the shortest leftmost match of [regex] in [this] with [newValue]. . */
fun Expression<StringSort>.replace_re(
    regex: (() -> Expression<RegLanSort>),
    newValue: Expression<StringSort>
) = this.replace_re(regex(), newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. .[newValue] is
 * converted to [StringLiteral]
 */
fun Expression<StringSort>.replace_re(regex: (() -> Expression<RegLanSort>), newValue: String) =
    this.replace_re(regex(), StringLiteral(newValue))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [regex] is converted to
 * [Expression] of type [RegLanSort] .
 */
fun Expression<StringSort>.replace_re(regex: (() -> String), newValue: Expression<StringSort>) =
    this.replace_re(StringLiteral(regex()).toRe(), newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [regex] is converted to
 * [Expression] of type [RegLanSort] .[newValue] is converted to [StringLiteral]
 */
fun Expression<StringSort>.replace_re(regex: (() -> String), newValue: String) =
    this.replace_re(StringLiteral(regex()).toRe(), StringLiteral(newValue))

/** Replace the shortest leftmost match of [regex] in [this] with [newValue]. . */
fun Expression<StringSort>.replace_re(
    regex: Expression<RegLanSort>,
    newValue: (() -> Expression<StringSort>)
) = this.replace_re(regex, newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. .[newValue] is
 * converted to [StringLiteral]
 */
fun Expression<StringSort>.replace_re(regex: Expression<RegLanSort>, newValue: (() -> String)) =
    this.replace_re(regex, StringLiteral(newValue()))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [regex] is converted to
 * [Expression] of type [RegLanSort] .
 */
fun Expression<StringSort>.replace_re(regex: String, newValue: (() -> Expression<StringSort>)) =
    this.replace_re(StringLiteral(regex).toRe(), newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [regex] is converted to
 * [Expression] of type [RegLanSort] .[newValue] is converted to [StringLiteral]
 */
fun Expression<StringSort>.replace_re(regex: String, newValue: (() -> String)) =
    this.replace_re(StringLiteral(regex).toRe(), StringLiteral(newValue()))

/** Replace the shortest leftmost match of [regex] in [this] with [newValue]. . */
fun Expression<StringSort>.replace_re(
    regex: (() -> Expression<RegLanSort>),
    newValue: (() -> Expression<StringSort>)
) = this.replace_re(regex(), newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. .[newValue] is
 * converted to [StringLiteral]
 */
fun Expression<StringSort>.replace_re(
    regex: (() -> Expression<RegLanSort>),
    newValue: (() -> String)
) = this.replace_re(regex(), StringLiteral(newValue()))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [regex] is converted to
 * [Expression] of type [RegLanSort] .
 */
fun Expression<StringSort>.replace_re(
    regex: (() -> String),
    newValue: (() -> Expression<StringSort>)
) = this.replace_re(StringLiteral(regex()).toRe(), newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [regex] is converted to
 * [Expression] of type [RegLanSort] .[newValue] is converted to [StringLiteral]
 */
fun Expression<StringSort>.replace_re(regex: (() -> String), newValue: (() -> String)) =
    this.replace_re(StringLiteral(regex()).toRe(), StringLiteral(newValue()))

/** Replace the shortest leftmost match of [regex] in [this] with [newValue]. . */
fun (() -> Expression<StringSort>).replace_re(
    regex: Expression<RegLanSort>,
    newValue: Expression<StringSort>
) = this().replace_re(regex, newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. .[newValue] is
 * converted to [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace_re(regex: Expression<RegLanSort>, newValue: String) =
    this().replace_re(regex, StringLiteral(newValue))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [regex] is converted to
 * [Expression] of type [RegLanSort] .
 */
fun (() -> Expression<StringSort>).replace_re(regex: String, newValue: Expression<StringSort>) =
    this().replace_re(StringLiteral(regex).toRe(), newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [regex] is converted to
 * [Expression] of type [RegLanSort] .[newValue] is converted to [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace_re(regex: String, newValue: String) =
    this().replace_re(StringLiteral(regex).toRe(), StringLiteral(newValue))

/** Replace the shortest leftmost match of [regex] in [this] with [newValue]. . */
fun (() -> Expression<StringSort>).replace_re(
    regex: (() -> Expression<RegLanSort>),
    newValue: Expression<StringSort>
) = this().replace_re(regex(), newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. .[newValue] is
 * converted to [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace_re(
    regex: (() -> Expression<RegLanSort>),
    newValue: String
) = this().replace_re(regex(), StringLiteral(newValue))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [regex] is converted to
 * [Expression] of type [RegLanSort] .
 */
fun (() -> Expression<StringSort>).replace_re(
    regex: (() -> String),
    newValue: Expression<StringSort>
) = this().replace_re(StringLiteral(regex()).toRe(), newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [regex] is converted to
 * [Expression] of type [RegLanSort] .[newValue] is converted to [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace_re(regex: (() -> String), newValue: String) =
    this().replace_re(StringLiteral(regex()).toRe(), StringLiteral(newValue))

/** Replace the shortest leftmost match of [regex] in [this] with [newValue]. . */
fun (() -> Expression<StringSort>).replace_re(
    regex: Expression<RegLanSort>,
    newValue: (() -> Expression<StringSort>)
) = this().replace_re(regex, newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. .[newValue] is
 * converted to [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace_re(
    regex: Expression<RegLanSort>,
    newValue: (() -> String)
) = this().replace_re(regex, StringLiteral(newValue()))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [regex] is converted to
 * [Expression] of type [RegLanSort] .
 */
fun (() -> Expression<StringSort>).replace_re(
    regex: String,
    newValue: (() -> Expression<StringSort>)
) = this().replace_re(StringLiteral(regex).toRe(), newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [regex] is converted to
 * [Expression] of type [RegLanSort] .[newValue] is converted to [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace_re(regex: String, newValue: (() -> String)) =
    this().replace_re(StringLiteral(regex).toRe(), StringLiteral(newValue()))

/** Replace the shortest leftmost match of [regex] in [this] with [newValue]. . */
fun (() -> Expression<StringSort>).replace_re(
    regex: (() -> Expression<RegLanSort>),
    newValue: (() -> Expression<StringSort>)
) = this().replace_re(regex(), newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. .[newValue] is
 * converted to [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace_re(
    regex: (() -> Expression<RegLanSort>),
    newValue: (() -> String)
) = this().replace_re(regex(), StringLiteral(newValue()))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [regex] is converted to
 * [Expression] of type [RegLanSort] .
 */
fun (() -> Expression<StringSort>).replace_re(
    regex: (() -> String),
    newValue: (() -> Expression<StringSort>)
) = this().replace_re(StringLiteral(regex()).toRe(), newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [regex] is converted to
 * [Expression] of type [RegLanSort] .[newValue] is converted to [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace_re(regex: (() -> String), newValue: (() -> String)) =
    this().replace_re(StringLiteral(regex()).toRe(), StringLiteral(newValue()))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .
 */
fun String.replace_re(regex: Expression<RegLanSort>, newValue: Expression<StringSort>) =
    StringLiteral(this).replace_re(regex, newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun String.replace_re(regex: Expression<RegLanSort>, newValue: String) =
    StringLiteral(this).replace_re(regex, StringLiteral(newValue))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [regex] is converted to [Expression] of type [RegLanSort] .
 */
fun String.replace_re(regex: String, newValue: Expression<StringSort>) =
    StringLiteral(this).replace_re(StringLiteral(regex).toRe(), newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [regex] is converted to [Expression] of type [RegLanSort] .[newValue] is
 * converted to [StringLiteral]
 */
fun String.replace_re(regex: String, newValue: String) =
    StringLiteral(this).replace_re(StringLiteral(regex).toRe(), StringLiteral(newValue))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .
 */
fun String.replace_re(regex: (() -> Expression<RegLanSort>), newValue: Expression<StringSort>) =
    StringLiteral(this).replace_re(regex(), newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun String.replace_re(regex: (() -> Expression<RegLanSort>), newValue: String) =
    StringLiteral(this).replace_re(regex(), StringLiteral(newValue))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [regex] is converted to [Expression] of type [RegLanSort] .
 */
fun String.replace_re(regex: (() -> String), newValue: Expression<StringSort>) =
    StringLiteral(this).replace_re(StringLiteral(regex()).toRe(), newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [regex] is converted to [Expression] of type [RegLanSort] .[newValue] is
 * converted to [StringLiteral]
 */
fun String.replace_re(regex: (() -> String), newValue: String) =
    StringLiteral(this).replace_re(StringLiteral(regex()).toRe(), StringLiteral(newValue))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .
 */
fun String.replace_re(regex: Expression<RegLanSort>, newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this).replace_re(regex, newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun String.replace_re(regex: Expression<RegLanSort>, newValue: (() -> String)) =
    StringLiteral(this).replace_re(regex, StringLiteral(newValue()))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [regex] is converted to [Expression] of type [RegLanSort] .
 */
fun String.replace_re(regex: String, newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this).replace_re(StringLiteral(regex).toRe(), newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [regex] is converted to [Expression] of type [RegLanSort] .[newValue] is
 * converted to [StringLiteral]
 */
fun String.replace_re(regex: String, newValue: (() -> String)) =
    StringLiteral(this).replace_re(StringLiteral(regex).toRe(), StringLiteral(newValue()))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .
 */
fun String.replace_re(
    regex: (() -> Expression<RegLanSort>),
    newValue: (() -> Expression<StringSort>)
) = StringLiteral(this).replace_re(regex(), newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun String.replace_re(regex: (() -> Expression<RegLanSort>), newValue: (() -> String)) =
    StringLiteral(this).replace_re(regex(), StringLiteral(newValue()))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [regex] is converted to [Expression] of type [RegLanSort] .
 */
fun String.replace_re(regex: (() -> String), newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this).replace_re(StringLiteral(regex()).toRe(), newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [regex] is converted to [Expression] of type [RegLanSort] .[newValue] is
 * converted to [StringLiteral]
 */
fun String.replace_re(regex: (() -> String), newValue: (() -> String)) =
    StringLiteral(this).replace_re(StringLiteral(regex()).toRe(), StringLiteral(newValue()))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .
 */
fun (() -> String).replace_re(regex: Expression<RegLanSort>, newValue: Expression<StringSort>) =
    StringLiteral(this()).replace_re(regex, newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun (() -> String).replace_re(regex: Expression<RegLanSort>, newValue: String) =
    StringLiteral(this()).replace_re(regex, StringLiteral(newValue))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [regex] is converted to [Expression] of type [RegLanSort] .
 */
fun (() -> String).replace_re(regex: String, newValue: Expression<StringSort>) =
    StringLiteral(this()).replace_re(StringLiteral(regex).toRe(), newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [regex] is converted to [Expression] of type [RegLanSort] .[newValue] is
 * converted to [StringLiteral]
 */
fun (() -> String).replace_re(regex: String, newValue: String) =
    StringLiteral(this()).replace_re(StringLiteral(regex).toRe(), StringLiteral(newValue))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .
 */
fun (() -> String).replace_re(
    regex: (() -> Expression<RegLanSort>),
    newValue: Expression<StringSort>
) = StringLiteral(this()).replace_re(regex(), newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun (() -> String).replace_re(regex: (() -> Expression<RegLanSort>), newValue: String) =
    StringLiteral(this()).replace_re(regex(), StringLiteral(newValue))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [regex] is converted to [Expression] of type [RegLanSort] .
 */
fun (() -> String).replace_re(regex: (() -> String), newValue: Expression<StringSort>) =
    StringLiteral(this()).replace_re(StringLiteral(regex()).toRe(), newValue)

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [regex] is converted to [Expression] of type [RegLanSort] .[newValue] is
 * converted to [StringLiteral]
 */
fun (() -> String).replace_re(regex: (() -> String), newValue: String) =
    StringLiteral(this()).replace_re(StringLiteral(regex()).toRe(), StringLiteral(newValue))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .
 */
fun (() -> String).replace_re(
    regex: Expression<RegLanSort>,
    newValue: (() -> Expression<StringSort>)
) = StringLiteral(this()).replace_re(regex, newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun (() -> String).replace_re(regex: Expression<RegLanSort>, newValue: (() -> String)) =
    StringLiteral(this()).replace_re(regex, StringLiteral(newValue()))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [regex] is converted to [Expression] of type [RegLanSort] .
 */
fun (() -> String).replace_re(regex: String, newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this()).replace_re(StringLiteral(regex).toRe(), newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [regex] is converted to [Expression] of type [RegLanSort] .[newValue] is
 * converted to [StringLiteral]
 */
fun (() -> String).replace_re(regex: String, newValue: (() -> String)) =
    StringLiteral(this()).replace_re(StringLiteral(regex).toRe(), StringLiteral(newValue()))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .
 */
fun (() -> String).replace_re(
    regex: (() -> Expression<RegLanSort>),
    newValue: (() -> Expression<StringSort>)
) = StringLiteral(this()).replace_re(regex(), newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] .[newValue] is converted to [StringLiteral]
 */
fun (() -> String).replace_re(regex: (() -> Expression<RegLanSort>), newValue: (() -> String)) =
    StringLiteral(this()).replace_re(regex(), StringLiteral(newValue()))

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [regex] is converted to [Expression] of type [RegLanSort] .
 */
fun (() -> String).replace_re(regex: (() -> String), newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this()).replace_re(StringLiteral(regex()).toRe(), newValue())

/**
 * Replace the shortest leftmost match of [regex] in [this] with [newValue]. [this] is converted to
 * [StringLiteral] [regex] is converted to [Expression] of type [RegLanSort] .[newValue] is
 * converted to [StringLiteral]
 */
fun (() -> String).replace_re(regex: (() -> String), newValue: (() -> String)) =
    StringLiteral(this()).replace_re(StringLiteral(regex()).toRe(), StringLiteral(newValue()))

/** Replace all matchs of [regex] in [this] with [newValue]. */
fun Expression<StringSort>.replace_re_all(
    regex: Expression<RegLanSort>,
    newValue: Expression<StringSort>
) = StrReplaceAllRegex(this, regex, newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue]. .[newValue] is converted to
 * [StringLiteral]
 */
fun Expression<StringSort>.replace_re_all(regex: Expression<RegLanSort>, newValue: String) =
    this.replace_re_all(regex, StringLiteral(newValue))

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [regex] is converted to [Expression] of
 * type [RegLanSort] .
 */
fun Expression<StringSort>.replace_re_all(regex: String, newValue: Expression<StringSort>) =
    this.replace_re_all(StringLiteral(regex).toRe(), newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [regex] is converted to [Expression] of
 * type [RegLanSort] .[newValue] is converted to [StringLiteral]
 */
fun Expression<StringSort>.replace_re_all(regex: String, newValue: String) =
    this.replace_re_all(StringLiteral(regex).toRe(), StringLiteral(newValue))

/** Replace all matchs of [regex] in [this] with [newValue]. . */
fun Expression<StringSort>.replace_re_all(
    regex: (() -> Expression<RegLanSort>),
    newValue: Expression<StringSort>
) = this.replace_re_all(regex(), newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue]. .[newValue] is converted to
 * [StringLiteral]
 */
fun Expression<StringSort>.replace_re_all(regex: (() -> Expression<RegLanSort>), newValue: String) =
    this.replace_re_all(regex(), StringLiteral(newValue))

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [regex] is converted to [Expression] of
 * type [RegLanSort] .
 */
fun Expression<StringSort>.replace_re_all(regex: (() -> String), newValue: Expression<StringSort>) =
    this.replace_re_all(StringLiteral(regex()).toRe(), newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [regex] is converted to [Expression] of
 * type [RegLanSort] .[newValue] is converted to [StringLiteral]
 */
fun Expression<StringSort>.replace_re_all(regex: (() -> String), newValue: String) =
    this.replace_re_all(StringLiteral(regex()).toRe(), StringLiteral(newValue))

/** Replace all matchs of [regex] in [this] with [newValue]. . */
fun Expression<StringSort>.replace_re_all(
    regex: Expression<RegLanSort>,
    newValue: (() -> Expression<StringSort>)
) = this.replace_re_all(regex, newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue]. .[newValue] is converted to
 * [StringLiteral]
 */
fun Expression<StringSort>.replace_re_all(regex: Expression<RegLanSort>, newValue: (() -> String)) =
    this.replace_re_all(regex, StringLiteral(newValue()))

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [regex] is converted to [Expression] of
 * type [RegLanSort] .
 */
fun Expression<StringSort>.replace_re_all(regex: String, newValue: (() -> Expression<StringSort>)) =
    this.replace_re_all(StringLiteral(regex).toRe(), newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [regex] is converted to [Expression] of
 * type [RegLanSort] .[newValue] is converted to [StringLiteral]
 */
fun Expression<StringSort>.replace_re_all(regex: String, newValue: (() -> String)) =
    this.replace_re_all(StringLiteral(regex).toRe(), StringLiteral(newValue()))

/** Replace all matchs of [regex] in [this] with [newValue]. . */
fun Expression<StringSort>.replace_re_all(
    regex: (() -> Expression<RegLanSort>),
    newValue: (() -> Expression<StringSort>)
) = this.replace_re_all(regex(), newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue]. .[newValue] is converted to
 * [StringLiteral]
 */
fun Expression<StringSort>.replace_re_all(
    regex: (() -> Expression<RegLanSort>),
    newValue: (() -> String)
) = this.replace_re_all(regex(), StringLiteral(newValue()))

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [regex] is converted to [Expression] of
 * type [RegLanSort] .
 */
fun Expression<StringSort>.replace_re_all(
    regex: (() -> String),
    newValue: (() -> Expression<StringSort>)
) = this.replace_re_all(StringLiteral(regex()).toRe(), newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [regex] is converted to [Expression] of
 * type [RegLanSort] .[newValue] is converted to [StringLiteral]
 */
fun Expression<StringSort>.replace_re_all(regex: (() -> String), newValue: (() -> String)) =
    this.replace_re_all(StringLiteral(regex()).toRe(), StringLiteral(newValue()))

/** Replace all matchs of [regex] in [this] with [newValue]. . */
fun (() -> Expression<StringSort>).replace_re_all(
    regex: Expression<RegLanSort>,
    newValue: Expression<StringSort>
) = this().replace_re_all(regex, newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue]. .[newValue] is converted to
 * [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace_re_all(regex: Expression<RegLanSort>, newValue: String) =
    this().replace_re_all(regex, StringLiteral(newValue))

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [regex] is converted to [Expression] of
 * type [RegLanSort] .
 */
fun (() -> Expression<StringSort>).replace_re_all(regex: String, newValue: Expression<StringSort>) =
    this().replace_re_all(StringLiteral(regex).toRe(), newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [regex] is converted to [Expression] of
 * type [RegLanSort] .[newValue] is converted to [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace_re_all(regex: String, newValue: String) =
    this().replace_re_all(StringLiteral(regex).toRe(), StringLiteral(newValue))

/** Replace all matchs of [regex] in [this] with [newValue]. . */
fun (() -> Expression<StringSort>).replace_re_all(
    regex: (() -> Expression<RegLanSort>),
    newValue: Expression<StringSort>
) = this().replace_re_all(regex(), newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue]. .[newValue] is converted to
 * [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace_re_all(
    regex: (() -> Expression<RegLanSort>),
    newValue: String
) = this().replace_re_all(regex(), StringLiteral(newValue))

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [regex] is converted to [Expression] of
 * type [RegLanSort] .
 */
fun (() -> Expression<StringSort>).replace_re_all(
    regex: (() -> String),
    newValue: Expression<StringSort>
) = this().replace_re_all(StringLiteral(regex()).toRe(), newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [regex] is converted to [Expression] of
 * type [RegLanSort] .[newValue] is converted to [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace_re_all(regex: (() -> String), newValue: String) =
    this().replace_re_all(StringLiteral(regex()).toRe(), StringLiteral(newValue))

/** Replace all matchs of [regex] in [this] with [newValue]. . */
fun (() -> Expression<StringSort>).replace_re_all(
    regex: Expression<RegLanSort>,
    newValue: (() -> Expression<StringSort>)
) = this().replace_re_all(regex, newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue]. .[newValue] is converted to
 * [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace_re_all(
    regex: Expression<RegLanSort>,
    newValue: (() -> String)
) = this().replace_re_all(regex, StringLiteral(newValue()))

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [regex] is converted to [Expression] of
 * type [RegLanSort] .
 */
fun (() -> Expression<StringSort>).replace_re_all(
    regex: String,
    newValue: (() -> Expression<StringSort>)
) = this().replace_re_all(StringLiteral(regex).toRe(), newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [regex] is converted to [Expression] of
 * type [RegLanSort] .[newValue] is converted to [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace_re_all(regex: String, newValue: (() -> String)) =
    this().replace_re_all(StringLiteral(regex).toRe(), StringLiteral(newValue()))

/** Replace all matchs of [regex] in [this] with [newValue]. . */
fun (() -> Expression<StringSort>).replace_re_all(
    regex: (() -> Expression<RegLanSort>),
    newValue: (() -> Expression<StringSort>)
) = this().replace_re_all(regex(), newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue]. .[newValue] is converted to
 * [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace_re_all(
    regex: (() -> Expression<RegLanSort>),
    newValue: (() -> String)
) = this().replace_re_all(regex(), StringLiteral(newValue()))

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [regex] is converted to [Expression] of
 * type [RegLanSort] .
 */
fun (() -> Expression<StringSort>).replace_re_all(
    regex: (() -> String),
    newValue: (() -> Expression<StringSort>)
) = this().replace_re_all(StringLiteral(regex()).toRe(), newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [regex] is converted to [Expression] of
 * type [RegLanSort] .[newValue] is converted to [StringLiteral]
 */
fun (() -> Expression<StringSort>).replace_re_all(regex: (() -> String), newValue: (() -> String)) =
    this().replace_re_all(StringLiteral(regex()).toRe(), StringLiteral(newValue()))

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral] .
 */
fun String.replace_re_all(regex: Expression<RegLanSort>, newValue: Expression<StringSort>) =
    StringLiteral(this).replace_re_all(regex, newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral]
 * .[newValue] is converted to [StringLiteral]
 */
fun String.replace_re_all(regex: Expression<RegLanSort>, newValue: String) =
    StringLiteral(this).replace_re_all(regex, StringLiteral(newValue))

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral]
 * [regex] is converted to [Expression] of type [RegLanSort] .
 */
fun String.replace_re_all(regex: String, newValue: Expression<StringSort>) =
    StringLiteral(this).replace_re_all(StringLiteral(regex).toRe(), newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral]
 * [regex] is converted to [Expression] of type [RegLanSort] .[newValue] is converted to
 * [StringLiteral]
 */
fun String.replace_re_all(regex: String, newValue: String) =
    StringLiteral(this).replace_re_all(StringLiteral(regex).toRe(), StringLiteral(newValue))

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral] .
 */
fun String.replace_re_all(regex: (() -> Expression<RegLanSort>), newValue: Expression<StringSort>) =
    StringLiteral(this).replace_re_all(regex(), newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral]
 * .[newValue] is converted to [StringLiteral]
 */
fun String.replace_re_all(regex: (() -> Expression<RegLanSort>), newValue: String) =
    StringLiteral(this).replace_re_all(regex(), StringLiteral(newValue))

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral]
 * [regex] is converted to [Expression] of type [RegLanSort] .
 */
fun String.replace_re_all(regex: (() -> String), newValue: Expression<StringSort>) =
    StringLiteral(this).replace_re_all(StringLiteral(regex()).toRe(), newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral]
 * [regex] is converted to [Expression] of type [RegLanSort] .[newValue] is converted to
 * [StringLiteral]
 */
fun String.replace_re_all(regex: (() -> String), newValue: String) =
    StringLiteral(this).replace_re_all(StringLiteral(regex()).toRe(), StringLiteral(newValue))

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral] .
 */
fun String.replace_re_all(regex: Expression<RegLanSort>, newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this).replace_re_all(regex, newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral]
 * .[newValue] is converted to [StringLiteral]
 */
fun String.replace_re_all(regex: Expression<RegLanSort>, newValue: (() -> String)) =
    StringLiteral(this).replace_re_all(regex, StringLiteral(newValue()))

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral]
 * [regex] is converted to [Expression] of type [RegLanSort] .
 */
fun String.replace_re_all(regex: String, newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this).replace_re_all(StringLiteral(regex).toRe(), newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral]
 * [regex] is converted to [Expression] of type [RegLanSort] .[newValue] is converted to
 * [StringLiteral]
 */
fun String.replace_re_all(regex: String, newValue: (() -> String)) =
    StringLiteral(this).replace_re_all(StringLiteral(regex).toRe(), StringLiteral(newValue()))

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral] .
 */
fun String.replace_re_all(
    regex: (() -> Expression<RegLanSort>),
    newValue: (() -> Expression<StringSort>)
) = StringLiteral(this).replace_re_all(regex(), newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral]
 * .[newValue] is converted to [StringLiteral]
 */
fun String.replace_re_all(regex: (() -> Expression<RegLanSort>), newValue: (() -> String)) =
    StringLiteral(this).replace_re_all(regex(), StringLiteral(newValue()))

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral]
 * [regex] is converted to [Expression] of type [RegLanSort] .
 */
fun String.replace_re_all(regex: (() -> String), newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this).replace_re_all(StringLiteral(regex()).toRe(), newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral]
 * [regex] is converted to [Expression] of type [RegLanSort] .[newValue] is converted to
 * [StringLiteral]
 */
fun String.replace_re_all(regex: (() -> String), newValue: (() -> String)) =
    StringLiteral(this).replace_re_all(StringLiteral(regex()).toRe(), StringLiteral(newValue()))

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral] .
 */
fun (() -> String).replace_re_all(regex: Expression<RegLanSort>, newValue: Expression<StringSort>) =
    StringLiteral(this()).replace_re_all(regex, newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral]
 * .[newValue] is converted to [StringLiteral]
 */
fun (() -> String).replace_re_all(regex: Expression<RegLanSort>, newValue: String) =
    StringLiteral(this()).replace_re_all(regex, StringLiteral(newValue))

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral]
 * [regex] is converted to [Expression] of type [RegLanSort] .
 */
fun (() -> String).replace_re_all(regex: String, newValue: Expression<StringSort>) =
    StringLiteral(this()).replace_re_all(StringLiteral(regex).toRe(), newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral]
 * [regex] is converted to [Expression] of type [RegLanSort] .[newValue] is converted to
 * [StringLiteral]
 */
fun (() -> String).replace_re_all(regex: String, newValue: String) =
    StringLiteral(this()).replace_re_all(StringLiteral(regex).toRe(), StringLiteral(newValue))

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral] .
 */
fun (() -> String).replace_re_all(
    regex: (() -> Expression<RegLanSort>),
    newValue: Expression<StringSort>
) = StringLiteral(this()).replace_re_all(regex(), newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral]
 * .[newValue] is converted to [StringLiteral]
 */
fun (() -> String).replace_re_all(regex: (() -> Expression<RegLanSort>), newValue: String) =
    StringLiteral(this()).replace_re_all(regex(), StringLiteral(newValue))

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral]
 * [regex] is converted to [Expression] of type [RegLanSort] .
 */
fun (() -> String).replace_re_all(regex: (() -> String), newValue: Expression<StringSort>) =
    StringLiteral(this()).replace_re_all(StringLiteral(regex()).toRe(), newValue)

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral]
 * [regex] is converted to [Expression] of type [RegLanSort] .[newValue] is converted to
 * [StringLiteral]
 */
fun (() -> String).replace_re_all(regex: (() -> String), newValue: String) =
    StringLiteral(this()).replace_re_all(StringLiteral(regex()).toRe(), StringLiteral(newValue))

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral] .
 */
fun (() -> String).replace_re_all(
    regex: Expression<RegLanSort>,
    newValue: (() -> Expression<StringSort>)
) = StringLiteral(this()).replace_re_all(regex, newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral]
 * .[newValue] is converted to [StringLiteral]
 */
fun (() -> String).replace_re_all(regex: Expression<RegLanSort>, newValue: (() -> String)) =
    StringLiteral(this()).replace_re_all(regex, StringLiteral(newValue()))

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral]
 * [regex] is converted to [Expression] of type [RegLanSort] .
 */
fun (() -> String).replace_re_all(regex: String, newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this()).replace_re_all(StringLiteral(regex).toRe(), newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral]
 * [regex] is converted to [Expression] of type [RegLanSort] .[newValue] is converted to
 * [StringLiteral]
 */
fun (() -> String).replace_re_all(regex: String, newValue: (() -> String)) =
    StringLiteral(this()).replace_re_all(StringLiteral(regex).toRe(), StringLiteral(newValue()))

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral] .
 */
fun (() -> String).replace_re_all(
    regex: (() -> Expression<RegLanSort>),
    newValue: (() -> Expression<StringSort>)
) = StringLiteral(this()).replace_re_all(regex(), newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral]
 * .[newValue] is converted to [StringLiteral]
 */
fun (() -> String).replace_re_all(regex: (() -> Expression<RegLanSort>), newValue: (() -> String)) =
    StringLiteral(this()).replace_re_all(regex(), StringLiteral(newValue()))

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral]
 * [regex] is converted to [Expression] of type [RegLanSort] .
 */
fun (() -> String).replace_re_all(regex: (() -> String), newValue: (() -> Expression<StringSort>)) =
    StringLiteral(this()).replace_re_all(StringLiteral(regex()).toRe(), newValue())

/**
 * Replace all matchs of [regex] in [this] with [newValue]. [this] is converted to [StringLiteral]
 * [regex] is converted to [Expression] of type [RegLanSort] .[newValue] is converted to
 * [StringLiteral]
 */
fun (() -> String).replace_re_all(regex: (() -> String), newValue: (() -> String)) =
    StringLiteral(this()).replace_re_all(StringLiteral(regex()).toRe(), StringLiteral(newValue()))

/** Regex complement. */
fun Expression<RegLanSort>.comp() = RegexComp(this)

/** Regex complement. [this] is converted to [Expression] of type [RegLanSort] */
fun String.comp() = StringLiteral(this).toRe().comp()

/** Regex complement. */
fun (() -> Expression<RegLanSort>).comp() = this().comp()

/** Regex complement. [this] is converted to [Expression] of type [RegLanSort] */
fun (() -> String).comp() = StringLiteral(this()).toRe().comp()

/** Regex difference. */
infix fun Expression<RegLanSort>.diff(rhs: Expression<RegLanSort>) =
    if (this is RegexDiff) {
      RegexDiff(this.children + rhs)
    } else {
      RegexDiff(this, rhs)
    }

/** Regex difference. [rhs] is converted to [Expression] of type [RegLanSort] . */
infix fun Expression<RegLanSort>.diff(rhs: String) = this diff StringLiteral(rhs).toRe()

/** Regex difference. . */
infix fun Expression<RegLanSort>.diff(rhs: (() -> Expression<RegLanSort>)) = this diff rhs()

/** Regex difference. [rhs] is converted to [Expression] of type [RegLanSort] . */
infix fun Expression<RegLanSort>.diff(rhs: (() -> String)) = this diff StringLiteral(rhs()).toRe()

/** Regex difference. */
infix fun (() -> Expression<RegLanSort>).diff(rhs: Expression<RegLanSort>) = this() diff rhs

/** Regex difference. [rhs] is converted to [Expression] of type [RegLanSort] */
infix fun (() -> Expression<RegLanSort>).diff(rhs: String) = this() diff StringLiteral(rhs).toRe()

/** Regex difference. */
infix fun (() -> Expression<RegLanSort>).diff(rhs: (() -> Expression<RegLanSort>)) =
    this() diff rhs()

/** Regex difference. [rhs] is converted to [Expression] of type [RegLanSort] */
infix fun (() -> Expression<RegLanSort>).diff(rhs: (() -> String)) =
    this() diff StringLiteral(rhs()).toRe()

/** Regex difference. [String] is converted to [Expression] of type [RegLanSort] . */
infix fun String.diff(rhs: Expression<RegLanSort>) = StringLiteral(this).toRe() diff rhs

/**
 * Regex difference. [String] is converted to [Expression] of type [RegLanSort] [rhs] is converted
 * to [Expression] of type [RegLanSort] .
 */
infix fun String.diff(rhs: String) = StringLiteral(this).toRe() diff StringLiteral(rhs).toRe()

/** Regex difference. [String] is converted to [Expression] of type [RegLanSort] . */
infix fun String.diff(rhs: (() -> Expression<RegLanSort>)) = StringLiteral(this).toRe() diff rhs()

/**
 * Regex difference. [String] is converted to [Expression] of type [RegLanSort] [rhs] is converted
 * to [Expression] of type [RegLanSort] .
 */
infix fun String.diff(rhs: (() -> String)) =
    StringLiteral(this).toRe() diff StringLiteral(rhs()).toRe()

/** Regex difference. */
infix fun (() -> String).diff(rhs: Expression<RegLanSort>) = StringLiteral(this()).toRe() diff rhs

/** Regex difference. [rhs] is converted to [Expression] of type [RegLanSort] */
infix fun (() -> String).diff(rhs: String) =
    StringLiteral(this()).toRe() diff StringLiteral(rhs).toRe()

/** Regex difference. */
infix fun (() -> String).diff(rhs: (() -> Expression<RegLanSort>)) =
    StringLiteral(this()).toRe() diff rhs()

/** Regex difference. [rhs] is converted to [Expression] of type [RegLanSort] */
infix fun (() -> String).diff(rhs: (() -> String)) =
    StringLiteral(this()).toRe() diff StringLiteral(rhs()).toRe()

/** Regex Kleene cross. */
fun Expression<RegLanSort>.plus() = RegexPlus(this)

/** Regex Kleene cross. [this] is converted to [Expression] of type [RegLanSort] */
fun String.plus() = StringLiteral(this).toRe().plus()

/** Regex Kleene cross. */
fun (() -> Expression<RegLanSort>).plus() = this().plus()

/** Regex Kleene cross. [this] is converted to [Expression] of type [RegLanSort] */
fun (() -> String).plus() = StringLiteral(this()).toRe().plus()

/** Regex option. */
fun Expression<RegLanSort>.opt() = RegexOption(this)

/** Regex option. [this] is converted to [Expression] of type [RegLanSort] */
fun String.opt() = StringLiteral(this).toRe().opt()

/** Regex option. */
fun (() -> Expression<RegLanSort>).opt() = this().opt()

/** Regex option. [this] is converted to [Expression] of type [RegLanSort] */
fun (() -> String).opt() = StringLiteral(this()).toRe().opt()

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language.
 */
infix fun Expression<StringSort>.range(end: Expression<StringSort>) = RegexRange(this, end)

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language. [end] is converted to [StringLiteral] .
 */
infix fun Expression<StringSort>.range(end: String) = this range StringLiteral(end)

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language. .
 */
infix fun Expression<StringSort>.range(end: (() -> Expression<StringSort>)) = this range end()

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language. [end] is converted to [StringLiteral] .
 */
infix fun Expression<StringSort>.range(end: (() -> String)) = this range StringLiteral(end())

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language.
 */
infix fun (() -> Expression<StringSort>).range(end: Expression<StringSort>) = this() range end

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language. [end] is converted to [StringLiteral]
 */
infix fun (() -> Expression<StringSort>).range(end: String) = this() range StringLiteral(end)

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language.
 */
infix fun (() -> Expression<StringSort>).range(end: (() -> Expression<StringSort>)) =
    this() range end()

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language. [end] is converted to [StringLiteral]
 */
infix fun (() -> Expression<StringSort>).range(end: (() -> String)) =
    this() range StringLiteral(end())

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language. [String] is converted to [StringLiteral] .
 */
infix fun String.range(end: Expression<StringSort>) = StringLiteral(this) range end

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language. [String] is converted to [StringLiteral] [end] is converted to
 * [StringLiteral] .
 */
infix fun String.range(end: String) = StringLiteral(this) range StringLiteral(end)

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language. [String] is converted to [StringLiteral] .
 */
infix fun String.range(end: (() -> Expression<StringSort>)) = StringLiteral(this) range end()

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language. [String] is converted to [StringLiteral] [end] is converted to
 * [StringLiteral] .
 */
infix fun String.range(end: (() -> String)) = StringLiteral(this) range StringLiteral(end())

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language.
 */
infix fun (() -> String).range(end: Expression<StringSort>) = StringLiteral(this()) range end

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language. [end] is converted to [StringLiteral]
 */
infix fun (() -> String).range(end: String) = StringLiteral(this()) range StringLiteral(end)

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language.
 */
infix fun (() -> String).range(end: (() -> Expression<StringSort>)) =
    StringLiteral(this()) range end()

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language. [end] is converted to [StringLiteral]
 */
infix fun (() -> String).range(end: (() -> String)) =
    StringLiteral(this()) range StringLiteral(end())

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language.
 */
infix fun Expression<StringSort>.rangeTo(end: Expression<StringSort>) = RegexRange(this, end)

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language. [end] is converted to [StringLiteral]
 */
infix operator fun Expression<StringSort>.rangeTo(end: String) = this rangeTo StringLiteral(end)

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language.
 */
infix operator fun Expression<StringSort>.rangeTo(end: (() -> Expression<StringSort>)) =
    this rangeTo end()

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language. [end] is converted to [StringLiteral]
 */
infix operator fun Expression<StringSort>.rangeTo(end: (() -> String)) =
    this rangeTo StringLiteral(end())

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language.
 */
infix operator fun (() -> Expression<StringSort>).rangeTo(end: Expression<StringSort>) =
    this() rangeTo end

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language. [end] is converted to [StringLiteral]
 */
infix operator fun (() -> Expression<StringSort>).rangeTo(end: String) =
    this() rangeTo StringLiteral(end)

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language.
 */
infix operator fun (() -> Expression<StringSort>).rangeTo(end: (() -> Expression<StringSort>)) =
    this() rangeTo end()

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language. [end] is converted to [StringLiteral]
 */
infix operator fun (() -> Expression<StringSort>).rangeTo(end: (() -> String)) =
    this() rangeTo StringLiteral(end())

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language. [String] is converted to [StringLiteral]
 */
infix operator fun String.rangeTo(end: Expression<StringSort>) = StringLiteral(this) rangeTo end

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language. [String] is converted to [StringLiteral] [end] is converted to
 * [StringLiteral]
 */
infix operator fun String.rangeTo(end: String) = StringLiteral(this) rangeTo StringLiteral(end)

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language. [String] is converted to [StringLiteral]
 */
infix operator fun String.rangeTo(end: (() -> Expression<StringSort>)) =
    StringLiteral(this) rangeTo end()

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language. [String] is converted to [StringLiteral] [end] is converted to
 * [StringLiteral]
 */
infix operator fun String.rangeTo(end: (() -> String)) =
    StringLiteral(this) rangeTo StringLiteral(end())

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language.
 */
infix operator fun (() -> String).rangeTo(end: Expression<StringSort>) =
    StringLiteral(this()) rangeTo end

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language. [end] is converted to [StringLiteral]
 */
infix operator fun (() -> String).rangeTo(end: String) =
    StringLiteral(this()) rangeTo StringLiteral(end)

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language.
 */
infix operator fun (() -> String).rangeTo(end: (() -> Expression<StringSort>)) =
    StringLiteral(this()) rangeTo end()

/**
 * Set of all singleton strings from [this] to [end], where [this] <= [end], otherwise evaluates to
 * the empty language. [end] is converted to [StringLiteral]
 */
infix operator fun (() -> String).rangeTo(end: (() -> String)) =
    StringLiteral(this()) rangeTo StringLiteral(end())

/** Regex power. */
fun Expression<RegLanSort>.power(n: Int) = RegexPower(this, n)

/** Regex power. */
fun (() -> Expression<RegLanSort>).power(n: Int) = RegexPower(this(), n)

/** Regex power. */
fun String.power(n: Int) = RegexPower(StringLiteral(this).toRe(), n)

/** Regex power. */
fun (() -> String).power(n: Int) = RegexPower(StringLiteral(this()).toRe(), n)

/** Regex loop. */
fun Expression<RegLanSort>.loop(n: Int, m: Int) = RegexLoop(this, n, m)

/** Regex loop. */
fun (() -> Expression<RegLanSort>).loop(n: Int, m: Int) = RegexLoop(this(), n, m)

/** Regex loop. */
fun String.loop(n: Int, m: Int) = RegexLoop(StringLiteral(this).toRe(), n, m)

/** Regex loop. */
fun (() -> String).loop(n: Int, m: Int) = RegexLoop(StringLiteral(this()).toRe(), n, m)

/**
 * Digit check. Evaluates to true iff [this] consists of a single character which is a decimal
 * digit.
 */
fun Expression<StringSort>.isDigit() = StrIsDigit(this)

/**
 * Digit check. Evaluates to true iff [this] consists of a single character which is a decimal
 * digit. [this] is converted to [StringLiteral]
 */
fun String.isDigit() = StringLiteral(this).isDigit()

/**
 * Digit check. Evaluates to true iff [this] consists of a single character which is a decimal
 * digit.
 */
fun (() -> Expression<StringSort>).isDigit() = this().isDigit()

/**
 * Digit check. Evaluates to true iff [this] consists of a single character which is a decimal
 * digit. [this] is converted to [StringLiteral]
 */
fun (() -> String).isDigit() = StringLiteral(this()).isDigit()

/**
 * Evaluates to the code point of [this], iff [this] is a singleton string, otherwise evaluates to
 * -1.
 */
fun Expression<StringSort>.toCode() = StrToCode(this)

/**
 * Evaluates to the code point of [this], iff [this] is a singleton string, otherwise evaluates to
 * -1. [this] is converted to [StringLiteral]
 */
fun String.toCode() = StringLiteral(this).toCode()

/**
 * Evaluates to the code point of [this], iff [this] is a singleton string, otherwise evaluates to
 * -1.
 */
fun (() -> Expression<StringSort>).toCode() = this().toCode()

/**
 * Evaluates to the code point of [this], iff [this] is a singleton string, otherwise evaluates to
 * -1. [this] is converted to [StringLiteral]
 */
fun (() -> String).toCode() = StringLiteral(this()).toCode()

/** Conversion from code point. */
fun Expression<IntSort>.fromCode() = StrFromCode(this)

/** Conversion from code point. [this] is converted to [IntLiteral] */
fun Byte.fromCode() = IntLiteral(this).fromCode()

/** Conversion from code point. [this] is converted to [IntLiteral] */
fun Short.fromCode() = IntLiteral(this).fromCode()

/** Conversion from code point. [this] is converted to [IntLiteral] */
fun Int.fromCode() = IntLiteral(this).fromCode()

/** Conversion from code point. [this] is converted to [IntLiteral] */
fun Long.fromCode() = IntLiteral(this).fromCode()

/** Conversion from code point. [this] is converted to [IntLiteral] */
fun BigInteger.fromCode() = IntLiteral(this).fromCode()

/** Conversion from code point. */
fun (() -> Expression<IntSort>).fromCode() = this().fromCode()

/** Conversion from code point. [this] is converted to [IntLiteral] */
fun (() -> Byte).fromCode() = IntLiteral(this()).fromCode()

/** Conversion from code point. [this] is converted to [IntLiteral] */
fun (() -> Short).fromCode() = IntLiteral(this()).fromCode()

/** Conversion from code point. [this] is converted to [IntLiteral] */
fun (() -> Int).fromCode() = IntLiteral(this()).fromCode()

/** Conversion from code point. [this] is converted to [IntLiteral] */
fun (() -> Long).fromCode() = IntLiteral(this()).fromCode()

/** Conversion from code point. [this] is converted to [IntLiteral] */
fun (() -> BigInteger).fromCode() = IntLiteral(this()).fromCode()

/** Conversion to integers. */
fun Expression<StringSort>.toSMTInt() = StrToInt(this)

/** Conversion to integers. [this] is converted to [StringLiteral] */
fun String.toSMTInt() = StringLiteral(this).toSMTInt()

/** Conversion to integers. */
fun (() -> Expression<StringSort>).toSMTInt() = this().toSMTInt()

/** Conversion to integers. [this] is converted to [StringLiteral] */
fun (() -> String).toSMTInt() = StringLiteral(this()).toSMTInt()

/** Conversion from integers. */
fun Expression<IntSort>.fromInt() = StrFromInt(this)

/** Conversion from integers. [this] is converted to [IntLiteral] */
fun Byte.fromInt() = IntLiteral(this).fromInt()

/** Conversion from integers. [this] is converted to [IntLiteral] */
fun Short.fromInt() = IntLiteral(this).fromInt()

/** Conversion from integers. [this] is converted to [IntLiteral] */
fun Int.fromInt() = IntLiteral(this).fromInt()

/** Conversion from integers. [this] is converted to [IntLiteral] */
fun Long.fromInt() = IntLiteral(this).fromInt()

/** Conversion from integers. [this] is converted to [IntLiteral] */
fun BigInteger.fromInt() = IntLiteral(this).fromInt()

/** Conversion from integers. */
fun (() -> Expression<IntSort>).fromInt() = this().fromInt()

/** Conversion from integers. [this] is converted to [IntLiteral] */
fun (() -> Byte).fromInt() = IntLiteral(this()).fromInt()

/** Conversion from integers. [this] is converted to [IntLiteral] */
fun (() -> Short).fromInt() = IntLiteral(this()).fromInt()

/** Conversion from integers. [this] is converted to [IntLiteral] */
fun (() -> Int).fromInt() = IntLiteral(this()).fromInt()

/** Conversion from integers. [this] is converted to [IntLiteral] */
fun (() -> Long).fromInt() = IntLiteral(this()).fromInt()

/** Conversion from integers. [this] is converted to [IntLiteral] */
fun (() -> BigInteger).fromInt() = IntLiteral(this()).fromInt()

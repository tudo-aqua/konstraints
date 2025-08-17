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

package tools.aqua.konstraints.smt

import tools.aqua.konstraints.parser.*

/*
 * String functions
 */

/**
 * String concatenation
 *
 * (str.++ String String String :left-assoc)
 */
class StrConcat(val strings: List<Expression<StringSort>>) :
    HomogenousExpression<StringSort, StringSort>("str.++".toSymbolWithQuotes(), SMTString) {
  override val theories = STRINGS_MARKER_SET

  constructor(vararg strings: Expression<StringSort>) : this(strings.toList())

  override val children: List<Expression<StringSort>> = strings

  override fun copy(children: List<Expression<*>>): Expression<StringSort> =
      StrConcatDecl.constructDynamic(children, emptyList())
}

/**
 * String length
 *
 * (str.len String Int)
 */
class StrLength(override val inner: Expression<StringSort>) :
    UnaryExpression<IntSort, StringSort>("str.len".toSymbolWithQuotes(), SMTInt) {
  override val theories = STRINGS_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      StrLengthDecl.constructDynamic(children, emptyList())
}

/**
 * Lexicographic ordering
 *
 * (str.< String String Bool :chainable)
 */
class StrLexOrder(val strings: List<Expression<StringSort>>) :
    HomogenousExpression<BoolSort, StringSort>("str.<".toSymbolWithQuotes(), Bool) {
  override val theories = STRINGS_MARKER_SET

  constructor(vararg strings: Expression<StringSort>) : this(strings.toList())

  override val children: List<Expression<StringSort>> = strings

  init {
    require(strings.size > 1) {
      "Lexicographic order needs at least two strings but ${strings.size} were given!"
    }
  }

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      StrLexOrderDecl.constructDynamic(children, emptyList())
}

/*
 * Regular expression functions
 */

/**
 * String to RE injection
 *
 * (str.to_re String RegLan)
 */
class ToRegex(override val inner: Expression<StringSort>) :
    UnaryExpression<RegLanSort, StringSort>("str.to_reg".toSymbolWithQuotes(), RegLan) {
  override val theories = STRINGS_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<RegLanSort> =
      ToRegexDecl.constructDynamic(children, emptyList())
}

/**
 * RE membership
 *
 * (str.in_re String RegLan Bool)
 */
class InRegex(val inner: Expression<StringSort>, val regex: Expression<RegLanSort>) :
    BinaryExpression<BoolSort, StringSort, RegLanSort>("str.in_reg".toSymbolWithQuotes(), Bool) {
  override val theories = STRINGS_MARKER_SET

  override val lhs: Expression<StringSort> = inner

  override val rhs: Expression<RegLanSort> = regex

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      InRegexDecl.constructDynamic(children, emptyList())
}

/**
 * Constant denoting the empty set of strings
 *
 * (re.none RegLan)
 */
object RegexNone : ConstantExpression<RegLanSort>("re.none".toSymbolWithQuotes(), RegLan) {
  override val theories = setOf(Theories.STRINGS)

  override fun copy(children: List<Expression<*>>): Expression<RegLanSort> = this
}

/**
 * Constant denoting the set of all strings
 *
 * (re.all RegLan)
 */
object RegexAll : ConstantExpression<RegLanSort>("re.all".toSymbolWithQuotes(), RegLan) {
  override val theories = setOf(Theories.STRINGS)

  override fun copy(children: List<Expression<*>>): Expression<RegLanSort> = this
}

/**
 * Constant denoting the set of all strings of length 1
 *
 * (re.allchar RegLan)
 */
object RegexAllChar : ConstantExpression<RegLanSort>("re.allchar".toSymbolWithQuotes(), RegLan) {
  override val theories = setOf(Theories.STRINGS)

  override fun copy(children: List<Expression<*>>): Expression<RegLanSort> = this
}

/**
 * RE concatenation
 *
 * (re.++ RegLan RegLan RegLan :left-assoc)
 */
class RegexConcat(val regex: List<Expression<RegLanSort>>) :
    HomogenousExpression<RegLanSort, RegLanSort>("re.++".toSymbolWithQuotes(), RegLan) {
  override val theories = STRINGS_MARKER_SET

  constructor(vararg regex: Expression<RegLanSort>) : this(regex.toList())

  override val children: List<Expression<RegLanSort>> = regex

  override fun copy(children: List<Expression<*>>): Expression<RegLanSort> =
      RegexConcatDecl.constructDynamic(children, emptyList())
}

/**
 * RE union
 *
 * (re.union RegLan RegLan RegLan :left-assoc)
 */
class RegexUnion(val regex: List<Expression<RegLanSort>>) :
    HomogenousExpression<RegLanSort, RegLanSort>("re.union".toSymbolWithQuotes(), RegLan) {
  override val theories = STRINGS_MARKER_SET

  constructor(vararg regex: Expression<RegLanSort>) : this(regex.toList())

  override val children: List<Expression<RegLanSort>> = regex

  override fun copy(children: List<Expression<*>>): Expression<RegLanSort> =
      RegexUnionDecl.constructDynamic(children, emptyList())
}

/**
 * RE intersection
 *
 * (re.inter RegLan RegLan RegLan :left-assoc)
 */
class RegexIntersec(val regex: List<Expression<RegLanSort>>) :
    HomogenousExpression<RegLanSort, RegLanSort>("re.inter".toSymbolWithQuotes(), RegLan) {
  override val theories = STRINGS_MARKER_SET

  constructor(vararg regex: Expression<RegLanSort>) : this(regex.toList())

  override val children: List<Expression<RegLanSort>> = regex

  override fun copy(children: List<Expression<*>>): Expression<RegLanSort> =
      RegexIntersecDecl.constructDynamic(children, emptyList())
}

/**
 * Kleene Closure
 *
 * (re.* RegLan RegLan)
 */
class RegexStar(override val inner: Expression<RegLanSort>) :
    UnaryExpression<RegLanSort, RegLanSort>("re.*".toSymbolWithQuotes(), RegLan) {
  override val theories = STRINGS_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<RegLanSort> =
      RegexStarDecl.constructDynamic(children, emptyList())
}

/*
 * Additional functions
 */

/**
 * Reflexive closure of lexicographic ordering
 *
 * (str.<= String String Bool :chainable)
 */
class StrRefLexOrder(val strings: List<Expression<StringSort>>) :
    HomogenousExpression<BoolSort, StringSort>("str.<=".toSymbolWithQuotes(), Bool) {
  override val theories = STRINGS_MARKER_SET

  constructor(vararg strings: Expression<StringSort>) : this(strings.toList())

  override val children: List<Expression<StringSort>> = strings

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      StrRefLexOrderDecl.constructDynamic(children, emptyList())
}

/**
 * Singleton string containing a character at given position or empty string when position is out of
 * range. The leftmost position is 0.
 *
 * (str.at String Int String)
 */
class StrAt(val inner: Expression<StringSort>, val position: Expression<IntSort>) :
    BinaryExpression<StringSort, StringSort, IntSort>("str.at".toSymbolWithQuotes(), SMTString) {
  override val theories = STRINGS_MARKER_SET

  override val lhs: Expression<StringSort> = inner

  override val rhs: Expression<IntSort> = position

  override fun copy(children: List<Expression<*>>): Expression<StringSort> =
      StrAtDecl.constructDynamic(children, emptyList())
}

/**
 * Substring
 *
 * (str.substr String Int Int String)
 */
class StrSubstring(
    val inner: Expression<StringSort>,
    val start: Expression<IntSort>,
    val length: Expression<IntSort>
) :
    TernaryExpression<StringSort, StringSort, IntSort, IntSort>(
        "str.substr".toSymbolWithQuotes(), SMTString) {
  override val theories = STRINGS_MARKER_SET

  override val lhs: Expression<StringSort> = inner

  override val mid: Expression<IntSort> = start

  override val rhs: Expression<IntSort> = length

  override fun copy(children: List<Expression<*>>): Expression<StringSort> =
      StrSubstringDecl.constructDynamic(children, emptyList())
}

/**
 * [prefix] is a prefix of [inner]
 *
 * (str.prefixof String String Bool)
 */
class StrPrefixOf(val prefix: Expression<StringSort>, val inner: Expression<StringSort>) :
    BinaryExpression<BoolSort, StringSort, StringSort>("str.prefixof".toSymbolWithQuotes(), Bool) {
  override val theories = STRINGS_MARKER_SET

  override val lhs: Expression<StringSort> = prefix

  override val rhs: Expression<StringSort> = inner

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      StrPrefixOfDecl.constructDynamic(children, emptyList())
}

/**
 * [suffix] is a suffix of [inner]
 *
 * (str.suffixof String String Bool)
 */
class StrSuffixOf(val suffix: Expression<StringSort>, val inner: Expression<StringSort>) :
    BinaryExpression<BoolSort, StringSort, StringSort>("str.suffixof".toSymbolWithQuotes(), Bool) {
  override val theories = STRINGS_MARKER_SET

  override val lhs: Expression<StringSort> = suffix

  override val rhs: Expression<StringSort> = inner

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      StrSuffixOfDecl.constructDynamic(children, emptyList())
}

/**
 * [string] contains [substring]
 *
 * (str.contains String String Bool)
 */
class StrContains(val string: Expression<StringSort>, val substring: Expression<StringSort>) :
    BinaryExpression<BoolSort, StringSort, StringSort>("str.contains".toSymbolWithQuotes(), Bool) {
  override val theories = STRINGS_MARKER_SET

  override val lhs: Expression<StringSort> = string

  override val rhs: Expression<StringSort> = substring

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      StrContainsDecl.constructDynamic(children, emptyList())
}

/**
 * Index of first occurrence of [substring] in [string] starting at [start]
 *
 * (str.indexof String String Int Int)
 */
class StrIndexOf(
    val string: Expression<StringSort>,
    val substring: Expression<StringSort>,
    val start: Expression<IntSort>
) :
    TernaryExpression<IntSort, StringSort, StringSort, IntSort>(
        "str.indexof".toSymbolWithQuotes(), SMTInt) {
  override val theories = STRINGS_MARKER_SET

  override val lhs: Expression<StringSort> = string

  override val mid: Expression<StringSort> = substring

  override val rhs: Expression<IntSort> = start

  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      StrIndexOfDecl.constructDynamic(children, emptyList())
}

/**
 * String Replace
 *
 * (str.replace String String String String)
 */
class StrReplace(
    val inner: Expression<StringSort>,
    val old: Expression<StringSort>,
    val new: Expression<StringSort>
) :
    TernaryExpression<StringSort, StringSort, StringSort, StringSort>(
        "str.replace".toSymbolWithQuotes(), SMTString) {
  override val theories = STRINGS_MARKER_SET

  override val lhs: Expression<StringSort> = inner

  override val mid: Expression<StringSort> = old

  override val rhs: Expression<StringSort> = new

  override fun copy(children: List<Expression<*>>): Expression<StringSort> =
      StrReplaceDecl.constructDynamic(children, emptyList())
}

/**
 * String Replace All
 *
 * (str.replace_all String String String String)
 */
class StrReplaceAll(
    val inner: Expression<StringSort>,
    val old: Expression<StringSort>,
    val new: Expression<StringSort>
) :
    TernaryExpression<StringSort, StringSort, StringSort, StringSort>(
        "str.replace_all".toSymbolWithQuotes(), SMTString) {
  override val theories = STRINGS_MARKER_SET

  override val lhs: Expression<StringSort> = inner

  override val mid: Expression<StringSort> = old

  override val rhs: Expression<StringSort> = new

  override fun copy(children: List<Expression<*>>): Expression<StringSort> =
      StrReplaceAllDecl.constructDynamic(children, emptyList())
}

/** (str.replace_re String RegLan String String) */
class StrReplaceRegex(
    val inner: Expression<StringSort>,
    val old: Expression<RegLanSort>,
    val new: Expression<StringSort>
) :
    TernaryExpression<StringSort, StringSort, RegLanSort, StringSort>(
        "str.replace_re".toSymbolWithQuotes(), SMTString) {
  override val theories = STRINGS_MARKER_SET

  override val lhs: Expression<StringSort> = inner

  override val mid: Expression<RegLanSort> = old

  override val rhs: Expression<StringSort> = new

  override fun copy(children: List<Expression<*>>): Expression<StringSort> =
      StrReplaceRegexDecl.constructDynamic(children, emptyList())
}

/** (str.replace_re_all String RegLan String String) */
class StrReplaceAllRegex(
    val inner: Expression<StringSort>,
    val old: Expression<RegLanSort>,
    val new: Expression<StringSort>
) :
    TernaryExpression<StringSort, StringSort, RegLanSort, StringSort>(
        "str.replace_re_all".toSymbolWithQuotes(), SMTString) {
  override val theories = STRINGS_MARKER_SET

  override val lhs: Expression<StringSort> = inner

  override val mid: Expression<RegLanSort> = old

  override val rhs: Expression<StringSort> = new

  override fun copy(children: List<Expression<*>>): Expression<StringSort> =
      StrReplaceAllRegexDecl.constructDynamic(children, emptyList())
}

/**
 * RE complement
 *
 * (re.comp RegLan RegLan)
 */
class RegexComp(override val inner: Expression<RegLanSort>) :
    UnaryExpression<RegLanSort, RegLanSort>("re.comp".toSymbolWithQuotes(), RegLan) {
  override val theories = STRINGS_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<RegLanSort> =
      RegexCompDecl.constructDynamic(children, emptyList())
}

/**
 * RE difference
 *
 * (re.diff RegLan RegLan RegLan :left-assoc)
 */
class RegexDiff(val regex: List<Expression<RegLanSort>>) :
    HomogenousExpression<RegLanSort, RegLanSort>("re.diff".toSymbolWithQuotes(), RegLan) {
  override val theories = STRINGS_MARKER_SET

  constructor(vararg regex: Expression<RegLanSort>) : this(regex.toList())

  override val children: List<Expression<RegLanSort>> = regex

  override fun copy(children: List<Expression<*>>): Expression<RegLanSort> =
      RegexDiffDecl.constructDynamic(children, emptyList())
}

/**
 * RE Kleene cross
 *
 * (re.+ RegLan RegLan)
 */
class RegexPlus(override val inner: Expression<RegLanSort>) :
    UnaryExpression<RegLanSort, RegLanSort>("re.+".toSymbolWithQuotes(), RegLan) {
  override val theories = STRINGS_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<RegLanSort> =
      RegexPlusDecl.constructDynamic(children, emptyList())
}

/**
 * RE option
 *
 * (re.opt RegLan RegLan)
 */
class RegexOption(override val inner: Expression<RegLanSort>) :
    UnaryExpression<RegLanSort, RegLanSort>("re.opt".toSymbolWithQuotes(), RegLan) {
  override val theories = STRINGS_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<RegLanSort> =
      RegexOptionDecl.constructDynamic(children, emptyList())
}

/**
 * RE range
 *
 * (re.range String String RegLan)
 */
class RegexRange(
    override val lhs: Expression<StringSort>,
    override val rhs: Expression<StringSort>
) : BinaryExpression<RegLanSort, StringSort, StringSort>("re.range".toSymbolWithQuotes(), RegLan) {
  override val theories = STRINGS_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<RegLanSort> =
      RegexRangeDecl.constructDynamic(children, emptyList())
}

/** ((_ re.^ n) RegLan RegLan) */
class RegexPower(override val inner: Expression<RegLanSort>, val n: Int) :
    UnaryExpression<RegLanSort, RegLanSort>("re.^".toSymbolWithQuotes(), RegLan) {
  override val theories = STRINGS_MARKER_SET

  override fun toString(): String = "((_ re.^ $n) $inner)"

  override fun copy(children: List<Expression<*>>): Expression<RegLanSort> =
      RegexPowerDecl.constructDynamic(children, emptyList())
}

/** ((_ re.loop n₁ n₂) RegLan RegLan) */
class RegexLoop(override val inner: Expression<RegLanSort>, val n: Int, val m: Int) :
    UnaryExpression<RegLanSort, RegLanSort>("re.loop".toSymbolWithQuotes(), RegLan) {
  override val theories = STRINGS_MARKER_SET

  override fun toString(): String = "((_ re.loop $n $m) $inner)"

  override fun copy(children: List<Expression<*>>): Expression<RegLanSort> =
      RegexLoopDecl.constructDynamic(children, emptyList())
}

/*
 * Maps to and from integer
 */

// TODO enforce inner is a single digit string
/**
 * Digit check
 *
 * (str.is_digit String Bool)
 */
class StrIsDigit(override val inner: Expression<StringSort>) :
    UnaryExpression<BoolSort, StringSort>("str.is_digit".toSymbolWithQuotes(), Bool) {
  override val theories = STRINGS_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      StrIsDigitDecl.constructDynamic(children, emptyList())
}

/** (str.to_code String Int) */
class StrToCode(override val inner: Expression<StringSort>) :
    UnaryExpression<IntSort, StringSort>("str.to_code".toSymbolWithQuotes(), SMTInt) {
  override val theories = STRINGS_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      StrToCodeDecl.constructDynamic(children, emptyList())
}

/** (str.from_code Int String) */
class StrFromCode(override val inner: Expression<IntSort>) :
    UnaryExpression<StringSort, IntSort>("str.from_code".toSymbolWithQuotes(), SMTString) {
  override val theories = STRINGS_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<StringSort> =
      StrFromCodeDecl.constructDynamic(children, emptyList())
}

/**
 * Conversion to integers
 *
 * (str.to_int String Int)
 */
class StrToInt(override val inner: Expression<StringSort>) :
    UnaryExpression<IntSort, StringSort>("str.to_int".toSymbolWithQuotes(), SMTInt) {
  override val theories = STRINGS_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      StrToIntDecl.constructDynamic(children, emptyList())
}

/**
 * Conversion from integers
 *
 * (str.from_int Int String)
 */
class StrFromInt(override val inner: Expression<IntSort>) :
    UnaryExpression<StringSort, IntSort>("str.from_int".toSymbolWithQuotes(), SMTString) {
  override val theories = STRINGS_MARKER_SET

  override fun copy(children: List<Expression<*>>): Expression<StringSort> =
      StrFromIntDecl.constructDynamic(children, emptyList())
}

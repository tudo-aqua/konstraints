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

package tools.aqua.konstraints.theories

import tools.aqua.konstraints.parser.*
import tools.aqua.konstraints.smt.*

/** Strings theory object */
object StringsTheory : Theory {
  override val functions =
      listOf(
          CharDecl,
          StrConcatDecl,
          StrLengthDecl,
          StrLexOrderDecl,
          StrRefLexOrderDecl,
          StrAtDecl,
          StrSubstringDecl,
          StrPrefixOfDecl,
          StrSuffixOfDecl,
          StrContainsDecl,
          StrIndexOfDecl,
          StrReplaceDecl,
          StrReplaceAllDecl,
          StrReplaceRegexDecl,
          StrIsDigitDecl,
          StrToCodeDecl,
          StrToIntDecl,
          StrFromCodeDecl,
          StrFromIntDecl,
          RegexNoneDecl,
          RegexAllDecl,
          RegexAllCharDecl,
          RegexConcatDecl,
          RegexUnionDecl,
          RegexIntersecDecl,
          RegexStarDecl,
          RegexCompDecl,
          RegexDiffDecl,
          RegexPlusDecl,
          RegexOptionDecl,
          RegexRangeDecl,
          RegexPowerDecl,
          RegexLoopDecl)

  override val sorts: Map<String, SortDecl<*>> =
      mapOf(Pair("String", StringSortDecl), Pair("RegLan", RegLanDecl), Pair("Int", IntSortDecl))
}

/** String sort */
object StringSort : Sort("String")

internal object StringSortDecl : SortDecl<StringSort>("String".symbol(), emptySet(), emptySet()) {
  override fun getSort(bindings: Bindings): StringSort = StringSort
}

/** Regular expression sort */
object RegLan : Sort("RegLan")

internal object RegLanDecl : SortDecl<RegLan>("RegLan".symbol(), emptySet(), emptySet()) {
  override fun getSort(bindings: Bindings): RegLan = RegLan
}

/**
 * [value] holds the hexadecimal unicode of the character, [character] hold the kotlin
 * representation, possible values range from #x0 to #x2FFFF and are generated by the following
 * grammar
 *
 * ```
 * ⟨H⟩ ::= #x⟨F⟩ | #x⟨F⟩⟨F⟩ | #x⟨F⟩⟨F⟩⟨F⟩ | #x⟨F⟩⟨F⟩⟨F⟩⟨F⟩ | #x⟨2⟩⟨F⟩⟨F⟩⟨F⟩⟨F⟩
 * ⟨2⟩ ::= 0 | 1 | 2
 * ⟨F⟩ ::= ⟨2⟩ | 3 | 4 | 5 | 6 | 7 | 8 | 9
 *             | a | b | b | d | e | f
 *             | A | B | C | D | E | F
 * ```
 */
class Char(val value: String) : Literal<StringSort>(LiteralString("char"), StringSort) {

  val character = Char(Integer.parseInt(value.substring(2)))

  override fun copy(children: List<Expression<*>>): Expression<StringSort> = this
}

object CharDecl :
    FunctionDecl0<StringSort>("char".symbol(), emptySet(), setOf("H".idx()), StringSort) {
  override fun buildExpression(bindings: Bindings): Expression<StringSort> = TODO()
}

class StringLiteral(val value: String) : Literal<StringSort>(LiteralString(value), StringSort) {
  // TODO the symbol needs a different value, probably should not be a symbol here

  // use symbol.toString here to get the unquoted string literal
  override fun toString(): String = name.toString()

  override fun copy(children: List<Expression<*>>): Expression<StringSort> = this
}

/*
 * String functions
 */

/**
 * String concatenation
 *
 * (str.++ String String String :left-assoc)
 */
class StrConcat(val strings: List<Expression<StringSort>>) :
    HomogenousExpression<StringSort, StringSort>("str.++".symbol(), StringSort) {
  constructor(vararg strings: Expression<StringSort>) : this(strings.toList())

  override fun subexpressions(): List<Expression<StringSort>> = strings

  override fun copy(children: List<Expression<*>>): Expression<StringSort> =
      StrConcatDecl.buildExpression(children, emptySet())
}

object StrConcatDecl :
    FunctionDeclLeftAssociative<StringSort, StringSort, StringSort>(
        "str.++".symbol(), emptySet(), StringSort, StringSort, emptySet(), emptySet(), StringSort) {
  override fun buildExpression(
      param1: Expression<StringSort>,
      param2: Expression<StringSort>,
      varargs: List<Expression<StringSort>>,
      bindings: Bindings
  ): Expression<StringSort> = StrConcat(param1, param2, *varargs.toTypedArray())
}

/**
 * String length
 *
 * (str.len String Int)
 */
class StrLength(override val inner: Expression<StringSort>) :
    UnaryExpression<IntSort, StringSort>("str.len".symbol(), IntSort) {
  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      StrLengthDecl.buildExpression(children, emptySet())
}

object StrLengthDecl :
    FunctionDecl1<StringSort, IntSort>(
        "str.len".symbol(), emptySet(), StringSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param: Expression<StringSort>,
      bindings: Bindings
  ): Expression<IntSort> = StrLength(param)
}

/**
 * Lexicographic ordering
 *
 * (str.< String String Bool :chainable)
 */
class StrLexOrder(val strings: List<Expression<StringSort>>) :
    HomogenousExpression<BoolSort, StringSort>("str.<".symbol(), BoolSort) {
  constructor(vararg strings: Expression<StringSort>) : this(strings.toList())

  override fun subexpressions(): List<Expression<StringSort>> = strings

  init {
    require(strings.size > 1) {
      "Lexicographic order needs at least two strings but ${strings.size} were given!"
    }
  }

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      StrLexOrderDecl.buildExpression(children, emptySet())
}

object StrLexOrderDecl :
    FunctionDeclChainable<StringSort>(
        "str.<".symbol(), emptySet(), StringSort, StringSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<StringSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = StrLexOrder(varargs)
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
    UnaryExpression<RegLan, StringSort>("str.to_reg".symbol(), RegLan) {
  override fun copy(children: List<Expression<*>>): Expression<RegLan> =
      ToRegexDecl.buildExpression(children, emptySet())
}

object ToRegexDecl :
    FunctionDecl1<StringSort, RegLan>(
        "str.to_reg".symbol(), emptySet(), StringSort, emptySet(), emptySet(), RegLan) {
  override fun buildExpression(
      param: Expression<StringSort>,
      bindings: Bindings
  ): Expression<RegLan> = ToRegex(param)
}

/**
 * RE membership
 *
 * (str.in_re String RegLan Bool)
 */
class InRegex(val inner: Expression<StringSort>, val regex: Expression<RegLan>) :
    BinaryExpression<BoolSort, StringSort, RegLan>("str.in_reg".symbol(), BoolSort) {
  override val lhs: Expression<StringSort> = inner

  override val rhs: Expression<RegLan> = regex

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      InRegexDecl.buildExpression(children, emptySet())
}

object InRegexDecl :
    FunctionDecl2<StringSort, RegLan, BoolSort>(
        "str.in_reg".symbol(), emptySet(), StringSort, RegLan, emptySet(), emptySet(), BoolSort) {
  override fun buildExpression(
      param1: Expression<StringSort>,
      param2: Expression<RegLan>,
      bindings: Bindings
  ): Expression<BoolSort> = InRegex(param1, param2)
}

/**
 * Constant denoting the empty set of strings
 *
 * (re.none RegLan)
 */
object RegexNone : ConstantExpression<RegLan>("re.none".symbol(), RegLan) {
  override fun copy(children: List<Expression<*>>): Expression<RegLan> = this
}

object RegexNoneDecl : FunctionDecl0<RegLan>("re.none".symbol(), emptySet(), emptySet(), RegLan) {
  override fun buildExpression(bindings: Bindings): Expression<RegLan> = RegexNone
}

/**
 * Constant denoting the set of all strings
 *
 * (re.all RegLan)
 */
object RegexAll : ConstantExpression<RegLan>("re.all".symbol(), RegLan) {
  override fun copy(children: List<Expression<*>>): Expression<RegLan> = this
}

object RegexAllDecl : FunctionDecl0<RegLan>("re.all".symbol(), emptySet(), emptySet(), RegLan) {
  override fun buildExpression(bindings: Bindings): Expression<RegLan> = RegexAll
}

/**
 * Constant denoting the set of all strings of length 1
 *
 * (re.allchar RegLan)
 */
object RegexAllChar : ConstantExpression<RegLan>("re.allchar".symbol(), RegLan) {
  override fun copy(children: List<Expression<*>>): Expression<RegLan> = this
}

object RegexAllCharDecl :
    FunctionDecl0<RegLan>("re.allchar".symbol(), emptySet(), emptySet(), RegLan) {
  override fun buildExpression(bindings: Bindings): Expression<RegLan> = RegexAllChar
}

/**
 * RE concatenation
 *
 * (re.++ RegLan RegLan RegLan :left-assoc)
 */
class RegexConcat(val regex: List<Expression<RegLan>>) :
    HomogenousExpression<RegLan, RegLan>("re.++".symbol(), RegLan) {
  constructor(vararg regex: Expression<RegLan>) : this(regex.toList())

  override fun subexpressions(): List<Expression<RegLan>> = regex

  override fun copy(children: List<Expression<*>>): Expression<RegLan> =
      RegexConcatDecl.buildExpression(children, emptySet())
}

object RegexConcatDecl :
    FunctionDeclLeftAssociative<RegLan, RegLan, RegLan>(
        "re.++".symbol(), emptySet(), RegLan, RegLan, emptySet(), emptySet(), RegLan) {
  override fun buildExpression(
      param1: Expression<RegLan>,
      param2: Expression<RegLan>,
      varargs: List<Expression<RegLan>>,
      bindings: Bindings
  ): Expression<RegLan> = RegexConcat(param1, param2, *varargs.toTypedArray())
}

/**
 * RE union
 *
 * (re.union RegLan RegLan RegLan :left-assoc)
 */
class RegexUnion(val regex: List<Expression<RegLan>>) :
    HomogenousExpression<RegLan, RegLan>("re.union".symbol(), RegLan) {
  constructor(vararg regex: Expression<RegLan>) : this(regex.toList())

  override fun subexpressions(): List<Expression<RegLan>> = regex

  override fun copy(children: List<Expression<*>>): Expression<RegLan> =
      RegexUnionDecl.buildExpression(children, emptySet())
}

object RegexUnionDecl :
    FunctionDeclLeftAssociative<RegLan, RegLan, RegLan>(
        "re.union".symbol(), emptySet(), RegLan, RegLan, emptySet(), emptySet(), RegLan) {
  override fun buildExpression(
      param1: Expression<RegLan>,
      param2: Expression<RegLan>,
      varargs: List<Expression<RegLan>>,
      bindings: Bindings
  ): Expression<RegLan> = RegexUnion(param1, param2, *varargs.toTypedArray())
}

/**
 * RE intersection
 *
 * (re.inter RegLan RegLan RegLan :left-assoc)
 */
class RegexIntersec(val regex: List<Expression<RegLan>>) :
    HomogenousExpression<RegLan, RegLan>("re.inter".symbol(), RegLan) {
  constructor(vararg regex: Expression<RegLan>) : this(regex.toList())

  override fun subexpressions(): List<Expression<RegLan>> = regex

  override fun copy(children: List<Expression<*>>): Expression<RegLan> =
      RegexIntersecDecl.buildExpression(children, emptySet())
}

object RegexIntersecDecl :
    FunctionDeclLeftAssociative<RegLan, RegLan, RegLan>(
        "re.inter".symbol(), emptySet(), RegLan, RegLan, emptySet(), emptySet(), RegLan) {
  override fun buildExpression(
      param1: Expression<RegLan>,
      param2: Expression<RegLan>,
      varargs: List<Expression<RegLan>>,
      bindings: Bindings
  ): Expression<RegLan> = RegexIntersec(param1, param2, *varargs.toTypedArray())
}

/**
 * Kleene Closure
 *
 * (re.* RegLan RegLan)
 */
class RegexStar(override val inner: Expression<RegLan>) :
    UnaryExpression<RegLan, RegLan>("re.*".symbol(), RegLan) {
  override fun copy(children: List<Expression<*>>): Expression<RegLan> =
      RegexStarDecl.buildExpression(children, emptySet())
}

object RegexStarDecl :
    FunctionDecl1<RegLan, RegLan>(
        "re.*".symbol(), emptySet(), RegLan, emptySet(), emptySet(), RegLan) {
  override fun buildExpression(param: Expression<RegLan>, bindings: Bindings): Expression<RegLan> =
      RegexStar(param)
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
    HomogenousExpression<BoolSort, StringSort>("str.<=".symbol(), BoolSort) {
  constructor(vararg strings: Expression<StringSort>) : this(strings.toList())

  override fun subexpressions(): List<Expression<StringSort>> = strings

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      StrRefLexOrderDecl.buildExpression(children, emptySet())
}

object StrRefLexOrderDecl :
    FunctionDeclChainable<StringSort>(
        "str.<=".symbol(), emptySet(), StringSort, StringSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<StringSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = StrRefLexOrder(varargs)
}

/**
 * Singleton string containing a character at given position or empty string when position is out of
 * range. The leftmost position is 0.
 *
 * (str.at String Int String)
 */
class StrAt(val inner: Expression<StringSort>, val position: Expression<IntSort>) :
    BinaryExpression<StringSort, StringSort, IntSort>("str.at".symbol(), StringSort) {
  override val lhs: Expression<StringSort> = inner

  override val rhs: Expression<IntSort> = position

  override fun copy(children: List<Expression<*>>): Expression<StringSort> =
      StrAtDecl.buildExpression(children, emptySet())
}

object StrAtDecl :
    FunctionDecl2<StringSort, IntSort, StringSort>(
        "str.at".symbol(), emptySet(), StringSort, IntSort, emptySet(), emptySet(), StringSort) {
  override fun buildExpression(
      param1: Expression<StringSort>,
      param2: Expression<IntSort>,
      bindings: Bindings
  ): Expression<StringSort> = StrAt(param1, param2)
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
) : TernaryExpression<StringSort, StringSort, IntSort, IntSort>("str.substr".symbol(), StringSort) {
  override val lhs: Expression<StringSort> = inner

  override val mid: Expression<IntSort> = start

  override val rhs: Expression<IntSort> = length

  override fun copy(children: List<Expression<*>>): Expression<StringSort> =
      StrSubstringDecl.buildExpression(children, emptySet())
}

object StrSubstringDecl :
    FunctionDecl3<StringSort, IntSort, IntSort, StringSort>(
        "str.substr".symbol(),
        emptySet(),
        StringSort,
        IntSort,
        IntSort,
        emptySet(),
        emptySet(),
        StringSort) {
  override fun buildExpression(
      param1: Expression<StringSort>,
      param2: Expression<IntSort>,
      param3: Expression<IntSort>,
      bindings: Bindings
  ): Expression<StringSort> = StrSubstring(param1, param2, param3)
}

/**
 * [prefix] is a prefix of [inner]
 *
 * (str.prefixof String String Bool)
 */
class StrPrefixOf(val prefix: Expression<StringSort>, val inner: Expression<StringSort>) :
    BinaryExpression<BoolSort, StringSort, StringSort>("str.prefixof".symbol(), BoolSort) {
  override val lhs: Expression<StringSort> = prefix

  override val rhs: Expression<StringSort> = inner

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      StrPrefixOfDecl.buildExpression(children, emptySet())
}

object StrPrefixOfDecl :
    FunctionDecl2<StringSort, StringSort, BoolSort>(
        "str.prefixof".symbol(),
        emptySet(),
        StringSort,
        StringSort,
        emptySet(),
        emptySet(),
        BoolSort) {
  override fun buildExpression(
      param1: Expression<StringSort>,
      param2: Expression<StringSort>,
      bindings: Bindings
  ): Expression<BoolSort> = StrPrefixOf(param1, param2)
}

/**
 * [suffix] is a suffix of [inner]
 *
 * (str.suffixof String String Bool)
 */
class StrSuffixOf(val suffix: Expression<StringSort>, val inner: Expression<StringSort>) :
    BinaryExpression<BoolSort, StringSort, StringSort>("str.suffixof".symbol(), BoolSort) {
  override val lhs: Expression<StringSort> = suffix

  override val rhs: Expression<StringSort> = inner

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      StrSuffixOfDecl.buildExpression(children, emptySet())
}

object StrSuffixOfDecl :
    FunctionDecl2<StringSort, StringSort, BoolSort>(
        "str.suffixof".symbol(),
        emptySet(),
        StringSort,
        StringSort,
        emptySet(),
        emptySet(),
        BoolSort) {
  override fun buildExpression(
      param1: Expression<StringSort>,
      param2: Expression<StringSort>,
      bindings: Bindings
  ): Expression<BoolSort> = StrSuffixOf(param1, param2)
}

/**
 * [string] contains [substring]
 *
 * (str.contains String String Bool)
 */
class StrContains(val string: Expression<StringSort>, val substring: Expression<StringSort>) :
    BinaryExpression<BoolSort, StringSort, StringSort>("str.contains".symbol(), BoolSort) {
  override val lhs: Expression<StringSort> = string

  override val rhs: Expression<StringSort> = substring

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      StrContainsDecl.buildExpression(children, emptySet())
}

object StrContainsDecl :
    FunctionDecl2<StringSort, StringSort, BoolSort>(
        "str.contains".symbol(),
        emptySet(),
        StringSort,
        StringSort,
        emptySet(),
        emptySet(),
        BoolSort) {
  override fun buildExpression(
      param1: Expression<StringSort>,
      param2: Expression<StringSort>,
      bindings: Bindings
  ): Expression<BoolSort> = StrContains(param1, param2)
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
) : TernaryExpression<IntSort, StringSort, StringSort, IntSort>("str.indexof".symbol(), IntSort) {
  override val lhs: Expression<StringSort> = string

  override val mid: Expression<StringSort> = substring

  override val rhs: Expression<IntSort> = start

  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      StrIndexOfDecl.buildExpression(children, emptySet())
}

object StrIndexOfDecl :
    FunctionDecl3<StringSort, StringSort, IntSort, IntSort>(
        "str.indexof".symbol(),
        emptySet(),
        StringSort,
        StringSort,
        IntSort,
        emptySet(),
        emptySet(),
        IntSort) {
  override fun buildExpression(
      param1: Expression<StringSort>,
      param2: Expression<StringSort>,
      param3: Expression<IntSort>,
      bindings: Bindings
  ): Expression<IntSort> = StrIndexOf(param1, param2, param3)
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
        "str.replace".symbol(), StringSort) {
  override val lhs: Expression<StringSort> = inner

  override val mid: Expression<StringSort> = old

  override val rhs: Expression<StringSort> = new

  override fun copy(children: List<Expression<*>>): Expression<StringSort> =
      StrReplaceDecl.buildExpression(children, emptySet())
}

object StrReplaceDecl :
    FunctionDecl3<StringSort, StringSort, StringSort, StringSort>(
        "str.replace".symbol(),
        emptySet(),
        StringSort,
        StringSort,
        StringSort,
        emptySet(),
        emptySet(),
        StringSort) {
  override fun buildExpression(
      param1: Expression<StringSort>,
      param2: Expression<StringSort>,
      param3: Expression<StringSort>,
      bindings: Bindings
  ): Expression<StringSort> = StrReplace(param1, param2, param3)
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
        "str.replace_all".symbol(), StringSort) {
  override val lhs: Expression<StringSort> = inner

  override val mid: Expression<StringSort> = old

  override val rhs: Expression<StringSort> = new

  override fun copy(children: List<Expression<*>>): Expression<StringSort> =
      StrReplaceAllDecl.buildExpression(children, emptySet())
}

object StrReplaceAllDecl :
    FunctionDecl3<StringSort, StringSort, StringSort, StringSort>(
        "str.replace".symbol(),
        emptySet(),
        StringSort,
        StringSort,
        StringSort,
        emptySet(),
        emptySet(),
        StringSort) {
  override fun buildExpression(
      param1: Expression<StringSort>,
      param2: Expression<StringSort>,
      param3: Expression<StringSort>,
      bindings: Bindings
  ): Expression<StringSort> = StrReplaceAll(param1, param2, param3)
}

/** (str.replace_re String RegLan String String) */
class StrReplaceRegex(
    val inner: Expression<StringSort>,
    val old: Expression<RegLan>,
    val new: Expression<StringSort>
) :
    TernaryExpression<StringSort, StringSort, RegLan, StringSort>(
        "str.replace_re".symbol(), StringSort) {
  override val lhs: Expression<StringSort> = inner

  override val mid: Expression<RegLan> = old

  override val rhs: Expression<StringSort> = new

  override fun copy(children: List<Expression<*>>): Expression<StringSort> =
      StrReplaceRegexDecl.buildExpression(children, emptySet())
}

object StrReplaceRegexDecl :
    FunctionDecl3<StringSort, RegLan, StringSort, StringSort>(
        "str.replace_re".symbol(),
        emptySet(),
        StringSort,
        RegLan,
        StringSort,
        emptySet(),
        emptySet(),
        StringSort) {
  override fun buildExpression(
      param1: Expression<StringSort>,
      param2: Expression<RegLan>,
      param3: Expression<StringSort>,
      bindings: Bindings
  ): Expression<StringSort> = StrReplaceRegex(param1, param2, param3)
}

/** (str.replace_re_all String RegLan String String) */
class StrReplaceAllRegex(
    val inner: Expression<StringSort>,
    val old: Expression<RegLan>,
    val new: Expression<StringSort>
) :
    TernaryExpression<StringSort, StringSort, RegLan, StringSort>(
        "str.replace_re_all".symbol(), StringSort) {
  override val lhs: Expression<StringSort> = inner

  override val mid: Expression<RegLan> = old

  override val rhs: Expression<StringSort> = new

  override fun copy(children: List<Expression<*>>): Expression<StringSort> =
      StrReplaceAllRegexDecl.buildExpression(children, emptySet())
}

object StrReplaceAllRegexDecl :
    FunctionDecl3<StringSort, RegLan, StringSort, StringSort>(
        "str.replace_re_all".symbol(),
        emptySet(),
        StringSort,
        RegLan,
        StringSort,
        emptySet(),
        emptySet(),
        StringSort) {
  override fun buildExpression(
      param1: Expression<StringSort>,
      param2: Expression<RegLan>,
      param3: Expression<StringSort>,
      bindings: Bindings
  ): Expression<StringSort> = StrReplaceRegex(param1, param2, param3)
}

/**
 * RE complement
 *
 * (re.comp RegLan RegLan)
 */
class RegexComp(override val inner: Expression<RegLan>) :
    UnaryExpression<RegLan, RegLan>("re.comp".symbol(), RegLan) {
  override fun copy(children: List<Expression<*>>): Expression<RegLan> =
      RegexCompDecl.buildExpression(children, emptySet())
}

object RegexCompDecl :
    FunctionDecl1<RegLan, RegLan>(
        "re.comp".symbol(), emptySet(), RegLan, emptySet(), emptySet(), RegLan) {
  override fun buildExpression(param: Expression<RegLan>, bindings: Bindings): Expression<RegLan> =
      RegexComp(param)
}

/**
 * RE difference
 *
 * (re.diff RegLan RegLan RegLan :left-assoc)
 */
class RegexDiff(val regex: List<Expression<RegLan>>) :
    HomogenousExpression<RegLan, RegLan>("re.diff".symbol(), RegLan) {
  constructor(vararg regex: Expression<RegLan>) : this(regex.toList())

  override fun subexpressions(): List<Expression<RegLan>> = regex

  override fun copy(children: List<Expression<*>>): Expression<RegLan> =
      RegexDiffDecl.buildExpression(children, emptySet())
}

object RegexDiffDecl :
    FunctionDeclLeftAssociative<RegLan, RegLan, RegLan>(
        "re.diff".symbol(), emptySet(), RegLan, RegLan, emptySet(), emptySet(), RegLan) {
  override fun buildExpression(
      param1: Expression<RegLan>,
      param2: Expression<RegLan>,
      varargs: List<Expression<RegLan>>,
      bindings: Bindings
  ): Expression<RegLan> = RegexDiff(param1, param2, *varargs.toTypedArray())
}

/**
 * RE Kleene cross
 *
 * (re.+ RegLan RegLan)
 */
class RegexPlus(override val inner: Expression<RegLan>) :
    UnaryExpression<RegLan, RegLan>("re.+".symbol(), RegLan) {
  override fun copy(children: List<Expression<*>>): Expression<RegLan> =
      RegexPlusDecl.buildExpression(children, emptySet())
}

object RegexPlusDecl :
    FunctionDecl1<RegLan, RegLan>(
        "re.+".symbol(), emptySet(), RegLan, emptySet(), emptySet(), RegLan) {
  override fun buildExpression(param: Expression<RegLan>, bindings: Bindings): Expression<RegLan> =
      RegexPlus(param)
}

/**
 * RE option
 *
 * (re.opt RegLan RegLan)
 */
class RegexOption(override val inner: Expression<RegLan>) :
    UnaryExpression<RegLan, RegLan>("re.opt".symbol(), RegLan) {
  override fun copy(children: List<Expression<*>>): Expression<RegLan> =
      RegexOptionDecl.buildExpression(children, emptySet())
}

object RegexOptionDecl :
    FunctionDecl1<RegLan, RegLan>(
        "re.opt".symbol(), emptySet(), RegLan, emptySet(), emptySet(), RegLan) {
  override fun buildExpression(param: Expression<RegLan>, bindings: Bindings): Expression<RegLan> =
      RegexOption(param)
}

/**
 * RE range
 *
 * (re.range String String RegLan)
 */
class RegexRange(
    override val lhs: Expression<StringSort>,
    override val rhs: Expression<StringSort>
) : BinaryExpression<RegLan, StringSort, StringSort>("re.range".symbol(), RegLan) {
  override fun copy(children: List<Expression<*>>): Expression<RegLan> =
      RegexRangeDecl.buildExpression(children, emptySet())
}

object RegexRangeDecl :
    FunctionDecl2<StringSort, StringSort, RegLan>(
        "re.range".symbol(), emptySet(), StringSort, StringSort, emptySet(), emptySet(), RegLan) {
  override fun buildExpression(
      param1: Expression<StringSort>,
      param2: Expression<StringSort>,
      bindings: Bindings
  ): Expression<RegLan> = RegexRange(param1, param2)
}

/** ((_ re.^ n) RegLan RegLan) */
class RegexPower(override val inner: Expression<RegLan>, val n: Int) :
    UnaryExpression<RegLan, RegLan>("re.^".symbol(), RegLan) {

  override fun toString(): String = "((_ re.^ $n) $inner)"

  override fun copy(children: List<Expression<*>>): Expression<RegLan> =
      RegexPowerDecl.buildExpression(children, emptySet())
}

object RegexPowerDecl :
    FunctionDecl1<RegLan, RegLan>(
        "re.^".symbol(), emptySet(), RegLan, setOf("n".idx()), emptySet(), RegLan) {
  override fun buildExpression(param: Expression<RegLan>, bindings: Bindings): Expression<RegLan> =
      RegexPower(param, bindings["n"].numeral)
}

/** ((_ re.loop n₁ n₂) RegLan RegLan) */
class RegexLoop(override val inner: Expression<RegLan>, val n: Int, val m: Int) :
    UnaryExpression<RegLan, RegLan>("re.loop".symbol(), RegLan) {

  override fun toString(): String = "((_ re.loop $n $m) $inner)"

  override fun copy(children: List<Expression<*>>): Expression<RegLan> =
      RegexLoopDecl.buildExpression(children, emptySet())
}

object RegexLoopDecl :
    FunctionDecl1<RegLan, RegLan>(
        "re.loop".symbol(), emptySet(), RegLan, setOf("n1".idx(), "n2".idx()), emptySet(), RegLan) {
  override fun buildExpression(param: Expression<RegLan>, bindings: Bindings): Expression<RegLan> =
      RegexLoop(param, bindings["n1"].numeral, bindings["n2"].numeral)
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
    UnaryExpression<BoolSort, StringSort>("str.is_digit".symbol(), BoolSort) {
  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      StrIsDigitDecl.buildExpression(children, emptySet())
}

object StrIsDigitDecl :
    FunctionDecl1<StringSort, BoolSort>(
        "str.is_digit".symbol(), emptySet(), StringSort, emptySet(), emptySet(), BoolSort) {
  override fun buildExpression(
      param: Expression<StringSort>,
      bindings: Bindings
  ): Expression<BoolSort> = StrIsDigit(param)
}

/** (str.to_code String Int) */
class StrToCode(override val inner: Expression<StringSort>) :
    UnaryExpression<IntSort, StringSort>("str.to_code".symbol(), IntSort) {
  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      StrToCodeDecl.buildExpression(children, emptySet())
}

object StrToCodeDecl :
    FunctionDecl1<StringSort, IntSort>(
        "str.to_code".symbol(), emptySet(), StringSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param: Expression<StringSort>,
      bindings: Bindings
  ): Expression<IntSort> = StrToCode(param)
}

/** (str.from_code Int String) */
class StrFromCode(override val inner: Expression<IntSort>) :
    UnaryExpression<StringSort, IntSort>("str.from_code".symbol(), StringSort) {
  override fun copy(children: List<Expression<*>>): Expression<StringSort> =
      StrFromCodeDecl.buildExpression(children, emptySet())
}

object StrFromCodeDecl :
    FunctionDecl1<IntSort, StringSort>(
        "str.from_code".symbol(), emptySet(), IntSort, emptySet(), emptySet(), StringSort) {
  override fun buildExpression(
      param: Expression<IntSort>,
      bindings: Bindings
  ): Expression<StringSort> = StrFromCode(param)
}

/**
 * Conversion to integers
 *
 * (str.to_int String Int)
 */
class StrToInt(override val inner: Expression<StringSort>) :
    UnaryExpression<IntSort, StringSort>("str.to_int".symbol(), IntSort) {
  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      StrToIntDecl.buildExpression(children, emptySet())
}

object StrToIntDecl :
    FunctionDecl1<StringSort, IntSort>(
        "str.to_code".symbol(), emptySet(), StringSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param: Expression<StringSort>,
      bindings: Bindings
  ): Expression<IntSort> = StrToInt(param)
}

/**
 * Conversion from integers
 *
 * (str.from_int Int String)
 */
class StrFromInt(override val inner: Expression<IntSort>) :
    UnaryExpression<StringSort, IntSort>("str.from_int".symbol(), StringSort) {
  override fun copy(children: List<Expression<*>>): Expression<StringSort> =
      StrFromIntDecl.buildExpression(children, emptySet())
}

object StrFromIntDecl :
    FunctionDecl1<IntSort, StringSort>(
        "str.from_code".symbol(), emptySet(), IntSort, emptySet(), emptySet(), StringSort) {
  override fun buildExpression(
      param: Expression<IntSort>,
      bindings: Bindings
  ): Expression<StringSort> = StrFromInt(param)
}

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

internal object StringContext : TheoryContext {
  override val functions: HashSet<FunctionDecl<*>> =
      hashSetOf(
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

object StringSort : Sort("String")

internal object StringSortDecl : SortDecl<StringSort>("String".symbol(), emptySet(), emptySet()) {
  override fun getSort(bindings: Bindings): StringSort = StringSort
}

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
class Char(val value: String) : Expression<StringSort>() {

  override val symbol: Symbol = "char".symbol()
  override val sort: StringSort = StringSort

  override fun toString(): String = "(_ char $value)"

  val character = Char(Integer.parseInt(value.substring(2)))
}

object CharDecl :
    FunctionDecl0<StringSort>("char".symbol(), emptySet(), setOf("H".idx()), StringSort) {
  override fun buildExpression(bindings: Bindings): Expression<StringSort> = TODO()
}

class StringLiteral(val value: String) : Expression<StringSort>() {
  // TODO the symbol needs a different value, probably should not be a symbol here
  override val symbol: Symbol = "|$value|".symbol()
  override val sort: StringSort = StringSort

  // use symbol.toString here to get the unquoted string literal
  override fun toString(): String = symbol.toString()
}

/*
 * String functions
 */

class StrConcat(val strings: List<Expression<StringSort>>) : Expression<StringSort>() {
  constructor(vararg strings: Expression<StringSort>) : this(strings.toList())

  override val symbol: Symbol = "str.++".symbol()
  override val sort: StringSort = StringSort

  override fun toString(): String = "(str.++ ${strings.joinToString(" ")})"
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

class StrLength(val inner: Expression<StringSort>) : Expression<IntSort>() {
  override val symbol: Symbol = "str.len".symbol()
  override val sort: IntSort = IntSort

  override fun toString(): String = "(str.len $inner)"
}

object StrLengthDecl :
    FunctionDecl1<StringSort, IntSort>(
        "str.len".symbol(), emptySet(), StringSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param: Expression<StringSort>,
      bindings: Bindings
  ): Expression<IntSort> = StrLength(param)
}

class StrLexOrder(val strings: List<Expression<StringSort>>) : Expression<BoolSort>() {
  constructor(vararg strings: Expression<StringSort>) : this(strings.toList())

  override val symbol: Symbol = "str.<".symbol()
  override val sort: BoolSort = BoolSort

  override fun toString(): String = "(str.< ${strings.joinToString(" ")})"

  init {
    require(strings.size > 1) {
      "Lexicographic order needs at least two strings but ${strings.size} were given!"
    }
  }
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

class ToRegex(val inner: Expression<StringSort>) : Expression<RegLan>() {
  override val symbol: Symbol = "str.to_reg".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "(str.to_reg $inner)"
}

object ToRegexDecl :
    FunctionDecl1<StringSort, RegLan>(
        "str.to_reg".symbol(), emptySet(), StringSort, emptySet(), emptySet(), RegLan) {
  override fun buildExpression(
      param: Expression<StringSort>,
      bindings: Bindings
  ): Expression<RegLan> = ToRegex(param)
}

class InRegex(val inner: Expression<StringSort>, val regex: Expression<RegLan>) :
    Expression<BoolSort>() {
  override val symbol: Symbol = "str.in_reg".symbol()
  override val sort: BoolSort = BoolSort

  override fun toString(): String = "(str.in_reg $inner $regex)"
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

class RegexNone() : Expression<RegLan>() {
  override val symbol: Symbol = "re.none".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "($symbol)"
}

object RegexNoneDecl : FunctionDecl0<RegLan>("re.none".symbol(), emptySet(), emptySet(), RegLan) {
  override fun buildExpression(bindings: Bindings): Expression<RegLan> = RegexNone()
}

class RegexAll() : Expression<RegLan>() {
  override val symbol: Symbol = "re.all".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "($symbol)"
}

object RegexAllDecl : FunctionDecl0<RegLan>("re.all".symbol(), emptySet(), emptySet(), RegLan) {
  override fun buildExpression(bindings: Bindings): Expression<RegLan> = RegexAll()
}

class RegexAllChar() : Expression<RegLan>() {
  override val symbol: Symbol = "re.allchar".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "($symbol)"
}

object RegexAllCharDecl :
    FunctionDecl0<RegLan>("re.allchar".symbol(), emptySet(), emptySet(), RegLan) {
  override fun buildExpression(bindings: Bindings): Expression<RegLan> = RegexAllChar()
}

class RegexConcat(val regex: List<Expression<RegLan>>) : Expression<RegLan>() {
  constructor(vararg regex: Expression<RegLan>) : this(regex.toList())

  override val symbol: Symbol = "re.++".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "(re.++ ${regex.joinToString (" ")})"
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

class RegexUnion(val regex: List<Expression<RegLan>>) : Expression<RegLan>() {
  constructor(vararg regex: Expression<RegLan>) : this(regex.toList())

  override val symbol: Symbol = "re.union".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "(re.union ${regex.joinToString (" ")})"
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

class RegexIntersec(val regex: List<Expression<RegLan>>) : Expression<RegLan>() {
  constructor(vararg regex: Expression<RegLan>) : this(regex.toList())

  override val symbol: Symbol = "re.inter".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "(re.inter ${regex.joinToString (" ")})"
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

class RegexStar(val inner: Expression<RegLan>) : Expression<RegLan>() {
  override val symbol: Symbol = "re.*".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "(re.* $inner)"
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

class StrRefLexOrder(val strings: List<Expression<StringSort>>) : Expression<BoolSort>() {
  constructor(vararg strings: Expression<StringSort>) : this(strings.toList())

  override val symbol: Symbol = "str.<=".symbol()
  override val sort: BoolSort = BoolSort

  override fun toString(): String = "(str.<= ${strings.joinToString(" ")})"
}

object StrRefLexOrderDecl :
    FunctionDeclChainable<StringSort>(
        "str.<=".symbol(), emptySet(), StringSort, StringSort, emptySet(), emptySet()) {
  override fun buildExpression(
      varargs: List<Expression<StringSort>>,
      bindings: Bindings
  ): Expression<BoolSort> = StrRefLexOrder(varargs)
}

class StrAt(val inner: Expression<StringSort>, val position: Expression<IntSort>) :
    Expression<StringSort>() {
  override val symbol: Symbol = "str.at".symbol()
  override val sort: StringSort = StringSort

  override fun toString(): String = "(str.at $inner $position)"
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

class StrSubstring(
    val inner: Expression<StringSort>,
    val start: Expression<IntSort>,
    val length: Expression<IntSort>
) : Expression<StringSort>() {
  override val symbol: Symbol = "str.substr".symbol()
  override val sort: StringSort = StringSort

  override fun toString(): String = "(str.substr $inner $start $length)"
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

class StrPrefixOf(val inner: Expression<StringSort>, val prefix: Expression<StringSort>) :
    Expression<BoolSort>() {
  override val symbol: Symbol = "str.prefixof".symbol()
  override val sort: BoolSort = BoolSort

  override fun toString(): String = "(str.prefixof $inner $prefix)"
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

class StrSuffixOf(val inner: Expression<StringSort>, val suffix: Expression<StringSort>) :
    Expression<BoolSort>() {
  override val symbol: Symbol = "str.suffixof".symbol()
  override val sort: BoolSort = BoolSort

  override fun toString(): String = "(str.suffixof $inner $suffix)"
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

class StrContains(val string: Expression<StringSort>, val substring: Expression<StringSort>) :
    Expression<BoolSort>() {
  override val symbol: Symbol = "str.contains".symbol()
  override val sort: BoolSort = BoolSort

  override fun toString(): String = "(str.contains $string $substring)"
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

class StrIndexOf(
    val string: Expression<StringSort>,
    val substring: Expression<StringSort>,
    val start: Expression<IntSort>
) : Expression<IntSort>() {
  override val symbol: Symbol = "str.indexof".symbol()
  override val sort: IntSort = IntSort

  override fun toString(): String = ("str.indexof $string $substring $start")
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

class StrReplace(
    val inner: Expression<StringSort>,
    val old: Expression<StringSort>,
    val new: Expression<StringSort>
) : Expression<StringSort>() {
  override val symbol: Symbol = "str.replace".symbol()
  override val sort: StringSort = StringSort

  override fun toString(): String = "(str.replace $inner $old $new)"
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

class StrReplaceAll(
    val inner: Expression<StringSort>,
    val old: Expression<StringSort>,
    val new: Expression<StringSort>
) : Expression<StringSort>() {
  override val symbol: Symbol = "str.replace_all".symbol()
  override val sort: StringSort = StringSort

  override fun toString(): String = "(str.replace_all $inner $old $new)"
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

class StrReplaceRegex(
    val inner: Expression<StringSort>,
    val old: Expression<RegLan>,
    val new: Expression<StringSort>
) : Expression<StringSort>() {
  override val symbol: Symbol = "str.replace_re".symbol()
  override val sort: StringSort = StringSort

  override fun toString(): String = "(str.replace_re $inner $old $new)"
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

class StrReplaceAllRegex(
    val inner: Expression<StringSort>,
    val old: Expression<RegLan>,
    val new: Expression<StringSort>
) : Expression<StringSort>() {
  override val symbol: Symbol = "str.replace_re_all".symbol()
  override val sort: StringSort = StringSort

  override fun toString(): String = "(str.replace_re_all $inner $old $new)"
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

class RegexComp(val inner: Expression<RegLan>) : Expression<RegLan>() {
  override val symbol: Symbol = "re.comp".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "(re.comp $inner)"
}

object RegexCompDecl :
    FunctionDecl1<RegLan, RegLan>(
        "re.comp".symbol(), emptySet(), RegLan, emptySet(), emptySet(), RegLan) {
  override fun buildExpression(param: Expression<RegLan>, bindings: Bindings): Expression<RegLan> =
      RegexComp(param)
}

class RegexDiff(val regex: List<Expression<RegLan>>) : Expression<RegLan>() {
  constructor(vararg regex: Expression<RegLan>) : this(regex.toList())

  override val symbol: Symbol = "re.diff".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "(re.diff ${regex.joinToString(" ")})"
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

class RegexPlus(val inner: Expression<RegLan>) : Expression<RegLan>() {
  override val symbol: Symbol = "re.+".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "(re.+ $inner)"
}

object RegexPlusDecl :
    FunctionDecl1<RegLan, RegLan>(
        "re.+".symbol(), emptySet(), RegLan, emptySet(), emptySet(), RegLan) {
  override fun buildExpression(param: Expression<RegLan>, bindings: Bindings): Expression<RegLan> =
      RegexPlus(param)
}

class RegexOption(val inner: Expression<RegLan>) : Expression<RegLan>() {
  override val symbol: Symbol = "re.opt".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "(re.opt $inner)"
}

object RegexOptionDecl :
    FunctionDecl1<RegLan, RegLan>(
        "re.opt".symbol(), emptySet(), RegLan, emptySet(), emptySet(), RegLan) {
  override fun buildExpression(param: Expression<RegLan>, bindings: Bindings): Expression<RegLan> =
      RegexOption(param)
}

class RegexRange(val lhs: Expression<StringSort>, val rhs: Expression<StringSort>) :
    Expression<RegLan>() {
  override val symbol: Symbol = "re.range".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "(re.range $lhs $rhs)"
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

class RegexPower(val inner: Expression<RegLan>, val n: Int) : Expression<RegLan>() {
  override val symbol: Symbol = "re.^".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "((_ re.^ $n) $inner)"
}

object RegexPowerDecl :
    FunctionDecl1<RegLan, RegLan>(
        "re.^".symbol(), emptySet(), RegLan, setOf("n".idx()), emptySet(), RegLan) {
  override fun buildExpression(param: Expression<RegLan>, bindings: Bindings): Expression<RegLan> =
      RegexPower(param, bindings["n"].numeral)
}

class RegexLoop(val inner: Expression<RegLan>, val n: Int, val m: Int) : Expression<RegLan>() {
  override val symbol: Symbol = "re.loop".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "((_ re.loop $n $m) $inner)"
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
class StrIsDigit(val inner: Expression<StringSort>) : Expression<BoolSort>() {
  override val symbol: Symbol = "str.is_digit".symbol()
  override val sort: BoolSort = BoolSort

  override fun toString(): String = "(str.is_digit $inner)"
}

object StrIsDigitDecl :
    FunctionDecl1<StringSort, BoolSort>(
        "str.is_digit".symbol(), emptySet(), StringSort, emptySet(), emptySet(), BoolSort) {
  override fun buildExpression(
      param: Expression<StringSort>,
      bindings: Bindings
  ): Expression<BoolSort> = StrIsDigit(param)
}

class StrToCode(val inner: Expression<StringSort>) : Expression<IntSort>() {
  override val symbol: Symbol = "str.to_code".symbol()
  override val sort: IntSort = IntSort

  override fun toString(): String = "(str.to_code $inner)"
}

object StrToCodeDecl :
    FunctionDecl1<StringSort, IntSort>(
        "str.to_code".symbol(), emptySet(), StringSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param: Expression<StringSort>,
      bindings: Bindings
  ): Expression<IntSort> = StrToCode(param)
}

class StrFromCode(val inner: Expression<IntSort>) : Expression<StringSort>() {
  override val symbol: Symbol = "str.from_code".symbol()
  override val sort: StringSort = StringSort

  override fun toString(): String = "(str.from_code $inner)"
}

object StrFromCodeDecl :
    FunctionDecl1<IntSort, StringSort>(
        "str.from_code".symbol(), emptySet(), IntSort, emptySet(), emptySet(), StringSort) {
  override fun buildExpression(
      param: Expression<IntSort>,
      bindings: Bindings
  ): Expression<StringSort> = StrFromCode(param)
}

class StrToInt(val inner: Expression<StringSort>) : Expression<IntSort>() {
  override val symbol: Symbol = "str.to_int".symbol()
  override val sort: IntSort = IntSort

  override fun toString(): String = "(str.to_int $inner)"
}

object StrToIntDecl :
    FunctionDecl1<StringSort, IntSort>(
        "str.to_code".symbol(), emptySet(), StringSort, emptySet(), emptySet(), IntSort) {
  override fun buildExpression(
      param: Expression<StringSort>,
      bindings: Bindings
  ): Expression<IntSort> = StrToInt(param)
}

class StrFromInt(val inner: Expression<IntSort>) : Expression<StringSort>() {
  override val symbol: Symbol = "str.from_int".symbol()
  override val sort: StringSort = StringSort

  override fun toString(): String = "(str.from_int $inner)"
}

object StrFromIntDecl :
    FunctionDecl1<IntSort, StringSort>(
        "str.from_code".symbol(), emptySet(), IntSort, emptySet(), emptySet(), StringSort) {
  override fun buildExpression(
      param: Expression<IntSort>,
      bindings: Bindings
  ): Expression<StringSort> = StrFromInt(param)
}

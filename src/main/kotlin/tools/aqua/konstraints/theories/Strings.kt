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

import tools.aqua.konstraints.smt.*

object StringSort : Sort("String")

object RegLan : Sort("RegLan")

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

class StrLength(val inner: Expression<StringSort>) : Expression<StringSort>() {
  override val symbol: Symbol = "str.len".symbol()
  override val sort: StringSort = StringSort

  override fun toString(): String = "(str.len $inner)"
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

/*
 * Regular expression functions
 */

class ToRegEx(val inner: Expression<StringSort>) : Expression<RegLan>() {
  override val symbol: Symbol = "str.to_reg".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "(str.to_reg $inner)"
}

class InRegEx(val inner: Expression<StringSort>, val regex: Expression<RegLan>) :
    Expression<BoolSort>() {
  override val symbol: Symbol = "str.in_reg".symbol()
  override val sort: BoolSort = BoolSort

  override fun toString(): String = "(str.in_reg $inner $regex)"
}

class RegexNone() : Expression<RegLan>() {
  override val symbol: Symbol = "re.none".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "($symbol)"
}

class RegexAll() : Expression<RegLan>() {
  override val symbol: Symbol = "re.all".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "($symbol)"
}

class RegexAllChar() : Expression<RegLan>() {
  override val symbol: Symbol = "re.allchar".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "($symbol)"
}

class RegexConcat(val regex: List<Expression<RegLan>>) : Expression<RegLan>() {
  constructor(vararg regex: Expression<RegLan>) : this(regex.toList())

  override val symbol: Symbol = "re.++".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "(re.++ ${regex.joinToString (" ")})"
}

class RegexUnion(val regex: List<Expression<RegLan>>) : Expression<RegLan>() {
  constructor(vararg regex: Expression<RegLan>) : this(regex.toList())

  override val symbol: Symbol = "re.union".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "(re.union ${regex.joinToString (" ")})"
}

class RegexIntersec(val regex: List<Expression<RegLan>>) : Expression<RegLan>() {
  constructor(vararg regex: Expression<RegLan>) : this(regex.toList())

  override val symbol: Symbol = "re.inter".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "(re.inter ${regex.joinToString (" ")})"
}

class RegexStar(val inner: Expression<RegLan>) : Expression<RegLan>() {
  override val symbol: Symbol = "re.*".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "(re.* $inner)"
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

class StrAt(val inner: Expression<StringSort>, val position: Expression<IntSort>) :
    Expression<StringSort>() {
  override val symbol: Symbol = "str.at".symbol()
  override val sort: StringSort = StringSort

  override fun toString(): String = "(str.at $inner $position)"
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

class StrPrefixOf(val inner: Expression<StringSort>, val prefix: Expression<StringSort>) :
    Expression<BoolSort>() {
  override val symbol: Symbol = "str.prefixof".symbol()
  override val sort: BoolSort = BoolSort

  override fun toString(): String = "(str.prefixof $inner $prefix)"
}

class StrSuffixOf(val inner: Expression<StringSort>, val suffix: Expression<StringSort>) :
    Expression<BoolSort>() {
  override val symbol: Symbol = "str.suffixof".symbol()
  override val sort: BoolSort = BoolSort

  override fun toString(): String = "(str.suffixof $inner $suffix)"
}

class StrContains(val string: Expression<StringSort>, val substring: Expression<StringSort>) :
    Expression<BoolSort>() {
  override val symbol: Symbol = "str.contains".symbol()
  override val sort: BoolSort = BoolSort

  override fun toString(): String = "(str.contains $string $substring)"
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

class StrReplace(
    val inner: Expression<StringSort>,
    val old: Expression<StringSort>,
    val new: Expression<StringSort>
) : Expression<StringSort>() {
  override val symbol: Symbol = "str.replace".symbol()
  override val sort: StringSort = StringSort

  override fun toString(): String = "(str.replace $inner $old $new)"
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

class StrReplaceRegex(
    val inner: Expression<StringSort>,
    val old: Expression<RegLan>,
    val new: Expression<StringSort>
) : Expression<StringSort>() {
  override val symbol: Symbol = "str.replace_re".symbol()
  override val sort: StringSort = StringSort

  override fun toString(): String = "(str.replace_re $inner $old $new)"
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

class RegexComp(val inner: Expression<RegLan>) : Expression<RegLan>() {
  override val symbol: Symbol = "re.comp".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "(re.comp $inner)"
}

class RegexDiff(val regex: List<Expression<RegLan>>) : Expression<RegLan>() {
  constructor(vararg regex: Expression<RegLan>) : this(regex.toList())

  override val symbol: Symbol = "re.diff".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "(re.diff ${regex.joinToString(" ")})"
}

class RegexPlus(val inner: Expression<RegLan>) : Expression<RegLan>() {
  override val symbol: Symbol = "re.+".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "(re.+ $inner)"
}

class RegexOption(val inner: Expression<RegLan>) : Expression<RegLan>() {
  override val symbol: Symbol = "re.opt".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "(re.opt $inner)"
}

class RegexRange(val lhs: Expression<StringSort>, val rhs: Expression<StringSort>) :
    Expression<RegLan>() {
  override val symbol: Symbol = "re.range".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "(re.range $lhs $rhs)"
}

class RegexPower(val inner: Expression<RegLan>, val n: Int) : Expression<RegLan>() {
  override val symbol: Symbol = "re.^".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "((_ re.^ $n) $inner)"
}

class RegexLoop(val inner: Expression<RegLan>, val n: Int, val m: Int) : Expression<RegLan>() {
  override val symbol: Symbol = "re.loop".symbol()
  override val sort: RegLan = RegLan

  override fun toString(): String = "((_ re.loop $n $m) $inner)"
}

/*
 * Maps to and from integer
 */

class StrIsDigit(val inner: Expression<StringSort>) : Expression<BoolSort>() {
  override val symbol: Symbol = "str.is_digit".symbol()
  override val sort: BoolSort = BoolSort

  override fun toString(): String = "(str.is_digit $inner)"
}

class StrToCode(val inner: Expression<StringSort>) : Expression<IntSort>() {
  override val symbol: Symbol = "str.to_code".symbol()
  override val sort: IntSort = IntSort

  override fun toString(): String = "(str.to_code $inner)"
}

class StrFromCode(val inner: Expression<IntSort>) : Expression<StringSort>() {
  override val symbol: Symbol = "str.from_code".symbol()
  override val sort: StringSort = StringSort

  override fun toString(): String = "(str.from_code $inner)"
}

class StrToInt(val inner: Expression<StringSort>) : Expression<IntSort>() {
  override val symbol: Symbol = "str.to_int".symbol()
  override val sort: IntSort = IntSort

  override fun toString(): String = "(str.to_int $inner)"
}

class StrFromInt(val inner: Expression<IntSort>) : Expression<StringSort>() {
  override val symbol: Symbol = "str.from_int".symbol()
  override val sort: StringSort = StringSort

  override fun toString(): String = "(str.from_int $inner)"
}
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

/** String sort */
object StringSort : Sort("String")

/** Regular expression sort */
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
class Char(val value: String) : Literal<StringSort>(LiteralString("char"), StringSort) {
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  val character = Char(Integer.parseInt(value.substring(2)))

  override fun copy(children: List<Expression<*>>): Expression<StringSort> = this
}

class StringLiteral(val value: String) : Literal<StringSort>(LiteralString(value), StringSort) {
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet
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
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  constructor(vararg strings: Expression<StringSort>) : this(strings.toList())

  override val children: List<Expression<StringSort>> = strings

  override fun copy(children: List<Expression<*>>): Expression<StringSort> =
      StrConcatDecl.buildExpression(children, emptyList())
}

/**
 * String length
 *
 * (str.len String Int)
 */
class StrLength(override val inner: Expression<StringSort>) :
    UnaryExpression<IntSort, StringSort>("str.len".symbol(), IntSort) {
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      StrLengthDecl.buildExpression(children, emptyList())
}

/**
 * Lexicographic ordering
 *
 * (str.< String String Bool :chainable)
 */
class StrLexOrder(val strings: List<Expression<StringSort>>) :
    HomogenousExpression<BoolSort, StringSort>("str.<".symbol(), BoolSort) {
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  constructor(vararg strings: Expression<StringSort>) : this(strings.toList())

  override val children: List<Expression<StringSort>> = strings

  init {
    require(strings.size > 1) {
      "Lexicographic order needs at least two strings but ${strings.size} were given!"
    }
  }

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      StrLexOrderDecl.buildExpression(children, emptyList())
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
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  override fun copy(children: List<Expression<*>>): Expression<RegLan> =
      ToRegexDecl.buildExpression(children, emptyList())
}

/**
 * RE membership
 *
 * (str.in_re String RegLan Bool)
 */
class InRegex(val inner: Expression<StringSort>, val regex: Expression<RegLan>) :
    BinaryExpression<BoolSort, StringSort, RegLan>("str.in_reg".symbol(), BoolSort) {
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  override val lhs: Expression<StringSort> = inner

  override val rhs: Expression<RegLan> = regex

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      InRegexDecl.buildExpression(children, emptyList())
}

/**
 * Constant denoting the empty set of strings
 *
 * (re.none RegLan)
 */
object RegexNone : ConstantExpression<RegLan>("re.none".symbol(), RegLan) {
    override val theories = setOf(Theories.STRINGS)

  override fun copy(children: List<Expression<*>>): Expression<RegLan> = this
}

/**
 * Constant denoting the set of all strings
 *
 * (re.all RegLan)
 */
object RegexAll : ConstantExpression<RegLan>("re.all".symbol(), RegLan) {
    override val theories = setOf(Theories.STRINGS)

  override fun copy(children: List<Expression<*>>): Expression<RegLan> = this
}

/**
 * Constant denoting the set of all strings of length 1
 *
 * (re.allchar RegLan)
 */
object RegexAllChar : ConstantExpression<RegLan>("re.allchar".symbol(), RegLan) {
    override val theories = setOf(Theories.STRINGS)

  override fun copy(children: List<Expression<*>>): Expression<RegLan> = this
}

/**
 * RE concatenation
 *
 * (re.++ RegLan RegLan RegLan :left-assoc)
 */
class RegexConcat(val regex: List<Expression<RegLan>>) :
    HomogenousExpression<RegLan, RegLan>("re.++".symbol(), RegLan) {
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  constructor(vararg regex: Expression<RegLan>) : this(regex.toList())

  override val children: List<Expression<RegLan>> = regex

  override fun copy(children: List<Expression<*>>): Expression<RegLan> =
      RegexConcatDecl.buildExpression(children, emptyList())
}

/**
 * RE union
 *
 * (re.union RegLan RegLan RegLan :left-assoc)
 */
class RegexUnion(val regex: List<Expression<RegLan>>) :
    HomogenousExpression<RegLan, RegLan>("re.union".symbol(), RegLan) {
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  constructor(vararg regex: Expression<RegLan>) : this(regex.toList())

  override val children: List<Expression<RegLan>> = regex

  override fun copy(children: List<Expression<*>>): Expression<RegLan> =
      RegexUnionDecl.buildExpression(children, emptyList())
}

/**
 * RE intersection
 *
 * (re.inter RegLan RegLan RegLan :left-assoc)
 */
class RegexIntersec(val regex: List<Expression<RegLan>>) :
    HomogenousExpression<RegLan, RegLan>("re.inter".symbol(), RegLan) {
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  constructor(vararg regex: Expression<RegLan>) : this(regex.toList())

  override val children: List<Expression<RegLan>> = regex

  override fun copy(children: List<Expression<*>>): Expression<RegLan> =
      RegexIntersecDecl.buildExpression(children, emptyList())
}

/**
 * Kleene Closure
 *
 * (re.* RegLan RegLan)
 */
class RegexStar(override val inner: Expression<RegLan>) :
    UnaryExpression<RegLan, RegLan>("re.*".symbol(), RegLan) {
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  override fun copy(children: List<Expression<*>>): Expression<RegLan> =
      RegexStarDecl.buildExpression(children, emptyList())
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
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  constructor(vararg strings: Expression<StringSort>) : this(strings.toList())

  override val children: List<Expression<StringSort>> = strings

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      StrRefLexOrderDecl.buildExpression(children, emptyList())
}

/**
 * Singleton string containing a character at given position or empty string when position is out of
 * range. The leftmost position is 0.
 *
 * (str.at String Int String)
 */
class StrAt(val inner: Expression<StringSort>, val position: Expression<IntSort>) :
    BinaryExpression<StringSort, StringSort, IntSort>("str.at".symbol(), StringSort) {
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  override val lhs: Expression<StringSort> = inner

  override val rhs: Expression<IntSort> = position

  override fun copy(children: List<Expression<*>>): Expression<StringSort> =
      StrAtDecl.buildExpression(children, emptyList())
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
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  override val lhs: Expression<StringSort> = inner

  override val mid: Expression<IntSort> = start

  override val rhs: Expression<IntSort> = length

  override fun copy(children: List<Expression<*>>): Expression<StringSort> =
      StrSubstringDecl.buildExpression(children, emptyList())
}

/**
 * [prefix] is a prefix of [inner]
 *
 * (str.prefixof String String Bool)
 */
class StrPrefixOf(val prefix: Expression<StringSort>, val inner: Expression<StringSort>) :
    BinaryExpression<BoolSort, StringSort, StringSort>("str.prefixof".symbol(), BoolSort) {
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  override val lhs: Expression<StringSort> = prefix

  override val rhs: Expression<StringSort> = inner

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      StrPrefixOfDecl.buildExpression(children, emptyList())
}

/**
 * [suffix] is a suffix of [inner]
 *
 * (str.suffixof String String Bool)
 */
class StrSuffixOf(val suffix: Expression<StringSort>, val inner: Expression<StringSort>) :
    BinaryExpression<BoolSort, StringSort, StringSort>("str.suffixof".symbol(), BoolSort) {
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  override val lhs: Expression<StringSort> = suffix

  override val rhs: Expression<StringSort> = inner

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      StrSuffixOfDecl.buildExpression(children, emptyList())
}

/**
 * [string] contains [substring]
 *
 * (str.contains String String Bool)
 */
class StrContains(val string: Expression<StringSort>, val substring: Expression<StringSort>) :
    BinaryExpression<BoolSort, StringSort, StringSort>("str.contains".symbol(), BoolSort) {
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  override val lhs: Expression<StringSort> = string

  override val rhs: Expression<StringSort> = substring

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      StrContainsDecl.buildExpression(children, emptyList())
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
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  override val lhs: Expression<StringSort> = string

  override val mid: Expression<StringSort> = substring

  override val rhs: Expression<IntSort> = start

  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      StrIndexOfDecl.buildExpression(children, emptyList())
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
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  override val lhs: Expression<StringSort> = inner

  override val mid: Expression<StringSort> = old

  override val rhs: Expression<StringSort> = new

  override fun copy(children: List<Expression<*>>): Expression<StringSort> =
      StrReplaceDecl.buildExpression(children, emptyList())
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
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  override val lhs: Expression<StringSort> = inner

  override val mid: Expression<StringSort> = old

  override val rhs: Expression<StringSort> = new

  override fun copy(children: List<Expression<*>>): Expression<StringSort> =
      StrReplaceAllDecl.buildExpression(children, emptyList())
}

/** (str.replace_re String RegLan String String) */
class StrReplaceRegex(
    val inner: Expression<StringSort>,
    val old: Expression<RegLan>,
    val new: Expression<StringSort>
) :
    TernaryExpression<StringSort, StringSort, RegLan, StringSort>(
        "str.replace_re".symbol(), StringSort) {
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  override val lhs: Expression<StringSort> = inner

  override val mid: Expression<RegLan> = old

  override val rhs: Expression<StringSort> = new

  override fun copy(children: List<Expression<*>>): Expression<StringSort> =
      StrReplaceRegexDecl.buildExpression(children, emptyList())
}

/** (str.replace_re_all String RegLan String String) */
class StrReplaceAllRegex(
    val inner: Expression<StringSort>,
    val old: Expression<RegLan>,
    val new: Expression<StringSort>
) :
    TernaryExpression<StringSort, StringSort, RegLan, StringSort>(
        "str.replace_re_all".symbol(), StringSort) {
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  override val lhs: Expression<StringSort> = inner

  override val mid: Expression<RegLan> = old

  override val rhs: Expression<StringSort> = new

  override fun copy(children: List<Expression<*>>): Expression<StringSort> =
      StrReplaceAllRegexDecl.buildExpression(children, emptyList())
}

/**
 * RE complement
 *
 * (re.comp RegLan RegLan)
 */
class RegexComp(override val inner: Expression<RegLan>) :
    UnaryExpression<RegLan, RegLan>("re.comp".symbol(), RegLan) {
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  override fun copy(children: List<Expression<*>>): Expression<RegLan> =
      RegexCompDecl.buildExpression(children, emptyList())
}

/**
 * RE difference
 *
 * (re.diff RegLan RegLan RegLan :left-assoc)
 */
class RegexDiff(val regex: List<Expression<RegLan>>) :
    HomogenousExpression<RegLan, RegLan>("re.diff".symbol(), RegLan) {
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  constructor(vararg regex: Expression<RegLan>) : this(regex.toList())

  override val children: List<Expression<RegLan>> = regex

  override fun copy(children: List<Expression<*>>): Expression<RegLan> =
      RegexDiffDecl.buildExpression(children, emptyList())
}

/**
 * RE Kleene cross
 *
 * (re.+ RegLan RegLan)
 */
class RegexPlus(override val inner: Expression<RegLan>) :
    UnaryExpression<RegLan, RegLan>("re.+".symbol(), RegLan) {
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  override fun copy(children: List<Expression<*>>): Expression<RegLan> =
      RegexPlusDecl.buildExpression(children, emptyList())
}

/**
 * RE option
 *
 * (re.opt RegLan RegLan)
 */
class RegexOption(override val inner: Expression<RegLan>) :
    UnaryExpression<RegLan, RegLan>("re.opt".symbol(), RegLan) {
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  override fun copy(children: List<Expression<*>>): Expression<RegLan> =
      RegexOptionDecl.buildExpression(children, emptyList())
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
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  override fun copy(children: List<Expression<*>>): Expression<RegLan> =
      RegexRangeDecl.buildExpression(children, emptyList())
}

/** ((_ re.^ n) RegLan RegLan) */
class RegexPower(override val inner: Expression<RegLan>, val n: Int) :
    UnaryExpression<RegLan, RegLan>("re.^".symbol(), RegLan) {
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  override fun toString(): String = "((_ re.^ $n) $inner)"

  override fun copy(children: List<Expression<*>>): Expression<RegLan> =
      RegexPowerDecl.buildExpression(children, emptyList())
}

/** ((_ re.loop n₁ n₂) RegLan RegLan) */
class RegexLoop(override val inner: Expression<RegLan>, val n: Int, val m: Int) :
    UnaryExpression<RegLan, RegLan>("re.loop".symbol(), RegLan) {
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  override fun toString(): String = "((_ re.loop $n $m) $inner)"

  override fun copy(children: List<Expression<*>>): Expression<RegLan> =
      RegexLoopDecl.buildExpression(children, emptyList())
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
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> =
      StrIsDigitDecl.buildExpression(children, emptyList())
}

/** (str.to_code String Int) */
class StrToCode(override val inner: Expression<StringSort>) :
    UnaryExpression<IntSort, StringSort>("str.to_code".symbol(), IntSort) {
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      StrToCodeDecl.buildExpression(children, emptyList())
}

/** (str.from_code Int String) */
class StrFromCode(override val inner: Expression<IntSort>) :
    UnaryExpression<StringSort, IntSort>("str.from_code".symbol(), StringSort) {
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  override fun copy(children: List<Expression<*>>): Expression<StringSort> =
      StrFromCodeDecl.buildExpression(children, emptyList())
}

/**
 * Conversion to integers
 *
 * (str.to_int String Int)
 */
class StrToInt(override val inner: Expression<StringSort>) :
    UnaryExpression<IntSort, StringSort>("str.to_int".symbol(), IntSort) {
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  override fun copy(children: List<Expression<*>>): Expression<IntSort> =
      StrToIntDecl.buildExpression(children, emptyList())
}

/**
 * Conversion from integers
 *
 * (str.from_int Int String)
 */
class StrFromInt(override val inner: Expression<IntSort>) :
    UnaryExpression<StringSort, IntSort>("str.from_int".symbol(), StringSort) {
    companion object {
        private val theoriesSet = setOf(Theories.STRINGS)
    }

    override val theories : Set<Theories>
        get() = theoriesSet

  override fun copy(children: List<Expression<*>>): Expression<StringSort> =
      StrFromIntDecl.buildExpression(children, emptyList())
}

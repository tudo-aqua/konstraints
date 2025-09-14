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

/**
 * Representation of an SMT Symbol.
 *
 * @throws IllegalSymbolException if [raw] is not a valid SMT Symbol
 */
// constructor is internal to prevent external subclassing of Symbol
// is simple has default value checkIsSimple(raw) this function returns true for simple symbols,
// false for all other symbols and throws for invalid strings
// this can be used to skip the legal symbol check internally by directly constructing a symbol and
// setting this manually (e.g. when the parser already verified that a symbol is simple)
open class Symbol
internal constructor(
    raw: String,
    val wasQuoted: Boolean,
    val isSimple: Boolean = checkIsSimple(raw)
) : BaseSymbol {
  /**
   * Internal representation of the symbol without quotes, quoting will be reconstructed by
   * [toSMTString] before giving the symbol to a solver.
   */
  val value: String = raw.trim('|')

  companion object {
    /** public substitute for constructor. */
    operator fun invoke(symbol: String, wasQuoted: Boolean): Symbol = this(symbol, wasQuoted)

    /**
     * @return true if [raw] is a simple symbol, false if [raw] is only valid as quoted symbol
     * @throws [IllegalSymbolException] if [raw] is not a legal symbol
     */
    private fun checkIsSimple(raw: String) =
        // check if we have a simple symbol (that is a symbol that is valid without quotes)
        if (!raw[0].isDigit() && raw.all { ch -> ch in simpleSet } && raw !in reservedSet) {
          true
        }
        // quoted symbols start and end with '|'
        else if (raw.startsWith('|') &&
            raw.endsWith('|') &&
            raw.drop(1).dropLast(1).all { ch -> ch in quotedSet }) {
          false
        }
        // check if we have a quoted symbol that is not already quoted (raw is of the form "symbol"
        // and is not a simple symbol)
        else if (raw.all { ch -> ch in quotedSet }) {
          false
        } else {
          throw IllegalSymbolException(raw)
        }

    // set of all smt reserved words
    private val reservedSet =
        setOf(
            "!",
            "_",
            "as",
            "BINARY",
            "DECIMAL",
            "exists",
            "HEXADECIMAL",
            "forall",
            "lambda",
            "let",
            "match",
            "NUMERAL",
            "par",
            "STRING",
            "assert",
            "check-sat",
            "check-sat-assuming",
            "declare-const",
            "declare-datatype",
            "declare-datatypes",
            "declare-fun",
            "declare-sort",
            "declare-sort-parameter",
            "define-const",
            "define-fun",
            "define-fun-rec",
            "define-sort",
            "echo",
            "exit",
            "get-assertions",
            "get-assignment",
            "get-info",
            "get-model",
            "get-option",
            "get-proof",
            "get-unsat-assumptions",
            "get-unsat-core",
            "get-value",
            "pop",
            "push",
            "reset",
            "reset-assertions",
            "set-info",
            "set-logic",
            "set-option")

    private val whitespaceSet = setOf(' ', '\t', '\r', '\n')
    private val digitSet = (0..9).map { n -> n.digitToChar() }.toSet()
    private val letterSet = ((65..90) + (97..122)).map { n -> n.toChar() }.toSet()

    // set of all legal characters in a simple symbol
    private val simpleSet =
        setOf('~', '!', '@', '$', '%', '^', '&', '*', '_', '-', '+', '=', '<', '>', '.', '?', '/')
            .union(digitSet)
            .union(letterSet)

    // set of all legal characters in a quoted symbol
    // 92 is skipped as '\' is not allowed
    // 124 is skipped as '|' is not allowed
    private val quotedSet =
        ((32..91) + (93..123) + (125..126) + (128..255))
            .map { n -> n.toChar() }
            .toSet()
            .union(whitespaceSet)
  }

  // TODO fun createSimilar replaces all illegal chars and marks with uuid to prevent name conflicts

  override fun hashCode(): Int = value.hashCode()

  override fun equals(other: Any?): Boolean =
      when {
        this === other -> true
        other !is Symbol -> false
        else -> value == other.value
      }

  /** Returns the internal representation of the symbol without any quotes. */
  override fun toString() = toSMTString(QuotingRule.SAME_AS_INPUT)

  /** Returns a valid SMT String with reconstructed quoting. */
  override fun toSMTString(rule: QuotingRule) =
      when (rule) {
        QuotingRule.NEVER -> if (!isSimple) throw IllegalSymbolException(value) else value
        QuotingRule.SAME_AS_INPUT -> if (!isSimple) "|$value|" else value
        QuotingRule.WHEN_NEEDED -> if (wasQuoted || !isSimple) "|$value|" else value
        QuotingRule.ALWAYS -> "|$value|"
      }

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule): Appendable =
      builder.append(toSMTString(quotingRule))
}

class IllegalSymbolException(val symbol: String) :
    RuntimeException("$symbol is not a legal SMT symbol")

fun String.toSymbolWithQuotes() = Symbol(this, this.startsWith("|") && this.endsWith("|"))

fun String.toSymbolAsIs(wasQuoted: Boolean = false) = Symbol(this, wasQuoted)

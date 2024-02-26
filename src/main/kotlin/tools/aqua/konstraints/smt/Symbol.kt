/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2023 The Konstraints Authors
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

import tools.aqua.konstraints.parser.Parser

/**
 * Quoting rules for SMT String
 *
 * @property NONE no modification will be done
 * @property SMART automatically determines whether the string needs quoting or not
 * @property FORCED quotes the string if it is not already quoted
 */
enum class QuotingRule {
  /** No modification will be done */
  NONE,

  /** Automatically determines whether the string needs quoting or not */
  SMART,

  /** Quotes the string if it is not already quoted */
  FORCED
}

/**
 * Representation of an SMT Symbol
 *
 * @param symbol String containing the SMT Symbol
 * @param rule [QuotingRule] applied to the Symbol
 * @throws IllegalSymbolException if [symbol] is not a valid SMT Symbol
 */
class Symbol(symbol: String, rule: QuotingRule) {
  /** If true the Symbol was explicitly quoted when constructed */
  val isQuoted: Boolean

  /** If true the Symbol is only a valid SMT Symbol if it is quoted */
  val mustQuote: Boolean

  /**
   * Internal representation of the symbol without quotes, quoting will be reconstructed by
   * [toSMTString] before giving the symbol to a solver
   */
  val value: String

  /**
   * Construct a Symbol from String with [QuotingRule.NONE]
   *
   * @throws IllegalSymbolException if [symbol] is not a valid SMT Symbol
   */
  constructor(symbol: String) : this(symbol, QuotingRule.NONE)

  init {
    when (rule) {
      QuotingRule.NONE -> {
        // Parser must consume the entire string so .end() is needed
        if (Parser.simpleSymbol.end().accept(symbol) && !Parser.reserved.end().accept(symbol)) {
          isQuoted = false
          mustQuote = false
        } else if (Parser.quotedSymbol.end().accept(symbol)) {
          isQuoted = true
          mustQuote = true
        } else {
          throw IllegalSymbolException(symbol)
        }
      }
      QuotingRule.SMART -> {
        if (Parser.simpleSymbol.end().accept(symbol)) {
          isQuoted = false
          mustQuote = false
        } else if (Parser.quotedSymbol.end().accept(symbol)) {
          isQuoted = false
          mustQuote = true
        } else {
          throw IllegalSymbolException(symbol)
        }
      }
      QuotingRule.FORCED -> {
        if (Parser.quotedSymbol.end().accept(symbol)) {
          isQuoted = true
          mustQuote = true
        } else if (Parser.simpleSymbol.end().accept(symbol)) {
          isQuoted = true
          mustQuote = true
        } else {
          throw IllegalSymbolException(symbol)
        }
      }
    }

    value = symbol.trim('|')
  }

  // TODO fun createSimilar replaces all illegal chars and marks with uuid to prevent name conflicts

  override fun hashCode(): Int = value.hashCode()

  override fun equals(other: Any?): Boolean =
      when {
        this === other -> true
        other !is Symbol -> false
        else -> symbolEquality(other)
      }

  private fun symbolEquality(other: Symbol): Boolean {
    return value == other.value
  }

  /** Returns the internal representation of the symbol without any quotes */
  override fun toString() = value

  /** Returns a valid SMT String with reconstructed quoting */
  fun toSMTString() = if (mustQuote) "|$value|" else value
}

class IllegalSymbolException(val symbol: String) :
    RuntimeException("$symbol is not a legal SMT symbol")

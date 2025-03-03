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

import tools.aqua.konstraints.parser.Parser
import tools.aqua.konstraints.theories.False

/**
 * Quoting rules for SMT String
 *
 * @property NONE no modification will be done
 * @property SMART automatically determines whether the string needs quoting or not
 * @property FORCED quotes the string if it is not already quoted
 */
enum class QuotingRule {
  /**
   * No Symbol will be quoted, note this will result in exceptions if symbols must be quoted to be
   * valid
   */
  NEVER,

  /** No modification will be done */
  SAME_AS_INPUT,

  /** Automatically determines whether the string needs quoting or not */
  WHEN_NEEDED,

  /** Quotes the string if it is not already quoted */
  ALWAYS
}

/**
 * Representation of an SMT Symbol
 *
 * @param raw String containing the SMT Symbol
 * @throws IllegalSymbolException if [raw] is not a valid SMT Symbol
 */
// constructor is internal to prevent external subclassing of Symbol
open class Symbol internal constructor(raw: String, val wasQuoted: Boolean) : SMTSerializable {
  /** If true the Symbol is only a valid SMT Symbol if it is quoted */
  // Parser must consume the entire string so .end() is needed
  val mustQuote: Boolean =
      // check if we have a simple symbol (that is a symbol that is valid without quotes)
      if (Parser.simpleSymbol.end().accept(raw) && !Parser.reserved.end().accept(raw)) {
        false
      }
      // check if we have a quoted symbol that is already quoted (raw is of the form "|symbol|" and is not a simple symbol)
      else if (Parser.quotedSymbol.end().accept(raw)) {
          true
      }
      // check if we have a quoted symbol that is not already quoted (raw is of the form "symbol" and is not a simple symbol)
      else if (Parser.quotedSymbol.end().accept("|$raw|")) {
        true
      } else {
        throw IllegalSymbolException(raw)
      }

  /**
   * Internal representation of the symbol without quotes, quoting will be reconstructed by
   * [toSMTString] before giving the symbol to a solver
   */
  val value: String = raw.trim('|')

  companion object {
    /** public substitute for constructor */
    operator fun invoke(symbol: String, wasQuoted: Boolean): Symbol = this(symbol, wasQuoted)
  }

  // TODO fun createSimilar replaces all illegal chars and marks with uuid to prevent name conflicts

  override fun hashCode(): Int = value.hashCode()

  override fun equals(other: Any?): Boolean =
      when {
        this === other -> true
        other !is Symbol -> false
        else -> value == other.value
      }

  /** Returns the internal representation of the symbol without any quotes */
  override fun toString() = value

  /** Returns a valid SMT String with reconstructed quoting */
  fun toSMTString(rule: QuotingRule = QuotingRule.SAME_AS_INPUT) =
      when (rule) {
        QuotingRule.NEVER -> if (mustQuote) throw IllegalSymbolException(value) else value
        QuotingRule.SAME_AS_INPUT -> if (wasQuoted) "|$value|" else value
        QuotingRule.WHEN_NEEDED -> if (wasQuoted || mustQuote) "|$value|" else value
        QuotingRule.ALWAYS -> "|$value|"
      }
}

class IllegalSymbolException(val symbol: String) :
    RuntimeException("$symbol is not a legal SMT symbol")

fun String.toSymbolWithQuotes() = Symbol(this, this.startsWith("|") && this.endsWith("|"))
fun String.toSymbolAsIs(wasQuoted : Boolean = false) = Symbol(this, wasQuoted)
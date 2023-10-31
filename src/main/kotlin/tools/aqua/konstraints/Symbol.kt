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

package tools.aqua.konstraints

import tools.aqua.konstraints.parser.Parser
import tools.aqua.konstraints.parser.ParseSymbol

enum class QUOTING_RULE {
  NONE,
  SMART,
  FORCED
}

class Symbol(symbol: String, rule: QUOTING_RULE) {
  var isQuoted = false
  var mustQuote = false
  var value = ""

  constructor(symbol: String) : this(symbol, QUOTING_RULE.NONE)

  init {
    when (rule) {
      QUOTING_RULE.NONE -> {
        // Parser must consume the entire string so .end() is needed
        if (Parser.simpleSymbol.end().accept(symbol) && !Parser.reserved.end().accept(symbol)) {
          isQuoted = false
          mustQuote = false
        } else if (Parser.quotedSymbol.end().accept(symbol)) {
          isQuoted = true
          mustQuote = true
        } else {
          // TODO Implement IllegalSymbolException
          throw IllegalArgumentException("$symbol is not a valid smt symbol")
        }

        value = symbol
      }
      QUOTING_RULE.SMART -> {
        if (Parser.simpleSymbol.end().accept(symbol)) {
          isQuoted = false
          mustQuote = false

          value = symbol
        } else if (Parser.quotedSymbol.end().accept(symbol)) {
          isQuoted = false
          mustQuote = true

          value = symbol.trim('|')
        } else {
          // TODO Implement IllegalSymbolException
          throw IllegalArgumentException("$symbol is not a valid smt symbol")
        }
      }
      QUOTING_RULE.FORCED -> {
        if (Parser.quotedSymbol.end().accept(symbol)) {
          isQuoted = true
          mustQuote = true

          value = symbol
        } else if (Parser.simpleSymbol.end().accept(symbol)) {
          isQuoted = true
          mustQuote = true

          value = "|$symbol|"
        } else {
          // TODO Implement IllegalSymbolException
          throw IllegalArgumentException("$symbol is not a valid smt symbol")
        }
      }
    }
  }

  //TODO fun createSimilar replaces all illegal chars and marks with uuid to prevent name conflicts

  override fun hashCode(): Int = value.hashCode()

  override fun equals(other: Any?): Boolean = when {
    this === other -> true
    other !is Symbol -> false
    else -> symbolEquality(other)
  }

  private fun symbolEquality(other : Symbol) : Boolean {
    return value.trim('|') == other.value.trim('|')
  }
}

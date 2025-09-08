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

/**
 * Quoting rules for SMT String, used when serializing program.
 *
 * @property NEVER will never quote any symbol, even if the constructing string is quoted
 * @property SAME_AS_INPUT no modification will be done
 * @property WHEN_NEEDED automatically determines whether the symbol needs quoting or not
 * @property ALWAYS quotes all symbols
 */
enum class QuotingRule {
  /**
   * No Symbol will be quoted, note this will result in exceptions if symbols must be quoted to be
   * valid.
   */
  NEVER,

  /** No modification will be done. */
  SAME_AS_INPUT,

  /** Automatically determines whether the string needs quoting or not. */
  WHEN_NEEDED,

  /** Quotes the string if it is not already quoted. */
  ALWAYS
}

interface SMTSerializable {
  fun toSMTString(quotingRule: QuotingRule): String

  fun toSMTString(builder: StringBuilder, quotingRule: QuotingRule): StringBuilder
}

interface BaseSymbol : SMTSerializable

/** String representation of a smt keyword. */
class Keyword(val value: String) : BaseSymbol {
  init {
    Parser.reserved.parse(value)
  }

  override fun equals(other: Any?): Boolean =
      if (this === other) true else if (other !is Keyword) false else value == other.value

  override fun hashCode() = value.hashCode()

  override fun toSMTString(quotingRule: QuotingRule) = value

  override fun toSMTString(builder: StringBuilder, quotingRule: QuotingRule) =
      builder.append(toSMTString(quotingRule))
}

/** String representation of a smt literal. */
class LiteralString(val value: String) : BaseSymbol {
  override fun toString() = value

  override fun toSMTString(quotingRule: QuotingRule) = value

  override fun toSMTString(builder: StringBuilder, quotingRule: QuotingRule) =
      builder.append(toSMTString(quotingRule))
}

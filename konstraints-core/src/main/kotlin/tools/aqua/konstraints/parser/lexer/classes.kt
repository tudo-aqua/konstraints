/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2026 The Konstraints Authors
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

package tools.aqua.konstraints.parser.lexer

val ASCII_PRINTABLES = ' '..'~'
val CAPITAL_HEX_DIGITS = 'A'..'F'
val CAPITAL_LETTERS = 'A'..'Z'
val DIGITS = '0'..'9'
val LOWERCASE_HEX_DIGITS = 'a'..'f'
val LOWERCASE_LETTERS = 'a'..'z'

val Char.isSMTWhiteSpace
  get() =
      when (this) {
        '\t',
        '\n',
        '\r',
        ' ' -> true
        else -> false
      }

val Char.isSMTLineBreak
  get() =
      when (this) {
        '\n',
        '\r' -> true
        else -> false
      }

val Char.isNotSMTLineBreak
  get() = !isSMTLineBreak

val Char.isDigit
  get() = this in DIGITS

val Char.isNotDigit
  get() = !isDigit

val Char.isHexadecimalDigit
  get() =
      when (this) {
        in DIGITS,
        in CAPITAL_HEX_DIGITS,
        in LOWERCASE_HEX_DIGITS -> true
        else -> false
      }

val Char.isBinaryDigit
  get() = this == '0' || this == '1'

val Char.isStringLetter
  get() =
      when (this) {
        in ASCII_PRINTABLES,
        '\t',
        '\n',
        '\r',
        ' ' -> true
        else -> this >= '\u0080'
      }

val Char.isSimpleSymbolLetter
  get() =
      when (this) {
        in CAPITAL_LETTERS,
        in LOWERCASE_LETTERS,
        in DIGITS,
        '+',
        '-',
        '/',
        '*',
        '=',
        '%',
        '?',
        '!',
        '.',
        '$',
        '_',
        '~',
        '&',
        '^',
        '<',
        '>',
        '@' -> true
        else -> false
      }

val Char.isQuotedSymbolLetter
  get() = isStringLetter && this != '\\'

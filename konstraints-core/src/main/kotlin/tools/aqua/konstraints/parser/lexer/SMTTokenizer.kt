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

package tools.aqua.konstraints.parser.lexer

import java.io.Reader
import java.io.StringReader
import java.math.BigDecimal
import java.math.BigInteger
import tools.aqua.konstraints.lexer.CAPITAL_LETTERS
import tools.aqua.konstraints.lexer.DIGITS
import tools.aqua.konstraints.lexer.LOWERCASE_LETTERS
import tools.aqua.konstraints.lexer.UnexpectedCharacterException
import tools.aqua.konstraints.lexer.UnexpectedEOFException
import tools.aqua.konstraints.lexer.isBinaryDigit
import tools.aqua.konstraints.lexer.isDigit
import tools.aqua.konstraints.lexer.isHexadecimalDigit
import tools.aqua.konstraints.lexer.isNotSMTLineBreak
import tools.aqua.konstraints.lexer.isQuotedSymbolLetter
import tools.aqua.konstraints.lexer.isSMTWhiteSpace
import tools.aqua.konstraints.lexer.isSimpleSymbolLetter
import tools.aqua.konstraints.lexer.isStringLetter
import tools.aqua.konstraints.location.SourceLocation
import tools.aqua.konstraints.util.lineColumnTracking
import tools.aqua.konstraints.util.peekIsNot
import tools.aqua.konstraints.util.peekable
import tools.aqua.konstraints.util.readWhile

class SMTTokenizer(sourceReader: Reader, private val source: String? = null) : Iterator<Token> {
  private val reader = sourceReader.buffered().peekable().lineColumnTracking()

  private val readerLastLocation
    get() = SourceLocation(reader.lastLine, reader.lastColumn, source)

  private val readerNextLocation
    get() = SourceLocation(reader.nextLine, reader.nextColumn, source)

  private var tokenStartLocation = readerNextLocation

  override fun hasNext(): Boolean = reader.peek() >= 0

  override fun next(): Token {
    // TODO maybe return EOF token here instead of throwing although this violates the iterator
    // interface
    if (!hasNext()) return EOFToken(tokenStartLocation.asSingletonSpan())

    tokenStartLocation = readerNextLocation

    // read next token skipping all whitespace and comment tokens
    var token: Token? = null
    do {
      token =
          when (reader.peek().toChar()) {
            '\t',
            '\r',
            '\n',
            ' ' -> readWhitespace()
            ';' -> readComment()
            '(' -> readOpeningBracket()
            ')' -> readClosingBracket()
            in DIGITS -> readNumeralOrDecimal()
            '#' -> readHexadecimalOrBinary()
            '"' -> readString()
            in CAPITAL_LETTERS,
            in LOWERCASE_LETTERS,
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
            '@' -> readSimpleSymbolOrReservedWord()
            '|' -> readQuotedSymbol()
            ':' -> readKeyword()
            else ->
                throw UnexpectedCharacterException(
                    readerNextLocation,
                    reader.peek().toChar(),
                    "a valid starting symbol for a SMT token",
                )
          }
    } while ((token is Whitespace || token is Comment) && hasNext())

    // reached EOF on whitespace tokens return EOF
    if ((token is Whitespace || token is Comment))
        token = EOFToken(readerNextLocation.asSingletonSpan())

    return token
  }

  private fun readWhitespace(): Whitespace {
    val string = reader.readWhile(Char::isSMTWhiteSpace)
    return Whitespace(string, tokenStartLocation..readerLastLocation)
  }

  private fun readComment(): Comment {
    requireReadChar(';')
    val string = reader.readWhile(Char::isNotSMTLineBreak)
    return Comment(string, tokenStartLocation..readerLastLocation)
  }

  private fun readOpeningBracket(): OpeningBracket {
    requireReadChar('(')
    return OpeningBracket(tokenStartLocation.asSingletonSpan())
  }

  private fun readClosingBracket(): ClosingBracket {
    requireReadChar(')')
    return ClosingBracket(tokenStartLocation.asSingletonSpan())
  }

  private fun readNumeralOrDecimal(): Token {
    val beforeDot = requireReadWhile("a number", Char::isDigit)
    if (reader.peekIsNot { it == '.' }) {
      return Numeral(BigInteger(beforeDot), tokenStartLocation..readerLastLocation)
    }

    requireReadChar('.')
    val afterDot = requireReadWhile("a number", Char::isDigit)

    return Decimal(BigDecimal("$beforeDot.$afterDot"), tokenStartLocation..readerLastLocation)
  }

  private fun readHexadecimalOrBinary(): Token {
    requireReadChar('#')
    val specifier = requireRead("either 'x' or 'b'") { it == 'x' || it == 'b' }

    return if (specifier == 'x') {
      val number = requireReadWhile("a hexadecimal number", Char::isHexadecimalDigit)
      Hexadecimal(number, tokenStartLocation..readerLastLocation)
    } else {
      val number = requireReadWhile("a binary number", Char::isBinaryDigit)
      Binary(number, tokenStartLocation..readerLastLocation)
    }
  }

  private fun readString(): SMTString {
    requireReadChar('"')
    val string = buildString {
      while (true) {
        val next = requireRead("whitespace or a printable character") { it.isStringLetter }

        if (next != '"') {
          // normal character
          append(next)
          continue
        }

        if (reader.peekIsNot { it == '"' }) {
          // end of string
          break
        } else {
          // quoted '"'
          requireReadChar('"') // discard second '"'
          append("\"\"")
        }
      }
    }
    return SMTString(string, tokenStartLocation..readerLastLocation)
  }

  private fun readSimpleSymbolOrReservedWord(): Token {
    val symbol = requireReadWhile("a simple symbol", Char::isSimpleSymbolLetter)
    val source = tokenStartLocation..readerLastLocation
    return reservedWords[symbol]?.let { it(source) } ?: SimpleSymbolToken(symbol, source)
  }

  private fun readQuotedSymbol(): QuotedSymbolToken {
    requireReadChar('|')
    val symbol = buildString {
      while (true) {
        val next =
            requireRead("whitespace or a printable character except '\\'") {
              it.isQuotedSymbolLetter
            }

        if (next == '|') {
          // end of symbol
          break
        } else {
          // normal character
          append(next)
        }
      }
    }
    return QuotedSymbolToken(symbol, tokenStartLocation..readerLastLocation)
  }

  private fun readKeyword(): KeywordToken {
    requireReadChar(':')
    val symbol = requireReadWhile("a simple symbol", Char::isSimpleSymbolLetter)
    return KeywordToken(symbol, tokenStartLocation..readerLastLocation)
  }

  private inline fun requirePeek(hint: String, predicate: (Char) -> Boolean): Char {
    val next = reader.peek()
    if (next < 0) throw UnexpectedEOFException(readerLastLocation, hint)

    val nextChar = next.toChar()
    if (!predicate(nextChar)) throw UnexpectedCharacterException(readerNextLocation, nextChar, hint)
    return nextChar
  }

  private inline fun requireReadWhile(hint: String, predicate: (Char) -> Boolean): String {
    requirePeek(hint, predicate)
    return reader.readWhile(predicate)
  }

  private inline fun requireRead(hint: String, predicate: (Char) -> Boolean): Char {
    val next = reader.read()
    // the reader location is not updated on EOF read
    if (next < 0) throw UnexpectedEOFException(readerLastLocation, hint)

    val nextChar = next.toChar()
    if (!predicate(nextChar)) throw UnexpectedCharacterException(readerLastLocation, nextChar, hint)
    return nextChar
  }

  private fun requireReadChar(expect: Char): Char = requireRead("a '$expect'") { it == expect }
}

fun Reader.tokenize(source: String? = null): SMTTokenizer = SMTTokenizer(this, source)

fun Reader.tokenizeFully(source: String? = null): List<Token> =
    tokenize(source).asSequence().toList()

fun String.tokenizeFully(source: String? = null): List<Token> =
    StringReader(this).use { it.tokenizeFully(source) }

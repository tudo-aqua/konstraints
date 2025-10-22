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

package tools.aqua.konstraints

import java.util.stream.Stream
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.assertThrows
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.Arguments.arguments
import org.junit.jupiter.params.provider.MethodSource
import org.junit.jupiter.params.provider.ValueSource
import tools.aqua.konstraints.smt.IllegalSymbolException
import tools.aqua.konstraints.smt.QuotingRule
import tools.aqua.konstraints.smt.Symbol
import tools.aqua.konstraints.smt.toSymbolWithQuotes

/*
 * Lifecycle.PER_CLASS is needed for MethodSource to avoid moving sources to a companion object
 * This also avoids creating a new class for every test, as this is not needed, because no data is modified
 */
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class SymbolTests {
  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "+",
              "<=",
              "x",
              "plus",
              "**",
              "$",
              "<sas",
              "<adf>",
              "abc77",
              "*\$s&6",
              ".kkk",
              ".8",
              "+34",
              "-32",
              "|32|",
              "|3bitvec|",
              "| this is a quoted symbol |",
              "| so is\nthis one |",
              "||",
              """| " can occur too |""",
              """| af klj ^*0 asfe2 (&*)&(#^ $ > > >?" ']]984|""",
              "|Łukasz|",
          ]
  )
  fun `test that same as input returns symbols with the same quotes as the input`(symbol: String) {
    val test = symbol.toSymbolWithQuotes()
    assertEquals(symbol, test.toSMTString(QuotingRule.SAME_AS_INPUT))
  }

  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "+",
              "<=",
              "x",
              "plus",
              "**",
              "$",
              "<sas",
              "<adf>",
              "abc77",
              "*\$s&6",
              ".kkk",
              ".8",
              "+34",
              "-32",
              "|32|",
              "|3bitvec|",
              "| this is a quoted symbol |",
              "| so is\nthis one |",
              "||",
              """| " can occur too |""",
              """| af klj ^*0 asfe2 (&*)&(#^ $ > > >?" ']]984|""",
          ]
  )
  fun `test that symbols internal representation is without quotes`(symbol: String) {
    val test = symbol.toSymbolWithQuotes()
    assertEquals(symbol.trim('|'), test.value)
  }

  @ParameterizedTest
  @ValueSource(strings = ["|32|", "|3bitvec|", "|assert|", "|(check-sat)|"])
  fun `test that symbol sets is simple to false for symbols that must be quoted`(symbol: String) {
    val test = symbol.toSymbolWithQuotes()
    assertTrue(!test.isSimple)
  }

  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "bit|vec",
              "|||",
              "||symbol||",
              "Łukasz", // ascii characters beyond 128dec are only allowed in quoted symbols
          ]
  )
  fun `test that symbol throws for illegal symbols`(symbol: String) {
    assertThrows<IllegalSymbolException> { symbol.toSymbolWithQuotes() }
  }

  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "+",
              "<=",
              "x",
              "plus",
              "**",
              "$",
              "<sas",
              "<adf>",
              "abc77",
              "*\$s&6",
              ".kkk",
              ".8",
              "+34",
              "-32",
          ]
  )
  fun `test that quoting mode always quotes simple symbols`(symbol: String) {
    val test = symbol.toSymbolWithQuotes()
    assertEquals("|$symbol|", test.toSMTString(QuotingRule.ALWAYS))
  }

  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "|32|",
              "|3bitvec|",
              "| this is a quoted symbol |",
              "| so is\nthis one |",
              "||",
              """| " can occur too |""",
              """| af klj ^*0 asfe2 (&*)&(#^ $ > > >?" ']]984|""",
          ]
  )
  fun `test that quoting mode always does not double quote symbols`(symbol: String) {
    val test = symbol.toSymbolWithQuotes()
    assertEquals(symbol, test.toSMTString(QuotingRule.ALWAYS))
  }

  @ParameterizedTest
  @MethodSource("getEqualSymbols")
  fun `test that equals works correct for equal symbols`(lhs: Symbol, rhs: Symbol) {
    assertEquals(lhs, rhs)
  }

  private fun getEqualSymbols(): Stream<Arguments> =
      Stream.of(
          arguments("A".toSymbolWithQuotes(), "A".toSymbolWithQuotes()),
          arguments("A".toSymbolWithQuotes(), "|A|".toSymbolWithQuotes()),
      )

  @ParameterizedTest
  @MethodSource("getUnequalSymbols")
  fun `test that equals works correct for unequal symbols`(lhs: Symbol, rhs: Symbol) {
    assertNotEquals(lhs, rhs)
  }

  private fun getUnequalSymbols(): Stream<Arguments> =
      Stream.of(arguments("A".toSymbolWithQuotes(), "B".toSymbolWithQuotes()))
}

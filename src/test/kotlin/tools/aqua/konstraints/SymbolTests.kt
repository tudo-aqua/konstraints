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

import kotlin.IllegalArgumentException
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.assertThrows
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.Arguments.arguments
import org.junit.jupiter.params.provider.MethodSource
import org.junit.jupiter.params.provider.ValueSource
import java.util.stream.Stream

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
              """| af klj ^*0 asfe2 (&*)&(#^ $ > > >?" ']]984|"""])
  fun `test that symbols without quoting rules work`(symbol: String) {
    val test = Symbol(symbol)
    assertEquals(symbol, test.value)
  }

  @ParameterizedTest
  @ValueSource(strings = ["32", "3bitvec", "assert", "(check-sat)"])
  fun `test that symbols without quoting rules throws for strings that must be quoted`(
      symbol: String
  ) {
    assertThrows<IllegalArgumentException> { Symbol(symbol) }
  }

  @ParameterizedTest
  @ValueSource(strings = ["bit|vec"])
  fun `test that symbol throws for illegal symbols`(symbol: String) {
    assertThrows<IllegalArgumentException> { Symbol(symbol) }
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
          ])
  fun `test that smart quote accepts simple symbols`(symbol: String) {
    val test = Symbol(symbol, QUOTING_RULE.SMART)
    assertEquals(symbol, test.value)
  }

  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "32",
              "3bitvec",
              " this is a quoted symbol ",
              " so is\nthis one ",
              "",
              """ " can occur too """,
              """ af klj ^*0 asfe2 (&*)&(#^ $ > > >?" ']]984"""])
  fun `test that smart quote dequotes quoted symbols`(symbol: String) {
    val test = Symbol("|$symbol|", QUOTING_RULE.SMART)
    assertEquals(symbol, test.value)
  }

  @ParameterizedTest
  @ValueSource(strings = ["bit|vec"])
  fun `test that smart quoting rejects illegal symbols`(symbol: String) {
    assertThrows<IllegalArgumentException> { Symbol(symbol, QUOTING_RULE.SMART) }
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
              "-32"])
  fun `test that forced quoting quotes simple symbols`(symbol: String) {
    val test = Symbol(symbol, QUOTING_RULE.FORCED)
    assertEquals("|$symbol|", test.value)
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
              """| af klj ^*0 asfe2 (&*)&(#^ $ > > >?" ']]984|"""])
  fun `test that forced quoting handles quoted strings correctly`(symbol: String) {
    val test = Symbol(symbol, QUOTING_RULE.FORCED)
    assertEquals(symbol, test.value)
  }

  @ParameterizedTest
  @ValueSource(strings = ["bit|vec"])
  fun `test that forced quoting does not accept illegal symbols`(symbol: String) {
    assertThrows<IllegalArgumentException> { Symbol(symbol, QUOTING_RULE.FORCED) }
  }

    @ParameterizedTest
    @MethodSource("getEqualSymbols")
    fun `test that equals works correct for equal symbols`(lhs: Symbol, rhs: Symbol) {
        assertEquals(lhs, rhs)
    }

    private fun getEqualSymbols() : Stream<Arguments> {
        return Stream.of(
            arguments(Symbol("A"), Symbol("A")),
            arguments(Symbol("A"), Symbol("|A|"))
        )
    }

    @ParameterizedTest
    @MethodSource("getUnequalSymbols")
    fun `test that equals works correct for unequal symbols`(lhs: Symbol, rhs: Symbol) {
        assertNotEquals(lhs, rhs)
    }

    private fun getUnequalSymbols() : Stream<Arguments> {
        return Stream.of(arguments(Symbol("A"), Symbol("B")))
    }
}

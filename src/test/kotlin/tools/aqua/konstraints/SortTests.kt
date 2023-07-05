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

import java.util.stream.Stream
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.assertDoesNotThrow
import org.junit.jupiter.api.assertThrows
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.Arguments.arguments
import org.junit.jupiter.params.provider.MethodSource
import org.junit.jupiter.params.provider.ValueSource
import tools.aqua.konstraints.*

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class SortTests {
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
              "32",
              "3bitvec", // these testcases are allowed as they will be quoted
              "| this is a quoted symbol |",
              "| so is\n" + "this one |",
              "||",
              """| " can occur too |""",
              """| af klj ^*0 asfe2 (&*)&(#^ $ > > >?" ']]984|"""])
  fun testSymbolPositive(symbol: String) {
    assertDoesNotThrow { SMTSymbol(symbol) }
  }

  @ParameterizedTest
  @ValueSource(strings = ["32", "3bitvec"])
  fun testImplicitQuoting(symbol: String) {
    assertEquals("|$symbol|", SMTSymbol(symbol).toString())
  }

  @ParameterizedTest
  @ValueSource(strings = ["bit|vec"])
  fun testSymbolNegative(symbol: String) {
    assertThrows<IllegalArgumentException> { SMTSymbol(symbol) }
  }

  @ParameterizedTest
  @MethodSource("testSortSerializationParameterization")
  fun testSortSerialization(symbol: String, sort: Sort) {
    assertEquals(symbol, sort.toString())
  }

  private fun testSortSerializationParameterization(): Stream<Arguments> {
    return Stream.of(
        arguments("Bool", BoolSort),
        arguments("(_ BitVec 32)", BVSort32),
        arguments("(List (Array Int Real))", ExampleListSort),
        arguments("((_ FixedSizeList 4) Real)", ExampleFixedSizeList),
        arguments("(Set (_ BitVec 32))", ExampleSet))
  }

  @ParameterizedTest
  @ValueSource(ints = [-1])
  fun testBitvectorConstraints(bits: Int) {
    assertThrows<IllegalArgumentException> { BVSort(bits) }
  }
}

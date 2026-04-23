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

package tools.aqua.konstraints

import org.junit.jupiter.api.*
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.ValueSource
import tools.aqua.konstraints.smt.FloatingPointLiteral

class FloatingPointLiteralTest {

  @Nested
  @DisplayName("Float Literal Tests")
  inner class FloatTests {

    @ParameterizedTest
    @ValueSource(
        floats =
            [
                1.23f,
                -4.56f,
                0.0f,
                -0.0f,
                Float.MAX_VALUE,
                Float.MIN_VALUE,
                Float.POSITIVE_INFINITY,
                Float.NEGATIVE_INFINITY,
            ]
    )
    fun `round trip conversion for floats`(input: Float) {
      val literal = FloatingPointLiteral(input)
      assertEquals(input, literal.asFloat())
    }

    @Test
    fun `round trip for NaN float`() {
      val literal = FloatingPointLiteral(Float.NaN)
      assertTrue(literal.asFloat().isNaN())
    }

    @Test
    fun `calling asDouble on float literal throws exception`() {
      val literal = FloatingPointLiteral(1.0f)
      assertThrows<IllegalStateException> { literal.asDouble() }
    }
  }

  @Nested
  @DisplayName("Double Literal Tests")
  inner class DoubleTests {

    @ParameterizedTest
    @ValueSource(
        doubles =
            [
                1.23,
                -4.56,
                0.0,
                -0.0,
                Double.MAX_VALUE,
                Double.MIN_VALUE,
                Double.POSITIVE_INFINITY,
                Double.NEGATIVE_INFINITY,
            ]
    )
    fun `round trip conversion for doubles`(input: Double) {
      val literal = FloatingPointLiteral(input)
      assertEquals(input, literal.asDouble())
    }

    @Test
    fun `round trip for NaN double`() {
      val literal = FloatingPointLiteral(Double.NaN)
      assertTrue(literal.asDouble().isNaN())
    }

    @Test
    fun `calling asFloat on double literal throws exception`() {
      val literal = FloatingPointLiteral(1.0)
      assertThrows<IllegalStateException> { literal.asFloat() }
    }
  }

  @Test
  @DisplayName("Verify type isolation")
  fun `ensure float and double literals are distinct`() {
    val f = FloatingPointLiteral(1.0f)
    val d = FloatingPointLiteral(1.0)

    // Even though the numeric value is the same, the internal storage type matters
    assertDoesNotThrow { f.asFloat() }
    assertDoesNotThrow { d.asDouble() }

    assertThrows<IllegalStateException> { f.asDouble() }
    assertThrows<IllegalStateException> { d.asFloat() }
  }
}

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

import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.assertDoesNotThrow
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.ValueSource
import tools.aqua.konstraints.parser.*
import tools.aqua.konstraints.smt.*

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class ParserTests {
  @ParameterizedTest
  @ValueSource(ints = [8, 32, 128, 1024, 2048, 8192])
  fun testDeepRecursion(level: Int) {
    var program = "(set-logic QF_UF)(declare-fun foo () Bool)(assert "
    (0..<level).forEach { program += "(= foo " }

    program += "(= foo foo)"

    (0..level).forEach { program += ")" }

    assertDoesNotThrow { Parser(program) }
  }
}

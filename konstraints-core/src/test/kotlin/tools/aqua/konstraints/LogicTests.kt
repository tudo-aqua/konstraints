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
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import tools.aqua.konstraints.smt.*

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class LogicTests {

  @ParameterizedTest
  @MethodSource("getLogicsAndString")
  fun testLogicToString(expected: String, actual: Logic) {
    assertEquals(expected, actual.toString())
  }

  private fun getLogicsAndString(): Stream<Arguments> {
    return Stream.of(
        Arguments.arguments("AUFLIA", AUFLIA),
        Arguments.arguments("AUFLIRA", AUFLIRA),
        Arguments.arguments("AUFNIRA", AUFNIRA),
        Arguments.arguments("LIA", LIA),
        Arguments.arguments("LRA", LRA),
        Arguments.arguments("QF_ABV", QF_ABV),
        Arguments.arguments("QF_AUFBV", QF_AUFBV),
        Arguments.arguments("QF_AUFLIA", QF_AUFLIA),
        Arguments.arguments("QF_AX", QF_AX),
        Arguments.arguments("QF_BV", QF_BV),
        Arguments.arguments("QF_IDL", QF_IDL),
        Arguments.arguments("QF_LIA", QF_LIA),
        Arguments.arguments("QF_LRA", QF_LRA),
        Arguments.arguments("QF_NIA", QF_NIA),
        Arguments.arguments("QF_NRA", QF_NRA),
        Arguments.arguments("QF_RDL", QF_RDL),
        Arguments.arguments("QF_UF", QF_UF),
        Arguments.arguments("QF_UFBV", QF_UFBV),
        Arguments.arguments("QF_UFIDL", QF_UFIDL),
        Arguments.arguments("QF_UFLIA", QF_UFLIA),
        Arguments.arguments("QF_UFLRA", QF_UFLRA),
        Arguments.arguments("QF_UFNRA", QF_UFNRA),
        Arguments.arguments("UFLRA", UFLRA),
        Arguments.arguments("UFNIA", UFNIA))
  }
}

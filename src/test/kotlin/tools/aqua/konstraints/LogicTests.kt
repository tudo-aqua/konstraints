/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2024 The Konstraints Authors
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

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class LogicTests {

  @ParameterizedTest
  @MethodSource("getLogicsAndString")
  fun testLogicToString(expected: String, actual: Logic) {
    assertEquals(expected, actual.toString())
  }

  private fun getLogicsAndString(): Stream<Arguments> {
    return Stream.of(
        Arguments.arguments("AUFLIA", Logic.AUFLIA),
        Arguments.arguments("AUFLIRA", Logic.AUFLIRA),
        Arguments.arguments("AUFNIRA", Logic.AUFNIRA),
        Arguments.arguments("LIA", Logic.LIA),
        Arguments.arguments("LRA", Logic.LRA),
        Arguments.arguments("QF_ABV", Logic.QF_ABV),
        Arguments.arguments("QF_AUFBV", Logic.QF_AUFBV),
        Arguments.arguments("QF_AUFLIA", Logic.QF_AUFLIA),
        Arguments.arguments("QF_AX", Logic.QF_AX),
        Arguments.arguments("QF_BV", Logic.QF_BV),
        Arguments.arguments("QF_IDL", Logic.QF_IDL),
        Arguments.arguments("QF_LIA", Logic.QF_LIA),
        Arguments.arguments("QF_LRA", Logic.QF_LRA),
        Arguments.arguments("QF_NIA", Logic.QF_NIA),
        Arguments.arguments("QF_NRA", Logic.QF_NRA),
        Arguments.arguments("QF_RDL", Logic.QF_RDL),
        Arguments.arguments("QF_UF", Logic.QF_UF),
        Arguments.arguments("QF_UFBV", Logic.QF_UFBV),
        Arguments.arguments("QF_UFIDL", Logic.QF_UFIDL),
        Arguments.arguments("QF_UFLIA", Logic.QF_UFLIA),
        Arguments.arguments("QF_UFLRA", Logic.QF_UFLRA),
        Arguments.arguments("QF_UFNRA", Logic.QF_UFNRA),
        Arguments.arguments("UFLRA", Logic.UFLRA),
        Arguments.arguments("UFNIA", Logic.UFNIA))
  }
}

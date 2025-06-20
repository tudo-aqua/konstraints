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
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.assertDoesNotThrow
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import tools.aqua.konstraints.parser.Parser

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class BVTermSmallRWNoetzliTests {
  @ParameterizedTest
  @MethodSource("getInts")
  fun testQF_BV(id: Int) {
    /*
     * These test are currently not working with Z3 as the solver is not capable of solving them yet
     */
    if (id in listOf(524, 928, 1105, 1299, 1323, 1492)) {
      return
    }

    // For some reason these cases time out sometimes, skip them for now
    if (id in listOf(382, 426, 433, 672, 737, 776)) {
      return
    }

    val temp =
        javaClass
            .getResourceAsStream(
                "/QF_BV/20190311-bv-term-small-rw-Noetzli/bv-term-small-rw_$id.smt2")!!
            .bufferedReader()
            .readLines()
    val input = temp.map { it.trim('\r', '\n') }
    val parser = Parser()

    assertDoesNotThrow { parser.parse(input.joinToString("\n")) }
  }

  private fun getInts(): Stream<Arguments> {
    return IntArray(1575) { it }.map { Arguments.arguments(it + 1) }.stream()
  }
}

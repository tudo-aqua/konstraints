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
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.assertNull
import org.junit.jupiter.api.assertThrows
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.Arguments.arguments
import org.junit.jupiter.params.provider.MethodSource
import tools.aqua.konstraints.util.LeveledMap
import tools.aqua.konstraints.util.zipWithSameLength

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class UtilsTest {
  @ParameterizedTest
  @MethodSource("getUnequalLengthLists")
  fun `test that zipWithSameLength throws for list with different size`(
      lhs: List<*>,
      rhs: List<*>,
  ) {
    assertThrows<IllegalArgumentException> { lhs zipWithSameLength rhs }
  }

  private fun getUnequalLengthLists(): Stream<Arguments> =
      Stream.of(
          arguments(listOf(1, 2, 3), listOf(1, 2)),
          arguments(listOf(1, 2), emptyList<Any>()),
          arguments(emptyList<Any>(), listOf(1, 2)),
      )

  @ParameterizedTest
  @MethodSource("getEqualLengthList")
  fun `test that zipWithSameLength works like zip`(lhs: List<*>, rhs: List<*>) {
    assertEquals(lhs zip rhs, lhs zipWithSameLength rhs)
  }

  private fun getEqualLengthList(): Stream<Arguments> =
      Stream.of(
          arguments(listOf(1, 2, 3), listOf(4, 5, 6)),
          arguments(listOf(1), listOf(2)),
          arguments(emptyList<Any>(), emptyList<Any>()),
      )

  @Test
  fun testPut() {
    val map = LeveledMap<Int, Int>()
    map.put(1, 1)

    assertEquals(1, map[1])
  }

  @Test
  fun testPop() {
    val map = LeveledMap<Int, Int>()
    map.push()
    map.put(1, 1)
    map.pop()

    assertNull(map[1])
  }

  @Test
  fun testPopSize() {
    val map = LeveledMap<Int, Int>()
    map.push()
    map.put(1, 1)
    map.pop()

    assertEquals(0, map.size)
  }

  @Test
  fun testPutAll() {
    val map = LeveledMap<Int, Int>()
    map.putAll(listOf(Pair(1, 1), Pair(2, 2)))

    assertEquals(1, map[1])
    assertEquals(2, map[2])
  }

  @Test
  fun testSize() {
    val map = LeveledMap<Int, Int>()
    map.put(1, 1)
    map.push()
    map.put(2, 2)

    assertEquals(2, map.size)
  }

  @Test
  fun testContainsKey() {
    val map = LeveledMap<Int, Int>()
    map.put(1, 2)

    assertTrue(map.containsKey(1))
  }

  @Test
  fun testContainsValue() {
    val map = LeveledMap<Int, Int>()
    map.put(1, 2)

    assertTrue(map.containsValue(2))
  }

  @Test fun testClear() {}
}

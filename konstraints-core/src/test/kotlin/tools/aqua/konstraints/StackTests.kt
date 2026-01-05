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

import java.util.stream.Stream
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.assertThrows
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.Arguments.arguments
import org.junit.jupiter.params.provider.MethodSource
import tools.aqua.konstraints.util.Stack

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class StackTests {
  @ParameterizedTest
  @MethodSource("getIntergerListsWithEmpty")
  fun testSize(integers: List<Int>) {
    val stack = Stack(integers)

    assertEquals(integers.size, stack.size)
  }

  @ParameterizedTest
  @MethodSource("getIntegerLists")
  fun testPeek(integers: List<Int>) {
    val stack = Stack(integers)

    assertEquals(integers.first(), stack.peek())
  }

  @ParameterizedTest
  @MethodSource("getIntergerListsWithEmpty")
  fun testPeekOrNull(integers: List<Int>) {
    val stack = Stack(integers)

    if (integers.isNotEmpty()) {
      assertEquals(integers.first(), stack.peekOrNull())
    } else {
      assertNull(stack.peekOrNull())
    }
  }

  @ParameterizedTest
  @MethodSource("getIntegerLists")
  fun testPopReturn(integers: List<Int>) {
    val stack = Stack(integers)

    assertEquals(integers.first(), stack.pop())
  }

  @ParameterizedTest
  @MethodSource("getIntergerListsWithEmpty")
  fun testPopOrNullReturn(integers: List<Int>) {
    val stack = Stack(integers)

    if (integers.isNotEmpty()) {
      assertEquals(integers.first(), stack.popOrNull())
    } else {
      assertNull(stack.popOrNull())
    }
  }

  @ParameterizedTest
  @MethodSource("getIntegerLists")
  fun testPopSize(integers: List<Int>) {
    val stack = Stack(integers)
    stack.pop()

    assertEquals(integers.size - 1, stack.size)
  }

  @ParameterizedTest
  @MethodSource("getIntegerLists")
  fun testPush(integers: List<Int>) {
    val stack1 = Stack(integers)
    val stack2 = Stack<Int>()

    integers.asReversed().forEach { stack2.push(it) }

    assertTrue((stack1 zip stack2).all { (lhs, rhs) -> lhs == rhs })
  }

  @ParameterizedTest
  @MethodSource("getEmptyLists")
  fun testPeekThrows(integers: List<Int>) {
    val stack = Stack(integers)

    assertThrows<NoSuchElementException> { stack.peek() }
  }

  @ParameterizedTest
  @MethodSource("getEmptyLists")
  fun testPopThrows(integers: List<Int>) {
    val stack = Stack(integers)

    assertThrows<NoSuchElementException> { stack.pop() }
  }

  private fun getIntegerLists(): Stream<Arguments> =
      Stream.of(
          arguments(listOf(10, 94, 81, 36, 71, 80, 66, 34, 52, 2)),
          arguments(listOf(68, 56, 35, 78, 92, 54, 45, 77, 99, 58)),
          arguments(listOf(57, 41, 51, 5, 37, 7, 16, 75, 88, 32)),
          arguments(listOf(1, 76, 26, 12, 44, 79, 86, 25, 74, 8)),
          arguments(listOf(85, 9, 63, 49, 87, 55, 31, 64, 65, 23)),
          arguments(listOf(62, 38, 69, 30, 14, 47, 29, 95, 97, 18)),
          arguments(listOf(50, 20, 96, 72, 17, 13, 89, 93, 33, 73)),
          arguments(listOf(24, 98, 84, 42, 60, 70, 19, 21, 22, 48)),
          arguments(listOf(11, 39, 4, 90, 46, 59, 91, 6, 40, 43)),
          arguments(listOf(15, 3, 83, 27, 61, 53, 82, 67, 28)),
      )

  private fun getIntergerListsWithEmpty(): Stream<Arguments> =
      Stream.of(
          arguments(emptyList<Int>()),
          arguments(listOf<Int>()),
          arguments(listOf(10, 94, 81, 36, 71, 80, 66, 34, 52, 2)),
          arguments(listOf(68, 56, 35, 78, 92, 54, 45, 77, 99, 58)),
          arguments(listOf(57, 41, 51, 5, 37, 7, 16, 75, 88, 32)),
          arguments(listOf(1, 76, 26, 12, 44, 79, 86, 25, 74, 8)),
          arguments(listOf(85, 9, 63, 49, 87, 55, 31, 64, 65, 23)),
          arguments(listOf(62, 38, 69, 30, 14, 47, 29, 95, 97, 18)),
          arguments(listOf(50, 20, 96, 72, 17, 13, 89, 93, 33, 73)),
          arguments(listOf(24, 98, 84, 42, 60, 70, 19, 21, 22, 48)),
          arguments(listOf(11, 39, 4, 90, 46, 59, 91, 6, 40, 43)),
          arguments(listOf(15, 3, 83, 27, 61, 53, 82, 67, 28)),
      )

  private fun getEmptyLists(): Stream<Arguments> =
      Stream.of(arguments(emptyList<Int>()), arguments(listOf<Int>()))
}

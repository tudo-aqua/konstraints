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
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.TestInstance.Lifecycle
import org.junit.jupiter.api.assertThrows
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.Arguments.arguments
import org.junit.jupiter.params.provider.MethodSource
import org.junit.jupiter.params.provider.ValueSource
import tools.aqua.konstraints.smt.Sort
import tools.aqua.konstraints.theories.BVSort
import tools.aqua.konstraints.theories.BoolSort

/*
 * Lifecycle.PER_CLASS is needed for MethodSource to avoid moving sources to a companion object
 * This also avoids creating a new class for every test, as this is not needed, because no data is modified
 */
@TestInstance(Lifecycle.PER_CLASS)
class SortTests {
  @ParameterizedTest
  @MethodSource("getSortsAndTheirSerialization")
  fun `test that serialization of sorts is correct`(symbol: String, sort: Sort) {
    assertEquals(symbol, sort.toString())
  }

  private fun getSortsAndTheirSerialization(): Stream<Arguments> {
    return Stream.of(arguments("Bool", BoolSort), arguments("(_ BitVec 32)", BVSort(32)))
  }

  @ParameterizedTest
  @ValueSource(ints = [-1, 0])
  fun `test that bitvectors can only be constructed with more than 0 bits`(bits: Int) {
    assertThrows<IllegalArgumentException> { BVSort(bits) }
  }

  @ParameterizedTest
  @MethodSource("getEqualBVSortObjects")
  fun `test that BVSort equals works for equal bitvectors`(lhs: BVSort, rhs: BVSort) {
    assertEquals(lhs, rhs)
  }

  // TODO implement BVSort factory so that there is only one instance of BVSort per bit length
  /*
  @ParameterizedTest
  @MethodSource("getEqualBVSortObjects")
  fun `test that BVSort objects with same bit length are the same objects`(
      lhs: BVSort,
      rhs: BVSort
  ) {
    assertSame(lhs, rhs)
  }
    */

  private fun getEqualBVSortObjects(): Stream<Arguments> {
    return Stream.of(
        arguments(BVSort(8), BVSort(8)),
        arguments(BVSort(16), BVSort(16)),
        arguments(BVSort(32), BVSort(32)))
  }

  @ParameterizedTest
  @MethodSource("getUnequalBVSortObjects")
  fun `test that BVSort equals works for unequal bitvectors`(lhs: BVSort, rhs: BVSort) {
    assertNotEquals(lhs, rhs)
  }

  @ParameterizedTest
  @MethodSource("getUnequalBVSortObjects")
  fun `test that BVSort objects with different bit length are different objects`(
      lhs: BVSort,
      rhs: BVSort
  ) {
    assertNotSame(lhs, rhs)
  }

  private fun getUnequalBVSortObjects(): Stream<Arguments> {
    return Stream.of(
        arguments(BVSort(8), BVSort(16)),
        arguments(BVSort(32), BVSort(16)),
        arguments(BVSort(16), BVSort(32)))
  }

  @ParameterizedTest
  @MethodSource("getBVSortObjects")
  fun `test that BVSort hash code returns the same value on multiple invocations`(
      bitvector: BVSort
  ) {
    assertEquals(bitvector.hashCode(), bitvector.hashCode())
  }

  private fun getBVSortObjects(): Stream<Arguments> {
    return Stream.of(arguments(BVSort(32)), arguments(BVSort(16)), arguments(BVSort(8)))
  }

  @ParameterizedTest
  @MethodSource("getEqualBVSortObjects")
  fun `test that equal BVSorts return the same hash code`(lhs: BVSort, rhs: BVSort) {
    assertEquals(lhs.hashCode(), rhs.hashCode())
  }
}

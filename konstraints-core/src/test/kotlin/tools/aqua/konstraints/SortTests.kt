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
import org.junit.jupiter.api.TestInstance.Lifecycle
import org.junit.jupiter.api.assertThrows
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.Arguments.arguments
import org.junit.jupiter.params.provider.MethodSource
import org.junit.jupiter.params.provider.ValueSource
import tools.aqua.konstraints.smt.BitVecFactory
import tools.aqua.konstraints.smt.BitVecSort
import tools.aqua.konstraints.smt.SMTBool
import tools.aqua.konstraints.smt.Sort

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
    return Stream.of(arguments("Bool", SMTBool), arguments("(_ BitVec 32)", BitVecSort(32)))
  }

  @ParameterizedTest
  @ValueSource(ints = [-1, 0])
  fun `test that bitvectors can only be constructed with more than 0 bits`(bits: Int) {
    assertThrows<IllegalArgumentException> { BitVecSort(bits) }
  }

  @ParameterizedTest
  @MethodSource("getEqualBVSortObjects")
  fun `test that BVSort equals works for equal bitvectors`(lhs: BitVecSort, rhs: BitVecSort) {
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
        arguments(BitVecSort(8), BitVecSort(8)),
        arguments(BitVecSort(16), BitVecSort(16)),
        arguments(BitVecSort(32), BitVecSort(32)),
    )
  }

  @ParameterizedTest
  @MethodSource("getUnequalBVSortObjects")
  fun `test that BVSort equals works for unequal bitvectors`(lhs: BitVecSort, rhs: BitVecSort) {
    assertNotEquals(lhs, rhs)
  }

  @ParameterizedTest
  @MethodSource("getUnequalBVSortObjects")
  fun `test that BVSort objects with different bit length are different objects`(
      lhs: BitVecSort,
      rhs: BitVecSort,
  ) {
    assertNotSame(lhs, rhs)
  }

  private fun getUnequalBVSortObjects(): Stream<Arguments> {
    return Stream.of(
        arguments(BitVecSort(8), BitVecSort(16)),
        arguments(BitVecSort(32), BitVecSort(16)),
        arguments(BitVecSort(16), BitVecSort(32)),
    )
  }

  @ParameterizedTest
  @MethodSource("getBVSortObjects")
  fun `test that BVSort hash code returns the same value on multiple invocations`(
      bitvector: BitVecSort
  ) {
    assertEquals(bitvector.hashCode(), bitvector.hashCode())
  }

  private fun getBVSortObjects(): Stream<Arguments> {
    return Stream.of(arguments(BitVecSort(32)), arguments(BitVecSort(16)), arguments(BitVecSort(8)))
  }

  @ParameterizedTest
  @MethodSource("getEqualBVSortObjects")
  fun `test that equal BVSorts return the same hash code`(lhs: BitVecSort, rhs: BitVecSort) {
    assertEquals(lhs.hashCode(), rhs.hashCode())
  }

  @ParameterizedTest
  @MethodSource("generateInts")
  fun `test that BitVecFactory cache works`(n: Int) {
    assert(BitVecFactory.build(n).bits == n)
  }

  private fun generateInts(): Stream<Arguments> {
    return (1..2048)
        .plus(listOf(4096, 8192, 16384, 32786, 65536))
        .map { i -> arguments(i) }
        .stream()
  }
}

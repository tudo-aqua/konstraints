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
import org.junit.jupiter.api.TestInstance.Lifecycle
import org.junit.jupiter.api.assertDoesNotThrow
import org.junit.jupiter.api.assertThrows
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.Arguments.arguments
import org.junit.jupiter.params.provider.MethodSource

/*
 * Lifecycle.PER_CLASS is needed for MethodSource to avoid moving sources to a companion object
 * This also avoids creating a new class for every test, as this is not needed, because no data is modified
 */
@TestInstance(Lifecycle.PER_CLASS)
class BitvectorTests {
  private val A = BasicExpression<BVSort>("A", BVSort(8))
  private val B = BasicExpression<BVSort>("B", BVSort(8))
  private val C = BasicExpression<BVSort>("C", BVSort(8))
  private val D = BasicExpression<BVSort>("D", BVSort(16))
  private val symbolicE = BasicExpression("E", BVSort.fromSymbol("a"))
  private val symbolicF = BasicExpression("F", BVSort.fromSymbol("b"))

  @ParameterizedTest
  @MethodSource("getBVExpressionsAndSerialization")
  fun `test that serialization of BV expressions is correct`(
      expected: String,
      expression: Expression<BVSort>
  ) {
    assertEquals(expected, expression.toString())
  }

  private fun getBVExpressionsAndSerialization(): Stream<Arguments> {
    return Stream.of(
        arguments("(concat A B)", BVConcat(A, B)),
        arguments("((_ extract 4 0) A)", BVExtract(4, 0, A)),
        arguments("((_ extract 0 0) A)", BVExtract(0, 0, A)),
        arguments("(bvnot A)", BVNot(A)),
        arguments("(bvneg A)", BVNeg(A)),
        arguments("(bvand A B)", BVAnd(A, B)),
        arguments("(bvand A B C)", BVAnd(A, B, C)),
        arguments("(bvor A B)", BVOr(A, B)),
        arguments("(bvor A B C)", BVOr(A, B, C)),
        arguments("(bvadd A B)", BVAdd(A, B)),
        arguments("(bvadd A B C)", BVAdd(A, B, C)),
        arguments("(bvmul A B)", BVMul(A, B)),
        arguments("(bvmul A B C)", BVMul(A, B, C)),
        arguments("(bvudiv A B)", BVUDiv(A, B)),
        arguments("(bvurem A B)", BVURem(A, B)),
        arguments("(bvshl A B)", BVShl(A, B)),
        arguments("(bvlshr A B)", BVLShr(A, B)),
        arguments("(bvult A B)", BVUlt(A, B)))
  }

  @ParameterizedTest
  @MethodSource("getBVExtractParametrization")
  fun `test that BVExtract throws an exception if constraints for i and j are not matched`(
      i: Int,
      j: Int
  ) {
    assertThrows<IllegalArgumentException> { BVExtract(i, j, A) }
  }

  private fun getBVExtractParametrization(): Stream<Arguments> {
    return Stream.of(
        arguments(0, -1),
        arguments(-1, 0),
        arguments(1, 2),
        arguments(8, 2),
    )
  }

  @ParameterizedTest
  @MethodSource("getListConstructorsAndErrorArgs")
  fun `test that an exception is thrown for different BV lengths`(
      constructor: (List<Expression<BVSort>>) -> Expression<BVSort>,
      args: List<Expression<BVSort>>
  ) {
    assertThrows<IllegalArgumentException> { constructor(args) }
  }

  private fun getListConstructorsAndErrorArgs(): Stream<Arguments> {
    val bvand: (List<Expression<BVSort>>) -> Expression<BVSort> = ::BVAnd
    val bvor: (List<Expression<BVSort>>) -> Expression<BVSort> = ::BVOr
    val bvadd: (List<Expression<BVSort>>) -> Expression<BVSort> = ::BVAdd
    val bvmul: (List<Expression<BVSort>>) -> Expression<BVSort> = ::BVMul
    return Stream.of(
        arguments(bvand, listOf(A, D)),
        arguments(bvor, listOf(A, D)),
        arguments(bvadd, listOf(A, D)),
        arguments(bvmul, listOf(A, D)))
  }

  @ParameterizedTest
  @MethodSource("getRegularConstructorsAndErrorArgs")
  fun `test that an exception is thrown when lhs and rhs BV length does not match`(
      constructor: (Expression<BVSort>, Expression<BVSort>) -> Expression<BVSort>,
      lhs: Expression<BVSort>,
      rhs: Expression<BVSort>
  ) {
    assertThrows<IllegalArgumentException> { constructor(lhs, rhs) }
  }

  private fun getRegularConstructorsAndErrorArgs(): Stream<Arguments> {
    return Stream.of(
        arguments(::BVShl, A, D),
        arguments(::BVURem, A, D),
        arguments(::BVShl, A, D),
        arguments(::BVLShr, A, D))
  }

  @ParameterizedTest
  @MethodSource("getRegularConstructors")
  fun `test that constructor does not throw when BV length matches`(
      constructor: (Expression<BVSort>, Expression<BVSort>) -> Expression<BVSort>,
      lhs: Expression<BVSort>,
      rhs: Expression<BVSort>
  ) {
    assertDoesNotThrow { constructor(lhs, rhs) }
  }

  private fun getRegularConstructors(): Stream<Arguments> {
    return Stream.of(
        arguments(::BVShl, A, B),
        arguments(::BVURem, A, B),
        arguments(::BVShl, A, B),
        arguments(::BVLShr, A, B))
  }

  @ParameterizedTest
  @MethodSource("getListConstructors")
  fun `test that list constructor does not throw when BV length matches`(
      constructor: (List<Expression<BVSort>>) -> Expression<BVSort>,
      args: List<Expression<BVSort>>
  ) {
    assertDoesNotThrow { constructor(args) }
  }

  private fun getListConstructors(): Stream<Arguments> {
    val bvand: (List<Expression<BVSort>>) -> Expression<BVSort> = ::BVAnd
    val bvor: (List<Expression<BVSort>>) -> Expression<BVSort> = ::BVOr
    val bvadd: (List<Expression<BVSort>>) -> Expression<BVSort> = ::BVAdd
    val bvmul: (List<Expression<BVSort>>) -> Expression<BVSort> = ::BVMul
    return Stream.of(
        arguments(bvand, listOf(A, B)),
        arguments(bvor, listOf(A, B)),
        arguments(bvadd, listOf(A, B)),
        arguments(bvmul, listOf(A, B)))
  }
}

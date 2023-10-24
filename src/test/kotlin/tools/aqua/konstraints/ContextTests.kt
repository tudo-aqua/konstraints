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
import org.junit.jupiter.api.assertThrows
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.Arguments.arguments
import org.junit.jupiter.params.provider.MethodSource
import tools.aqua.konstraints.parser.Context
import tools.aqua.konstraints.parser.FunctionDecl

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class ContextTests {
  private val context = Context()
  private val boolExpression = BasicExpression("A", BoolSort)
  private val bv32Expression = BasicExpression("B", BVSort(32))
  private val bv16Expression = BasicExpression("B", BVSort(16))

  init {
    context.registerTheory(CoreContext)
    context.registerTheory(BitVectorExpressionContext)
      context.registerFunction("O", listOf(BoolSort, BoolSort), BoolSort)
      context.registerFunction("O", listOf(BVSort(32), BVSort(32)), BVSort(32))
  }

  @ParameterizedTest
  @MethodSource("getFunctionNameAndArgs")
  fun `Check that Context returns none null function`(
      name: String,
      args: List<Expression<*>>,
      sort: Sort
  ) {
    val function = context.getFunction(name, args)

    assertNotNull(function)
  }

  @ParameterizedTest
  @MethodSource("getFunctionNameAndArgs")
  fun `Check that Context returns function with correct name`(
      name: String,
      args: List<Expression<*>>,
      sort: Sort
  ) {
    val function = context.getFunction(name, args)

    assertEquals(name, function?.name)
  }

  @ParameterizedTest
  @MethodSource("getFunctionNameAndArgs")
  fun `Check that Context returns function with correct sort`(
      name: String,
      args: List<Expression<*>>,
      sort: Sort
  ) {
    val function = context.getFunction(name, args)

    assertEquals(sort, function?.sort)
  }

  @ParameterizedTest
  @MethodSource("getFunctionNameAndArgs")
  fun `Check that Function accepts parameters`(
      name: String,
      args: List<Expression<*>>,
      sort: Sort
  ) {
    val function = context.getFunction(name, args)

    requireNotNull(function)
    assert(function.accepts(args))
  }

  private fun getFunctionNameAndArgs(): Stream<Arguments> {
    return Stream.of(
        arguments("and", listOf(boolExpression, boolExpression), BoolSort),
        arguments("and", listOf(boolExpression, boolExpression, boolExpression), BoolSort),
        arguments("or", listOf(boolExpression, boolExpression), BoolSort),
        arguments("or", listOf(boolExpression, boolExpression, boolExpression), BoolSort),
        arguments("xor", listOf(boolExpression, boolExpression), BoolSort),
        arguments("xor", listOf(boolExpression, boolExpression, boolExpression), BoolSort),
        arguments("bvult", listOf(bv16Expression, bv16Expression), BoolSort),
        arguments("bvult", listOf(bv32Expression, bv32Expression), BoolSort),
        arguments("O", listOf(boolExpression, boolExpression), BoolSort),
        arguments("O", listOf(bv32Expression, bv32Expression), BVSort(32)),
        arguments("O", listOf(bv16Expression, bv16Expression), BVSort(32))
    )
  }

  @ParameterizedTest
  @MethodSource("getFunctionNameAndIncorrectArgs")
  fun `Check that Function rejects incorrect parameters`(
      function: FunctionDecl<*>,
      args: List<Expression<*>>
  ) {
    assertFalse(function.accepts(args))
  }

    @ParameterizedTest
    @MethodSource("getFunctionNameAndIncorrectArgs")
    fun `Check that Expression generation fails for incorrect parameters`(
        function: FunctionDecl<*>,
        args: List<Expression<*>>
    ) {
        assertThrows<Exception> { function.getExpression(args) }
    }

  private fun getFunctionNameAndIncorrectArgs(): Stream<Arguments> {
    return Stream.of(
        arguments(AndDecl, listOf(boolExpression, boolExpression, bv16Expression)),
        arguments(OrDecl, listOf(boolExpression, boolExpression, bv16Expression)),
        arguments(XOrDecl, listOf(boolExpression, boolExpression, bv16Expression)),
        arguments(BVUltDecl, listOf(bv16Expression)),
        arguments(BVUltDecl, listOf(boolExpression, boolExpression)),
        arguments(BVUltDecl, listOf(bv16Expression, boolExpression)),
        arguments(BVUltDecl, listOf(bv16Expression, bv32Expression)),
        arguments(BVUltDecl, listOf(bv32Expression, bv16Expression)))
  }
}

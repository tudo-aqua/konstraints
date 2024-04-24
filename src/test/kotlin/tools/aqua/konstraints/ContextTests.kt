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
import org.junit.jupiter.api.*
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.Arguments.arguments
import org.junit.jupiter.params.provider.MethodSource
import tools.aqua.konstraints.parser.*
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.theories.*

/*
 * TestInstance per class is needed for parameterized tests
 * It is important to note that the class will not be reinitialized for each test,
 * so we need to make sure the test does not modify the context in an unpredictable way
 */
@TestInstance(TestInstance.Lifecycle.PER_CLASS)

/*
 * Test order will be fixed here to modify context in later tests without breaking other tests
 */
@TestMethodOrder(MethodOrderer.OrderAnnotation::class)
class ContextTests {
  private val context = Context(BitVectorExpressionContext)
  private val boolExpression = BasicExpression("A".symbol(), BoolSort)
  private val bv32Expression = BasicExpression("B".symbol(), BVSort(32))
  private val bv16Expression = BasicExpression("B".symbol(), BVSort(16))

  // this function has no indices as it is not infinitary, BVSort(32) here means actually only
  // bitvectors of length 32
  private val overloadedBV =
      FunctionDecl(
          "O".symbol(),
          emptySet(),
          listOf(BVSort(32), BVSort(32)),
          emptySet(),
          emptySet(),
          BVSort(32),
          Associativity.NONE)

  init {
    context.registerFunction("O", listOf(BoolSort, BoolSort), BoolSort)
  }

  @ParameterizedTest
  @MethodSource("getFunctionNameAndArgs")
  @Order(1)
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
  @Order(2)
  fun `Check that Context returns function with correct name`(
      name: String,
      args: List<Expression<*>>,
      sort: Sort
  ) {
    val function = context.getFunction(name, args)

    assertEquals(name.symbol(), function?.name)
  }

  @ParameterizedTest
  @MethodSource("getFunctionNameAndArgs")
  @Order(3)
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
  @Order(4)
  fun `Check that Function accepts parameters`(
      name: String,
      args: List<Expression<*>>,
      sort: Sort
  ) {
    val function = context.getFunction(name, args)

    requireNotNull(function)
    assert(function.acceptsExpressions(args, emptySet()))
  }

  private fun getFunctionNameAndArgs(): Stream<Arguments> {
    return Stream.of(arguments("O", listOf(boolExpression, boolExpression), BoolSort))
  }

  @ParameterizedTest
  @MethodSource("getFunctionNameAndIncorrectArgs")
  @Order(5)
  fun `Check that Function rejects incorrect parameters`(
      function: FunctionDecl<*>,
      args: List<Expression<*>>
  ) {
    assertFalse(function.acceptsExpressions(args, emptySet()))
  }

  @ParameterizedTest
  @MethodSource("getFunctionNameAndIncorrectArgs")
  @Order(6)
  fun `Check that Expression generation fails for incorrect parameters`(
      function: FunctionDecl<*>,
      args: List<Expression<*>>
  ) {
    assertThrows<Exception> { function.buildExpression(args, emptySet()) }
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
        arguments(BVUltDecl, listOf(bv32Expression, bv16Expression)),
        arguments(overloadedBV, listOf(bv16Expression, bv16Expression)),
        arguments(EqualsDecl, listOf(boolExpression, bv16Expression)),
        arguments(EqualsDecl, listOf(boolExpression, boolExpression, bv16Expression)),
        arguments(EqualsDecl, listOf(boolExpression, bv16Expression, boolExpression)))
  }

  /*
   * This test must be executed after all of the above tests, as the function symbol "and" will become ambiguous
   * making it illegal to use outside "match" and "as"
   */
  @ParameterizedTest
  @MethodSource("getFunctionDeclarations")
  @Order(7)
  fun `test that legal functions can be registered`(func: FunctionDecl<*>) {
    context.registerFunction(func)
  }

  private fun getFunctionDeclarations(): Stream<Arguments> {
    return Stream.of(
        /* No conflict */
        arguments(
            FunctionDecl(
                "foo".symbol(),
                emptySet(),
                listOf(BoolSort, BoolSort),
                emptySet(),
                emptySet(),
                BoolSort,
                Associativity.NONE)))
  }

  @Test
  fun testLetShadowingOfLet() {
    context.let(listOf(VarBinding("A".symbol(), And(True, True)))) {
      context.let(listOf(VarBinding("A".symbol(), Or(True, True)))) {
        assert((context.getFunction("A", emptyList()) as VarBinding).term.symbol.toString() == "or")
      }
    }
  }

  @ParameterizedTest
  @MethodSource("getIllegalFunctionDeclarations")
  @Order(8)
  fun `test that redeclaration of functions throws FunctionAlreadyDeclaredException`(
      func: FunctionDecl<*>
  ) {
    assertThrows<IllegalFunctionOverloadException> { context.registerFunction(func) }
  }

  private fun getIllegalFunctionDeclarations(): Stream<Arguments> {
    return Stream.of(
        /* Illegal */
        arguments(
            FunctionDecl(
                "and".symbol(),
                emptySet(),
                listOf(BoolSort, BoolSort, BoolSort),
                emptySet(),
                emptySet(),
                BoolSort,
                Associativity.NONE)),
        /* Illegal */
        arguments(
            FunctionDecl(
                "bvult".symbol(),
                emptySet(),
                listOf(BVSort(16), BVSort(16)),
                emptySet(),
                emptySet(),
                BoolSort,
                Associativity.NONE)),
        /* New overloaded */
        arguments(
            FunctionDecl(
                "and".symbol(),
                emptySet(),
                listOf(BVSort(16), BVSort(16)),
                emptySet(),
                emptySet(),
                BoolSort,
                Associativity.NONE)),
        /* New ambiguous */
        arguments(
            FunctionDecl(
                "and".symbol(),
                emptySet(),
                listOf(BoolSort, BoolSort, BoolSort),
                emptySet(),
                emptySet(),
                BVSort(16),
                Associativity.NONE)),
        /* New ambiguous */
        arguments(
            FunctionDecl(
                "bvult".symbol(),
                emptySet(),
                listOf(BVSort(16), BVSort(16)),
                emptySet(),
                emptySet(),
                BVSort(16),
                Associativity.NONE)),
        /* ??? */
        arguments(
            FunctionDecl(
                "bvult".symbol(),
                emptySet(),
                listOf(BVSort(16), BVSort(32)),
                emptySet(),
                emptySet(),
                BoolSort,
                Associativity.NONE)))
  }
}

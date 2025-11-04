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
import org.junit.jupiter.api.*
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.Arguments.arguments
import org.junit.jupiter.params.provider.MethodSource
import tools.aqua.konstraints.dsl.*
import tools.aqua.konstraints.smt.*

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class ContextTests {
  val boolFunc1 = UserDeclaredSMTFunction0("A".toSymbolWithQuotes(), Bool)
  val boolFunc2 = UserDeclaredSMTFunction2("B".toSymbolWithQuotes(), Bool, BVSort(8), BVSort(8))
  val boolFunc2Copy = UserDeclaredSMTFunction2("B".toSymbolWithQuotes(), Bool, BVSort(8), BVSort(8))
  val boolFunc2Overloaded =
      UserDeclaredSMTFunction2("B".toSymbolWithQuotes(), Bool, BVSort(16), BVSort(16))

  @ParameterizedTest
  @MethodSource("getContextAndNames")
  fun testContains(context: Context, func: String) {
    assertTrue(context.contains(func))
  }

  private fun getContextAndNames(): Stream<Arguments> =
      Stream.of(arguments(createContext(), "A"), arguments(createContext(), "B"))

  @ParameterizedTest
  @MethodSource("getContextAndFunctions")
  fun testGetFunction(context: Context, func: SMTFunction<*>) {
    assertTrue(context.getFunc(func.symbol) == func)
  }

  private fun getContextAndFunctions(): Stream<Arguments> =
      Stream.of(arguments(createContext(), boolFunc1), arguments(createContext(), boolFunc2))

  @ParameterizedTest
  @MethodSource("getContextAndIllegalFunctions")
  fun testAddFails(context: Context, func: SMTFunction<*>) {
    assertThrows<IllegalArgumentException> { context.addFun(func) }
  }

  private fun getContextAndIllegalFunctions(): Stream<Arguments> =
      Stream.of(
          arguments(createContext(), boolFunc1),
          arguments(createContext(), boolFunc2),
          arguments(createContext(), boolFunc2Overloaded),
      )

  @ParameterizedTest
  @MethodSource("getContextAndIllegalNameFunctions")
  fun testAddIllegalNameFails(context: Context, func: SMTFunction<*>) {
    assertThrows<IllegalArgumentException> { context.addFun(func) }
  }

  private fun getContextAndIllegalNameFunctions(): Stream<Arguments> =
      Stream.of(
          arguments(createContext(), UserDeclaredSMTFunction0("and".toSymbolWithQuotes(), Bool)),
          arguments(createContext(), UserDeclaredSMTFunction0("true".toSymbolWithQuotes(), Bool)),
          arguments(
              createContext(),
              UserDeclaredSMTFunction0("distinct".toSymbolWithQuotes(), Bool),
          ),
          arguments(createContext(), UserDeclaredSMTFunction0("bvadd".toSymbolWithQuotes(), Bool)),
          arguments(
              createContext(),
              UserDeclaredSMTFunction0("extract".toSymbolWithQuotes(), Bool),
          ),
      )

  @Test
  fun testPopFailsOnContextWithOnlyOneLevel() {
    val context = createContext()

    assertThrows<IllegalStateException> { context.pop(1) }
  }

  @ParameterizedTest
  @MethodSource("getContextAndNewFunction")
  fun testPopRemovesFunction(context: Context, func: SMTFunction<*>) {
    context.push {
      addFun(func)

      assertTrue(context.contains(func.symbol))
    }

    assertFalse(context.contains(func.symbol))
  }

  private fun getContextAndNewFunction() =
      Stream.of(
          arguments(createContext(), UserDeclaredSMTFunction0("C".toSymbolWithQuotes(), Bool)),
      )

  @ParameterizedTest
  @MethodSource("getContextAndBindings")
  fun testBindingsAreRemovedAfterLet(context: Context, bindings: List<VarBinding<*>>) {
    context.let(bindings) { context, bindings -> True }

    assertFalse(context.contains(bindings[0].name))
  }

  private fun getContextAndBindings() =
      Stream.of(
          arguments(createContext(), listOf(VarBinding("binding".toSymbolWithQuotes(), True))),
      )

  @ParameterizedTest
  @MethodSource("getContextAndShadowingBindings")
  fun testShadowedFunctionsAreInsertedBackCorrectly(
      context: Context,
      bindings: List<VarBinding<*>>,
  ) {
    val function = context.getFunc(bindings[0].name)

    context.let(bindings) { context, bindings -> True }

    assertTrue(context.getFunc(function.symbol) == function)
  }

  @ParameterizedTest
  @MethodSource("getContextAndShadowingBindings")
  fun testFunctionsAreShadowedCorrectly(context: Context, bindings: List<VarBinding<*>>) {
    val function = context.getFunc(bindings[0].name)

    context.let(bindings) { bindings, context ->
      assertFalse(context.getFunc(function.symbol) == function)
      True
    }
  }

  private fun getContextAndShadowingBindings() =
      Stream.of(
          arguments(createContext(), listOf(VarBinding("A".toSymbolWithQuotes(), True))),
      )

  @ParameterizedTest
  @MethodSource("getContextAndQuotedFunctions")
  fun testQuotedFunctionLookup(context: Context, func: SMTFunction<*>, lookupName: String) {
    context.addFun(func)

    assertTrue(context.contains(lookupName))
  }

  private fun getContextAndQuotedFunctions() =
      Stream.of(
          arguments(
              createContext(),
              UserDeclaredSMTFunction0("|Quoted|".toSymbolWithQuotes(), Bool),
              "Quoted",
          ),
          arguments(
              createContext(),
              UserDeclaredSMTFunction0("|Quoted|".toSymbolWithQuotes(), Bool),
              "|Quoted|",
          ),
          arguments(
              createContext(),
              UserDeclaredSMTFunction0("Unquoted".toSymbolWithQuotes(), Bool),
              "|Unquoted|",
          ),
      )

  private fun createContext(): Context {
    val context = Context()
    context.setLogic(QF_BV)

    context.addFun(boolFunc1)
    context.addFun(boolFunc2)

    return context
  }
}

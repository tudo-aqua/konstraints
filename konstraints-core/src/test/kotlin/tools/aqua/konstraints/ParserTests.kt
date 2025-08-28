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
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.assertDoesNotThrow
import org.junit.jupiter.api.assertThrows
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.Arguments.arguments
import org.junit.jupiter.params.provider.MethodSource
import org.junit.jupiter.params.provider.ValueSource
import org.petitparser.context.ParseError
import org.petitparser.context.Success
import org.petitparser.parser.primitive.StringParser.of
import tools.aqua.konstraints.parser.*
import tools.aqua.konstraints.parser.Parser.Companion.anythingButQuotes
import tools.aqua.konstraints.parser.times
import tools.aqua.konstraints.smt.*

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class ParserTests {

    @ParameterizedTest
    @ValueSource(strings = [
        "(set-logic QF_S)\n"+
                "(set-info :source |\n" +
                "this is a;\n" +
                "multiline symbol\" containing\n" +
                "problematic ; characters|)\n" +
                "(set-info :status sat)\n" +
                "(declare-fun s () String)\n" +
                "(assert (\n" +
                "= ( ;this is a comment\n" +
                "str.length \";\"\"|;\"\"||;\")\n" +
                "10))" +
                "(check-sat)\n(exit)"
    ])
    fun testCommentRemoval(program : String) {
        val clean = Parser().removeComments2(program)
        println(clean)
    }

    @ParameterizedTest
    @ValueSource(strings = [
        "\"\"\"\"",
        "\"\"",
        "\"foo\"\"\"",
        "\"bar\"",
        "\"\"\"bar\""
    ])
    fun testStringParsing(string : String) {
        val parser = ((of("\"") *
                ((anythingButQuotes.star() * of("\"\"") * anythingButQuotes.star()).star()) *
                of("\"")) + (
                        of("\"") * anythingButQuotes.star() * of("\"")
                        ))
            .flatten()
            .map { str: String ->
                str.drop(1).dropLast(1)
            }

        val result = parser.parse(string).get<String>()

        assertEquals(string.drop(1).dropLast(1), result)
    }

  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "(set-logic AUFLIA)(set-info :status sat)(define-sort Arr (A) (Array Int A))(declare-fun key () Int)(declare-fun val () Int)(declare-fun array () (Arr Int))(assert (= val (select (store array key val) key)))(check-sat)",
              "(set-logic QF_UF)(define-sort custom-bool (A) Bool)(declare-fun foo () (custom-bool Bool))(assert foo)(check-sat)",
              "(set-logic QF_UF)(declare-sort sort 1)(define-sort custom-bool (A) (sort A))(declare-fun foo () (custom-bool Bool))(declare-fun bar ((custom-bool Bool)) Bool)(assert (bar foo))(check-sat)"])
  fun testDefineSort(program: String) {
    assertDoesNotThrow { Parser().parse(program) }
  }

  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "(set-logic QF_UF)(set-info :status sat)(declare-fun A () Bool)(push 1)(declare-fun B () Bool)(assert (= A B))(pop 1)(assert (= A B))(check-sat)"])
  fun testPushPopFails(program: String) {
    assertThrows<FunctionNotFoundException> { Parser().parse(program) }
  }

  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "(set-logic QF_UF)(set-info :status unknown)(assert (true true true))",
              "(set-logic QF_BV)(set-info :status unknown)(declare-fun A () (_ BitVec 8))(assert (bvult A A A))",
              "(set-logic QF_BV)(set-info :status unknown)(declare-fun A () (_ BitVec 8))(assert (bvult (bvneg A) (bvadd A A) A))",
              "(set-logic QF_FP)(set-info :status unknown)(declare-fun A () Float16)(assert (fp.isNormal A A))"])
  fun testTooManyArgsFails(program: String) {
    println(assertThrows<IllegalArgumentException> { Parser().parse(program) }.message)
  }

  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "(set-logic QF_BV)(set-info :status unknown)(declare-fun A () (_ BitVec 8))(assert (bvult A))",
              "(set-logic QF_BV)(set-info :status unknown)(declare-fun A () (_ BitVec 8))(assert (bvult (bvneg A)))",
              "(set-logic QF_FP)(set-info :status unknown)(declare-fun A () Float16)(assert (fp.isNormal (fp.fma A A)))"])
  fun testTooFewArgsFails(program: String) {
    println(assertThrows<IllegalArgumentException> { Parser().parse(program) }.message)
  }

  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "(set-logic QF_NIA)(set-info :status unknown)(declare-fun A () Int)(assert (divisible A))"])
  fun testTooFewIndicesFails(program: String) {
    println(assertThrows<IllegalArgumentException> { Parser().parse(program) }.message)
  }

  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "(set-logic QF_NIA)(set-info :status unknown)(declare-fun A () Int)(assert ((_ divisible 4 4) A))"])
  fun testTooManyIndicesFails(program: String) {
    println(assertThrows<IllegalArgumentException> { Parser().parse(program) }.message)
  }

  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "(set-logic QF_BV)(declare-fun s () (_ BitVec 32))(declare-fun t () (_ BitVec 32))(assert (not (= (bvand s s) s)))(check-sat)",
              "(set-logic QF_UF)(declare-sort S 1)(declare-fun foo ((S Bool) (S Bool)) Bool)(declare-const S1 (S Bool))(declare-const S2 (S Bool))(assert (foo S1 S2))(check-sat)",
              "(set-logic QF_UF)(declare-sort S 0)(declare-fun foo (S S) Bool)(declare-const S1 S)(declare-const S2 S)(assert (foo S1 S2))(check-sat)"])
  fun testScriptParsing(script: String) {
    val parser = Parser()
    val result = parser.script.parse(script)

    if (result.isSuccess) {
      println(result.get<String>())
    } else {
      throw ParseError(result.failure(result.message))
    }
  }

  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "(set-logic QF_UF)(push 1)(declare-sort S 0)(declare-fun foo (S S) Bool)(declare-const S1 S)(declare-const S2 S)(assert (foo S1 S2))(pop 1)(declare-fun bar (S S) Bool)(assert (bar S1 S2))(check-sat)"])
  fun testIllegalScriptParsing(script: String) {
    val parser = Parser()
    assertThrows<IllegalArgumentException> { parser.script.parse(script) }
  }

  @ParameterizedTest
  @ValueSource(
      strings =
          [
              ":produce-models true",
              ":smt-lib-version 2.6",
              ":funs ( (par (X) (emptySet (Set X)))\n" +
                  "(par (X) (univSet (Set X)))\n" +
                  "(par (X) (singleton X (Set X)))\n" +
                  "(par (X) (union (Set X) (Set X) (Set X) :left-assoc))\n" +
                  "(par (X) (inters (Set X) (Set X) (Set X) :left-assoc))\n" +
                  "(par (X) (in X (Set X) Bool))\n" +
                  "(par (X) (subset (Set X) (Set X) Bool :chainable)) )\n"])
  fun testAttributeParsing(attribute: String) {
    val result = Parser.attribute.parse(attribute)

    if (result.isSuccess) {
      println(result.get<String>())
    } else {
      throw ParseError(result.failure(result.message))
    }
  }

  @ParameterizedTest
  @MethodSource("getLogics")
  fun testLogicParsing(expected: Logic) {
    println(expected.toString())
    val result = Parser.logic.parse(expected.toString())

    if (result.isSuccess) {
      assertEquals(expected, result.get<Logic>())
    } else {
      throw ParseError(result.failure(result.message))
    }
  }

  private fun getLogics(): Stream<Arguments> {
    return Stream.of(
        arguments(AUFLIA),
        arguments(AUFLIRA),
        arguments(AUFNIRA),
        arguments(LIA),
        arguments(LRA),
        arguments(QF_ABV),
        arguments(QF_AUFBV),
        arguments(QF_AUFLIA),
        arguments(QF_AX),
        arguments(QF_BV),
        arguments(QF_IDL),
        arguments(QF_LIA),
        arguments(QF_LRA),
        arguments(QF_NIA),
        arguments(QF_NRA),
        arguments(QF_RDL),
        arguments(QF_UF),
        arguments(QF_UFBV),
        arguments(QF_UFIDL),
        arguments(QF_UFLIA),
        arguments(QF_UFLRA),
        arguments(QF_UFNRA),
        arguments(UFLRA),
        arguments(UFNIA))
  }
}

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

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.assertDoesNotThrow
import tools.aqua.konstraints.smt.And
import tools.aqua.konstraints.smt.BoolSort
import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.smt.False
import tools.aqua.konstraints.smt.Not
import tools.aqua.konstraints.smt.Or
import tools.aqua.konstraints.smt.Order
import tools.aqua.konstraints.smt.QuotingRule
import tools.aqua.konstraints.smt.True

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class ExpressionTests {
  val expr = And(Not(True), Or(False, And(True, False)))

  @Test
  fun testDeepRecursiveSequence() {
    val deepExpr = (0..2048).fold(False) { acc: Expression<BoolSort>, _ -> Not(acc) }

    assertDoesNotThrow {
      deepExpr.asSequence().forEach { println(it.toSMTString(QuotingRule.SAME_AS_INPUT, true)) }
    }
  }

  @Test
  fun testRecursivePreorderSequence() {
    val expected = mutableListOf("And", "Not", "True", "Or", "False", "And", "True", "False")
    expr.asSequence(Order.PREORDER).forEach {
      assertEquals(expected.first(), it.javaClass.name.removePrefix("tools.aqua.konstraints.smt."))
      expected.removeFirst()
    }
  }

  @Test
  fun testIterativePreorderSequence() {
    val expected = mutableListOf("And", "Not", "True", "Or", "False", "And", "True", "False")
    expr.asSequence(Order.PREORDER, true).forEach {
      assertEquals(expected.first(), it.javaClass.name.removePrefix("tools.aqua.konstraints.smt."))
      expected.removeFirst()
    }
  }

  @Test
  fun testRecursivePostorderSequence() {
    val expected = mutableListOf("True", "Not", "False", "True", "False", "And", "Or", "And")
    expr.asSequence(Order.POSTORDER).forEach {
      assertEquals(expected.first(), it.javaClass.name.removePrefix("tools.aqua.konstraints.smt."))
      expected.removeFirst()
    }
  }

  @Test
  fun testIterativePostorderSequence() {
    val expected = mutableListOf("True", "Not", "False", "True", "False", "And", "Or", "And")
    expr.asSequence(Order.POSTORDER, true).forEach {
      assertEquals(expected.first(), it.javaClass.name.removePrefix("tools.aqua.konstraints.smt."))
      expected.removeFirst()
    }
  }

  @Test
  fun testRecursivePreorderForEach() {
    val expected = mutableListOf("And", "Not", "True", "Or", "False", "And", "True", "False")
    expr.forEach(Order.PREORDER) {
      assertEquals(expected.first(), it.javaClass.name.removePrefix("tools.aqua.konstraints.smt."))
      expected.removeFirst()
    }
  }

  @Test
  fun testIterativePreorderForEach() {
    val expected = mutableListOf("And", "Not", "True", "Or", "False", "And", "True", "False")
    expr.forEach(Order.PREORDER, true) {
      assertEquals(expected.first(), it.javaClass.name.removePrefix("tools.aqua.konstraints.smt."))
      expected.removeFirst()
    }
  }

  @Test
  fun testRecursivePostorderForEach() {
    val expected = mutableListOf("True", "Not", "False", "True", "False", "And", "Or", "And")
    expr.forEach(Order.POSTORDER) {
      assertEquals(expected.first(), it.javaClass.name.removePrefix("tools.aqua.konstraints.smt."))
      expected.removeFirst()
    }
  }

  @Test
  fun testIterativePostorderForEach() {
    val expected = mutableListOf("True", "Not", "False", "True", "False", "And", "Or", "And")
    expr.forEach(Order.POSTORDER, true) {
      assertEquals(expected.first(), it.javaClass.name.removePrefix("tools.aqua.konstraints.smt."))
      expected.removeFirst()
    }
  }

  @Test
  fun testRecursiveAny() {
    assertTrue(expr.any { it is False })
  }

  @Test
  fun testIterativeAny() {
    assertTrue(expr.any(true) { it is False })
  }

  @Test
  fun testRecursiveAll() {
    assertTrue(expr.all { it.sort is BoolSort })
  }

  @Test
  fun testIterativeAll() {
    assertTrue(expr.all(true) { it.sort is BoolSort })
  }
}

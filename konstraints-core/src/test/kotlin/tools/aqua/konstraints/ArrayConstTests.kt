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
import org.junit.jupiter.api.assertThrows
import tools.aqua.konstraints.parser.SMTScriptParser
import tools.aqua.konstraints.smt.ArrayConst
import tools.aqua.konstraints.smt.ArrayStore
import tools.aqua.konstraints.smt.Assert
import tools.aqua.konstraints.smt.BitVecLiteral
import tools.aqua.konstraints.smt.BitVecSort
import tools.aqua.konstraints.smt.Equals
import tools.aqua.konstraints.smt.QuotingRule
import tools.aqua.konstraints.smt.SMTArray
import tools.aqua.konstraints.smt.SMTInt

private const val SPOUT_DECLARATION = "(declare-fun arr.content.0 () (Array Int (_ BitVec 8)))"

class ArrayConstTests {
  private fun parseAssert(declarations: String, assertion: String): Assert =
      SMTScriptParser("(set-logic ALL)$declarations$assertion")
          .commands
          .filterIsInstance<Assert>()
          .single()

  @Test
  fun `constant array as emitted by SPouT is parsed`() {
    val assert =
        parseAssert(
            SPOUT_DECLARATION,
            "(assert (= arr.content.0 (store ((as const (Array Int (_ BitVec 8))) #x00) 0 #x61)))",
        )

    val store = (assert.expr as Equals<*>).children[1] as ArrayStore<*, *>
    val const = store.array as ArrayConst<*, *>

    assertEquals(SMTArray(SMTInt, BitVecSort(8)), const.sort)
    assertEquals(BitVecLiteral("#x00"), const.value)
  }

  @Test
  fun `constant arrays are serialized back to SMT-LIB`() {
    val assertion =
        "(assert (= arr.content.0 (store ((as const (Array Int (_ BitVec 8))) #x00) 0 #x61)))"
    val assert = parseAssert(SPOUT_DECLARATION, assertion)

    assertEquals(assertion, assert.toSMTString(QuotingRule.SAME_AS_INPUT, false))
  }

  @Test
  fun `iteratively serialized constant arrays parse back to the same term`() {
    val assert =
        parseAssert(
            SPOUT_DECLARATION,
            "(assert (= arr.content.0 (store ((as const (Array Int (_ BitVec 8))) #x00) 0 #x61)))",
        )

    // the iterative serializer pads leaves with spaces, so compare the re-parsed terms instead
    val reparsed =
        parseAssert(SPOUT_DECLARATION, assert.toSMTString(QuotingRule.SAME_AS_INPUT, true))
    assertEquals(assert.expr, reparsed.expr)
  }

  @Test
  fun `nested constant arrays are parsed and serialized`() {
    val assertion =
        "(assert (= a ((as const (Array Int (Array Int Bool))) ((as const (Array Int Bool)) true))))"
    val assert = parseAssert("(declare-fun a () (Array Int (Array Int Bool)))", assertion)

    val const = (assert.expr as Equals<*>).children[1] as ArrayConst<*, *>
    assertTrue(const.value is ArrayConst<*, *>)
    assertEquals(assertion, assert.toSMTString(QuotingRule.SAME_AS_INPUT, false))
    assertEquals(
        assert.expr,
        parseAssert(
                "(declare-fun a () (Array Int (Array Int Bool)))",
                assert.toSMTString(QuotingRule.SAME_AS_INPUT, true),
            )
            .expr,
    )
  }

  @Test
  fun `constant array with mismatching value sort is rejected`() {
    assertThrows<IllegalArgumentException> {
      parseAssert(
          "(declare-fun a () (Array Int Int))",
          "(assert (= a ((as const (Array Int Int)) true)))",
      )
    }
  }

  @Test
  fun `unsupported qualified identifier application is rejected`() {
    assertThrows<IllegalArgumentException> {
      parseAssert(
          "(declare-fun a () (Array Int Int))",
          "(assert (= a ((as foo (Array Int Int)) 0)))",
      )
    }
  }
}

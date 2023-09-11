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

import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.ValueSource
import org.petitparser.context.ParseError
import tools.aqua.konstraints.parser.PetitParser

class PetitParserTests {
  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "(declare-fun A () Bool)",
              "(declare-fun B () Bool)",
              "(declare-fun C () Bool)",
              "(assert (and (or (not A) (not B)) (xor A B (not C)) (and B (or A C))))",
              "(check-sat)",
              "(declare-fun A (Bool (_ BitVec 32)) (_ BitVec 16))",
              /* QF_BV 20190311-bv-small-term-rw-Noetzli / bv-term-small-rw_1.smt */
              "(declare-fun s () (_ BitVec 32))",
              "(declare-fun t () (_ BitVec 32))",
              "(assert (not (= (bvand s s) s)))",
              /* QF_BV 20190311-bv-small-term-rw-Noetzli / bv-term-small-rw_100.smt */
              "(assert (not (= (bvlshr s (bvshl t #b00000000000000000000000000000000)) (bvlshr s t))))",
          ])
  fun testParse(statement: String) {
    val result = PetitParser.sExpression.parse(statement)

    if (result.isSuccess) {
      println(result.get<String>())
    } else {
      throw ParseError(result.failure(result.message))
    }
  }
}

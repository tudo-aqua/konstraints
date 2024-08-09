/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2024 The Konstraints Authors
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
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.TestInstance.Lifecycle
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.Arguments.arguments
import org.junit.jupiter.params.provider.MethodSource
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.theories.*

/*
 * Lifecycle.PER_CLASS is needed for MethodSource to avoid moving sources to a companion object
 * This also avoids creating a new class for every test, as this is not needed, because no data is modified
 */
@TestInstance(Lifecycle.PER_CLASS)
class CoreTests {
  private val A = UserDeclaredExpression("A".symbol(), BoolSort)
  private val B = UserDeclaredExpression("B".symbol(), BoolSort)
  private val C = UserDeclaredExpression("C".symbol(), BoolSort)

  @ParameterizedTest
  @MethodSource("getCoreTheoryExpressionsAndTheirSerialization")
  fun `test that serialization of boolean expressions is correct`(
      expected: String,
      expression: Expression<BoolSort>
  ) {
    Assertions.assertEquals(expected, expression.toString())
  }

  private fun getCoreTheoryExpressionsAndTheirSerialization(): Stream<Arguments> {
    return Stream.of(
        arguments("true", True),
        arguments("false", False),
        arguments("(not A)", Not(A)),
        arguments("(=> A B)", Implies(A, B)),
        arguments("(=> A B C)", Implies(A, B, C)),
        arguments("(and A B)", And(A, B)),
        arguments("(and A B C)", And(A, B, C)),
        arguments("(or A B)", Or(A, B)),
        arguments("(or A B C)", Or(A, B, C)),
        arguments("(xor A B)", XOr(A, B)),
        arguments("(xor A B C)", XOr(A, B, C)),
        arguments("(= A B)", Equals(A, B)),
        arguments("(= A B C)", Equals(A, B, C)),
        arguments("(distinct A B)", Distinct(A, B)),
        arguments("(distinct A B C)", Distinct(A, B, C)),
        arguments("(ite A B C)", Ite(A, B, C)),
        arguments("(and A (or B C))", And(A, Or(B, C))),
        arguments("(and (or A B) C)", And(Or(A, B), C)))
  }
}

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

import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.assertDoesNotThrow
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.ValueSource
import tools.aqua.konstraints.parser.*
import tools.aqua.konstraints.smt.*

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class ParserTests {
  val deepRecursiveSerializer: DeepRecursiveFunction<Pair<Appendable, Expression<*>>, Appendable> =
      DeepRecursiveFunction<Pair<Appendable, Expression<*>>, Appendable> { (builder, expr) ->
        when (expr) {
          is AnnotatedExpression<*> -> {
            builder.append("(! ")
            deepRecursiveSerializer.callRecursive(builder to expr.term)

            expr.annoations.forEach {
              builder.append(" ")
              it.toSMTString(builder, QuotingRule.SAME_AS_INPUT)
            }

            builder.append(")")
          }
          is ExistsExpression -> {
            builder.append("(exists (")

            var counter = 0
            expr.vars.forEach {
              if (counter++ > 1) builder.append(" ")
              it.toSMTString(builder, QuotingRule.SAME_AS_INPUT)
            }

            builder.append(") ")
            deepRecursiveSerializer.callRecursive(builder to expr.term)

            builder.append(")")
          }
          is ForallExpression -> {
            builder.append("(forall (")

            var counter = 0
            expr.vars.forEach {
              if (counter++ > 1) builder.append(" ")
              it.toSMTString(builder, QuotingRule.SAME_AS_INPUT)
            }

            builder.append(") ")
            deepRecursiveSerializer.callRecursive(builder to expr.term)

            builder.append(")")
          }
          is LetExpression<*> -> {
            builder.append("(let (")

            var counter = 0
            expr.bindings.forEach {
              if (counter++ > 1) builder.append(" ")
              it.toSMTString(builder, QuotingRule.SAME_AS_INPUT)
            }

            builder.append(") ")
            deepRecursiveSerializer.callRecursive(builder to expr.inner)

            builder.append(")")
          }
          else -> {
            if (expr.children.isEmpty())
                expr.nameStringWithIndices(builder, QuotingRule.SAME_AS_INPUT)
            else {
              builder.append("(")
              expr.nameStringWithIndices(builder, QuotingRule.SAME_AS_INPUT)

              expr.children.forEach {
                builder.append(" ")
                deepRecursiveSerializer.callRecursive(builder to it)
              }

              builder.append(")")
            }
          }
        }
      }

  val serialize =
      DeepRecursiveFunction<Pair<Appendable, SMTProgram>, Appendable> { (builder, program) ->
        program.commands.forEach {
          if (it is Assert) {
            builder.append("(assert ")
            deepRecursiveSerializer.callRecursive(builder to it.expr)
            builder.append(")")
          } else {
            it.toSMTString(builder, QuotingRule.SAME_AS_INPUT)
          }
        }
        builder
      }

  @ParameterizedTest
  @ValueSource(ints = [8, 32, 128, 1024, 2048, 8192, 32768])
  fun testDeepRecursion(level: Int) {
    var program = "(set-logic QF_UF)(declare-fun foo () Bool)(assert "
    (0..<level).forEach { program += "(= foo " }

    program += "(= foo foo)"

    (0..level).forEach { program += ")" }

    assertDoesNotThrow {
      val program = Parser(program)
      println(serialize(StringBuilder() to program).toString())
    }
  }

  @Test
  fun test() {
    Parser(
        "(set-logic QF_UF)(declare-fun __ADDRESS_OF_h () Bool)(assert (= __ADDRESS_OF_h __ADDRESS_OF_h))(exit)"
    )
  }
}

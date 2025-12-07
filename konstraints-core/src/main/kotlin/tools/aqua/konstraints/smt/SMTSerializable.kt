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

package tools.aqua.konstraints.smt

import tools.aqua.konstraints.util.StackOperation
import tools.aqua.konstraints.util.StackOperationType

/**
 * Quoting rules for SMT String, used when serializing program.
 *
 * @property NEVER will never quote any symbol, even if the constructing string is quoted
 * @property SAME_AS_INPUT no modification will be done
 * @property WHEN_NEEDED automatically determines whether the symbol needs quoting or not
 * @property ALWAYS quotes all symbols
 */
enum class QuotingRule {
  /**
   * No Symbol will be quoted, note this will result in exceptions if symbols must be quoted to be
   * valid.
   */
  NEVER,

  /** No modification will be done. */
  SAME_AS_INPUT,

  /** Automatically determines whether the string needs quoting or not. */
  WHEN_NEEDED,

  /** Quotes the string if it is not already quoted. */
  ALWAYS,
}

interface SMTSerializable {
  fun toSMTString(quotingRule: QuotingRule): String

  fun toSMTString(builder: Appendable, quotingRule: QuotingRule): Appendable
}

class SMTSerializer {
  fun serialize(expression: Expression<*>, quotingRule: QuotingRule): String {
    val builder = StringBuilder()

    // pair of string, expression to be able to add varbindings to the stack
    val stack = ArrayDeque<StackOperation<Pair<String, Expression<*>>>>(listOf(StackOperation(StackOperationType.BIND, "" to expression)))

    while(stack.isNotEmpty()) {
      val op = stack.removeLast()

      op.let { (operation, temp) ->
        temp.let { (name, expr) ->
          when (operation) {
            StackOperationType.BIND -> {
              if (expr.children.isNotEmpty()) {
                builder.append('(')
                stack.addLast(op.unbind())
              }

              when (expr) {
                is ForallExpression -> {
                  serializeQuantifier("forall", quotingRule, builder, expr.vars)
                }

                is ExistsExpression -> {
                  serializeQuantifier("exists", quotingRule, builder, expr.vars)
                }

                is LetExpression -> {
                  builder.append("let (")

                  stack.addAll(expr.bindings.map { binding ->
                    StackOperation(StackOperationType.BIND, binding.symbol.toSMTString(quotingRule) to binding.term)
                  })

                  builder.append(") ")
                }

                is LocalExpression -> {
                  require(name.isNotEmpty())
                  builder.append("( $name ")
                  expr.nameStringWithIndices(builder, quotingRule)
                  stack.addLast(op.unbind())
                }

                else -> expr.nameStringWithIndices(builder, quotingRule)
              }

              stack.addAll(expr.children.map { expr ->
                StackOperation(StackOperationType.BIND, "" to expr)
              })
            }

            StackOperationType.UNBIND -> builder.append(')')
            StackOperationType.NONE -> throw RuntimeException("Unexpected operation")
          }
        }
      }
    }

    return builder.toString()
  }

  private fun serializeQuantifier(expr: String, quotingRule: QuotingRule, builder: StringBuilder, vars: List<SortedVar<*>>): StringBuilder {
    builder.append("$expr (")

    var counter = 0
    vars.forEach {
      if (counter++ > 1) builder.append(" ")
      it.toSMTString(builder, quotingRule)
    }

    return builder.append(") ")
  }
}
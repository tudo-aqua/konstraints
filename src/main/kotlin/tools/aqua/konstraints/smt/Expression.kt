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

package tools.aqua.konstraints.smt

import tools.aqua.konstraints.util.reduceOrDefault

abstract class Expression<T : Sort> {
  abstract val symbol: Symbol
  abstract val sort: T

  override fun toString() = symbol.toSMTString()

  open val subexpressions = emptyList<Expression<*>>()

  /** Recursive all implementation */
  fun all(predicate: (Expression<*>) -> Boolean): Boolean {
    return predicate(this) and
        subexpressions.map { it.all(predicate) }.reduceOrDefault(true) { t1, t2 -> t1 and t2 }
  }

  // TODO implement more operations like filter, filterIsInstance, filterIsSort, forEach, onEach
  // etc.

  /**
   * Safely cast this expression to an Expression of Sort S, if this.sort is S Avoids unchecked cast
   * warnings when casting Expression<*> after binding
   */
  infix fun <S : Sort> castTo(to: S): Expression<S> {
    if (sort == to) {
      throw ExpressionCastException(sort, to.toString())
    }

    @Suppress("UNCHECKED_CAST") return this as Expression<S>
  }
}

class BasicExpression<T : Sort>(override val symbol: Symbol, override val sort: T) :
    Expression<T>() {
  override fun toString() = "$symbol"
}

class UnaryExpression<T : Sort>(symbol: Symbol, override val sort: T, val other: Expression<T>) :
    Expression<T>() {
  override val symbol: Symbol = symbol

  override fun toString() = "($symbol ${other})"
}

class BinaryExpression<T : Sort>(
    symbol: Symbol,
    override val sort: T,
    val left: Expression<T>,
    val right: Expression<T>
) : Expression<T>() {
  override val symbol: Symbol = symbol

  override fun toString() = "($symbol ${left} ${right})"
}

class NAryExpression<T : Sort>(
    symbol: Symbol,
    override val sort: T,
    val tokens: List<Expression<*>>
) : Expression<T>() {
  override val symbol: Symbol = symbol

  override fun toString() =
      if (tokens.isNotEmpty()) "($symbol ${tokens.joinToString(" ")})" else symbol.toSMTString()
}

class ExpressionCastException(from: Sort, to: String) :
    ClassCastException("Can not cast expression from $from to $to")

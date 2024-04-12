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

import tools.aqua.konstraints.parser.VarBinding
import tools.aqua.konstraints.util.reduceOrDefault

sealed interface Expression<T : Sort> {
  abstract val symbol: Symbol
  abstract val sort: T

  /**
   * Recursive all implementation fun all(predicate: (Expression<*>) -> Boolean): Boolean { return
   * predicate(this) and subexpressions.map { it.all(predicate) }.reduceOrDefault(true) { t1, t2 ->
   * t1 and t2 } }
   */

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

  fun all(predicate: (Expression<*>) -> Boolean): Boolean =
      when (this) {
        is UnaryExpression<*, *> -> predicate(this) and this.inner().all(predicate)
        is BasicExpression -> predicate(this)
        is BinaryExpression<*, *, *> ->
            predicate(this) and this.lhs().all(predicate) and this.rhs().all(predicate)
        is HomogenousExpression<*, *> ->
            predicate(this) and
                this.subexpressions()
                    .map { it.all(predicate) }
                    .reduceOrDefault(true) { t1, t2 -> t1 and t2 }
        is Ite -> TODO()
        is Literal -> TODO()
        is NAryExpression ->
            predicate(this) and
                this.subexpressions()
                    .map { it.all(predicate) }
                    .reduceOrDefault(true) { t1, t2 -> t1 and t2 }
        is TernaryExpression<*, *, *, *> -> TODO()
          is LetExpression -> TODO()
      }

  val subexpressions: List<Expression<*>>
}

// TODO this should be variable
class BasicExpression<T : Sort>(override val symbol: Symbol, override val sort: T) : Expression<T> {
  override val subexpressions: List<Expression<*>> = emptyList()

  override fun toString() = "$symbol"
}

open class Literal<T : Sort>(override val symbol: Symbol, override val sort: T) : Expression<T> {
  override val subexpressions: List<Expression<*>> = emptyList()

  override fun toString() = "$symbol"
}

abstract class UnaryExpression<T : Sort, S : Sort>(
    override val symbol: Symbol,
    override val sort: T
) : Expression<T> {

  abstract fun inner(): Expression<S>

  override val subexpressions: List<Expression<*>>
    get() = listOf(inner())

  override fun toString() = "($symbol ${inner()})"
}

abstract class BinaryExpression<T : Sort, S1 : Sort, S2 : Sort>(
    override val symbol: Symbol,
    override val sort: T
) : Expression<T> {

  abstract fun lhs(): Expression<S1>

  abstract fun rhs(): Expression<S2>

  override val subexpressions: List<Expression<*>>
    get() = listOf(lhs(), rhs())

  override fun toString() = "($symbol ${lhs()} ${rhs()})"
}

abstract class TernaryExpression<T : Sort, S1 : Sort, S2 : Sort, S3 : Sort>(
    override val symbol: Symbol,
    override val sort: T
) : Expression<T> {
  abstract fun lhs(): Expression<S1>

  abstract fun mid(): Expression<S2>

  abstract fun rhs(): Expression<S3>

  override val subexpressions: List<Expression<*>>
    get() = listOf(lhs(), mid(), rhs())

  override fun toString() = "($symbol ${lhs()} ${mid()} ${rhs()})"
}

abstract class HomogenousExpression<T : Sort, S : Sort>(
    override val symbol: Symbol,
    override val sort: T
) : Expression<T> {
  abstract fun subexpressions(): List<Expression<S>>

  override val subexpressions: List<Expression<*>>
    get() = subexpressions()

  override fun toString() =
      if (subexpressions().isNotEmpty()) "($symbol ${subexpressions().joinToString(" ")})"
      else symbol.toSMTString()
}

/**
 * Implements ite according to Core theory (par (A) (ite Bool A A A))
 *
 * @param statement indicates whether [then] or [els] should be returned
 * @param then value to be returned if [statement] is true
 * @param els value to be returned if [statement] is false
 */
class Ite(val statement: Expression<BoolSort>, val then: Expression<*>, val els: Expression<*>) :
    Expression<Sort> {
  override val sort: BoolSort = BoolSort
  override val symbol: Symbol = "ite".symbol()

  override val subexpressions: List<Expression<*>> = listOf(statement, then, els)

  override fun toString(): String = "(ite $statement $then $els)"
}

abstract class NAryExpression<T : Sort>(override val symbol: Symbol, override val sort: T) :
    Expression<T> {

  abstract fun subexpressions(): List<Expression<*>>

  override val subexpressions: List<Expression<*>>
    get() = subexpressions()

  override fun toString() =
      if (subexpressions().isNotEmpty()) "($symbol ${subexpressions().joinToString(" ")})"
      else symbol.toSMTString()
}

class LetExpression<T : Sort>(
    override val symbol: Symbol,
    override val sort: T,
    val bindings: List<VarBinding>,
    val inner: Expression<*>
) : Expression<T> {
    override val subexpressions: List<Expression<*>> = listOf(inner)
}

class UserDefinedExpression<T : Sort>(name: Symbol, sort: T, val args: List<Expression<*>>) :
    NAryExpression<T>(name, sort) {
  override fun subexpressions(): List<Expression<*>> = args
}

class ExpressionCastException(from: Sort, to: String) :
    ClassCastException("Can not cast expression from $from to $to")

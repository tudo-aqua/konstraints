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

/** Interface for all sorted SMT terms */
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
        is Variable -> predicate(this)
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
        is LocalExpression -> predicate(this)
      }

  val subexpressions: List<Expression<*>>
}

/** Constant expression without any children */
class Variable<T : Sort>(override val symbol: Symbol, override val sort: T) : Expression<T> {
  override val subexpressions: List<Expression<*>> = emptyList()

  override fun toString() = "$symbol"
}

/** SMT Literal */
open class Literal<T : Sort>(override val symbol: Symbol, override val sort: T) : Expression<T> {
  override val subexpressions: List<Expression<*>> = emptyList()

  override fun toString() = "$symbol"
}

/** Base class of all expressions with exactly one child */
abstract class UnaryExpression<T : Sort, S : Sort>(
    override val symbol: Symbol,
    override val sort: T
) : Expression<T> {

  abstract fun inner(): Expression<S>

  override val subexpressions: List<Expression<*>>
    get() = listOf(inner())

  override fun toString() = "($symbol ${inner()})"
}

/** Base class of all expressions with exactly two children */
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

/** Base class of all expressions with exactly three children */
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

/**
 * Base class of all expressions with any children, where all children are expressions of the same
 * sort
 */
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
 * @param statement indicates whether [then] or [otherwise] should be returned
 * @param then value to be returned if [statement] is true
 * @param otherwise value to be returned if [statement] is false
 */
class Ite<T : Sort>(
    val statement: Expression<BoolSort>,
    val then: Expression<T>,
    val otherwise: Expression<T>
) : Expression<T> {
  init {
    require(then.sort == otherwise.sort)
  }

  override val sort: T = then.sort
  override val symbol: Symbol = "ite".symbol()

  override val subexpressions: List<Expression<*>> = listOf(statement, then, otherwise)

  override fun toString(): String = "(ite $statement $then $otherwise)"
}

/** Base class of all expressions with any number of children */
abstract class NAryExpression<T : Sort>(override val symbol: Symbol, override val sort: T) :
    Expression<T> {

  abstract fun subexpressions(): List<Expression<*>>

  override val subexpressions: List<Expression<*>>
    get() = subexpressions()

  override fun toString() =
      if (subexpressions().isNotEmpty()) "($symbol ${subexpressions().joinToString(" ")})"
      else symbol.toSMTString()
}

/** Let expression */
class LetExpression<T : Sort>(
    override val symbol: Symbol,
    override val sort: T,
    val bindings: List<VarBinding<*>>,
    val inner: Expression<T>
) : Expression<T> {
  override val subexpressions: List<Expression<*>> = listOf(inner)
}

class UserDefinedExpression<T : Sort>(name: Symbol, sort: T, val args: List<Expression<*>>) :
    NAryExpression<T>(name, sort) {
  override fun subexpressions(): List<Expression<*>> = args
}

/** Expression with a local variable */
class LocalExpression<T : Sort>(
    override val symbol: Symbol,
    override val sort: T,
    val term: Expression<T>,
) : Expression<T> {
  override val subexpressions: List<Expression<*>> = emptyList()
}

/*
class BoundExpression(
    override val symbol: Symbol,
    override val sort: BoolSort,
    val term: Expression<BoolSort>
) : Expression<BoolSort> {
    override val subexpressions: List<Expression<*>> = emptyList()
}
*/

class ExpressionCastException(from: Sort, to: String) :
    ClassCastException("Can not cast expression from $from to $to")

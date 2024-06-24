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

import tools.aqua.konstraints.parser.SortedVar
import tools.aqua.konstraints.parser.VarBinding
import tools.aqua.konstraints.theories.BoolSort
import tools.aqua.konstraints.theories.IteDecl
import tools.aqua.konstraints.util.reduceOrDefault

/** Interface for all sorted SMT terms */
sealed interface Expression<T : Sort> {
  val name: SMTSerializable
  val sort: T

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
    if (sort != to) {
      throw ExpressionCastException(sort, to.toString())
    }

    @Suppress("UNCHECKED_CAST") return this as Expression<S>
  }

  fun all(predicate: (Expression<*>) -> Boolean): Boolean =
      when (this) {
        is ConstantExpression -> predicate(this)
        is UnaryExpression<*, *> -> predicate(this) and this.inner.all(predicate)
        is BinaryExpression<*, *, *> ->
            predicate(this) and this.lhs.all(predicate) and this.rhs.all(predicate)
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
        is BoundVariable -> TODO()
        is ExistsExpression -> TODO()
        is ForallExpression -> TODO()
      }

  fun transform(transformation: (Expression<*>) -> Expression<*>): Expression<T> {
    // transform all children
    val transformedChildren = this.children.map { it.transform(transformation) }

    // check if any child was copied
    return if ((transformedChildren zip this.children).any { (new, old) -> new !== old }) {
      // return copied expression with new children
      // val copied = this.copy(transformedChildren)
      // transformation(copied) castTo sort
      transformation(this) castTo sort
    } else {
      // transform this expression, prevent it from changing the sort
      transformation(this) castTo sort
    }
  }

  fun copy(children: List<Expression<*>>): Expression<T>

  val children: List<Expression<*>>
}

/** SMT Literal */
abstract class Literal<T : Sort>(override val name: LiteralString, override val sort: T) :
    Expression<T> {
  override val children: List<Expression<*>> = emptyList()

  override fun toString() = name.toString()
}

abstract class ConstantExpression<T : Sort>(override val name: Symbol, override val sort: T) :
    Expression<T> {
  override val children: List<Expression<*>> = emptyList()

  override fun toString() = "$name"
}

/** Base class of all expressions with exactly one child */
abstract class UnaryExpression<T : Sort, S : Sort>(
    override val name: Symbol,
    override val sort: T
) : Expression<T> {

  abstract val inner: Expression<S>

  override val children: List<Expression<*>>
    get() = listOf(inner)

  override fun toString() = "($name ${inner})"
}

/** Base class of all expressions with exactly two children */
abstract class BinaryExpression<T : Sort, S1 : Sort, S2 : Sort>(
    override val name: Symbol,
    override val sort: T
) : Expression<T> {

  abstract val lhs: Expression<S1>

  abstract val rhs: Expression<S2>

  override val children: List<Expression<*>>
    get() = listOf(lhs, rhs)

  override fun toString() = "($name $lhs $rhs)"
}

/** Base class of all expressions with exactly three children */
abstract class TernaryExpression<T : Sort, S1 : Sort, S2 : Sort, S3 : Sort>(
    override val name: Symbol,
    override val sort: T
) : Expression<T> {
  abstract val lhs: Expression<S1>

  abstract val mid: Expression<S2>

  abstract val rhs: Expression<S3>

  override val children: List<Expression<*>>
    get() = listOf(lhs, mid, rhs)

  override fun toString() = "($name $lhs $mid $rhs)"
}

/**
 * Base class of all expressions with any children, where all children are expressions of the same
 * sort
 */
abstract class HomogenousExpression<T : Sort, S : Sort>(
    override val name: Symbol,
    override val sort: T
) : Expression<T> {
  abstract fun subexpressions(): List<Expression<S>>

  override val children: List<Expression<*>>
    get() = subexpressions()

  override fun toString() =
      if (subexpressions().isNotEmpty()) "($name ${subexpressions().joinToString(" ")})"
      else name.toSMTString()
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

  override fun copy(children: List<Expression<*>>): Expression<T> =
      IteDecl.buildExpression(children, emptySet()) castTo sort

  override val name: Symbol = "ite".symbol()

  override val children: List<Expression<*>> = listOf(statement, then, otherwise)

  override fun toString(): String = "(ite $statement $then $otherwise)"
}

/** Base class of all expressions with any number of children */
abstract class NAryExpression<T : Sort>(override val name: Symbol, override val sort: T) :
    Expression<T> {

  abstract fun subexpressions(): List<Expression<*>>

  override val children: List<Expression<*>>
    get() = subexpressions()

  override fun toString() =
      if (subexpressions().isNotEmpty()) "($name ${subexpressions().joinToString(" ")})"
      else name.toSMTString()
}

/** Let expression */
class LetExpression<T : Sort>(
    override val sort: T,
    val bindings: List<VarBinding<*>>,
    val inner: Expression<T>
) : Expression<T> {
  override val name = Keyword("let")

  override fun copy(children: List<Expression<*>>): Expression<T> {
    require(children.size == 1)

    return LetExpression(sort, bindings, children.single() castTo sort) castTo sort
  }

  override val children: List<Expression<*>> = listOf(inner)
}

class UserDefinedExpression<T : Sort>(name: Symbol, sort: T, val args: List<Expression<*>>) :
    NAryExpression<T>(name, sort) {

  constructor(name: Symbol, sort: T) : this(name, sort, emptyList())

  override fun subexpressions(): List<Expression<*>> = args

  override fun copy(children: List<Expression<*>>): Expression<T> =
      UserDefinedExpression(name, sort, children)
}

/** Expression with a local variable */
class LocalExpression<T : Sort>(
    override val name: Symbol,
    override val sort: T,
    val term: Expression<T>,
) : Expression<T> {
  override fun copy(children: List<Expression<*>>): Expression<T> {
    require(children.size == 1)

    return LocalExpression(name, sort, children.single() castTo sort) castTo sort
  }

  override val children: List<Expression<*>> = emptyList()
}

class ExistsExpression(val vars: List<SortedVar<*>>, val term: Expression<BoolSort>) :
    Expression<BoolSort> {
  override val sort = BoolSort
  override val name = Keyword("exists")
  override val children: List<Expression<*>> = listOf(term)

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> {
    require(children.size == 1)

    return ExistsExpression(vars, children.single() castTo sort)
  }
}

class ForallExpression(val vars: List<SortedVar<*>>, val term: Expression<BoolSort>) :
    Expression<BoolSort> {
  override val sort = BoolSort
  override val name = Keyword("forall")
  override val children: List<Expression<*>> = listOf(term)

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> {
    require(children.size == 1)

    return ForallExpression(vars, children.single() castTo sort)
  }
}

class BoundVariable<T : Sort>(override val name: Symbol, override val sort: T) : Expression<T> {
  override val children: List<Expression<*>> = emptyList()

  override fun copy(children: List<Expression<*>>): Expression<T> = BoundVariable(name, sort)
}

class ExpressionCastException(from: Sort, to: String) :
    ClassCastException("Can not cast expression from $from to $to")

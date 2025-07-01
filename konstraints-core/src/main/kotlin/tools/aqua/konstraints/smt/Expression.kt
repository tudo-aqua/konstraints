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

import tools.aqua.konstraints.parser.IteDecl
import tools.aqua.konstraints.util.reduceOrDefault

/** Interface for all sorted SMT terms */
sealed interface Expression<out T : Sort> {
  val name: SMTSerializable
  val sort: T
  val theories: Set<Theories>
  val func: SMTFunction<T>?

  /**
   * Recursive all implementation fun all(predicate: (Expression<*>) -> Boolean): Boolean { return
   * predicate(this) and subexpressions.map { it.all(predicate) }.reduceOrDefault(true) { t1, t2 ->
   * t1 and t2 } }
   */

  // TODO implement more operations like filter, filterIsInstance, filterIsSort, forEach, onEach
  // etc.

  fun all(predicate: (Expression<*>) -> Boolean): Boolean =
      when (this) {
        is ConstantExpression -> predicate(this)
        is UnaryExpression<*, *> -> predicate(this) and inner.all(predicate)
        is BinaryExpression<*, *, *> ->
            predicate(this) and lhs.all(predicate) and rhs.all(predicate)
        is HomogenousExpression<*, *> ->
            predicate(this) and
                children.map { it.all(predicate) }.reduceOrDefault(true) { t1, t2 -> t1 and t2 }
        is Ite ->
            predicate(statement) and
                predicate(then) and
                predicate(otherwise) and
                statement.all(predicate) and
                then.all(predicate) and
                otherwise.all(predicate)
        is Literal -> predicate(this)
        is NAryExpression ->
            predicate(this) and
                children.map { it.all(predicate) }.reduceOrDefault(true) { t1, t2 -> t1 and t2 }
        is TernaryExpression<*, *, *, *> ->
            predicate(this) and lhs.all(predicate) and mid.all(predicate) and lhs.all(predicate)
        is LetExpression -> inner.all(predicate) // TODO maybe this should also check all bindings
        is LocalExpression -> predicate(this)
        is BoundVariable -> predicate(this)
        is ExistsExpression -> term.all(predicate)
        is ForallExpression -> term.all(predicate)
        is AnnotatedExpression -> predicate(this) and term.all(predicate)
      }

  fun asSequence(): Sequence<Expression<*>> = sequence {
    yield(this@Expression)
    children.forEach { yieldAll(it.asSequence()) }
  }

  fun forEach(action: (Expression<*>) -> Unit) {
    action(this)
    children.forEach { it.forEach(action) }
  }

  fun transform(transformation: (Expression<*>) -> Expression<*>): Expression<T> {
    // transform all children
    val transformedChildren = this.children.map { it.transform(transformation) }

    // check if any child was copied
    return if ((transformedChildren zip this.children).any { (new, old) -> new !== old }) {
      // return copied expression with new children
      transformation(this.copy(transformedChildren)) as Expression<T>
    } else {
      // transform this expression, prevent it from changing the sort
      transformation(this) as Expression<T>
    }
  }

  fun copy(children: List<Expression<*>>): Expression<T>

  val children: List<Expression<*>>
}

/** SMT Literal */
abstract class Literal<out T : Sort>(override val name: LiteralString, override val sort: T) :
    Expression<T> {
  override val func = null

  override val children: List<Expression<*>> = emptyList()

  override fun toString() = name.toString()
}

abstract class ConstantExpression<out T : Sort>(override val name: Symbol, override val sort: T) :
    Expression<T> {
  override val func = null

  override val children: List<Expression<*>> = emptyList()

  override fun toString() = "$name"
}

/** Base class of all expressions with exactly one child */
abstract class UnaryExpression<out T : Sort, out S : Sort>(
    override val name: Symbol,
    override val sort: T
) : Expression<T> {
  override val func = null

  abstract val inner: Expression<S>

  override val children: List<Expression<*>>
    get() = listOf(inner)

  override fun toString() = "($name ${inner})"
}

/** Base class of all expressions with exactly two children */
abstract class BinaryExpression<out T : Sort, out S1 : Sort, out S2 : Sort>(
    override val name: Symbol,
    override val sort: T
) : Expression<T> {
  override val func = null

  abstract val lhs: Expression<S1>

  abstract val rhs: Expression<S2>

  override val children: List<Expression<*>>
    get() = listOf(lhs, rhs)

  override fun toString() = "($name $lhs $rhs)"
}

/** Base class of all expressions with exactly three children */
abstract class TernaryExpression<out T : Sort, out S1 : Sort, out S2 : Sort, out S3 : Sort>(
    override val name: Symbol,
    override val sort: T
) : Expression<T> {
  override val func = null

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
abstract class HomogenousExpression<out T : Sort, out S : Sort>(
    override val name: Symbol,
    override val sort: T
) : Expression<T> {
  override val func = null
  abstract override val children: List<Expression<S>>

  override fun toString() =
      if (children.isNotEmpty()) "($name ${children.joinToString(" ")})"
      else name.toSMTString(QuotingRule.SAME_AS_INPUT)
}

/**
 * Implements ite according to Core theory (par (A) (ite Bool A A A))
 *
 * @param statement indicates whether [then] or [otherwise] should be returned
 * @param then value to be returned if [statement] is true
 * @param otherwise value to be returned if [statement] is false
 */
class Ite<out T : Sort>(
    val statement: Expression<BoolSort>,
    val then: Expression<T>,
    val otherwise: Expression<T>
) : Expression<T> {
  init {
    require(then.sort == otherwise.sort)
  }

  override val sort: T = then.sort
  override val theories = CORE_MARKER_SET
  override val func = null

  override fun copy(children: List<Expression<*>>): Expression<T> =
      IteDecl.constructDynamic(children, emptyList()) as Expression<T>

  override val name: Symbol = "ite".toSymbolWithQuotes()

  override val children: List<Expression<*>> = listOf(statement, then, otherwise)

  override fun toString(): String = "(ite $statement $then $otherwise)"
}

/** Base class of all expressions with any number of children */
abstract class NAryExpression<out T : Sort>(override val name: Symbol, override val sort: T) :
    Expression<T> {

  override fun toString() =
      if (children.isNotEmpty()) "($name ${children.joinToString(" ")})"
      else name.toSMTString(QuotingRule.SAME_AS_INPUT)
}

/** Let expression */
class LetExpression<out T : Sort>(val bindings: List<VarBinding<*>>, val inner: Expression<T>) :
    Expression<T> {
  override val sort = inner.sort
  override val name = Keyword("let")
  override val theories = emptySet<Theories>()
  override val func = null

  constructor(
      bindings: List<VarBinding<*>>,
      inner: (List<Expression<*>>) -> Expression<T>
  ) : this(bindings, inner(bindings.map { it.instance }))

  /*constructor(
      vararg bindings: VarBinding<*>,
      inner: (List<Expression<*>>) -> Expression<T>
  ) : this(bindings.toList(), inner(bindings.map { it.instance }))*/

  constructor(
      binding: VarBinding<*>,
      inner: (Expression<*>) -> Expression<T>
  ) : this(listOf(binding), inner(binding.instance))

  constructor(
      binding1: VarBinding<*>,
      binding2: VarBinding<*>,
      inner: (Expression<*>, Expression<*>) -> Expression<T>
  ) : this(listOf(binding1, binding2), inner(binding1.instance, binding2.instance))

  override fun copy(children: List<Expression<*>>): Expression<T> {
    require(children.size == 1)
    require(children.single().sort == sort)

    @Suppress("UNCHECKED_CAST")
    return LetExpression(bindings, children.single() as Expression<T>) as Expression<T>
  }

  override val children: List<Expression<*>> = listOf(inner)
}

class UserDeclaredExpression<out T : Sort>(
    name: Symbol,
    sort: T,
    args: List<Expression<*>>,
    override val func: SMTFunction<T>
) : NAryExpression<T>(name, sort) {
  override val theories = emptySet<Theories>()

  constructor(name: Symbol, sort: T, func: SMTFunction<T>) : this(name, sort, emptyList(), func)

  override val children: List<Expression<*>> = args

  override fun copy(children: List<Expression<*>>): Expression<T> =
      UserDeclaredExpression(name, sort, children, func)
}

class UserDefinedExpression<T : Sort>(
    name: Symbol,
    sort: T,
    args: List<Expression<*>>,
    val definition: FunctionDef<T>,
    override val func: DefinedSMTFunction<T>
) : NAryExpression<T>(name, sort) {
  override val theories = emptySet<Theories>()

  init {
    // check that args.sort matches expected sorts from definition
    require(args.zip(definition.parameters).all { (arg, par) -> arg.sort == par.sort })
  }

  override val children: List<Expression<*>> = args

  override fun copy(children: List<Expression<*>>): Expression<T> =
      UserDefinedExpression(name, sort, children, definition, func)

  fun expand(): Expression<*> = definition.expand(children)
}

/** Expression with a local variable */
class LocalExpression<T : Sort>(
    override val name: Symbol,
    override val sort: T,
    val term: Expression<T>,
    override val func: VarBinding<T>
) : Expression<T> {
  override val theories = emptySet<Theories>()

  override fun copy(children: List<Expression<*>>): Expression<T> {
    require(children.size == 1)
    require(children.single().sort == sort)

    @Suppress("UNCHECKED_CAST")
    return LocalExpression(name, sort, children.single() as Expression<T>, func) as Expression<T>
  }

  override val children: List<Expression<*>> = emptyList()
}

class ExistsExpression(val vars: List<SortedVar<*>>, val term: Expression<BoolSort>) :
    Expression<BoolSort> {
  override val theories = emptySet<Theories>()
  override val func = null

  constructor(vararg vars: SortedVar<*>, term: Expression<BoolSort>) : this(vars.toList(), term)

  override val sort = Bool
  override val name = Keyword("exists")
  override val children: List<Expression<*>> = listOf(term)

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> {
    require(children.size == 1)

    return ExistsExpression(vars, children.single().cast<BoolSort>())
  }
}

class ForallExpression(val vars: List<SortedVar<*>>, val term: Expression<BoolSort>) :
    Expression<BoolSort> {
  override val theories = emptySet<Theories>()
  override val func = null

  override val sort = Bool
  override val name = Keyword("forall")
  override val children: List<Expression<*>> = listOf(term)

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> {
    require(children.size == 1)

    return ForallExpression(vars, children.single().cast<BoolSort>())
  }
}

class BoundVariable<out T : Sort>(
    override val name: Symbol,
    override val sort: T,
    override val func: SortedVar<T>
) : Expression<T> {
  override val theories = emptySet<Theories>()

  override val children: List<Expression<*>> = emptyList()

  override fun copy(children: List<Expression<*>>): Expression<T> = BoundVariable(name, sort, func)
}

class AnnotatedExpression<T : Sort>(val term: Expression<T>, val annoations: List<Attribute>) :
    Expression<T> {
  override val theories = emptySet<Theories>()
  override val func = null

  override val name = Keyword("!")
  override val sort = term.sort

  override fun copy(children: List<Expression<*>>): Expression<T> {
    require(children.size == 1)

    return AnnotatedExpression(children.single() as Expression<T>, annoations)
  }

  override val children: List<Expression<*>> = listOf(term)
}

class ExpressionCastException(msg: String) : ClassCastException(msg)

class VarBinding<T : Sort>(override val symbol: Symbol, val term: Expression<T>) :
    SMTFunction<T>() {

  operator fun invoke(args: List<Expression<*>>) = instance

  override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>) = instance

  val name = symbol.toString()
  override val sort: T = term.sort
  override val parameters = emptyList<Sort>()

  val instance = LocalExpression(symbol, sort, term, this)
}

class SortedVar<out T : Sort>(override val symbol: Symbol, override val sort: T) :
    SMTFunction<T>() {
  operator fun invoke(args: List<Expression<*>>) = instance

  override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>) = instance

  override fun toString(): String = "($symbol $sort)"

  val instance = BoundVariable(symbol, sort, this)
  override val parameters: List<Sort> = emptyList()
}

/**
 * Safely cast this expression to an Expression of Sort T.
 *
 * @throws [ExpressionCastException] if [sort] is not [T]
 */
inline fun <reified T : Sort> Expression<*>.cast(): Expression<T> {
  if (sort !is T)
      throw ExpressionCastException("Can not cast expression $name of sort $sort to ${T::class}")

  @Suppress("UNCHECKED_CAST")
  return this as Expression<T>
}

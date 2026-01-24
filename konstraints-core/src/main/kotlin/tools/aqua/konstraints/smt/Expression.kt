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

package tools.aqua.konstraints.smt

/** Interface for all sorted SMT terms. */
sealed class Expression<out T : Sort> : SMTSerializable {
  abstract val name: BaseSymbol
  abstract val sort: T
  abstract val theories: Set<Theories>
  abstract val func: SMTFunction<T>?
  abstract val children: List<Expression<*>>

  // TODO combine into list index, provide views as symbol/int list
  open val indices = emptyList<Int>()
  open val symbolicIndices = emptyList<Symbol>()

  /**
   * Recursive all implementation fun all(predicate: (Expression<*>) -> Boolean): Boolean { return
   * predicate(this) and subexpressions.map { it.all(predicate) }.reduceOrDefault(true) { t1, t2 ->
   * t1 and t2 } }
   */

  // TODO implement more operations like filter, filterIsInstance, filterIsSort, forEach, onEach
  // etc.

  fun all(predicate: (Expression<*>) -> Boolean): Boolean {
    val deepAll =
        DeepRecursiveFunction<Expression<*>, Boolean> { expr ->
          // Apply predicate to current node
          if (!predicate(expr)) return@DeepRecursiveFunction false

          // Recursively check all children using the DeepRecursiveScope
          for (child in expr.children) {
            if (!this.callRecursive(child)) return@DeepRecursiveFunction false
          }

          true
        }

    return deepAll(this)
  }

  /*
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
            predicate(this) and
                predicate(condition) and
                predicate(then) and
                predicate(otherwise) and
                condition.all(predicate) and
                then.all(predicate) and
                otherwise.all(predicate)
        is Literal -> predicate(this)
        is NAryExpression ->
            predicate(this) and
                children.map { it.all(predicate) }.reduceOrDefault(true) { t1, t2 -> t1 and t2 }
        is TernaryExpression<*, *, *, *> ->
            predicate(this) and lhs.all(predicate) and mid.all(predicate) and rhs.all(predicate)
        is LetExpression -> predicate(this) and inner.all(predicate)
        is LocalExpression -> predicate(this)
        is BoundVariable -> predicate(this)
        is ExistsExpression -> predicate(this) and term.all(predicate)
        is ForallExpression -> predicate(this) and term.all(predicate)
        is AnnotatedExpression -> predicate(this) and term.all(predicate)
      }
    */

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

  override fun equals(other: Any?): Boolean {
    return if (this === other) true
    else if (other !is Expression<*>) false
    else
        sort == other.sort &&
            name == other.name &&
            func == other.func &&
            (children zip other.children).all { (lhs, rhs) -> lhs == rhs }
  }

  abstract fun copy(children: List<Expression<*>>): Expression<T>

  // use only name for hashcode as names are almost unique and thus mostly conflict free
  override fun hashCode() = name.hashCode()

  override fun toString() =
      if (children.isEmpty()) name.toString() else "$($name ${children.joinToString(" ")})"

  fun nameStringWithIndices(quotingRule: QuotingRule, useIterative: Boolean) =
      if (indices.isEmpty()) {
        name.toSMTString(quotingRule, useIterative)
      } else {
        "(_ ${name.toSMTString(quotingRule, useIterative)} ${indices.joinToString(" ")})"
      }

  fun nameStringWithIndices(
      builder: Appendable,
      quotingRule: QuotingRule,
      useIterative: Boolean,
  ): Appendable =
      if (indices.isEmpty()) {
        name.toSMTString(builder, quotingRule, useIterative)
      } else {
        builder.append("(_ ")
        name.toSMTString(builder, quotingRule, useIterative)

        indices.forEach { builder.append(" $it") }

        builder.append(")")
      }

  override fun toSMTString(quotingRule: QuotingRule, useIterative: Boolean): String =
      if (useIterative) {
        SMTSerializer.serialize(this, quotingRule)
      } else {
        if (children.isEmpty()) {
          nameStringWithIndices(quotingRule, useIterative)
        } else
            "(${nameStringWithIndices(quotingRule, useIterative)} ${
                  children.joinToString(" ") { expr: Expression<*> ->
                      expr.toSMTString(quotingRule, useIterative)
                  }
              })"
      }

  override fun toSMTString(
      builder: Appendable,
      quotingRule: QuotingRule,
      useIterative: Boolean,
  ): Appendable =
      if (useIterative) {
        SMTSerializer.serialize(this, quotingRule, builder)
      } else {
        if (children.isEmpty()) nameStringWithIndices(builder, quotingRule, useIterative)
        else {
          builder.append("(")
          nameStringWithIndices(builder, quotingRule, useIterative)

          children.forEach {
            builder.append(" ")
            it.toSMTString(builder, quotingRule, useIterative)
          }

          builder.append(")")
        }
      }
}

/** SMT Literal */
sealed class Literal<out T : Sort>(override val name: LiteralString, override val sort: T) :
    Expression<T>() {
  override val func = null

  override val children: List<Expression<*>> = emptyList()

  override fun toString() = name.toString()
}

abstract class ConstantExpression<out T : Sort>(override val name: Symbol, override val sort: T) :
    Expression<T>() {
  override val func = null

  override val children: List<Expression<*>> = emptyList()

  override fun toString() = name.toSMTString(QuotingRule.SAME_AS_INPUT, false)
}

/** Base class of all expressions with exactly one child */
abstract class UnaryExpression<out T : Sort, out S : Sort>(
    override val name: Symbol,
    override val sort: T,
) : Expression<T>() {
  override val func = null

  abstract val inner: Expression<S>

  override val children: List<Expression<*>>
    get() = listOf(inner)

  override fun toString() = "($name ${inner})"
}

/** Base class of all expressions with exactly two children */
abstract class BinaryExpression<out T : Sort, out S1 : Sort, out S2 : Sort>(
    override val name: Symbol,
    override val sort: T,
) : Expression<T>() {
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
    override val sort: T,
) : Expression<T>() {
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
    override val sort: T,
) : Expression<T>() {
  override val func = null
  abstract override val children: List<Expression<S>>

  override fun toString() =
      if (children.isNotEmpty()) "($name ${children.joinToString(" ")})"
      else name.toSMTString(QuotingRule.SAME_AS_INPUT, false)
}

/** Base class of all expressions with any number of children */
abstract class NAryExpression<out T : Sort>(override val name: Symbol, override val sort: T) :
    Expression<T>() {

  override fun toString() =
      if (children.isNotEmpty()) "($name ${children.joinToString(" ")})"
      else name.toSMTString(QuotingRule.SAME_AS_INPUT, false)
}

/** Let expression */
class LetExpression<out T : Sort>(val bindings: List<VarBinding<*>>, val inner: Expression<T>) :
    Expression<T>() {
  override val sort = inner.sort
  override val name = Keyword("let")
  override val theories = emptySet<Theories>()
  override val func = null

  constructor(
      bindings: List<VarBinding<*>>,
      inner: (List<Expression<*>>) -> Expression<T>,
  ) : this(bindings, inner(bindings.map { it.instance }))

  /*constructor(
      vararg bindings: VarBinding<*>,
      inner: (List<Expression<*>>) -> Expression<T>
  ) : this(bindings.toList(), inner(bindings.map { it.instance }))*/

  constructor(
      binding: VarBinding<*>,
      inner: (Expression<*>) -> Expression<T>,
  ) : this(listOf(binding), inner(binding.instance))

  constructor(
      binding1: VarBinding<*>,
      binding2: VarBinding<*>,
      inner: (Expression<*>, Expression<*>) -> Expression<T>,
  ) : this(listOf(binding1, binding2), inner(binding1.instance, binding2.instance))

  override fun copy(children: List<Expression<*>>): Expression<T> {
    require(children.size == 1)
    require(children.single().sort == sort)

    @Suppress("UNCHECKED_CAST")
    return LetExpression(bindings, children.single() as Expression<T>) as Expression<T>
  }

  override val children: List<Expression<*>> = listOf(inner)

  override fun toString() = "(let (${bindings.joinToString(" ")}) $inner)"

  override fun toSMTString(quotingRule: QuotingRule, useIterative: Boolean) =
      "(let (${bindings.joinToString(" "){it.toSMTString(quotingRule, useIterative)}}) ${if(useIterative) SMTSerializer.serialize(inner, quotingRule) else inner.toSMTString(quotingRule, useIterative)})"

  override fun toSMTString(
      builder: Appendable,
      quotingRule: QuotingRule,
      useIterative: Boolean,
  ): Appendable {
    builder.append("(let (")

    var counter = 0
    bindings.forEach {
      if (counter++ > 1) builder.append(" ")
      it.toSMTString(builder, quotingRule, useIterative)
    }

    builder.append(") ")
    if (useIterative) {
      SMTSerializer.serialize(inner, quotingRule, builder)
    } else {
      inner.toSMTString(builder, quotingRule, useIterative)
    }

    return builder.append(")")
  }
}

class UserDeclaredExpression<out T : Sort>(
    name: Symbol,
    sort: T,
    args: List<Expression<*>>,
    override val func: SMTFunction<T>,
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
    override val func: DefinedSMTFunction<T>,
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
    override val func: VarBinding<T>,
) : Expression<T>() {
  override val theories = emptySet<Theories>()

  override fun copy(children: List<Expression<*>>): Expression<T> {
    require(children.size == 1)
    require(children.single().sort == sort)

    @Suppress("UNCHECKED_CAST")
    return LocalExpression(name, sort, children.single() as Expression<T>, func) as Expression<T>
  }

  // children are empty here since a local expression is always of arity 0
  // and an alias for term
  override val children: List<Expression<*>> = emptyList()

  override fun toString() = name.toString()
}

class ExistsExpression(val vars: List<SortedVar<*>>, val term: Expression<BoolSort>) :
    Expression<BoolSort>() {
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

  override fun toString() = "(exists (${vars.joinToString(" ")}) $term)"

  override fun toSMTString(quotingRule: QuotingRule, useIterative: Boolean) =
      "(exists (${vars.joinToString(" "){it.toSMTString(quotingRule, useIterative)}}) ${term.toSMTString(quotingRule, useIterative)})"

  override fun toSMTString(
      builder: Appendable,
      quotingRule: QuotingRule,
      useIterative: Boolean,
  ): Appendable {
    builder.append("(exists (")

    var counter = 0
    vars.forEach {
      if (counter++ > 1) builder.append(" ")
      it.toSMTString(builder, quotingRule, useIterative)
    }

    builder.append(") ")
    term.toSMTString(builder, quotingRule, useIterative)

    return builder.append(")")
  }
}

class ForallExpression(val vars: List<SortedVar<*>>, val term: Expression<BoolSort>) :
    Expression<BoolSort>() {
  override val theories = emptySet<Theories>()
  override val func = null

  override val sort = Bool
  override val name = Keyword("forall")
  override val children: List<Expression<*>> = listOf(term)

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> {
    require(children.size == 1)

    return ForallExpression(vars, children.single().cast<BoolSort>())
  }

  override fun toString() = "(forall (${vars.joinToString(" ")}) $term)"

  override fun toSMTString(quotingRule: QuotingRule, useIterative: Boolean) =
      "(forall (${vars.joinToString(" "){it.toSMTString(quotingRule, useIterative)}}) ${term.toSMTString(quotingRule, useIterative)})"

  override fun toSMTString(
      builder: Appendable,
      quotingRule: QuotingRule,
      useIterative: Boolean,
  ): Appendable {
    builder.append("(forall (")

    var counter = 0
    vars.forEach {
      if (counter++ > 1) builder.append(" ")
      it.toSMTString(builder, quotingRule, useIterative)
    }

    builder.append(") ")
    term.toSMTString(builder, quotingRule, useIterative)

    return builder.append(")")
  }
}

/** Instance of a sorted var */
class BoundVariable<out T : Sort>(
    override val name: Symbol,
    override val sort: T,
    override val func: SortedVar<T>,
) : Expression<T>() {
  override val theories = emptySet<Theories>()

  override val children: List<Expression<*>> = emptyList()

  override fun copy(children: List<Expression<*>>): Expression<T> = BoundVariable(name, sort, func)

  override fun toString() = name.toString()
}

class AnnotatedExpression<T : Sort>(val term: Expression<T>, val annoations: List<Attribute>) :
    Expression<T>() {
  override val theories = emptySet<Theories>()
  override val func = null

  override val name = Keyword("!")
  override val sort = term.sort

  override fun copy(children: List<Expression<*>>): Expression<T> {
    require(children.size == 1)

    return AnnotatedExpression(children.single() as Expression<T>, annoations)
  }

  override val children: List<Expression<*>> = listOf(term)

  override fun toString() = "(! $term ${annoations.joinToString(" ")})"

  override fun toSMTString(quotingRule: QuotingRule, useIterative: Boolean): String =
      "(! ${term.toSMTString(quotingRule, useIterative)} ${annoations.joinToString(" ") { it.toSMTString(quotingRule, useIterative) }})"

  override fun toSMTString(
      builder: Appendable,
      quotingRule: QuotingRule,
      useIterative: Boolean,
  ): Appendable {
    builder.append("(! ")
    term.toSMTString(builder, quotingRule, useIterative)

    annoations.forEach {
      builder.append(" ")
      it.toSMTString(builder, quotingRule, useIterative)
    }

    return builder.append(")")
  }
}

class ExpressionCastException(msg: String) : ClassCastException(msg)

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

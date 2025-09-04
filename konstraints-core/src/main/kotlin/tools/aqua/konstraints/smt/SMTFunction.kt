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

import java.util.*
import tools.aqua.konstraints.util.zipWithSameLength

/**
 * SMTFunction of any arity.
 *
 * Use [invoke] to generate an expression with the given parameters applied.
 */
abstract class SMTFunction<out T : Sort> {
  abstract val symbol: Symbol
  abstract val sort: T
  abstract val parameters: List<Sort>

  /**
   * Construct an expressions from [args] and [indices].
   *
   * @throws [Exception] when [args] or [indices] are not applicable to this function
   */
  abstract fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<T>

  /**
   * Returns true if [this] and [other] match in [symbol], [sort] and have pairwise equal
   * [parameters].
   */
  final override fun equals(other: Any?): Boolean {
    if (this === other) return true
    if (other !is SMTFunction<*>) return false
    if (this is VarBinding && other !is VarBinding<*>) return false
    if (this !is VarBinding && other is VarBinding<*>) return false
    if (this is SortedVar && other !is SortedVar<*>) return false
    if (this !is SortedVar && other is SortedVar<*>) return false
    else if (symbol == other.symbol && // symbol equality
        sort == other.sort && // same sort
        parameters.size == other.parameters.size && // same number of parameters
        (parameters zip other.parameters).all { (s1, s2) -> s1 == s2 } // pairwise equal parameters
    ) return true
    return false

    // does not consider definition for equality because two functions
    // with the exact same signature (name, sort and parameters) can not be
    // overloaded by a differing definition
  }

  final override fun hashCode(): Int =
      symbol.hashCode() /* Objects.hash(symbol, sort, parameters) */

  /**
   * Cast [this] to [SMTFunction] with generic [T].
   *
   * @throws [FunctionCastException] if [this.sort] != [to]
   */
  infix fun <T : Sort> castTo(to: T): SMTFunction<T> {
    if (sort != to) {
      throw FunctionCastException(sort, to.toString())
    }

    @Suppress("UNCHECKED_CAST")
    return this as SMTFunction<T>
  }
}

/** Base class for all functions declared by the user. */
abstract class UserDeclaredSMTFunction<T : Sort> : SMTFunction<T>() {

  /**
   * Construct an expression from [args] and [indices].
   *
   * @returns [UserDeclaredExpression]
   * @throws [IllegalArgumentException] if [indices] is not empty
   * @throws [IllegalArgumentException] if [args] and [parameters] differ in length or are not
   *   pairwise equal
   */
  override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<T> {
    require(indices.isEmpty()) { "User declared functions can not be indexed!" }

    require(args.size == parameters.size) {
      "Expected ${parameters.size} arguments but got ${args.size}"
    }
    require((args zipWithSameLength parameters).all { (par, sort) -> par.sort == sort }) {
      "Expected arguments of $symbol to be (${parameters.joinToString(" ")}) but was (${args.map { expr -> expr.sort }.joinToString(" ")})"
    }

    return UserDeclaredExpression(symbol, sort, args, this)
  }
}

/** Base class for all functions defined by the user. */
abstract class DefinedSMTFunction<T : Sort> : SMTFunction<T>() {
  abstract val term: Expression<T>
  abstract val sortedVars: List<SortedVar<*>>

  /**
   * Construct an expression from [args] and [indices].
   *
   * @returns [UserDefinedExpression]
   * @throws [IllegalArgumentException] if [indices] is not empty
   * @throws [IllegalArgumentException] if [args] and [parameters] differ in length or are not
   *   pairwise equal
   */
  override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<T> {
    require(indices.isEmpty()) { "User declared functions can not be indexed!" }

    require(args.size == parameters.size) {
      "Expected ${parameters.size} arguments but got ${args.size}"
    }
    require((args zipWithSameLength parameters).all { (par, sort) -> par.sort == sort }) {
      "Expected arguments of $symbol to be (${parameters.joinToString(" ")}) but was (${args.map { expr -> expr.sort }.joinToString(" ")})"
    }

    return UserDefinedExpression(
        symbol, sort, args, FunctionDef(symbol, sortedVars, sort, term), this)
  }
}

/** Specialization of [ClassCastException], thrown when casting functions to an illegal sort. */
class FunctionCastException(from: Sort, to: String) :
    ClassCastException("Can not cast expression from $from to $to")

/** Variable bound inside a let. */
class VarBinding<T : Sort>(override val symbol: Symbol, val term: Expression<T>) :
    SMTFunction<T>() {

  operator fun invoke(args: List<Expression<*>>) = instance

  override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>) = instance

  val name = symbol.toString()
  override val sort: T = term.sort
  override val parameters = emptyList<Sort>()

  val instance = LocalExpression(symbol, sort, term, this)

  override fun toString() = "(${symbol.toSMTString()} $term)"
}

/** Variable bound by exists or forall quantifier. */
class SortedVar<out T : Sort>(override val symbol: Symbol, override val sort: T) :
    SMTFunction<T>() {
  operator fun invoke(args: List<Expression<*>>) = instance

  override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>) = instance

  override fun toString(): String = "(${symbol.toSMTString()} $sort)"

  val instance = BoundVariable(symbol, sort, this)
  override val parameters: List<Sort> = emptyList()
}

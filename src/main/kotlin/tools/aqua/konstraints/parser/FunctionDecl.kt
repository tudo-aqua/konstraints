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

package tools.aqua.konstraints.parser

import tools.aqua.konstraints.*

enum class Associativity {
  LEFT_ASSOC,
  RIGHT_ASSOC,
  PAIRWISE,
  CHAINABLE,
  NONE
}

open class FunctionDecl<S : Sort>(
    val name: String,
    val params: List<Sort>,
    val indices: Set<Index>,
    val sort: S,
    val associativity: Associativity = Associativity.NONE,
    val isAmbiguous: Boolean = false
) {
  val signature = Signature(emptySet(), indices, params, sort)

  open fun buildExpression(args: List<Expression<*>>): Expression<S> {
    bindTo(args)

    // TODO generate expression with args (data model flaw?)
    return NAryExpression(name, sort, args)
  }

  fun bindTo(args: List<Expression<*>>) =
      when (associativity) {
        Associativity.LEFT_ASSOC -> {
          args.slice(2 ..< args.size).forEach { require(args[0].sort == it.sort) }
          signature.bindTo(args.slice(0..1).map { it.sort }, sort)
        }
        Associativity.RIGHT_ASSOC -> {
          args.slice(2 ..< args.size).forEach { require(args[1].sort == it.sort) }
          signature.bindTo(args.slice(0..1).map { it.sort }, sort)
        }
        Associativity.PAIRWISE -> TODO("Implement pairwise binding")
        Associativity.CHAINABLE -> TODO("Implement chainable binding")
        Associativity.NONE -> signature.bindTo(args.map { it.sort }, sort)
      }

  /** Returns true if the function accepts the arguments provided */
  fun accepts(args: List<Expression<*>>): Boolean {
    try {
      bindTo(args)
    } catch (e: Exception) {
      return false
    }

    return true
  }

  override fun equals(other: Any?): Boolean =
      when {
        this === other -> true
        other !is FunctionDecl<*> -> false
        else -> (name == other.name) && (params == other.params) && (sort == other.sort)
      }

  override fun hashCode(): Int = name.hashCode() * 961 + params.hashCode() * 31 + sort.hashCode()
}

// TODO refactor sort into more meaningful name i.e. return
// TODO implement for indexed sorts
abstract class FunctionDecl1<P : Sort, S : Sort>(
    name: String,
    param: P,
    sort: S,
    associativity: Associativity
) : FunctionDecl<S>(name, listOf(param), emptySet(), sort, associativity) {

  override fun buildExpression(args: List<Expression<*>>): Expression<S> {
    val bindings = bindTo(args)

    return buildExpression(args.single() as Expression<P>, bindings)
  }

  abstract fun buildExpression(
      param: Expression<P>,
      bindings: Pair<Map<Sort, Sort>, Map<Index, NumeralIndex>>
  ): Expression<S>
}

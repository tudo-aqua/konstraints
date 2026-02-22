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

import kotlin.collections.sort

data class SelectorDecl<T : Sort>(val symbol: Symbol, val sort: T)

// selectors are functions that take a datatype and map to any sort type (e.g. for complex re maps
// from complex to real)
class Selector<T : Sort>(override val symbol: Symbol, override val sort: T, datatype: Datatype) :
    SMTFunction<T>() {
  override val parameters = listOf(datatype)

  fun toSMTString(quotingRule: QuotingRule, useIterative: Boolean) =
      "(${symbol.toSMTString(quotingRule, useIterative)} ${sort.toSMTString(quotingRule, useIterative)})"

  override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<T> {
    assert(args.size == 1)
    return SelectorExpression(symbol, sort, this, args)
  }
}

class SelectorExpression<T : Sort>(
    override val name: BaseSymbol,
    override val sort: T,
    override val func: SMTFunction<T>?,
    override val children: List<Expression<*>>,
) : Expression<T>() {
  override val theories: Set<Theories> = emptySet()

  override fun copy(children: List<Expression<*>>): Expression<T> {
    TODO("Not yet implemented")
  }
}

// constructors are functions that define how a datatype may be used or more accurately constructed
data class Constructor(
    override val symbol: Symbol,
    val selectors: List<Selector<*>>,
    override val sort: Datatype,
) : SMTFunction<Datatype>() {
  fun toSMTString(
      builder: Appendable,
      quotingRule: QuotingRule,
      useIterative: Boolean,
  ): Appendable {
    builder.append("(")
    symbol.toSMTString(builder, quotingRule, useIterative)
    selectors.joinTo(builder, " ") { it.toSMTString(quotingRule, useIterative) }
    return builder.append(")")
  }

  fun toSMTString(quotingRule: QuotingRule, useIterative: Boolean) =
      "(${symbol.toSMTString(quotingRule, useIterative)} ${selectors.joinToString(" ") { it.toSMTString(quotingRule, useIterative) }})"

  override val parameters: List<Sort> = selectors.map { selector -> selector.sort }

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<Datatype> {
    assert(args.size == selectors.size)
    assert((args zip selectors).all { (arg, selector) -> arg.sort == selector.sort })
    assert(indices.isEmpty())
    return ConstructorExpression(symbol, sort, this, args)
  }
}

class ConstructorExpression(
    override val name: BaseSymbol,
    override val sort: Datatype,
    override val func: SMTFunction<Datatype>?,
    override val children: List<Expression<*>>,
) : Expression<Datatype>() {
  override val theories: Set<Theories> = emptySet()

  override fun copy(children: List<Expression<*>>): Expression<Datatype> {
    TODO("Not yet implemented")
  }
}

data class ConstructorDecl(val symbol: Symbol, val selectors: List<SelectorDecl<*>>)

class DatatypeFactory(val instance: Datatype) : SortFactory {
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): Sort {
    assert(indices.isEmpty())
    // TODO assert parameters match DT parameters

    return instance
  }

  override fun isInstanceOf(sort: Sort): Boolean {
    assert(sort is Datatype)
    TODO()
  }

  override val isIndexed = false
  override val numIndicies = 0
}

/*
 * datatype dsl
 * buildDatatype(listOf(symbol, arity)) { Datatypes ->
 * compileDT()
 * }
 */

// TODO this should maybe be the factory (constructors etc. can be shared between instances)
open class Datatype(val arity: Int, symbol: Symbol) : Sort(symbol) {
  constructor(
      arity: Int,
      symbol: Symbol,
      constructorDecls: List<ConstructorDecl>,
  ) : this(arity, symbol) {
    _constructors.addAll(
        constructorDecls.map { constr ->
          Constructor(
              constr.symbol,
              constr.selectors.map { selectorDecl ->
                Selector(selectorDecl.symbol, selectorDecl.sort, this)
              },
              this,
          )
        }
    )
    _selectors.addAll(
        constructorDecls.flatMap { decl ->
          decl.selectors.map { selectorDecl ->
            Selector(selectorDecl.symbol, selectorDecl.sort, this)
          }
        }
    )
  }

  override val theories = emptySet<Theories>()
  private val _constructors = mutableListOf<Constructor>()
  private val _selectors = mutableListOf<Selector<*>>()

  val constructors: List<Constructor>
    get() = _constructors.toList()

  val selectors: List<Selector<*>>
    get() = _selectors.toList()

  internal fun add(constructor: ConstructorDecl) {
    _constructors.add(
        Constructor(
            constructor.symbol,
            constructor.selectors.map { selectorDecl ->
              Selector(selectorDecl.symbol, selectorDecl.sort, this)
            },
            this,
        )
    )
  }
}

object Testers : SMTFunction<BoolSort>() {
  override val symbol = "is".toSymbol()
  override val sort = SMTBool
  override val parameters: List<Sort> = emptyList()

  val constructors = mutableSetOf<Symbol>()

  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<BoolSort> {
    require(indices.size == 1)
    require(args.isEmpty())

    val index = indices.single()

    require(index is SymbolIndex)
    require(constructors.contains(index.symbol))

    return TesterExpression(index)
  }
}

class TesterExpression(index: SymbolIndex) : Expression<BoolSort>() {
  override val name = "is".toSymbol()
  override val sort = SMTBool
  override val theories = emptySet<Theories>()
  override val func = Testers
  override val children = emptyList<Expression<*>>()
  override val symbolicIndices = listOf(index.symbol)

  override fun copy(children: List<Expression<*>>): Expression<BoolSort> {
    return this
  }
}

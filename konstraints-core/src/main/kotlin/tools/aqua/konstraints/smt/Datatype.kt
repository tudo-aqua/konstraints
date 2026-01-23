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

data class SelectorDecl<T : Sort>(val symbol: Symbol, val sort: T)

// selectors are functions that take a datatype and map to any sort type (e.g. for complex re maps
// from complex to real)
class Selector<T : Sort>(override val symbol: Symbol, override val sort: T, datatype: Datatype) :
    SMTFunction<T>() {
  override val parameters = listOf(datatype)

  override fun constructDynamic(args: List<Expression<*>>, indices: List<Index>): Expression<T> {
      assert(args.size == 1)
    return SelectorExpression(symbol, sort, this, args)
  }
}

class SelectorExpression<T : Sort>(
    override val name: BaseSymbol,
    override val sort: T,
    override val func: SMTFunction<T>?,
    override val children: List<Expression<*>>
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
    override val children: List<Expression<*>>
) : Expression<Datatype>() {
    override val theories: Set<Theories> = emptySet()

    override fun copy(children: List<Expression<*>>): Expression<Datatype> {
        TODO("Not yet implemented")
    }

}

data class ConstructorDecl(val symbol: Symbol, val selectors: List<SelectorDecl<*>>)

class Datatype(val arity: Int, constructorDecls: List<ConstructorDecl>, symbol: Symbol) : Sort(symbol) {
  override val theories = emptySet<Theories>()
  val constructors =
      constructorDecls.map { constr ->
        Constructor(
            constr.symbol,
            constr.selectors.map { selectorDecl ->
              Selector(selectorDecl.symbol, selectorDecl.sort, this)
            },
            this,
        )
      }
  val selectors = constructorDecls.flatMap { decl -> decl.selectors.map { selectorDecl ->
      Selector(selectorDecl.symbol, selectorDecl.sort, this)
  } }

    val testers: Nothing = TODO()
}

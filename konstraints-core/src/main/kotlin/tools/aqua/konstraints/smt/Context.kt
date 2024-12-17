/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2024 The Konstraints Authors
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

import tools.aqua.konstraints.dsl.SMTFunction
import tools.aqua.konstraints.util.Stack


abstract class Context {
    private val nameLookup = mutableMapOf<String, Int>()
    private val assertionStack = Stack<AssertionLevel<>>()

    abstract fun let(bindings: List<VarBinding<*>>, lambda: (List<VarBinding<*>>) -> Unit)
    abstract fun exists(locals: List<SortedVar<*>>)
    abstract fun forall(locals: List<SortedVar<*>>)
}

interface AssertionLevel<SortType> {
    fun contains(function: String, args: List<Expression<*>>) = get(function, args) != null

    fun contains(function: Symbol) = functions.contains(function.toString())

    fun get(function: String, args: List<Expression<*>>) =
        functions[function]?.takeIf { it.accepts(args.map { it.sort }) }

    /*
    fun contains(sort: SortDecl<*>) = sorts.containsKey(sort.name.toString())

    fun contains(sort: Sort) = sorts.containsKey(sort.name.toString())

    fun containsSort(sort: String) = sorts.containsKey(sort)
    */

    fun add(function: SMTFunction<*>): Boolean

    //fun add(sort: SortDecl<*>): SortDecl<*>?

    val functions: Map<String, SMTFunction<*>>
    val sorts: Map<String, SortType>
}

interface GenericAssertionLevel : AssertionLevel<SMTFunction, ContextSort> {
    override fun contains(function: String, args: List<Expression<*>>) = get(function, args) != null

    override fun contains(function: Symbol) = functions.contains(function.toString())

    override fun get(function: String, args: List<Expression<*>>) =
        functions[function]?.takeIf { it(args) }

    override fun contains(sort: SortDecl<*>) = sorts.containsKey(sort.name.toString())

    override fun contains(sort: Sort) = sorts.containsKey(sort.name.toString())

    override fun containsSort(sort: String) = sorts.containsKey(sort)

    override fun add(function: FunctionDecl<*>): Boolean

    override fun add(sort: SortDecl<*>): SortDecl<*>?
}

interface ContextFunction {
    fun name(): String
    fun accepts(args: List<Sort>): Boolean
    fun acceptsExpressions(args: List<Expression<*>>): Boolean

}

interface ContextSort {

}
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
import tools.aqua.konstraints.util.zipWithSameLength

// TODO ambiguous lookup with params and return type
// TODO left-assoc, right-assoc, chainable, pairwise
data class Signature(
    val parametricSorts: Set<Sort>,
    val indices: Set<Index>,
    val parameters: List<Sort>,
    val sort: Sort
) {
    fun bindToOrNull(
        actualParameters: List<Sort>,
        actualReturn: Sort
    ): Pair<Map<Sort, Sort>, Map<Index, NumeralIndex>>? =
        try {
            bindTo(actualParameters, actualReturn)
        }  catch (exception : Exception) {
            null
        }

    fun bindTo(
        actualParameters: List<Sort>,
        actualReturn: Sort
    ): Pair<Map<Sort, Sort>, Map<Index, NumeralIndex>> {
        val parametricBindings = mutableMapOf<Sort, Sort>()
        val indexBindings = mutableMapOf<Index, NumeralIndex>()

        bindToInternal(parameters, actualParameters, parametricBindings, indexBindings)
        bindToInternal(sort, actualReturn, parametricBindings, indexBindings)

        return parametricBindings to indexBindings
    }

    private fun bindToInternal(
        symbolicParameters: List<Sort>,
        actualParameters: List<Sort>,
        parametricBindings: MutableMap<Sort, Sort>,
        indexBindings: MutableMap<Index, NumeralIndex>
    ) {
        (symbolicParameters zipWithSameLength actualParameters).forEach { (symbolic, actual) ->
            bindToInternal(symbolic, actual, parametricBindings, indexBindings)
        }
    }

    private fun bindToInternal(
        symbolic: Sort,
        actual: Sort,
        parametricBindings: MutableMap<Sort, Sort>,
        indexBindings: MutableMap<Index, NumeralIndex>
    ) {
        if (symbolic in parametricSorts) {
            // bind if not already bound
            parametricBindings.bindTo(symbolic, actual)
        } else {
            require(symbolic.name == actual.name)

            (symbolic.indices zipWithSameLength actual.indices).forEach { (symbolicIndex, actualIndex) ->
                bindToInternal(symbolicIndex, actualIndex, indexBindings)
            }
            bindToInternal(
                symbolic.parameters, actual.parameters, parametricBindings, indexBindings
            )
        }
    }

    private fun bindToInternal(
        symbolic: Index,
        actual: Index,
        indexBindings: MutableMap<Index, NumeralIndex>
    ) {
        require(actual is NumeralIndex)
        if (symbolic in indices) {
            indexBindings.bindTo(symbolic, actual)
        } else {
            require(symbolic is NumeralIndex)
            require(symbolic.numeral == actual.numeral)
        }
    }
}

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
        return BasicExpression(name, sort)
    }

    fun bindTo(args : List<Expression<*>>) = when(associativity) {
        Associativity.LEFT_ASSOC -> {
            args.slice(2..<args.size).forEach { require(args[0].sort == it.sort) }
            signature.bindTo(args.slice(0..1).map { it.sort }, sort)
        }
        Associativity.RIGHT_ASSOC -> {
            args.slice(2..<args.size).forEach { require(args[1].sort == it.sort) }
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

internal abstract class SortDecl<T : Sort>(val name: String) {
    abstract fun getSort(sort: ProtoSort): T
}

internal class Context {
    fun registerTheory(other: TheoryContext) {
        functions.addAll(other.functions)
        other.sorts.forEach { registerSort(it.value) }
    }

    /* Function is private to not allow illegal FunctionDecl to be registered */
    fun registerFunction(function: FunctionDecl<*>) {
        val other = functions.find { it.name == function.name && it.params == function.params }
        if (other != null) {
            if (other.sort == function.sort) {
                throw Exception(
                    "Function (${function.name} (${function.params.joinToString(" ")}) ${function.sort}) is already in context"
                )
            } else {
                TODO("Implement ambiguous function overloading")
            }
        } else {
            functions.add(function)
        }
    }

    fun registerFunction(const: ProtoDeclareConst, sort: Sort) {
        functions.add(FunctionDecl(const.name.token.getValue(), listOf(), emptySet(), sort))
    }

    fun registerFunction(function: ProtoDeclareFun, parameters: List<Sort>, sort: Sort) {
        if (parameters.isEmpty()) {
            registerFunction(function.name.token.getValue<String>(), listOf(), sort)
        } else {
            registerFunction(function.name.token.getValue<String>(), parameters, sort)
        }
    }

    fun registerFunction(name: String, params: List<Sort>, sort: Sort) {
        registerFunction(FunctionDecl(name, params, emptySet(), sort))
    }

    fun registerSort(sort: SortDecl<*>) {
        if (sorts.containsKey(sort.name))
            throw Exception("Sort ${sort.name} is already defined in context")

        sorts[sort.name] = sort
    }

    /**
     * Returns a function matching the identifier, which accepts the provided arguments Function must
     * not be ambiguous
     */
    fun getFunction(name: Identifier, args: List<Expression<*>>): FunctionDecl<*>? {
        return getFunction(name.symbol.token.getValue<String>(), args)
    }

    /**
     * Returns a function matching the name, which accepts the provided arguments Function must not be
     * ambiguous
     */
    fun getFunction(name: String, args: List<Expression<*>>): FunctionDecl<*>? {
        return functions.find { (it.name == name) && (it.accepts(args)) && !it.isAmbiguous }
    }

    /**
     * Returns a function matching the name and sort, which accepts the provided arguments Function
     * can be ambiguous
     */
    fun getFunction(name: String, args: List<Expression<*>>, sort: Sort): FunctionDecl<*>? {
        return functions.find { (it.name == name) && (it.accepts(args)) && it.sort == sort }
    }

    fun getSort(protoSort: ProtoSort): Sort {
        return sorts[protoSort.identifier.symbol.token.getValue()]?.getSort(protoSort)
            ?: throw Exception("Unknown sort ${protoSort.identifier.symbol.token.getValue<String>()}")
    }

    private val functions: HashSet<FunctionDecl<*>> = hashSetOf()
    private val sorts: MutableMap<String, SortDecl<*>> = mutableMapOf()
}

internal interface TheoryContext {
    val functions: HashSet<FunctionDecl<*>>
    val sorts: Map<String, SortDecl<*>>
}

class BindException(val key: Any, val existing: Any, val new: Any) :
    RuntimeException("$new could not be bound to $key; already bound to $existing")

fun <K : Any, V : Any> MutableMap<K, V>.bindTo(key: K, value: V) {
    putIfAbsent(key, value)?.let { if (it != value) throw BindException(key, it, value) }
}

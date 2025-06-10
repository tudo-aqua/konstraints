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

import tools.aqua.konstraints.parser.ArrayExTheory
import tools.aqua.konstraints.parser.BitVectorExpressionTheory
import tools.aqua.konstraints.parser.CoreTheory
import tools.aqua.konstraints.parser.FloatingPointTheory
import tools.aqua.konstraints.parser.IntsTheory
import tools.aqua.konstraints.parser.RealsIntsTheory
import tools.aqua.konstraints.parser.RealsTheory
import tools.aqua.konstraints.parser.StringsTheory
import tools.aqua.konstraints.theories.ArraySort
import tools.aqua.konstraints.theories.BVSort
import tools.aqua.konstraints.theories.BoolSort
import tools.aqua.konstraints.theories.FPSort
import tools.aqua.konstraints.theories.IntSort
import tools.aqua.konstraints.theories.RealSort
import tools.aqua.konstraints.theories.RegLan
import tools.aqua.konstraints.theories.RoundingMode
import tools.aqua.konstraints.theories.StringSort
import tools.aqua.konstraints.theories.Theories
import tools.aqua.konstraints.util.Stack

private class CurrentContext {
  val functions = mutableMapOf<Symbol, SMTFunction<*>>()
  val sorts = mutableMapOf<Symbol, SortFactory>()
}

class Context {
  private val forbiddenNames = mutableSetOf<Symbol>()
  private val currentContext = CurrentContext()
  private val shadowingMap = Stack<MutableMap<SMTFunction<*>, SMTFunction<*>>>()
  private val functionUndoStack = Stack<MutableSet<Symbol>>()
  private val sortUndoStack = Stack<MutableSet<Symbol>>()
  private val sortParameters = mutableListOf<Symbol>()
  var locals: List<SortedVar<*>> = emptyList()
  private var logic: Logic? = null

  // true if we are currently in any binder (let/exists/forall/par/match)
  private var activeBinderState = false

  fun <T : Sort> addFunOrNull(func: SMTFunction<T>): SMTFunction<T>? {
    return try {
      addFun(func)
    } catch (_: IllegalArgumentException) {
      null
    } catch (_: IllegalStateException) {
      null
    }
  }

  fun <T : Sort> addFun(func: SMTFunction<T>): SMTFunction<T> {
    require(func.symbol !in forbiddenNames) {
      "Can not overload or shadow theory symbol ${func.symbol}!"
    }
    require(func.symbol !in currentContext.functions) {
      "Can not overload or shadow user defined symbol ${func.symbol}!"
    }
    check(!activeBinderState) { "Can not add functions to the current context in this state!" }

    currentContext.functions[func.symbol] = func

    // if the undoStack is not empty, and we are not currently inside any binder
    // there was at least one push, so we save the added func to remove on the next pop operation
    if (functionUndoStack.isNotEmpty()) {
      functionUndoStack.peek().add(func.symbol)
    }

    return func
  }

  fun addSortOrNull(sort: UserDeclaredSortFactory): UserDeclaredSortFactory? {
    return try {
      declareSort(sort)
    } catch (_: IllegalArgumentException) {
      null
    } catch (_: IllegalStateException) {
      null
    }
  }

  fun declareSort(decl: DeclareSort) = declareSort(UserDeclaredSortFactory(decl.name, decl.arity))

  fun declareSort(name: Symbol, arity: Int) = declareSort(UserDeclaredSortFactory(name, arity))

  fun declareSort(sort: UserDeclaredSortFactory) =
      addSort(sort, sort.symbol) as UserDeclaredSortFactory

  internal fun addSort(sort: SortFactory, symbol: Symbol): SortFactory {
    require(symbol !in currentContext.sorts) { "Can not overload or shadow sort symbol ${symbol}!" }

    check(!activeBinderState) { "Can not add sort to the current context in this state!" }

    currentContext.sorts[symbol] = sort

    if (sortUndoStack.isNotEmpty()) {
      sortUndoStack.peek().add(symbol)
    }

    return sort
  }

  fun addSortParameters(parameters: List<Symbol>) =
      parameters.map { symbol -> addSortParameter(symbol) }

  fun addSortParameter(parameter: Symbol): SortParameterFactory {
    sortParameters.add(parameter)

    return addSort(SortParameterFactory(parameter), parameter) as SortParameterFactory
  }

  fun clearSortParameters() {
    currentContext.sorts.keys.removeAll(sortParameters)
    sortParameters.clear()
  }

  fun defineSort(def: DefineSort) = defineSort(def.name, def.sortParameters, def.sort)

  fun defineSort(name: Symbol, parameters: List<Symbol>, sort: Sort) =
      when (sort) {
        is BoolSort -> defineSort(name, BoolFactory)
        is IntSort -> defineSort(name, IntFactory)
        is RealSort -> defineSort(name, RealFactory)
        is StringSort -> defineSort(name, StringFactory)
        is RegLan -> defineSort(name, RegLanFactory)
        is RoundingMode -> defineSort(name, RoundingModeFactory)
        is BVSort -> defineSort(name, UserDefinedBitVectorFactory(name, sort.bits, parameters))
        is FPSort ->
            defineSort(
                name,
                UserDefinedFloatingPointFactory(
                    name, sort.exponentBits, sort.significantBits, parameters))
        is ArraySort<*, *> ->
            defineSort(name, UserDefinedArrayFactory(name, sort.parameters, parameters))
        else -> TODO("Implement UserDefinedUserDeclaredSortFactory")
      }

  fun defineSort(symbol: Symbol, factory: SortFactory): SortFactory {
    require(symbol !in currentContext.sorts) { "Can not overload or shadow sort symbol ${symbol}!" }

    check(!activeBinderState) { "Can not add sort to the current context in this state!" }

    currentContext.sorts[symbol] = factory

    if (sortUndoStack.isNotEmpty()) {
      sortUndoStack.peek().add(symbol)
    }

    return factory
  }

  fun defineSort(factory: UserDefinedSortFactory) =
      defineSort(factory.symbol, factory) as UserDefinedSortFactory

  operator fun contains(func: Symbol) = currentContext.functions[func] != null

  // TODO this function should probably not exist look into checkContext
  operator fun contains(expression: Expression<*>) =
      expression.func?.symbol in currentContext.functions

  operator fun contains(sort: Sort): Boolean = sort.symbol in currentContext.sorts

  fun containsSort(sort: Symbol): Boolean = sort in currentContext.sorts

  fun <T : Sort> getFuncOrNull(name: Symbol, sort: T) =
      try {
        getFunc(name, sort)
      } catch (_: FunctionNotFoundException) {
        null
      }

  fun <T : Sort> getFunc(name: Symbol, sort: T) =
      currentContext.functions[name]?.castTo(sort) ?: throw FunctionNotFoundException(name)

  fun getFuncOrNull(name: Symbol): SMTFunction<*>? {
    return try {
      getFunc(name)
    } catch (_: FunctionNotFoundException) {
      null
    }
  }

  fun getFunc(name: Symbol) =
      if (currentContext.functions[name] != null) {
        currentContext.functions[name]!!
      } else {
        locals.find { it -> it.symbol == name } ?: throw FunctionNotFoundException(name)
      }

  fun push(n: Int) = repeat(n) { _ -> push() }

  // use if you have to pop manually or the operation can not be completed within the lambda passed
  // to push
  fun push() {
    functionUndoStack.push(mutableSetOf<Symbol>())
    sortUndoStack.push(mutableSetOf<Symbol>())
  }

  fun getSortOrNull(name: Symbol): SortFactory? {
    return try {
      getSort(name)
    } catch (_: FunctionNotFoundException) {
      null
    }
  }

  fun getSort(name: Symbol): SortFactory =
      currentContext.sorts[name] ?: throw SortNotFoundException(name)

  // auto pops after block
  fun push(block: Context.() -> Unit) {
    functionUndoStack.push(mutableSetOf<Symbol>())
    sortUndoStack.push(mutableSetOf<Symbol>())
    block()
    pop(1)
  }

  fun pop(n: Int) {
    check(n <= functionUndoStack.size)
    check(!activeBinderState) { "Can not pop inside binder!" }

    repeat(n) { _ ->
      functionUndoStack.pop().forEach { symbol -> currentContext.functions.remove(symbol) }
      currentContext.sorts.keys.removeAll(sortUndoStack.pop())
    }
  }

  internal fun <T> let(varBindings: List<VarBinding<*>>, block: () -> T): T {
    bindVariables(varBindings)
    val result = block()
    unbindVariables()

    return result
  }

  internal fun <T> exists(sortedVars: List<SortedVar<*>>, block: () -> T): T {
    bindVariables(sortedVars)
    val result = block()
    unbindVariables()

    return result
  }

  internal fun <T> forall(sortedVars: List<SortedVar<*>>, block: () -> T): T {
    bindVariables(sortedVars)
    val result = block()
    unbindVariables()

    return result
  }

  /**
   * Bind local variables by
   * - adding all bindings that shadow a function in the current context to the shadowing map
   * - adding all remaining functions to the undo stack all bindings must be distinct by name
   */
  @JvmName("bindVariablesLet")
  internal fun bindVariables(varBindings: List<VarBinding<*>>) {
    require(varBindings.distinctBy { it.name }.size == varBindings.size) {
      "VarBindings in let must be distinct!"
    }
    require(varBindings.all { it.symbol !in forbiddenNames }) {
      "VarBindings can not shadow theory function symbols!"
    }

    shadowingMap.push(mutableMapOf())

    // add all bindings to undoStack first, remove all binding that shadow from undoStack later
    functionUndoStack.push(mutableSetOf())
    functionUndoStack.peek().addAll(varBindings.map { it.symbol })

    varBindings.forEach { binding ->
      currentContext.functions.put(binding.symbol, binding)?.let { old ->
        shadowingMap.peek().put(binding, old)
        functionUndoStack.peek().remove(binding.symbol)
      }
    }
  }

  /**
   * Bind local variables by
   * - adding all bindings that shadow a function in the current context to the shadowing map
   * - adding all remaining functions to the undo stack
   */
  @JvmName("bindVariablesQuantifier")
  internal fun bindVariables(sortedVars: List<SortedVar<*>>) {
    require(sortedVars.all { it.symbol !in forbiddenNames }) {
      "VarBindings can not shadow theory function symbols!"
    }

    // remove all shadowing bindings keep only the !last! instance on each conflict
    val vars = sortedVars.reversed().distinctBy { it.symbol }.reversed()

    shadowingMap.push(mutableMapOf())

    // add all bindings to undoStack first, remove all binding that shadow from undoStack later
    functionUndoStack.push(mutableSetOf())
    functionUndoStack.peek().addAll(vars.map { it.symbol })

    vars.forEach { binding ->
      currentContext.functions.put(binding.symbol, binding)?.let { old ->
        shadowingMap.peek().put(binding, old)
        functionUndoStack.peek().remove(binding.symbol)
      }
    }
  }

  /**
   * Reverse the last binder operation by
   * - reversing all shadowing on the current context
   * - removing all local variable from the current context Pops the top level of the shadowingMap
   *   and undo stack
   */
  internal fun unbindVariables() {
    // add all shadowed elements back first, then remove all remaining bindings
    shadowingMap.pop().forEach { (local, shadowed) ->
      currentContext.functions[local.symbol] = shadowed
    }
    functionUndoStack.pop().forEach { symbol -> currentContext.functions.remove(symbol) }
  }

  internal fun bindSortParameters(bindings: List<Symbol>) {}

  fun setLogic(logic: Logic) {
    this.logic = logic

    logic.theories.forEach { theory ->
      when (theory) {
        Theories.CORE -> CoreTheory
        Theories.ARRAYS_EX -> ArrayExTheory
        Theories.FIXED_SIZE_BIT_VECTORS -> BitVectorExpressionTheory
        Theories.FLOATING_POINT -> FloatingPointTheory
        Theories.INTS -> IntsTheory
        Theories.REALS -> RealsTheory
        Theories.REALS_INTS -> RealsIntsTheory
        Theories.STRINGS -> StringsTheory
      }.let {
        forbiddenNames.addAll(it.functions.map { (_, func) -> func.symbol })
        currentContext.functions.putAll(it.functions)
        currentContext.sorts.putAll(it.sorts)
      }
    }
  }
}

fun Context.contains(func: String) = contains(func.toSymbolWithQuotes())

fun <T : Sort> Context.getFuncOrNull(name: String, sort: T) =
    getFuncOrNull(name.toSymbolWithQuotes(), sort)

fun Context.getFuncOrNull(name: String) = getFuncOrNull(name.toSymbolWithQuotes())

fun Context.getFunc(name: String) = getFunc(name.toSymbolWithQuotes())

fun <T : Sort> Context.let(
    varBindings: List<VarBinding<*>>,
    block: (List<Expression<*>>, Context) -> Expression<T>
) = let(varBindings) { block(varBindings.map { it.instance }, this) }

fun <T : Sort, S : Sort> Context.let(
    varBinding: VarBinding<T>,
    block: (Expression<T>, Context) -> Expression<S>
) = let(listOf(varBinding)) { block(varBinding.instance, this) }

fun <T1 : Sort, T2 : Sort, S : Sort> Context.let(
    varBinding1: VarBinding<T1>,
    varBinding2: VarBinding<T2>,
    block: (Expression<T1>, Expression<T2>, Context) -> Expression<S>
) =
    let(listOf(varBinding1, varBinding2)) {
      block(varBinding1.instance, varBinding2.instance, this)
    }

fun <T1 : Sort, T2 : Sort, T3 : Sort, S : Sort> Context.let(
    varBinding1: VarBinding<T1>,
    varBinding2: VarBinding<T2>,
    varBinding3: VarBinding<T3>,
    block: (Expression<T1>, Expression<T2>, Expression<T3>, Context) -> Expression<S>
) =
    let(listOf(varBinding1, varBinding2, varBinding3)) {
      block(varBinding1.instance, varBinding2.instance, varBinding3.instance, this)
    }

fun <T1 : Sort, T2 : Sort, T3 : Sort, T4 : Sort, S : Sort> Context.let(
    varBinding1: VarBinding<T1>,
    varBinding2: VarBinding<T2>,
    varBinding3: VarBinding<T3>,
    varBinding4: VarBinding<T4>,
    block:
        (Expression<T1>, Expression<T2>, Expression<T3>, Expression<T4>, Context) -> Expression<S>
) =
    let(listOf(varBinding1, varBinding2, varBinding3, varBinding4)) {
      block(
          varBinding1.instance,
          varBinding2.instance,
          varBinding3.instance,
          varBinding4.instance,
          this)
    }

fun <T1 : Sort, T2 : Sort, T3 : Sort, T4 : Sort, T5 : Sort, S : Sort> Context.let(
    varBinding1: VarBinding<T1>,
    varBinding2: VarBinding<T2>,
    varBinding3: VarBinding<T3>,
    varBinding4: VarBinding<T4>,
    varBinding5: VarBinding<T5>,
    block:
        (
            Expression<T1>,
            Expression<T2>,
            Expression<T3>,
            Expression<T4>,
            Expression<T5>,
            Context) -> Expression<S>
) =
    let(listOf(varBinding1, varBinding2, varBinding3, varBinding4, varBinding5)) {
      block(
          varBinding1.instance,
          varBinding2.instance,
          varBinding3.instance,
          varBinding4.instance,
          varBinding5.instance,
          this)
    }

@JvmName("letWithExpression")
fun <T : Sort> Context.let(
    varBindings: List<Expression<*>>,
    block: (List<Expression<*>>, Context) -> Expression<T>
) =
    let(
        varBindings.mapIndexed { idx, expr ->
          VarBinding("local${expr.sort}${idx}".toSymbolWithQuotes(), expr)
        },
        block)

fun <T : Sort, S : Sort> Context.let(
    term: Expression<T>,
    block: (Expression<T>, Context) -> Expression<S>
) = let(VarBinding("local${term.sort}".toSymbolWithQuotes(), term), block)

fun <T1 : Sort, T2 : Sort, S : Sort> Context.let(
    term1: Expression<T1>,
    term2: Expression<T2>,
    block: (Expression<T1>, Expression<T2>, Context) -> Expression<S>
) =
    let(
        VarBinding("local${term1.sort}1".toSymbolWithQuotes(), term1),
        VarBinding("local${term2.sort}2".toSymbolWithQuotes(), term2),
        block)

fun <T1 : Sort, T2 : Sort, T3 : Sort, S : Sort> Context.let(
    term1: Expression<T1>,
    term2: Expression<T2>,
    term3: Expression<T3>,
    block: (Expression<T1>, Expression<T2>, Expression<T3>, Context) -> Expression<S>
) =
    let(
        VarBinding("local${term1.sort}1".toSymbolWithQuotes(), term1),
        VarBinding("local${term2.sort}2".toSymbolWithQuotes(), term2),
        VarBinding("local${term3.sort}3".toSymbolWithQuotes(), term3),
        block)

fun <T1 : Sort, T2 : Sort, T3 : Sort, T4 : Sort, S : Sort> Context.let(
    term1: Expression<T1>,
    term2: Expression<T2>,
    term3: Expression<T3>,
    term4: Expression<T4>,
    block:
        (Expression<T1>, Expression<T2>, Expression<T3>, Expression<T4>, Context) -> Expression<S>
) =
    let(
        VarBinding("local${term1.sort}1".toSymbolWithQuotes(), term1),
        VarBinding("local${term2.sort}2".toSymbolWithQuotes(), term2),
        VarBinding("local${term3.sort}3".toSymbolWithQuotes(), term3),
        VarBinding("local${term4.sort}4".toSymbolWithQuotes(), term4),
        block)

fun <T1 : Sort, T2 : Sort, T3 : Sort, T4 : Sort, T5 : Sort, S : Sort> Context.let(
    term1: Expression<T1>,
    term2: Expression<T2>,
    term3: Expression<T3>,
    term4: Expression<T4>,
    term5: Expression<T5>,
    block:
        (
            Expression<T1>,
            Expression<T2>,
            Expression<T3>,
            Expression<T4>,
            Expression<T5>,
            Context) -> Expression<S>
) =
    let(
        VarBinding("local${term1.sort}1".toSymbolWithQuotes(), term1),
        VarBinding("local${term2.sort}2".toSymbolWithQuotes(), term2),
        VarBinding("local${term3.sort}3".toSymbolWithQuotes(), term3),
        VarBinding("local${term4.sort}4".toSymbolWithQuotes(), term4),
        VarBinding("local${term5.sort}5".toSymbolWithQuotes(), term5),
        block)

fun Context.exists(
    sortedVars: List<SortedVar<*>>,
    block: (List<Expression<*>>, Context) -> Expression<BoolSort>
) = exists(sortedVars) { block(sortedVars.map { it.instance }, this) }

fun <S : Sort> Context.exists(
    sortedVar: SortedVar<S>,
    block: (Expression<S>, Context) -> Expression<BoolSort>
) = exists(listOf(sortedVar)) { block(sortedVar.instance, this) }

fun <S1 : Sort, S2 : Sort> Context.exists(
    sortedVar1: SortedVar<S1>,
    sortedVar2: SortedVar<S2>,
    block: (Expression<S1>, Expression<S2>, Context) -> Expression<BoolSort>
) = exists(listOf(sortedVar1, sortedVar2)) { block(sortedVar1.instance, sortedVar2.instance, this) }

fun <S1 : Sort, S2 : Sort, S3 : Sort> Context.exists(
    sortedVar1: SortedVar<S1>,
    sortedVar2: SortedVar<S2>,
    sortedVar3: SortedVar<S3>,
    block: (Expression<S1>, Expression<S2>, Expression<S3>, Context) -> Expression<BoolSort>
) =
    exists(listOf(sortedVar1, sortedVar2, sortedVar3)) {
      block(sortedVar1.instance, sortedVar2.instance, sortedVar3.instance, this)
    }

fun <S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort> Context.exists(
    sortedVar1: SortedVar<S1>,
    sortedVar2: SortedVar<S2>,
    sortedVar3: SortedVar<S3>,
    sortedVar4: SortedVar<S4>,
    block:
        (Expression<S1>, Expression<S2>, Expression<S3>, Expression<S4>, Context) -> Expression<
                BoolSort>
) =
    exists(listOf(sortedVar1, sortedVar2, sortedVar3, sortedVar4)) {
      block(
          sortedVar1.instance, sortedVar2.instance, sortedVar3.instance, sortedVar4.instance, this)
    }

fun <S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort, S5 : Sort> Context.exists(
    sortedVar1: SortedVar<S1>,
    sortedVar2: SortedVar<S2>,
    sortedVar3: SortedVar<S3>,
    sortedVar4: SortedVar<S4>,
    sortedVar5: SortedVar<S5>,
    block:
        (
            Expression<S1>,
            Expression<S2>,
            Expression<S3>,
            Expression<S4>,
            Expression<S5>,
            Context) -> Expression<BoolSort>
) =
    exists(listOf(sortedVar1, sortedVar2, sortedVar3, sortedVar4, sortedVar5)) {
      block(
          sortedVar1.instance,
          sortedVar2.instance,
          sortedVar3.instance,
          sortedVar4.instance,
          sortedVar5.instance,
          this)
    }

@JvmName("existsWithSorts")
fun Context.exists(
    sortedVars: List<Sort>,
    block: (List<Expression<*>>, Context) -> Expression<BoolSort>
) =
    exists(
        sortedVars.mapIndexed { idx, sort ->
          SortedVar("local!${sort}${idx}".toSymbolWithQuotes(), sort)
        },
        block)

fun <S : Sort> Context.exists(sort: S, block: (Expression<S>, Context) -> Expression<BoolSort>) =
    exists(SortedVar("local!${sort}".toSymbolWithQuotes(), sort), block)

fun <S1 : Sort, S2 : Sort> Context.exists(
    sort1: S1,
    sort2: S2,
    block: (Expression<S1>, Expression<S2>, Context) -> Expression<BoolSort>
) =
    exists(
        SortedVar("local!${sort1}1".toSymbolWithQuotes(), sort1),
        SortedVar("local!${sort2}2".toSymbolWithQuotes(), sort2),
        block)

fun <S1 : Sort, S2 : Sort, S3 : Sort> Context.exists(
    sort1: S1,
    sort2: S2,
    sort3: S3,
    block: (Expression<S1>, Expression<S2>, Expression<S3>, Context) -> Expression<BoolSort>
) =
    exists(
        SortedVar("local!${sort1}1".toSymbolWithQuotes(), sort1),
        SortedVar("local!${sort2}2".toSymbolWithQuotes(), sort2),
        SortedVar("local!${sort3}3".toSymbolWithQuotes(), sort3),
        block)

fun <S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort> Context.exists(
    sort1: S1,
    sort2: S2,
    sort3: S3,
    sort4: S4,
    block:
        (Expression<S1>, Expression<S2>, Expression<S3>, Expression<S4>, Context) -> Expression<
                BoolSort>
) =
    exists(
        SortedVar("local!${sort1}1".toSymbolWithQuotes(), sort1),
        SortedVar("local!${sort2}2".toSymbolWithQuotes(), sort2),
        SortedVar("local!${sort3}3".toSymbolWithQuotes(), sort3),
        SortedVar("local!${sort4}4".toSymbolWithQuotes(), sort4),
        block)

fun <S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort, S5 : Sort> Context.exists(
    sort1: S1,
    sort2: S2,
    sort3: S3,
    sort4: S4,
    sort5: S5,
    block:
        (
            Expression<S1>,
            Expression<S2>,
            Expression<S3>,
            Expression<S4>,
            Expression<S5>,
            Context) -> Expression<BoolSort>
) =
    exists(
        SortedVar("local!${sort1}1".toSymbolWithQuotes(), sort1),
        SortedVar("local!${sort2}2".toSymbolWithQuotes(), sort2),
        SortedVar("local!${sort3}3".toSymbolWithQuotes(), sort3),
        SortedVar("local!${sort4}4".toSymbolWithQuotes(), sort4),
        SortedVar("local!${sort5}5".toSymbolWithQuotes(), sort5),
        block)

fun Context.forall(
    sortedVars: List<SortedVar<*>>,
    block: (List<Expression<*>>, Context) -> Expression<BoolSort>
) = forall(sortedVars) { block(sortedVars.map { it.instance }, this) }

fun <S : Sort> Context.forall(
    sortedVar: SortedVar<S>,
    block: (Expression<S>, Context) -> Expression<BoolSort>
) = forall(listOf(sortedVar)) { block(sortedVar.instance, this) }

fun <S1 : Sort, S2 : Sort> Context.forall(
    sortedVar1: SortedVar<S1>,
    sortedVar2: SortedVar<S2>,
    block: (Expression<S1>, Expression<S2>, Context) -> Expression<BoolSort>
) = forall(listOf(sortedVar1, sortedVar2)) { block(sortedVar1.instance, sortedVar2.instance, this) }

fun <S1 : Sort, S2 : Sort, S3 : Sort> Context.forall(
    sortedVar1: SortedVar<S1>,
    sortedVar2: SortedVar<S2>,
    sortedVar3: SortedVar<S3>,
    block: (Expression<S1>, Expression<S2>, Expression<S3>, Context) -> Expression<BoolSort>
) =
    forall(listOf(sortedVar1, sortedVar2, sortedVar3)) {
      block(sortedVar1.instance, sortedVar2.instance, sortedVar3.instance, this)
    }

fun <S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort> Context.forall(
    sortedVar1: SortedVar<S1>,
    sortedVar2: SortedVar<S2>,
    sortedVar3: SortedVar<S3>,
    sortedVar4: SortedVar<S4>,
    block:
        (Expression<S1>, Expression<S2>, Expression<S3>, Expression<S4>, Context) -> Expression<
                BoolSort>
) =
    forall(listOf(sortedVar1, sortedVar2, sortedVar3, sortedVar4)) {
      block(
          sortedVar1.instance, sortedVar2.instance, sortedVar3.instance, sortedVar4.instance, this)
    }

fun <S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort, S5 : Sort> Context.forall(
    sortedVar1: SortedVar<S1>,
    sortedVar2: SortedVar<S2>,
    sortedVar3: SortedVar<S3>,
    sortedVar4: SortedVar<S4>,
    sortedVar5: SortedVar<S5>,
    block:
        (
            Expression<S1>,
            Expression<S2>,
            Expression<S3>,
            Expression<S4>,
            Expression<S5>,
            Context) -> Expression<BoolSort>
) =
    forall(listOf(sortedVar1, sortedVar2, sortedVar3, sortedVar4, sortedVar5)) {
      block(
          sortedVar1.instance,
          sortedVar2.instance,
          sortedVar3.instance,
          sortedVar4.instance,
          sortedVar5.instance,
          this)
    }

@JvmName("forallWithSorts")
fun Context.forall(
    sortedVars: List<Sort>,
    block: (List<Expression<*>>, Context) -> Expression<BoolSort>
) =
    forall(
        sortedVars.mapIndexed { idx, sort ->
          SortedVar("local!${sort}${idx}".toSymbolWithQuotes(), sort)
        },
        block)

fun <S : Sort> Context.forall(sort: S, block: (Expression<S>, Context) -> Expression<BoolSort>) =
    forall(SortedVar("local!${sort}".toSymbolWithQuotes(), sort), block)

fun <S1 : Sort, S2 : Sort> Context.forall(
    sort1: S1,
    sort2: S2,
    block: (Expression<S1>, Expression<S2>, Context) -> Expression<BoolSort>
) =
    forall(
        SortedVar("local!${sort1}1".toSymbolWithQuotes(), sort1),
        SortedVar("local!${sort2}2".toSymbolWithQuotes(), sort2),
        block)

fun <S1 : Sort, S2 : Sort, S3 : Sort> Context.forall(
    sort1: S1,
    sort2: S2,
    sort3: S3,
    block: (Expression<S1>, Expression<S2>, Expression<S3>, Context) -> Expression<BoolSort>
) =
    forall(
        SortedVar("local!${sort1}1".toSymbolWithQuotes(), sort1),
        SortedVar("local!${sort2}2".toSymbolWithQuotes(), sort2),
        SortedVar("local!${sort3}3".toSymbolWithQuotes(), sort3),
        block)

fun <S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort> Context.forall(
    sort1: S1,
    sort2: S2,
    sort3: S3,
    sort4: S4,
    block:
        (Expression<S1>, Expression<S2>, Expression<S3>, Expression<S4>, Context) -> Expression<
                BoolSort>
) =
    forall(
        SortedVar("local!${sort1}1".toSymbolWithQuotes(), sort1),
        SortedVar("local!${sort2}2".toSymbolWithQuotes(), sort2),
        SortedVar("local!${sort3}3".toSymbolWithQuotes(), sort3),
        SortedVar("local!${sort4}4".toSymbolWithQuotes(), sort4),
        block)

fun <S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort, S5 : Sort> Context.forall(
    sort1: S1,
    sort2: S2,
    sort3: S3,
    sort4: S4,
    sort5: S5,
    block:
        (
            Expression<S1>,
            Expression<S2>,
            Expression<S3>,
            Expression<S4>,
            Expression<S5>,
            Context) -> Expression<BoolSort>
) =
    forall(
        SortedVar("local!${sort1}1".toSymbolWithQuotes(), sort1),
        SortedVar("local!${sort2}2".toSymbolWithQuotes(), sort2),
        SortedVar("local!${sort3}3".toSymbolWithQuotes(), sort3),
        SortedVar("local!${sort4}4".toSymbolWithQuotes(), sort4),
        SortedVar("local!${sort5}5".toSymbolWithQuotes(), sort5),
        block)

class FunctionNotFoundException(name: Symbol) : NoSuchElementException("Function $name not found")

class SortNotFoundException(name: Symbol) : NoSuchElementException("Sort $name not found")

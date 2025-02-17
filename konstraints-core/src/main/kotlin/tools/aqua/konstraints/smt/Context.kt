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

import tools.aqua.konstraints.parser.Theory
import tools.aqua.konstraints.theories.BoolSort
import tools.aqua.konstraints.util.Stack
import tools.aqua.konstraints.util.zipWithSameLength

private class CurrentContext {
  val functions = mutableMapOf<Symbol, SMTFunction<*>>()
  val sorts = mutableMapOf<Symbol, Sort>()
}

class Context {
  private val forbiddenNames = mutableSetOf<Symbol>()
  private val currentContext = CurrentContext()
  private val shadowingMap = Stack<MutableMap<SMTFunction<*>, SMTFunction<*>>>()
  private val undoStack = Stack<MutableSet<SMTFunction<*>>>()
  private var logic: Logic? = null

  // true if we are currently in any binder (let/exists/forall/par/match)
  private var activeBinderState = false

  fun <T : Sort> addFunOrNull(func: SMTFunction<T>): SMTFunction<T>? {
    return try {
      addFun(func)
    } catch (_: IllegalArgumentException) {
      return null
    } catch (_: IllegalStateException) {
      return null
    }
  }

  fun <T : Sort> addFun(func: SMTFunction<T>): SMTFunction<T> {
    require(func.symbol !in forbiddenNames) {
      "Can not overload or shadow theory symbol ${func.name}!"
    }
    require(func.symbol !in currentContext.functions) {
      "Can not overload or shadow user defined symbol ${func.name}!"
    }
    check(!activeBinderState) { "Can not add functions to the current context in this state!" }

    currentContext.functions[func.symbol] = func

    // if the undoStack is not empty, and we are not currently inside any binder
    // there was at least one push, so we save the added func to remove on the appropriate pop
    if (undoStack.isNotEmpty()) {
      undoStack.peek().add(func)
    }

    return func
  }

  fun contains(func: Symbol) = currentContext.functions[func] != null

  fun contains(expression: Expression<*>) = expression.func in currentContext.functions.values

  fun contains(sort: Sort): Boolean = sort in currentContext.sorts.values

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
      currentContext.functions[name] ?: throw FunctionNotFoundException(name)

  fun push(block: Context.() -> Unit) {
    undoStack.push(mutableSetOf<SMTFunction<*>>())
    block()
    pop(1)
  }

  fun pop(n: Int) {
    check(n <= undoStack.size)
    check(!activeBinderState) { "Can not pop inside binder!" }

    (0..<n).forEach { _ -> currentContext.functions.values.removeAll(undoStack.pop()) }
  }

  internal fun <T : Sort> let(
      varBindings: List<VarBinding<*>>,
      block: () -> Expression<T>
  ): LetExpression<T> {
    bindVariables(varBindings)
    val term = block()
    unbindVariables()

    return LetExpression(varBindings, term)
  }

  internal fun exists(
      sortedVars: List<SortedVar<*>>,
      block: () -> Expression<BoolSort>
  ): ExistsExpression {
    bindVariables(sortedVars)
    val term = block()
    unbindVariables()

    return ExistsExpression(sortedVars, term)
  }

  internal fun forall(
      sortedVars: List<SortedVar<*>>,
      block: () -> Expression<BoolSort>
  ): ForallExpression {
    bindVariables(sortedVars)
    val term = block()
    unbindVariables()

    return ForallExpression(sortedVars, term)
  }

  /**
   * Bind local variables by
   * - adding all bindings that shadow a function in the current context to the shadowing map
   * - adding all remaining functions to the undo stack all bindings must be distinct by name
   */
  @JvmName("bindVariablesLet")
  private fun bindVariables(varBindings: List<VarBinding<*>>) {
    require(varBindings.distinctBy { it.name }.size == varBindings.size) {
      "VarBindings in let must be distinct!"
    }
    require(varBindings.all { it.symbol !in forbiddenNames }) {
      "VarBindings can not shadow theory function symbols!"
    }

    shadowingMap.push(mutableMapOf())

    // add all bindings to undoStack first, remove all binding that shadow from undoStack later
    undoStack.push(mutableSetOf())
    undoStack.peek().addAll(varBindings)

    varBindings.forEach { binding ->
      currentContext.functions.put(binding.symbol, binding)?.let { old ->
        shadowingMap.peek().put(binding, old)
        undoStack.peek().remove(binding)
      }
    }
  }

  /**
   * Bind local variables by
   * - adding all bindings that shadow a function in the current context to the shadowing map
   * - adding all remaining functions to the undo stack
   */
  @JvmName("bindVariablesQuantifier")
  private fun bindVariables(sortedVars: List<SortedVar<*>>) {
    require(sortedVars.all { it.symbol !in forbiddenNames }) {
      "VarBindings can not shadow theory function symbols!"
    }

    // remove all shadowing bindings keep only the !last! instance on each conflict
    val vars = sortedVars.reversed().distinctBy { it.symbol }.reversed()

    shadowingMap.push(mutableMapOf())

    // add all bindings to undoStack first, remove all binding that shadow from undoStack later
    undoStack.push(mutableSetOf())
    undoStack.peek().addAll(vars)

    vars.forEach { binding ->
      currentContext.functions.put(binding.symbol, binding)?.let { old ->
        shadowingMap.peek().put(binding, old)
        undoStack.peek().remove(binding)
      }
    }
  }

  /**
   * Reverse the last binder operation by
   * - reversing all shadowing on the current context
   * - removing all local variable from the current context Pops the top level of the shadowingMap
   *   and undo stack
   */
  private fun unbindVariables() {
    // add all shadowed elements back first, then remove all remaining bindings
    shadowingMap.pop().forEach { (local, shadowed) ->
      currentContext.functions[local.symbol] = shadowed
    }
    currentContext.functions.values.removeAll(undoStack.pop())
  }

  fun setLogic(logic: Logic) {
    this.logic = logic
    forbiddenNames.addAll(
        logic.theories.flatMap { theory ->
          Theory.logicLookup[theory]!!.functions.map { (_, func) -> func.symbol }
        })
  }
}

fun Context.contains(func: String) = contains(func.symbol())

fun <T : Sort> Context.getFuncOrNull(name: String, sort: T) = getFuncOrNull(name.symbol(), sort)

fun Context.getFuncOrNull(name: String) = getFuncOrNull(name.symbol())

fun Context.getFunc(name: String) = getFunc(name.symbol())

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
          VarBinding("local${expr.sort}${idx}".symbol(), expr)
        },
        block)

fun <T : Sort, S : Sort> Context.let(
    term: Expression<T>,
    block: (Expression<T>, Context) -> Expression<S>
) = let(VarBinding("local${term.sort}".symbol(), term), block)

fun <T1 : Sort, T2 : Sort, S : Sort> Context.let(
    term1: Expression<T1>,
    term2: Expression<T2>,
    block: (Expression<T1>, Expression<T2>, Context) -> Expression<S>
) =
    let(
        VarBinding("local${term1.sort}1".symbol(), term1),
        VarBinding("local${term2.sort}2".symbol(), term2),
        block)

fun <T1 : Sort, T2 : Sort, T3 : Sort, S : Sort> Context.let(
    term1: Expression<T1>,
    term2: Expression<T2>,
    term3: Expression<T3>,
    block: (Expression<T1>, Expression<T2>, Expression<T3>, Context) -> Expression<S>
) =
    let(
        VarBinding("local${term1.sort}1".symbol(), term1),
        VarBinding("local${term2.sort}2".symbol(), term2),
        VarBinding("local${term3.sort}3".symbol(), term3),
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
        VarBinding("local${term1.sort}1".symbol(), term1),
        VarBinding("local${term2.sort}2".symbol(), term2),
        VarBinding("local${term3.sort}3".symbol(), term3),
        VarBinding("local${term4.sort}4".symbol(), term4),
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
        VarBinding("local${term1.sort}1".symbol(), term1),
        VarBinding("local${term2.sort}2".symbol(), term2),
        VarBinding("local${term3.sort}3".symbol(), term3),
        VarBinding("local${term4.sort}4".symbol(), term4),
        VarBinding("local${term5.sort}5".symbol(), term5),
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
        sortedVars.mapIndexed { idx, sort -> SortedVar("local!${sort}${idx}".symbol(), sort) },
        block)

fun <S : Sort> Context.exists(sort: S, block: (Expression<S>, Context) -> Expression<BoolSort>) =
    exists(SortedVar("local!${sort}".symbol(), sort), block)

fun <S1 : Sort, S2 : Sort> Context.exists(
    sort1: S1,
    sort2: S2,
    block: (Expression<S1>, Expression<S2>, Context) -> Expression<BoolSort>
) =
    exists(
        SortedVar("local!${sort1}1".symbol(), sort1),
        SortedVar("local!${sort2}2".symbol(), sort2),
        block)

fun <S1 : Sort, S2 : Sort, S3 : Sort> Context.exists(
    sort1: S1,
    sort2: S2,
    sort3: S3,
    block: (Expression<S1>, Expression<S2>, Expression<S3>, Context) -> Expression<BoolSort>
) =
    exists(
        SortedVar("local!${sort1}1".symbol(), sort1),
        SortedVar("local!${sort2}2".symbol(), sort2),
        SortedVar("local!${sort3}3".symbol(), sort3),
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
        SortedVar("local!${sort1}1".symbol(), sort1),
        SortedVar("local!${sort2}2".symbol(), sort2),
        SortedVar("local!${sort3}3".symbol(), sort3),
        SortedVar("local!${sort4}4".symbol(), sort4),
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
        SortedVar("local!${sort1}1".symbol(), sort1),
        SortedVar("local!${sort2}2".symbol(), sort2),
        SortedVar("local!${sort3}3".symbol(), sort3),
        SortedVar("local!${sort4}4".symbol(), sort4),
        SortedVar("local!${sort5}5".symbol(), sort5),
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

@JvmName("existsWithSorts")
fun Context.forall(
    sortedVars: List<Sort>,
    block: (List<Expression<*>>, Context) -> Expression<BoolSort>
) =
    forall(
        sortedVars.mapIndexed { idx, sort -> SortedVar("local!${sort}${idx}".symbol(), sort) },
        block)

fun <S : Sort> Context.forall(sort: S, block: (Expression<S>, Context) -> Expression<BoolSort>) =
    forall(SortedVar("local!${sort}".symbol(), sort), block)

fun <S1 : Sort, S2 : Sort> Context.forall(
    sort1: S1,
    sort2: S2,
    block: (Expression<S1>, Expression<S2>, Context) -> Expression<BoolSort>
) =
    forall(
        SortedVar("local!${sort1}1".symbol(), sort1),
        SortedVar("local!${sort2}2".symbol(), sort2),
        block)

fun <S1 : Sort, S2 : Sort, S3 : Sort> Context.forall(
    sort1: S1,
    sort2: S2,
    sort3: S3,
    block: (Expression<S1>, Expression<S2>, Expression<S3>, Context) -> Expression<BoolSort>
) =
    forall(
        SortedVar("local!${sort1}1".symbol(), sort1),
        SortedVar("local!${sort2}2".symbol(), sort2),
        SortedVar("local!${sort3}3".symbol(), sort3),
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
        SortedVar("local!${sort1}1".symbol(), sort1),
        SortedVar("local!${sort2}2".symbol(), sort2),
        SortedVar("local!${sort3}3".symbol(), sort3),
        SortedVar("local!${sort4}4".symbol(), sort4),
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
        SortedVar("local!${sort1}1".symbol(), sort1),
        SortedVar("local!${sort2}2".symbol(), sort2),
        SortedVar("local!${sort3}3".symbol(), sort3),
        SortedVar("local!${sort4}4".symbol(), sort4),
        SortedVar("local!${sort5}5".symbol(), sort5),
        block)

interface AssertionLevel<out FuncType : ContextFunction<*>, out SortType : ContextSort> {
  fun contains(function: String, args: List<Expression<*>>) = get(function, args) != null

  fun contains(function: Symbol) = functions.contains(function.toString())

  fun contains(function: String) = functions.contains(function)

  fun get(function: String, args: List<Expression<*>>) =
      functions[function]?.takeIf { func ->
        (func.parameters zipWithSameLength args.map { it.sort }).all { (param, actual) ->
          param == actual
        }
      }

  fun contains(sort: Sort) = sorts.containsKey(sort.symbol.toString())

  fun containsSort(sort: String) = sorts.containsKey(sort)

  val functions: Map<String, FuncType>
  val sorts: Map<String, SortType>
}

fun <SortType : ContextSort> AssertionLevel<*, SortType>.contains(sort: SortType) =
    sorts.containsKey(sort.name.toString())

interface ContextFunction<S> {
  val name: String
  val parameters: List<S>
  val sort: Sort
}

interface ContextSort {
  val name: String
  val arity: Int
}

class FunctionNotFoundException(name: Symbol) : NoSuchElementException("Function $name not found")

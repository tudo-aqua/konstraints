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

package tools.aqua.konstraints.smt

import tools.aqua.konstraints.parser.Attribute
import tools.aqua.konstraints.parser.OptionValue
import tools.aqua.konstraints.parser.SortedVar
import tools.aqua.konstraints.theories.BoolSort

/** Base class for each SMT command */
sealed class Command(val command: String) {
  override fun toString(): String = "($command)"
}

/** SMT (check-sat) command */
object CheckSat : Command("check-sat")

/** SMT (exit) command */
object Exit : Command("exit")

/** SMT (get-model) command */
object GetModel : Command("get-model")

/** SMT (assert) command */
data class Assert(val expression: Expression<BoolSort>) : Command("assert $expression") {
  override fun toString(): String = super.toString()
}

/**
 * SMT (declare-const [name] [sort]) command
 *
 * Declares a new a constant function of [sort] with the given [name]
 */
data class DeclareConst(val name: Symbol, val sort: Sort) : Command("declare-const $name $sort") {
  override fun toString(): String = super.toString()
}

/**
 * SMT (declare-fun [name] ([parameters]) [sort]) command
 *
 * Declares a new a function of [sort] with the given [name] and [parameters]
 */
data class DeclareFun(val name: Symbol, val parameters: List<Sort>, val sort: Sort) :
    Command("declare-fun $name (${parameters.joinToString(" ")}) $sort") {
  override fun toString(): String = super.toString()
}

/** SMT (set-info [Attribute.keyword] [Attribute.value]) command */
data class SetInfo(val attribute: Attribute) :
    Command("set-info ${attribute.keyword} ${attribute.value})")

/**
 * SMT (declare-sort [name] [arity]) command
 *
 * Declare a new sort with the given [name] and [arity]
 */
data class DeclareSort(val name: Symbol, val arity: Int) : Command("declare-sort $name $arity")

// TODO string serialization of OptionValue
/** SMT (set-option [name] [OptionValue]) command */
data class SetOption(val name: String, val value: OptionValue) : Command("set-option $name $value")

/** SMT (set-logic [logic]) command */
data class SetLogic(val logic: Logic) : Command("set-logic $logic")

/** SMT (define-fun [functionDef]) command */
data class DefineFun(val functionDef: FunctionDef<*>) : Command("define-fun $functionDef") {
  /**
   * SMT (define-fun [functionDef]) command
   *
   * Automatically construct [functionDef] from individual parameters
   */
  constructor(
      name: Symbol,
      parameters: List<SortedVar<*>>,
      sort: Sort,
      term: Expression<Sort>
  ) : this(FunctionDef(name, parameters, sort, term))
}

/**
 * Function definition object holding, [name], [parameters], [sort] and [term] of a function defined
 * via [DefineFun]
 */
data class FunctionDef<S : Sort>(
    val name: Symbol,
    val parameters: List<SortedVar<*>>,
    val sort: S,
    val term: Expression<S>
) {
  override fun toString(): String = "$name (${parameters.joinToString(" ")}) $sort $term)"
}

data class Push(val n: Int) : Command("push $n")

data class Pop(val n: Int) : Command("pop $n")

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

package tools.aqua.konstraints.dsl

import java.util.UUID
import tools.aqua.konstraints.parser.*
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.theories.BoolSort

@DslMarker annotation class SMTDSL

@SMTDSL
class SMTProgramBuilder(logic: Logic) {
  private val commands = mutableListOf<Command>()
  private val context = Context(logic)

  /*fun assert(block: Builder<BoolSort>.() -> Expression<BoolSort>) =
  assert(Builder<BoolSort>().block())*/

  fun assert(block: () -> Expression<BoolSort>) = assert(block())

  fun assert(expr: Expression<BoolSort>) {
    commands.add(Assert(expr))
  }

  fun setOptions(init: OptionsBuilder.() -> OptionsBuilder) {
    val options = OptionsBuilder().init()

    commands.addAll(
        options.stringOptions.map { (option, value) ->
          SetOption(option, StringOptionValue(value))
        })

    commands.addAll(
        options.numeralOptions.map { (option, value) ->
          SetOption(option, NumeralOptionValue(value))
        })

    commands.addAll(
        options.boolOptions.map { (option, value) -> SetOption(option, BooleanOptionValue(value)) })
  }

  internal fun registerFun(name: String, sort: Sort, parameters: List<Sort>) {
    context.registerFunction(name, parameters, sort)
    commands.add(DeclareFun(name.symbol(), parameters, sort))
  }

  internal fun <T : Sort> registerFun(
      name: String,
      sort: T,
      parameters: List<SortedVar<*>>,
      term: Expression<T>
  ) {
    val def = FunctionDef(name.symbol(), parameters, sort, term)

    context.registerFunction(def)
    commands.add(DefineFun(def))
  }

  fun <T : Sort> const(sort: T) = const("|const!${UUID.randomUUID()}|", sort)

  fun <T : Sort> const(name: String, sort: T): Expression<T> {
    registerFun(name, sort, emptyList())

    return UserDeclaredExpression(name.symbol(), sort)
  }

  fun finalize() = DefaultSMTProgram(commands.also { it.add(CheckSat) }.toList(), context)
}

fun smt(logic: Logic, init: SMTProgramBuilder.() -> Unit): SMTProgram {
  val program = SMTProgramBuilder(logic)
  program.init()

  return program.finalize()
}

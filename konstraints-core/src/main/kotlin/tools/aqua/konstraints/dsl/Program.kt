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

  /** Adds a new assertion: (assert [block]) */
  fun assert(block: () -> Expression<BoolSort>) = assert(block())

  /** Adds a new assertion: (assert [expr]) */
  fun assert(expr: Expression<BoolSort>) {
    commands.add(Assert(expr))
  }

  /**
   * Sets all options that may be supported by the solver.
   *
   * Inside [init] as many options as necessary can be set.
   */
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

  /** Registers a new constant smt function with the given [sort] and auto generated name. */
  fun <T : Sort> const(sort: T) = const("|const!${UUID.randomUUID()}|", sort)

  /** Registers a new constant smt function with the given [name] and [sort] */
  fun <T : Sort> const(name: String, sort: T): Expression<T> {
    registerFun(name, sort, emptyList())

    return UserDeclaredExpression(name.symbol(), sort)
  }

  /** Converts this [SMTProgramBuilder] to a finished [DefaultSMTProgram] */
  fun finalize() = DefaultSMTProgram(commands.also { it.add(CheckSat) }.toList(), context)
}

/** Builds an [SMTProgram] based on the given [logic] */
fun smt(logic: Logic, init: SMTProgramBuilder.() -> Unit): SMTProgram {
  val program = SMTProgramBuilder(logic)
  program.init()

  return program.finalize()
}

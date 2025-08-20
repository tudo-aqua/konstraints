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
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.smt.BoolSort

@DslMarker annotation class SMTDSL

/** Builder for [SMTProgram] class. */
@SMTDSL
class SMTProgramBuilder(logic: Logic) {
  private val program = MutableSMTProgram(emptyList()).also { program -> program.setLogic(logic) }

  /** Adds a new assertion: (assert [block]). */
  fun assert(block: () -> Expression<BoolSort>) = assert(block())

  /** Adds a new assertion: (assert [expr]). */
  fun assert(expr: Expression<BoolSort>) {
    program.assert(expr)
  }

  /**
   * Sets all options that may be supported by the solver.
   *
   * Inside [init] as many options as necessary can be set.
   */
  fun setOptions(init: OptionsBuilder.() -> OptionsBuilder) {
    val options = OptionsBuilder().init()

    options.stringOptions.map { (option, value) ->
      program.setOption(SetOption(option, StringOptionValue(value)))
    }

    options.numeralOptions.map { (option, value) ->
      program.setOption(SetOption(option, NumeralOptionValue(value)))
    }

    options.boolOptions.map { (option, value) ->
      program.setOption(SetOption(option, BooleanOptionValue(value)))
    }
  }

  internal fun <T : UserDeclaredSMTFunction<S>, S : Sort> declareFun(func: T): T {
    program.declareFun(func)

    return func
  }

  internal fun <T : DefinedSMTFunction<S>, S : Sort> defineFun(func: T): T {
    program.defineFun(func)

    return func
  }

  /** Registers a new constant smt function with the given [sort] and auto generated name. */
  fun <T : Sort> const(sort: T) = const("|const!${UUID.randomUUID()}|", sort)

  /** Registers a new constant smt function with the given [name] and [sort]. */
  fun <T : Sort> const(name: String, sort: T) =
      program.declareConst(name.toSymbolWithQuotes(), sort)()

  /** Converts this [SMTProgramBuilder] to a finished [DefaultSMTProgram]. */
  fun finalize() = program.apply { add(CheckSat) }
}

/** Builds an [SMTProgram] based on the given [logic] */
fun smt(logic: Logic, init: SMTProgramBuilder.() -> Unit): SMTProgram {
  val program = SMTProgramBuilder(logic)
  program.init()

  return program.finalize()
}

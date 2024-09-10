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
import tools.aqua.konstraints.parser.Context
import tools.aqua.konstraints.parser.FunctionDefinition
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.theories.BoolSort
import kotlin.reflect.KProperty

@DslMarker annotation class SMTDSL

@SMTDSL
class SMTProgramBuilder(logic: Logic) {
  private val commands = mutableListOf<Command>()
  private val context = Context(logic)

  fun assert(block: Builder<BoolSort>.() -> Expression<BoolSort>) =
      assert(Builder<BoolSort>().block())

  fun assert(expr: Expression<BoolSort>) {
    commands.add(Assert(expr))
  }

  fun <T : Sort> const(sort: T) = Const(sort, "|const!$sort!${UUID.randomUUID()}|")
  fun <T : Sort> const(sort: Sort, name: String) = Const(sort, name)
  fun <T : Sort> declare(sort: T) = Declare(sort)

  val test by declare(BoolSort)

  fun finalize() = DefaultSMTProgram(commands.also { it.add(CheckSat) }.toList(), context)
}

fun smt(logic: Logic, init: SMTProgramBuilder.() -> Unit): SMTProgram {
  val program = SMTProgramBuilder(logic)
  program.init()

  return program.finalize()
}

class Const<T : Sort>(val sort: T, val name: String){
  operator fun getValue(thisRef: Any?, property: KProperty<*>) = UserDeclaredExpression(name.symbol(), sort)

}

class Declare<T: Sort>(val sort: T, val parameters: List<Sort> = emptyList(), val name: String = "") {
  operator fun getValue(thisRef: Any?, property: KProperty<*>) = SMTFunction("|${thisRef.toString()}|".symbol(), sort, parameters, null)

}

class Define<T: Sort>(val sort: T, val block: Builder<T>.(List<Expression<Sort>>) -> Expression<T>, val parameters: List<Sort> = emptyList(), val name: String = "") {
  operator fun getValue(thisRef: Any?, property: KProperty<*>) =
    SMTFunction("|${thisRef.toString()}|".symbol(), sort, parameters, Builder<T>().block(parameters.mapIndexed { id, sort -> UserDeclaredExpression("|${thisRef.toString()}!local!$sort!$id|".symbol(), sort) }))

}

data class SMTFunction<T : Sort>(val name: Symbol, val sort: T, val parameters: List<Sort>, val definition: Expression<T>?) {
    operator fun invoke(args : List<Expression<*>>): Expression<T> {
      require(args.size == parameters.size)

      return if (definition == null) {
        UserDeclaredExpression(name, sort, args)
      } else {
        UserDefinedExpression(name, sort, args, definition)
      }
    }
}
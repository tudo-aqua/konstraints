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

package tools.aqua.konstraints
class SMTProgram(commands: List<Command>) {
  // checkWellSorted, etc...
}

sealed class Command(val command: String) {
  override fun toString(): String = "($command)"
}

object CheckSat : Command("check-sat")

data class Assert(val expression: Expression<BoolSort>) : Command("assert $expression") {
  override fun toString(): String = super.toString()
}

data class DeclareConst(val name: Symbol, val sort: Sort) :
    Command("declare-const $name $sort") {
  override fun toString(): String = super.toString()
}

data class DeclareFun(val name: Symbol, val parameters: List<Sort>, val sort: Sort) :
    Command("declare-fun $name (${parameters.joinToString(" ")}) $sort") {
  override fun toString(): String = super.toString()
}

// tools.aqua.konstraints.DeclareConst(expr, expr.sort)

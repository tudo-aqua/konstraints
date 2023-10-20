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

import tools.aqua.konstraints.BasicExpression
import tools.aqua.konstraints.Expression
import tools.aqua.konstraints.Sort

// TODO ambiguous lookup with params and return type

abstract class FunctionDecl<T : Sort>(
    val name: String,
    val params: List<Sort>,
    val sort: T,
    val isAmbiguous: Boolean = false
) {
  abstract fun getExpression(args: List<Expression<*>>): Expression<T>
}

class ConstDecl<T : Sort>(name: String, sort: T) : FunctionDecl<T>(name, listOf(), sort) {
  override fun getExpression(args: List<Expression<*>>): Expression<T> {
    return BasicExpression(name, sort)
  }
}

abstract class SortDecl<T : Sort>(val name: String) {
  abstract fun getSort(sort: ProtoSort): T
}

class Context {
  val funs: MutableMap<String, FunctionDecl<*>> = mutableMapOf()
  val sorts: MutableMap<String, SortDecl<*>> = mutableMapOf()
}

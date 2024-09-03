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

import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.smt.Ite
import tools.aqua.konstraints.smt.Sort
import tools.aqua.konstraints.theories.BoolSort

@SMTDSL
class ITE1(val statement: Expression<BoolSort>) {
  infix fun <T : Sort> then(expr: Builder<T>.() -> Expression<T>): ITE2<T> =
      ITE2(statement, Builder<T>().expr())
}

class ITE2<T : Sort>(val statement: Expression<BoolSort>, val then: Expression<T>) {
  infix fun otherwise(expr: Builder<T>.() -> Expression<T>): Ite<T> =
      Ite(statement, then, Builder<T>().expr())
}

fun ite(init: Builder<BoolSort>.() -> Expression<BoolSort>): ITE1 = ITE1(Builder<BoolSort>().init())

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

package tools.aqua.konstraints.visitors

import tools.aqua.konstraints.*

interface CoreVisitor<T> {
  fun visit(expression: Expression<*>): T =
      when (expression) {
        is True -> visit(expression)
        is False -> visit(expression)
        is Not -> visit(expression)
        is Implies -> visit(expression)
        is And -> visit(expression)
        is Or -> visit(expression)
        is XOr -> visit(expression)
        is Equals -> visit(expression)
        is Distinct -> visit(expression)
        is Ite -> visit(expression)
        else -> throw IllegalArgumentException("Core visitor can not visit expression $expression!")
      }

  fun visit(trueExpr: True): T

  fun visit(falseExpr: False): T

  fun visit(notExpr: Not): T

  fun visit(impliesExpr: Implies): T

  fun visit(andExpr: And): T

  fun visit(orExpr: Or): T

  fun visit(xorExpr: XOr): T

  fun visit(equalsExpr: Equals): T

  fun visit(distinctExpr: Distinct): T

  fun visit(iteExpr: Ite): T
}

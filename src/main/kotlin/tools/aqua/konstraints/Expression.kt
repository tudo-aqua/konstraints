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

abstract class Expression<T : Sort> {
  abstract val symbol: String
  abstract val sort: T

  override fun toString() = symbol
}

class BasicExpression<T : Sort>(override val symbol: String, override val sort: T) :
    Expression<T>() {
  override fun toString() = "$symbol"
}

class UnaryExpression<T : Sort>(symbol: String, override val sort: T, val other: Expression<T>) :
    Expression<T>() {
  override val symbol = symbol

  override fun toString() = "($symbol ${other})"
}

class BinaryExpression<T : Sort>(
    symbol: String,
    override val sort: T,
    val left: Expression<T>,
    val right: Expression<T>
) : Expression<T>() {
  override val symbol = symbol

  override fun toString() = "($symbol ${left} ${right})"
}

class NAryExpression<T : Sort>(
    symbol: String,
    override val sort: T,
    val tokens: List<Expression<T>>
) : Expression<T>() {
  override val symbol = symbol

  override fun toString() = "($symbol ${tokens.joinToString(" ")})"
}
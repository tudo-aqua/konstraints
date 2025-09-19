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

package tools.aqua.konstraints.smt

// S-Expression

/** Base class for explicit SExpressions. */
sealed interface SExpression

/** SubSExpression. */
data class SubSExpression(val subExpressions: List<SExpression>) : SExpression {
  override fun toString() =
      subExpressions.joinToString(separator = " ", prefix = "(", postfix = ")")
}

/** SExpressionConstant. */
data class SExpressionConstant(val constant: SpecConstant) : SExpression {
  override fun toString() = constant.toString()
}

/** SExpressionSymbol. */
data class SExpressionSymbol(val symbol: Symbol) : SExpression {
  override fun toString() = TODO()
}

/** SExpressionReserved. */
data class SExpressionReserved(val reserved: String) : SExpression {
  override fun toString() = reserved
}

/** SExpressionKeyword. */
data class SExpressionKeyword(val keyword: String) : SExpression {
  override fun toString() = keyword
}

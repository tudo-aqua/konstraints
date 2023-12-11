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

interface FSBVVisitor<T> {
  fun visit(expression: Expression<*>): T =
      when (expression) {
        is BVLiteral -> visit(expression)
        is BVConcat -> visit(expression)
        is BVExtract -> visit(expression)
        is BVNot -> visit(expression)
        is BVNeg -> visit(expression)
        is BVAnd -> visit(expression)
        is BVOr -> visit(expression)
        is BVAdd -> visit(expression)
        is BVMul -> visit(expression)
        is BVUDiv -> visit(expression)
        is BVURem -> visit(expression)
        is BVShl -> visit(expression)
        is BVLShr -> visit(expression)
        is BVUlt -> visit(expression)
        else -> visitUnknownExpression(expression)
      }

  fun visitUnknownExpression(expression: Expression<*>): T {
    throw IllegalArgumentException(
        "FixedSizeBitvector visitor can not visit expression $expression!")
  }

  fun visit(bvLiteral: BVLiteral): T

  fun visit(bvConcat: BVConcat): T

  fun visit(bvExtract: BVExtract): T

  fun visit(bvNot: BVNot): T

  fun visit(bvNeg: BVNeg): T

  fun visit(bvAnd: BVAnd): T

  fun visit(bvOr: BVOr): T

  fun visit(bvAdd: BVAdd): T

  fun visit(bvMul: BVMul): T

  fun visit(bvuDiv: BVUDiv): T

  fun visit(bvuRem: BVURem): T

  fun visit(bvShl: BVShl): T

  fun visit(bvlShr: BVLShr): T

  fun visit(bvUlt: BVUlt): T
}

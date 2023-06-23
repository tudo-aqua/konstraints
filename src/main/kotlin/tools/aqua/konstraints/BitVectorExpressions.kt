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

// concat bvs
class BVConcat(val lhs: Expression<BVSort>, val rhs: Expression<BVSort>) : Expression<BVSort>() {
  override val sort: BVSort = BVSort(lhs.sort.bits + rhs.sort.bits)
  override val symbol: String = TODO()
}

// extract bits from bv
class BVExtract

// bitwise not
class BVNot(val inner: Expression<BVSort>) : Expression<BVSort>() {
  override val sort: BVSort = TODO()
  override val symbol: String = TODO()
}

// negate bv
class BVNeg(val inner: Expression<BVSort>) : Expression<BVSort>() {
  override val sort: BVSort = TODO()
  override val symbol: String = TODO()
}

// bitwise and
class BVAnd(conjuncts: List<Expression<BVSort>>) : Expression<BVSort>() {
  constructor(vararg summands: Expression<BVSort>) : this(summands.toList())

  override val sort: BVSort = TODO()
  override val symbol: String = TODO()
}

// bitwise or
class BVOr(disjuncts: List<Expression<BVSort>>) : Expression<BVSort>() {
  constructor(vararg summands: Expression<BVSort>) : this(summands.toList())

  override val sort: BVSort = TODO()
  override val symbol: String = TODO()
}

// addition
class BVAdd(summands: List<Expression<BVSort>>) : Expression<BVSort>() {
  constructor(vararg summands: Expression<BVSort>) : this(summands.toList())

  override val sort: BVSort = TODO()
  override val symbol: String = TODO()
}

// multiplication
class BVMul(factors: List<Expression<BVSort>>) : Expression<BVSort>() {
  constructor(vararg factors: Expression<BVSort>) : this(factors.toList())

  override val sort: BVSort = TODO()
  override val symbol: String = TODO()
}

// unsigned division
class BVUDiv(numerator: Expression<BVSort>, denominator: Expression<BVSort>) :
    Expression<BVSort>() {
  override val sort: BVSort = TODO()
  override val symbol: String = TODO()
}

// unsigned remainder
class BVURem(numerator: Expression<BVSort>, denominator: Expression<BVSort>) :
    Expression<BVSort>() {
  override val sort: BVSort = TODO()
  override val symbol: String = TODO()
}

// shift left
class BVShl(value: Expression<BVSort>, shift: Expression<BVSort>) : Expression<BVSort>() {
  override val sort: BVSort = TODO()
  override val symbol: String = TODO()
}

// logical shift right
class BVLShr(value: Expression<BVSort>, shift: Expression<BVSort>) : Expression<BVSort>() {
  override val sort: BVSort = TODO()
  override val symbol: String = TODO()
}

// unsigned less than
class BVUlt(val lhs: Expression<BVSort>, val rhs: Expression<BVSort>) : Expression<BoolSort>() {
  override val sort: BoolSort = TODO()
  override val symbol: String = TODO()
}

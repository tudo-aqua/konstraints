/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2026 The Konstraints Authors
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

import tools.aqua.konstraints.smt.Complex
import tools.aqua.konstraints.smt.ComplexAdd
import tools.aqua.konstraints.smt.ComplexDiv
import tools.aqua.konstraints.smt.ComplexInv
import tools.aqua.konstraints.smt.ComplexMul
import tools.aqua.konstraints.smt.ComplexSort
import tools.aqua.konstraints.smt.ComplexSub
import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.smt.toExpression

infix fun Expression<ComplexSort>.cpxadd(lhs: Expression<ComplexSort>) = ComplexAdd(this, lhs)

infix fun Expression<ComplexSort>.cpxadd(lhs: Complex) = ComplexAdd(this, lhs.toExpression())

infix fun Complex.cpxadd(lhs: Expression<ComplexSort>) = ComplexAdd(this.toExpression(), lhs)

infix fun Complex.cpxadd(lhs: Complex) = ComplexAdd(this.toExpression(), lhs.toExpression())

infix fun Expression<ComplexSort>.cpxsub(lhs: Expression<ComplexSort>) = ComplexSub(this, lhs)

infix fun Expression<ComplexSort>.cpxsub(lhs: Complex) = ComplexSub(this, lhs.toExpression())

infix fun Complex.cpxsub(lhs: Expression<ComplexSort>) = ComplexSub(this.toExpression(), lhs)

infix fun Complex.cpxsub(lhs: Complex) = ComplexSub(this.toExpression(), lhs.toExpression())

infix fun Expression<ComplexSort>.cpxmul(lhs: Expression<ComplexSort>) = ComplexMul(this, lhs)

infix fun Expression<ComplexSort>.cpxmul(lhs: Complex) = ComplexMul(this, lhs.toExpression())

infix fun Complex.cpxmul(lhs: Expression<ComplexSort>) = ComplexMul(this.toExpression(), lhs)

infix fun Complex.cpxmul(lhs: Complex) = ComplexMul(this.toExpression(), lhs.toExpression())

infix fun Expression<ComplexSort>.cpxdiv(lhs: Expression<ComplexSort>) = ComplexDiv(this, lhs)

infix fun Expression<ComplexSort>.cpxdiv(lhs: Complex) = ComplexDiv(this, lhs.toExpression())

infix fun Complex.cpxdiv(lhs: Expression<ComplexSort>) = ComplexDiv(this.toExpression(), lhs)

infix fun Complex.cpxdiv(lhs: Complex) = ComplexDiv(this.toExpression(), lhs.toExpression())

fun Expression<ComplexSort>.cpxinv() = ComplexInv(this)

fun Complex.cpxinv() = ComplexInv(this.toExpression())

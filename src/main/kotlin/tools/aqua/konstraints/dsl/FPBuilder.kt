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
import tools.aqua.konstraints.smt.Sort
import tools.aqua.konstraints.theories.*

/*
 * floating-point infix operations
 */

infix fun Expression<FPSort>.fpadd(rhs: Expression<FPSort>) = FPAdd(RNE, this, rhs)

infix fun Expression<FPSort>.fpadd_rne(rhs: Expression<FPSort>) = this fpadd rhs

infix fun Expression<FPSort>.fpadd_rna(rhs: Expression<FPSort>) = FPAdd(RNA, this, rhs)

infix fun Expression<FPSort>.fpadd_rtp(rhs: Expression<FPSort>) = FPAdd(RTP, this, rhs)

infix fun Expression<FPSort>.fpadd_rtn(rhs: Expression<FPSort>) = FPAdd(RTN, this, rhs)

infix fun Expression<FPSort>.fpadd_rtz(rhs: Expression<FPSort>) = FPAdd(RTZ, this, rhs)

infix fun Expression<FPSort>.fpsub(rhs: Expression<FPSort>) = FPSub(RNE, this, rhs)

infix fun Expression<FPSort>.fpsub_rne(rhs: Expression<FPSort>) = this fpsub rhs

infix fun Expression<FPSort>.fpsub_rna(rhs: Expression<FPSort>) = FPSub(RNA, this, rhs)

infix fun Expression<FPSort>.fpsub_rtp(rhs: Expression<FPSort>) = FPSub(RTP, this, rhs)

infix fun Expression<FPSort>.fpsub_rtn(rhs: Expression<FPSort>) = FPSub(RTN, this, rhs)

infix fun Expression<FPSort>.fpsub_rtz(rhs: Expression<FPSort>) = FPSub(RTZ, this, rhs)

infix fun Expression<FPSort>.fpmul(rhs: Expression<FPSort>) = FPMul(RNE, this, rhs)

infix fun Expression<FPSort>.fpmul_rne(rhs: Expression<FPSort>) = this fpmul rhs

infix fun Expression<FPSort>.fpmul_rna(rhs: Expression<FPSort>) = FPMul(RNA, this, rhs)

infix fun Expression<FPSort>.fpmul_rtp(rhs: Expression<FPSort>) = FPMul(RTP, this, rhs)

infix fun Expression<FPSort>.fpmul_rtn(rhs: Expression<FPSort>) = FPMul(RTN, this, rhs)

infix fun Expression<FPSort>.fpmul_rtz(rhs: Expression<FPSort>) = FPMul(RTZ, this, rhs)

infix fun Expression<FPSort>.fpdiv(rhs: Expression<FPSort>) = FPDiv(RNE, this, rhs)

infix fun Expression<FPSort>.fpdiv_rne(rhs: Expression<FPSort>) = this fpdiv rhs

infix fun Expression<FPSort>.fpdiv_rna(rhs: Expression<FPSort>) = FPDiv(RNA, this, rhs)

infix fun Expression<FPSort>.fpdiv_rtp(rhs: Expression<FPSort>) = FPDiv(RTP, this, rhs)

infix fun Expression<FPSort>.fpdiv_rtn(rhs: Expression<FPSort>) = FPDiv(RTN, this, rhs)

infix fun Expression<FPSort>.fpdiv_rtz(rhs: Expression<FPSort>) = FPDiv(RTZ, this, rhs)

infix fun Expression<FPSort>.fprem(rhs: Expression<FPSort>) = FPRem(this, rhs)

/*
 * unary floating-point operations
 */

private fun Builder<FPSort>.makeUnaryOperation(
    roundingMode: Expression<RoundingMode>,
    block: Builder<FPSort>.() -> Expression<FPSort>,
    operation: (Expression<RoundingMode>, Expression<FPSort>) -> Expression<FPSort>
): Expression<FPSort> {
  this.children.add(operation(roundingMode, Builder<FPSort>().block()))

  return this.children.last()
}

fun Builder<FPSort>.fpsqrt(
    roundingMode: Expression<RoundingMode> = RNE,
    block: Builder<FPSort>.() -> Expression<FPSort>
) = this.makeUnaryOperation(roundingMode, block, ::FPSqrt)

fun Builder<FPSort>.fproundToIntegral(
    roundingMode: Expression<RoundingMode> = RNE,
    block: Builder<FPSort>.() -> Expression<FPSort>
) = this.makeUnaryOperation(roundingMode, block, ::FPRoundToIntegral)

/*
 * floating-point comparison operators
 */

fun fpmin(rhs: Expression<FPSort>, lhs: Expression<FPSort>) = FPMin(rhs, lhs)

fun fpmax(rhs: Expression<FPSort>, lhs: Expression<FPSort>) = FPMax(rhs, lhs)

infix fun Expression<FPSort>.fpleq(rhs: Expression<FPSort>) = FPLeq(this, rhs)

infix fun FPLeq.fpleq(rhs: Expression<FPSort>) = FPLeq(*this.children.toTypedArray(), rhs)

infix fun Expression<FPSort>.fplt(rhs: Expression<FPSort>) = FPLt(this, rhs)

infix fun FPLeq.fplt(rhs: Expression<FPSort>) = FPLt(*this.children.toTypedArray(), rhs)

infix fun Expression<FPSort>.fpgeq(rhs: Expression<FPSort>) = FPGeq(this, rhs)

infix fun FPLeq.fpgeq(rhs: Expression<FPSort>) = FPLeq(*this.children.toTypedArray(), rhs)

infix fun Expression<FPSort>.fpgt(rhs: Expression<FPSort>) = FPGt(this, rhs)

infix fun FPLeq.fpgt(rhs: Expression<FPSort>) = FPGt(*this.children.toTypedArray(), rhs)

infix fun Expression<FPSort>.fpeq(rhs: Expression<FPSort>) = FPEq(this, rhs)

infix fun FPLeq.fpeq(rhs: Expression<FPSort>) = FPEq(*this.children.toTypedArray(), rhs)

/*
 * floating-point conversion operations
 */

private fun <T : Sort> Builder<FPSort>.makeConversionOperator(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingMode>,
    block: Builder<T>.() -> Expression<T>,
    op: (Expression<RoundingMode>, Expression<T>, Int, Int) -> Expression<FPSort>
): Expression<FPSort> {
  this.children.add(op(roundingMode, Builder<T>().block(), eb, sb))

  return this.children.last()
}

@JvmName("FPToFP")
fun Builder<FPSort>.toFP(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingMode> = RNE,
    block: Builder<FPSort>.() -> Expression<FPSort>
) = this.makeConversionOperator(eb, sb, roundingMode, block, ::FPToFP)

@JvmName("FPToReal")
fun Builder<FPSort>.toFP(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingMode> = RNE,
    block: Builder<RealSort>.() -> Expression<RealSort>
) = this.makeConversionOperator(eb, sb, roundingMode, block, ::RealToFP)

@JvmName("FPToSBV")
fun Builder<FPSort>.toFP(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingMode> = RNE,
    block: Builder<BVSort>.() -> Expression<BVSort>
) = this.makeConversionOperator(eb, sb, roundingMode, block, ::SBitVecToFP)

@JvmName("FPToUBV")
fun Builder<FPSort>.toFPUnsigned(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingMode> = RNE,
    block: Builder<BVSort>.() -> Expression<BVSort>
) = this.makeConversionOperator(eb, sb, roundingMode, block, ::UBitVecToFP)

fun Builder<FPSort>.toFP(
    eb: Int,
    sb: Int,
    block: Builder<BVSort>.() -> Expression<BVSort>,
    op: (Expression<RoundingMode>, Expression<BVSort>, Int, Int) -> Expression<FPSort>
): Expression<FPSort> {
  this.children.add(BitVecToFP(Builder<BVSort>().block(), eb, sb))

  return this.children.last()
}

fun Builder<BVSort>.toUBV(
    m: Int,
    roundingMode: Expression<RoundingMode> = RNE,
    block: Builder<FPSort>.() -> Expression<FPSort>
): Expression<BVSort> {
  this.children.add(FPToUBitVec(roundingMode, Builder<FPSort>().block(), m))

  return this.children.last()
}

fun Builder<BVSort>.toSBV(
    m: Int,
    roundingMode: Expression<RoundingMode> = RNE,
    block: Builder<FPSort>.() -> Expression<FPSort>
): Expression<BVSort> {
  this.children.add(FPToSBitVec(roundingMode, Builder<FPSort>().block(), m))

  return this.children.last()
}

fun Builder<RealSort>.toReal(
    block: Builder<FPSort>.() -> Expression<FPSort>
): Expression<RealSort> {
  this.children.add(FPToReal(Builder<FPSort>().block()))

  return this.children.last()
}

/*
 * fpfma
 */

fun fpfma(
    roundingMode: Expression<RoundingMode> = RNE,
    multiplier: Builder<FPSort>.() -> Expression<FPSort>
) = FPFMA1(roundingMode, Builder<FPSort>().multiplier())

class FPFMA1(val roundingMode: Expression<RoundingMode>, val multiplier: Expression<FPSort>) {
  infix fun mul(multiplicant: Builder<FPSort>.() -> Expression<FPSort>) =
      FPFMA2(roundingMode, multiplier, Builder<FPSort>().multiplicant())
}

class FPFMA2(
    val roundingMode: Expression<RoundingMode>,
    val multiplier: Expression<FPSort>,
    val multiplicant: Expression<FPSort>
) {
  infix fun add(summand: Builder<FPSort>.() -> Expression<FPSort>) =
      FPFma(roundingMode, multiplier, multiplicant, Builder<FPSort>().summand())
}

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
import tools.aqua.konstraints.theories.*

/*
 * floating-point infix operations
 */

infix fun Expression<FPSort>.fpadd(rhs: Expression<FPSort>) = this fpadd_rne rhs

infix fun Expression<FPSort>.fpadd_rne(rhs: Expression<FPSort>) = FPAdd(RNE, this, rhs)

infix fun Expression<FPSort>.fpadd_rna(rhs: Expression<FPSort>) = FPAdd(RNA, this, rhs)

infix fun Expression<FPSort>.fpadd_rtp(rhs: Expression<FPSort>) = FPAdd(RTP, this, rhs)

infix fun Expression<FPSort>.fpadd_rtn(rhs: Expression<FPSort>) = FPAdd(RTN, this, rhs)

infix fun Expression<FPSort>.fpadd_rtz(rhs: Expression<FPSort>) = FPAdd(RTZ, this, rhs)

infix fun Expression<FPSort>.fpadd(rhs: () -> Expression<FPSort>) = this fpadd_rne rhs()

infix fun Expression<FPSort>.fpadd_rne(rhs: () -> Expression<FPSort>) = FPAdd(RNE, this, rhs())

infix fun Expression<FPSort>.fpadd_rna(rhs: () -> Expression<FPSort>) = FPAdd(RNA, this, rhs())

infix fun Expression<FPSort>.fpadd_rtp(rhs: () -> Expression<FPSort>) = FPAdd(RTP, this, rhs())

infix fun Expression<FPSort>.fpadd_rtn(rhs: () -> Expression<FPSort>) = FPAdd(RTN, this, rhs())

infix fun Expression<FPSort>.fpadd_rtz(rhs: () -> Expression<FPSort>) = FPAdd(RTZ, this, rhs())

infix fun (() -> Expression<FPSort>).fpadd(rhs: Expression<FPSort>) = this() fpadd_rne rhs

infix fun (() -> Expression<FPSort>).fpadd_rne(rhs: Expression<FPSort>) = FPAdd(RNE, this(), rhs)

infix fun (() -> Expression<FPSort>).fpadd_rna(rhs: Expression<FPSort>) = FPAdd(RNA, this(), rhs)

infix fun (() -> Expression<FPSort>).fpadd_rtp(rhs: Expression<FPSort>) = FPAdd(RTP, this(), rhs)

infix fun (() -> Expression<FPSort>).fpadd_rtn(rhs: Expression<FPSort>) = FPAdd(RTN, this(), rhs)

infix fun (() -> Expression<FPSort>).fpadd_rtz(rhs: Expression<FPSort>) = FPAdd(RTZ, this(), rhs)

infix fun (() -> Expression<FPSort>).fpadd(rhs: () -> Expression<FPSort>) = this() fpadd_rne rhs()

infix fun (() -> Expression<FPSort>).fpadd_rne(rhs: () -> Expression<FPSort>) =
    FPAdd(RNE, this(), rhs())

infix fun (() -> Expression<FPSort>).fpadd_rna(rhs: () -> Expression<FPSort>) =
    FPAdd(RNA, this(), rhs())

infix fun (() -> Expression<FPSort>).fpadd_rtp(rhs: () -> Expression<FPSort>) =
    FPAdd(RTP, this(), rhs())

infix fun (() -> Expression<FPSort>).fpadd_rtn(rhs: () -> Expression<FPSort>) =
    FPAdd(RTN, this(), rhs())

infix fun (() -> Expression<FPSort>).fpadd_rtz(rhs: () -> Expression<FPSort>) =
    FPAdd(RTZ, this(), rhs())

infix fun Expression<FPSort>.fpsub(rhs: Expression<FPSort>) = this fpsub_rne rhs

infix fun Expression<FPSort>.fpsub_rne(rhs: Expression<FPSort>) = FPSub(RNE, this, rhs)

infix fun Expression<FPSort>.fpsub_rna(rhs: Expression<FPSort>) = FPSub(RNA, this, rhs)

infix fun Expression<FPSort>.fpsub_rtp(rhs: Expression<FPSort>) = FPSub(RTP, this, rhs)

infix fun Expression<FPSort>.fpsub_rtn(rhs: Expression<FPSort>) = FPSub(RTN, this, rhs)

infix fun Expression<FPSort>.fpsub_rtz(rhs: Expression<FPSort>) = FPSub(RTZ, this, rhs)

infix fun Expression<FPSort>.fpsub(rhs: () -> Expression<FPSort>) = this fpsub_rne rhs()

infix fun Expression<FPSort>.fpsub_rne(rhs: () -> Expression<FPSort>) = FPSub(RNE, this, rhs())

infix fun Expression<FPSort>.fpsub_rna(rhs: () -> Expression<FPSort>) = FPSub(RNA, this, rhs())

infix fun Expression<FPSort>.fpsub_rtp(rhs: () -> Expression<FPSort>) = FPSub(RTP, this, rhs())

infix fun Expression<FPSort>.fpsub_rtn(rhs: () -> Expression<FPSort>) = FPSub(RTN, this, rhs())

infix fun Expression<FPSort>.fpsub_rtz(rhs: () -> Expression<FPSort>) = FPSub(RTZ, this, rhs())

infix fun (() -> Expression<FPSort>).fpsub(rhs: Expression<FPSort>) = this() fpsub_rne rhs

infix fun (() -> Expression<FPSort>).fpsub_rne(rhs: Expression<FPSort>) = FPSub(RNE, this(), rhs)

infix fun (() -> Expression<FPSort>).fpsub_rna(rhs: Expression<FPSort>) = FPSub(RNA, this(), rhs)

infix fun (() -> Expression<FPSort>).fpsub_rtp(rhs: Expression<FPSort>) = FPSub(RTP, this(), rhs)

infix fun (() -> Expression<FPSort>).fpsub_rtn(rhs: Expression<FPSort>) = FPSub(RTN, this(), rhs)

infix fun (() -> Expression<FPSort>).fpsub_rtz(rhs: Expression<FPSort>) = FPSub(RTZ, this(), rhs)

infix fun (() -> Expression<FPSort>).fpsub(rhs: () -> Expression<FPSort>) = this() fpsub_rne rhs()

infix fun (() -> Expression<FPSort>).fpsub_rne(rhs: () -> Expression<FPSort>) =
    FPSub(RNE, this(), rhs())

infix fun (() -> Expression<FPSort>).fpsub_rna(rhs: () -> Expression<FPSort>) =
    FPSub(RNA, this(), rhs())

infix fun (() -> Expression<FPSort>).fpsub_rtp(rhs: () -> Expression<FPSort>) =
    FPSub(RTP, this(), rhs())

infix fun (() -> Expression<FPSort>).fpsub_rtn(rhs: () -> Expression<FPSort>) =
    FPSub(RTN, this(), rhs())

infix fun (() -> Expression<FPSort>).fpsub_rtz(rhs: () -> Expression<FPSort>) =
    FPSub(RTZ, this(), rhs())

infix fun Expression<FPSort>.fpmul(rhs: Expression<FPSort>) = this fpmul_rne rhs

infix fun Expression<FPSort>.fpmul_rne(rhs: Expression<FPSort>) = FPMul(RNE, this, rhs)

infix fun Expression<FPSort>.fpmul_rna(rhs: Expression<FPSort>) = FPMul(RNA, this, rhs)

infix fun Expression<FPSort>.fpmul_rtp(rhs: Expression<FPSort>) = FPMul(RTP, this, rhs)

infix fun Expression<FPSort>.fpmul_rtn(rhs: Expression<FPSort>) = FPMul(RTN, this, rhs)

infix fun Expression<FPSort>.fpmul_rtz(rhs: Expression<FPSort>) = FPMul(RTZ, this, rhs)

infix fun Expression<FPSort>.fpmul(rhs: () -> Expression<FPSort>) = this fpmul_rne rhs()

infix fun Expression<FPSort>.fpmul_rne(rhs: () -> Expression<FPSort>) = FPMul(RNE, this, rhs())

infix fun Expression<FPSort>.fpmul_rna(rhs: () -> Expression<FPSort>) = FPMul(RNA, this, rhs())

infix fun Expression<FPSort>.fpmul_rtp(rhs: () -> Expression<FPSort>) = FPMul(RTP, this, rhs())

infix fun Expression<FPSort>.fpmul_rtn(rhs: () -> Expression<FPSort>) = FPMul(RTN, this, rhs())

infix fun Expression<FPSort>.fpmul_rtz(rhs: () -> Expression<FPSort>) = FPMul(RTZ, this, rhs())

infix fun (() -> Expression<FPSort>).fpmul(rhs: Expression<FPSort>) = this() fpmul_rne rhs

infix fun (() -> Expression<FPSort>).fpmul_rne(rhs: Expression<FPSort>) = FPMul(RNE, this(), rhs)

infix fun (() -> Expression<FPSort>).fpmul_rna(rhs: Expression<FPSort>) = FPMul(RNA, this(), rhs)

infix fun (() -> Expression<FPSort>).fpmul_rtp(rhs: Expression<FPSort>) = FPMul(RTP, this(), rhs)

infix fun (() -> Expression<FPSort>).fpmul_rtn(rhs: Expression<FPSort>) = FPMul(RTN, this(), rhs)

infix fun (() -> Expression<FPSort>).fpmul_rtz(rhs: Expression<FPSort>) = FPMul(RTZ, this(), rhs)

infix fun (() -> Expression<FPSort>).fpmul(rhs: () -> Expression<FPSort>) = this() fpmul_rne rhs()

infix fun (() -> Expression<FPSort>).fpmul_rne(rhs: () -> Expression<FPSort>) =
    FPMul(RNE, this(), rhs())

infix fun (() -> Expression<FPSort>).fpmul_rna(rhs: () -> Expression<FPSort>) =
    FPMul(RNA, this(), rhs())

infix fun (() -> Expression<FPSort>).fpmul_rtp(rhs: () -> Expression<FPSort>) =
    FPMul(RTP, this(), rhs())

infix fun (() -> Expression<FPSort>).fpmul_rtn(rhs: () -> Expression<FPSort>) =
    FPMul(RTN, this(), rhs())

infix fun (() -> Expression<FPSort>).fpmul_rtz(rhs: () -> Expression<FPSort>) =
    FPMul(RTZ, this(), rhs())

infix fun Expression<FPSort>.fpdiv(rhs: Expression<FPSort>) = this fpdiv_rne rhs

infix fun Expression<FPSort>.fpdiv_rne(rhs: Expression<FPSort>) = FPDiv(RNE, this, rhs)

infix fun Expression<FPSort>.fpdiv_rna(rhs: Expression<FPSort>) = FPDiv(RNA, this, rhs)

infix fun Expression<FPSort>.fpdiv_rtp(rhs: Expression<FPSort>) = FPDiv(RTP, this, rhs)

infix fun Expression<FPSort>.fpdiv_rtn(rhs: Expression<FPSort>) = FPDiv(RTN, this, rhs)

infix fun Expression<FPSort>.fpdiv_rtz(rhs: Expression<FPSort>) = FPDiv(RTZ, this, rhs)

infix fun Expression<FPSort>.fpdiv(rhs: () -> Expression<FPSort>) = this fpdiv_rne rhs()

infix fun Expression<FPSort>.fpdiv_rne(rhs: () -> Expression<FPSort>) = FPDiv(RNE, this, rhs())

infix fun Expression<FPSort>.fpdiv_rna(rhs: () -> Expression<FPSort>) = FPDiv(RNA, this, rhs())

infix fun Expression<FPSort>.fpdiv_rtp(rhs: () -> Expression<FPSort>) = FPDiv(RTP, this, rhs())

infix fun Expression<FPSort>.fpdiv_rtn(rhs: () -> Expression<FPSort>) = FPDiv(RTN, this, rhs())

infix fun Expression<FPSort>.fpdiv_rtz(rhs: () -> Expression<FPSort>) = FPDiv(RTZ, this, rhs())

infix fun (() -> Expression<FPSort>).fpdiv(rhs: Expression<FPSort>) = this() fpdiv_rne rhs

infix fun (() -> Expression<FPSort>).fpdiv_rne(rhs: Expression<FPSort>) = FPDiv(RNE, this(), rhs)

infix fun (() -> Expression<FPSort>).fpdiv_rna(rhs: Expression<FPSort>) = FPDiv(RNA, this(), rhs)

infix fun (() -> Expression<FPSort>).fpdiv_rtp(rhs: Expression<FPSort>) = FPDiv(RTP, this(), rhs)

infix fun (() -> Expression<FPSort>).fpdiv_rtn(rhs: Expression<FPSort>) = FPDiv(RTN, this(), rhs)

infix fun (() -> Expression<FPSort>).fpdiv_rtz(rhs: Expression<FPSort>) = FPDiv(RTZ, this(), rhs)

infix fun (() -> Expression<FPSort>).fpdiv(rhs: () -> Expression<FPSort>) = this() fpdiv_rne rhs()

infix fun (() -> Expression<FPSort>).fpdiv_rne(rhs: () -> Expression<FPSort>) =
    FPDiv(RNE, this(), rhs())

infix fun (() -> Expression<FPSort>).fpdiv_rna(rhs: () -> Expression<FPSort>) =
    FPDiv(RNA, this(), rhs())

infix fun (() -> Expression<FPSort>).fpdiv_rtp(rhs: () -> Expression<FPSort>) =
    FPDiv(RTP, this(), rhs())

infix fun (() -> Expression<FPSort>).fpdiv_rtn(rhs: () -> Expression<FPSort>) =
    FPDiv(RTN, this(), rhs())

infix fun (() -> Expression<FPSort>).fpdiv_rtz(rhs: () -> Expression<FPSort>) =
    FPDiv(RTZ, this(), rhs())

infix fun Expression<FPSort>.fprem(rhs: Expression<FPSort>) = FPRem(this, rhs)

infix fun Expression<FPSort>.fprem(rhs: () -> Expression<FPSort>) = FPRem(this, rhs())

infix fun (() -> Expression<FPSort>).fprem(rhs: Expression<FPSort>) = FPRem(this(), rhs)

infix fun (() -> Expression<FPSort>).fprem(rhs: () -> Expression<FPSort>) = FPRem(this(), rhs())

/*
 * unary floating-point operations
 */

fun fpsqrt(roundingMode: Expression<RoundingMode> = RNE, block: () -> Expression<FPSort>) =
    FPSqrt(roundingMode, block())

fun fpsqrt(roundingMode: Expression<RoundingMode> = RNE, expr: Expression<FPSort>) =
    FPSqrt(roundingMode, expr)

fun fproundToIntegral(
    roundingMode: Expression<RoundingMode> = RNE,
    block: () -> Expression<FPSort>
) = FPRoundToIntegral(roundingMode, block())

fun fproundToIntegral(roundingMode: Expression<RoundingMode> = RNE, expr: Expression<FPSort>) =
    FPRoundToIntegral(roundingMode, expr)

/*
 * floating-point comparison operators
 */

fun fpmin(rhs: Expression<FPSort>, lhs: Expression<FPSort>) = FPMin(rhs, lhs)

fun fpmin(rhs: Expression<FPSort>, lhs: () -> Expression<FPSort>) = FPMin(rhs, lhs())

fun fpmin(rhs: () -> Expression<FPSort>, lhs: Expression<FPSort>) = FPMin(rhs(), lhs)

fun fpmin(rhs: () -> Expression<FPSort>, lhs: () -> Expression<FPSort>) = FPMin(rhs(), lhs())

fun fpmax(rhs: Expression<FPSort>, lhs: Expression<FPSort>) = FPMax(rhs, lhs)

fun fpmax(rhs: Expression<FPSort>, lhs: () -> Expression<FPSort>) = FPMax(rhs, lhs())

fun fpmax(rhs: () -> Expression<FPSort>, lhs: Expression<FPSort>) = FPMax(rhs(), lhs)

fun fpmax(rhs: () -> Expression<FPSort>, lhs: () -> Expression<FPSort>) = FPMax(rhs(), lhs())

infix fun Expression<FPSort>.fpleq(rhs: Expression<FPSort>) = FPLeq(this, rhs)

infix fun Expression<FPSort>.fplt(rhs: Expression<FPSort>) = FPLt(this, rhs)

infix fun Expression<FPSort>.fpgeq(rhs: Expression<FPSort>) = FPGeq(this, rhs)

infix fun Expression<FPSort>.fpgt(rhs: Expression<FPSort>) = FPGt(this, rhs)

infix fun Expression<FPSort>.fpeq(rhs: Expression<FPSort>) = FPEq(this, rhs)

infix fun Expression<FPSort>.fpleq(rhs: () -> Expression<FPSort>) = FPLeq(this, rhs())

infix fun Expression<FPSort>.fplt(rhs: () -> Expression<FPSort>) = FPLt(this, rhs())

infix fun Expression<FPSort>.fpgeq(rhs: () -> Expression<FPSort>) = FPGeq(this, rhs())

infix fun Expression<FPSort>.fpgt(rhs: () -> Expression<FPSort>) = FPGt(this, rhs())

infix fun Expression<FPSort>.fpeq(rhs: () -> Expression<FPSort>) = FPEq(this, rhs())

infix fun (() -> Expression<FPSort>).fpleq(rhs: Expression<FPSort>) = FPLeq(this(), rhs)

infix fun (() -> Expression<FPSort>).fplt(rhs: Expression<FPSort>) = FPLt(this(), rhs)

infix fun (() -> Expression<FPSort>).fpgeq(rhs: Expression<FPSort>) = FPGeq(this(), rhs)

infix fun (() -> Expression<FPSort>).fpgt(rhs: Expression<FPSort>) = FPGt(this(), rhs)

infix fun (() -> Expression<FPSort>).fpeq(rhs: Expression<FPSort>) = FPEq(this(), rhs)

infix fun (() -> Expression<FPSort>).fpleq(rhs: () -> Expression<FPSort>) = FPLeq(this(), rhs())

infix fun (() -> Expression<FPSort>).fplt(rhs: () -> Expression<FPSort>) = FPLt(this(), rhs())

infix fun (() -> Expression<FPSort>).fpgeq(rhs: () -> Expression<FPSort>) = FPGeq(this(), rhs())

infix fun (() -> Expression<FPSort>).fpgt(rhs: () -> Expression<FPSort>) = FPGt(this(), rhs())

infix fun (() -> Expression<FPSort>).fpeq(rhs: () -> Expression<FPSort>) = FPEq(this(), rhs())

infix fun FPLeq.fpleq(rhs: Expression<FPSort>) = FPLeq(*this.children.toTypedArray(), rhs)

infix fun FPLt.fplt(rhs: Expression<FPSort>) = FPLt(*this.children.toTypedArray(), rhs)

infix fun FPGeq.fpgeq(rhs: Expression<FPSort>) = FPGeq(*this.children.toTypedArray(), rhs)

infix fun FPGt.fpgt(rhs: Expression<FPSort>) = FPGt(*this.children.toTypedArray(), rhs)

infix fun FPEq.fpeq(rhs: Expression<FPSort>) = FPEq(*this.children.toTypedArray(), rhs)

infix fun FPLeq.fpleq(rhs: () -> Expression<FPSort>) = FPLeq(*this.children.toTypedArray(), rhs())

infix fun FPLt.fplt(rhs: () -> Expression<FPSort>) = FPLt(*this.children.toTypedArray(), rhs())

infix fun FPGeq.fpgeq(rhs: () -> Expression<FPSort>) = FPGeq(*this.children.toTypedArray(), rhs())

infix fun FPGt.fpgt(rhs: () -> Expression<FPSort>) = FPGt(*this.children.toTypedArray(), rhs())

infix fun FPEq.fpeq(rhs: () -> Expression<FPSort>) = FPEq(*this.children.toTypedArray(), rhs())

infix fun (() -> FPLeq).fpleq(rhs: Expression<FPSort>) = FPLeq(*this().children.toTypedArray(), rhs)

infix fun (() -> FPLt).fplt(rhs: Expression<FPSort>) = FPLt(*this().children.toTypedArray(), rhs)

infix fun (() -> FPGeq).fpgeq(rhs: Expression<FPSort>) = FPGeq(*this().children.toTypedArray(), rhs)

infix fun (() -> FPGt).fpgt(rhs: Expression<FPSort>) = FPGt(*this().children.toTypedArray(), rhs)

infix fun (() -> FPEq).fpeq(rhs: Expression<FPSort>) = FPEq(*this().children.toTypedArray(), rhs)

infix fun (() -> FPLeq).fpleq(rhs: () -> Expression<FPSort>) =
    FPLeq(*this().children.toTypedArray(), rhs())

infix fun (() -> FPLt).fplt(rhs: () -> Expression<FPSort>) =
    FPLt(*this().children.toTypedArray(), rhs())

infix fun (() -> FPGeq).fpgeq(rhs: () -> Expression<FPSort>) =
    FPGeq(*this().children.toTypedArray(), rhs())

infix fun (() -> FPGt).fpgt(rhs: () -> Expression<FPSort>) =
    FPGt(*this().children.toTypedArray(), rhs())

infix fun (() -> FPEq).fpeq(rhs: () -> Expression<FPSort>) =
    FPEq(*this().children.toTypedArray(), rhs())

/*
 * floating-point conversion operations
 */

@JvmName("FPToFP")
fun toFP(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingMode> = RNE,
    block: () -> Expression<FPSort>
) = FPToFP(roundingMode, block(), eb, sb)

@JvmName("FPToFP")
fun toFP(eb: Int, sb: Int, roundingMode: Expression<RoundingMode> = RNE, expr: Expression<FPSort>) =
    FPToFP(roundingMode, expr, eb, sb)

@JvmName("FPToReal")
fun toFP(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingMode> = RNE,
    block: () -> Expression<RealSort>
) = RealToFP(roundingMode, block(), eb, sb)

@JvmName("FPToReal")
fun toFP(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingMode> = RNE,
    expr: Expression<RealSort>
) = RealToFP(roundingMode, expr, eb, sb)

@JvmName("FPToSBV")
fun toFP(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingMode> = RNE,
    block: () -> Expression<BVSort>
) = SBitVecToFP(roundingMode, block(), eb, sb)

@JvmName("FPToSBV")
fun toFP(eb: Int, sb: Int, roundingMode: Expression<RoundingMode> = RNE, expr: Expression<BVSort>) =
    SBitVecToFP(roundingMode, expr, eb, sb)

@JvmName("FPToUBV")
fun toFPUnsigned(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingMode> = RNE,
    block: () -> Expression<BVSort>
) = UBitVecToFP(roundingMode, block(), eb, sb)

@JvmName("FPToUBV")
fun toFPUnsigned(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingMode> = RNE,
    expr: Expression<BVSort>
) = UBitVecToFP(roundingMode, expr, eb, sb)

@JvmName("BVToFP")
fun toFP(eb: Int, sb: Int, block: () -> Expression<BVSort>) = BitVecToFP(block(), eb, sb)

@JvmName("BVToFP") fun toFP(eb: Int, sb: Int, expr: Expression<BVSort>) = BitVecToFP(expr, eb, sb)

fun toUBV(m: Int, roundingMode: Expression<RoundingMode> = RNE, block: () -> Expression<FPSort>) =
    FPToUBitVec(roundingMode, block(), m)

fun toUBV(m: Int, roundingMode: Expression<RoundingMode> = RNE, expr: Expression<FPSort>) =
    FPToUBitVec(roundingMode, expr, m)

fun toSBV(m: Int, roundingMode: Expression<RoundingMode> = RNE, block: () -> Expression<FPSort>) =
    FPToSBitVec(roundingMode, block(), m)

fun toSBV(m: Int, roundingMode: Expression<RoundingMode> = RNE, expr: Expression<FPSort>) =
    FPToSBitVec(roundingMode, expr, m)

fun toReal(block: () -> Expression<FPSort>) = FPToReal(block())

fun toReal(expr: Expression<FPSort>) = FPToReal(expr)

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

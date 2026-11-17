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

import kotlin.experimental.ExperimentalTypeInference
import tools.aqua.konstraints.smt.BitVecSort
import tools.aqua.konstraints.smt.BitVecToFP
import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.smt.FPAdd
import tools.aqua.konstraints.smt.FPDiv
import tools.aqua.konstraints.smt.FPEq
import tools.aqua.konstraints.smt.FPFma
import tools.aqua.konstraints.smt.FPGeq
import tools.aqua.konstraints.smt.FPGt
import tools.aqua.konstraints.smt.FPIsInfinite
import tools.aqua.konstraints.smt.FPIsNaN
import tools.aqua.konstraints.smt.FPIsNegative
import tools.aqua.konstraints.smt.FPIsNormal
import tools.aqua.konstraints.smt.FPIsPositive
import tools.aqua.konstraints.smt.FPIsSubnormal
import tools.aqua.konstraints.smt.FPIsZero
import tools.aqua.konstraints.smt.FPLeq
import tools.aqua.konstraints.smt.FPLt
import tools.aqua.konstraints.smt.FPMax
import tools.aqua.konstraints.smt.FPMin
import tools.aqua.konstraints.smt.FPMul
import tools.aqua.konstraints.smt.FPRem
import tools.aqua.konstraints.smt.FPRoundToIntegral
import tools.aqua.konstraints.smt.FPSqrt
import tools.aqua.konstraints.smt.FPSub
import tools.aqua.konstraints.smt.FPToFP
import tools.aqua.konstraints.smt.FPToReal
import tools.aqua.konstraints.smt.FPToSBitVec
import tools.aqua.konstraints.smt.FPToUBitVec
import tools.aqua.konstraints.smt.FloatingPointLiteral
import tools.aqua.konstraints.smt.FloatingPointSort
import tools.aqua.konstraints.smt.RNA
import tools.aqua.konstraints.smt.RNE
import tools.aqua.konstraints.smt.RTN
import tools.aqua.konstraints.smt.RTP
import tools.aqua.konstraints.smt.RTZ
import tools.aqua.konstraints.smt.RealSort
import tools.aqua.konstraints.smt.RealToFP
import tools.aqua.konstraints.smt.RoundingModeSort
import tools.aqua.konstraints.smt.SBitVecToFP
import tools.aqua.konstraints.smt.UBitVecToFP

/*
 * floating-point infix operations
 */

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun Expression<FloatingPointSort>.fpadd(summand: Expression<FloatingPointSort>) =
    this fpadd_rne summand

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun Expression<FloatingPointSort>.fpadd_rne(summand: Expression<FloatingPointSort>) =
    FPAdd(RNE, this, summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun Expression<FloatingPointSort>.fpadd_rna(summand: Expression<FloatingPointSort>) =
    FPAdd(RNA, this, summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun Expression<FloatingPointSort>.fpadd_rtp(summand: Expression<FloatingPointSort>) =
    FPAdd(RTP, this, summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun Expression<FloatingPointSort>.fpadd_rtn(summand: Expression<FloatingPointSort>) =
    FPAdd(RTN, this, summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun Expression<FloatingPointSort>.fpadd_rtz(summand: Expression<FloatingPointSort>) =
    FPAdd(RTZ, this, summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun Expression<FloatingPointSort>.fpadd(summand: () -> Expression<FloatingPointSort>) =
    this fpadd_rne summand()

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun Expression<FloatingPointSort>.fpadd_rne(summand: () -> Expression<FloatingPointSort>) =
    FPAdd(RNE, this, summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun Expression<FloatingPointSort>.fpadd_rna(summand: () -> Expression<FloatingPointSort>) =
    FPAdd(RNA, this, summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun Expression<FloatingPointSort>.fpadd_rtp(summand: () -> Expression<FloatingPointSort>) =
    FPAdd(RTP, this, summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun Expression<FloatingPointSort>.fpadd_rtn(summand: () -> Expression<FloatingPointSort>) =
    FPAdd(RTN, this, summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun Expression<FloatingPointSort>.fpadd_rtz(summand: () -> Expression<FloatingPointSort>) =
    FPAdd(RTZ, this, summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpadd(summand: Expression<FloatingPointSort>) =
    this() fpadd_rne summand

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpadd_rne(summand: Expression<FloatingPointSort>) =
    FPAdd(RNE, this(), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpadd_rna(summand: Expression<FloatingPointSort>) =
    FPAdd(RNA, this(), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpadd_rtp(summand: Expression<FloatingPointSort>) =
    FPAdd(RTP, this(), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpadd_rtn(summand: Expression<FloatingPointSort>) =
    FPAdd(RTN, this(), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpadd_rtz(summand: Expression<FloatingPointSort>) =
    FPAdd(RTZ, this(), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpadd(
    summand: () -> Expression<FloatingPointSort>
) = this() fpadd_rne summand()

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpadd_rne(
    summand: () -> Expression<FloatingPointSort>
) = FPAdd(RNE, this(), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpadd_rna(
    summand: () -> Expression<FloatingPointSort>
) = FPAdd(RNA, this(), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpadd_rtp(
    summand: () -> Expression<FloatingPointSort>
) = FPAdd(RTP, this(), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpadd_rtn(
    summand: () -> Expression<FloatingPointSort>
) = FPAdd(RTN, this(), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpadd_rtz(
    summand: () -> Expression<FloatingPointSort>
) = FPAdd(RTZ, this(), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [summand] from [Float] to
 * [tools.aqua.konstraints.smt.FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FloatingPointSort>.fpadd(summand: Float) =
    this fpadd_rne FloatingPointLiteral(summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest even'. Converts [summand] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FloatingPointSort>.fpadd_rne(summand: Float) =
    FPAdd(RNE, this, FloatingPointLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest away'. Converts [summand] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FloatingPointSort>.fpadd_rna(summand: Float) =
    FPAdd(RNA, this, FloatingPointLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward positive'. Converts [summand] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FloatingPointSort>.fpadd_rtp(summand: Float) =
    FPAdd(RTP, this, FloatingPointLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward negative'. Converts [summand] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FloatingPointSort>.fpadd_rtn(summand: Float) =
    FPAdd(RTN, this, FloatingPointLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward zero'. Converts [summand] from [Float] to [FloatingPointLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FloatingPointSort>.fpadd_rtz(summand: Float) =
    FPAdd(RTZ, this, FloatingPointLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [summand] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpadd(summand: Float) =
    this() fpadd_rne FloatingPointLiteral(summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest even'. Converts [summand] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpadd_rne(summand: Float) =
    FPAdd(RNE, this(), FloatingPointLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest away'. Converts [summand] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpadd_rna(summand: Float) =
    FPAdd(RNA, this(), FloatingPointLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward positive'. Converts [summand] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpadd_rtp(summand: Float) =
    FPAdd(RTP, this(), FloatingPointLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward negative'. Converts [summand] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpadd_rtn(summand: Float) =
    FPAdd(RTN, this(), FloatingPointLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward zero'. Converts [summand] from [Float] to [FloatingPointLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpadd_rtz(summand: Float) =
    FPAdd(RTZ, this(), FloatingPointLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [summand] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpadd(summand: Expression<FloatingPointSort>) =
    FloatingPointLiteral(this) fpadd_rne summand

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest even'. Converts [summand] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpadd_rne(summand: Expression<FloatingPointSort>) =
    FPAdd(RNE, FloatingPointLiteral(this), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest away'. Converts [summand] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpadd_rna(summand: Expression<FloatingPointSort>) =
    FPAdd(RNA, FloatingPointLiteral(this), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward positive'. Converts [summand] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpadd_rtp(summand: Expression<FloatingPointSort>) =
    FPAdd(RTP, FloatingPointLiteral(this), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward negative'. Converts [summand] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpadd_rtn(summand: Expression<FloatingPointSort>) =
    FPAdd(RTN, FloatingPointLiteral(this), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward zero'. Converts [summand] from [Float] to [FloatingPointLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpadd_rtz(summand: Expression<FloatingPointSort>) =
    FPAdd(RTZ, FloatingPointLiteral(this), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [summand] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpadd(summand: () -> Expression<FloatingPointSort>) =
    FloatingPointLiteral(this) fpadd_rne summand()

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest even'. Converts [summand] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpadd_rne(summand: () -> Expression<FloatingPointSort>) =
    FPAdd(RNE, FloatingPointLiteral(this), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest away'. Converts [summand] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpadd_rna(summand: () -> Expression<FloatingPointSort>) =
    FPAdd(RNA, FloatingPointLiteral(this), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward positive'. Converts [summand] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpadd_rtp(summand: () -> Expression<FloatingPointSort>) =
    FPAdd(RTP, FloatingPointLiteral(this), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward negative'. Converts [summand] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpadd_rtn(summand: () -> Expression<FloatingPointSort>) =
    FPAdd(RTN, FloatingPointLiteral(this), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward zero'. Converts [summand] from [Float] to [FloatingPointLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpadd_rtz(summand: () -> Expression<FloatingPointSort>) =
    FPAdd(RTZ, FloatingPointLiteral(this), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [summand] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FloatingPointSort>.fpadd(summand: Double) =
    this fpadd_rne FloatingPointLiteral(summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest even'. Converts [summand] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FloatingPointSort>.fpadd_rne(summand: Double) =
    FPAdd(RNE, this, FloatingPointLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest away'. Converts [summand] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FloatingPointSort>.fpadd_rna(summand: Double) =
    FPAdd(RNA, this, FloatingPointLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward positive'. Converts [summand] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FloatingPointSort>.fpadd_rtp(summand: Double) =
    FPAdd(RTP, this, FloatingPointLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward negative'. Converts [summand] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FloatingPointSort>.fpadd_rtn(summand: Double) =
    FPAdd(RTN, this, FloatingPointLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward zero'. Converts [summand] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FloatingPointSort>.fpadd_rtz(summand: Double) =
    FPAdd(RTZ, this, FloatingPointLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [summand] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpadd(summand: Double) =
    this() fpadd_rne FloatingPointLiteral(summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest even'. Converts [summand] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpadd_rne(summand: Double) =
    FPAdd(RNE, this(), FloatingPointLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest away'. Converts [summand] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpadd_rna(summand: Double) =
    FPAdd(RNA, this(), FloatingPointLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward positive'. Converts [summand] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpadd_rtp(summand: Double) =
    FPAdd(RTP, this(), FloatingPointLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward negative'. Converts [summand] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpadd_rtn(summand: Double) =
    FPAdd(RTN, this(), FloatingPointLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward zero'. Converts [summand] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpadd_rtz(summand: Double) =
    FPAdd(RTZ, this(), FloatingPointLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [summand] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpadd(summand: Expression<FloatingPointSort>) =
    FloatingPointLiteral(this) fpadd_rne summand

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest even'. Converts [summand] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpadd_rne(summand: Expression<FloatingPointSort>) =
    FPAdd(RNE, FloatingPointLiteral(this), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest away'. Converts [summand] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpadd_rna(summand: Expression<FloatingPointSort>) =
    FPAdd(RNA, FloatingPointLiteral(this), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward positive'. Converts [summand] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpadd_rtp(summand: Expression<FloatingPointSort>) =
    FPAdd(RTP, FloatingPointLiteral(this), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward negative'. Converts [summand] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpadd_rtn(summand: Expression<FloatingPointSort>) =
    FPAdd(RTN, FloatingPointLiteral(this), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward zero'. Converts [summand] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpadd_rtz(summand: Expression<FloatingPointSort>) =
    FPAdd(RTZ, FloatingPointLiteral(this), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [summand] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpadd(summand: () -> Expression<FloatingPointSort>) =
    FloatingPointLiteral(this) fpadd_rne summand()

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest even'. Converts [summand] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpadd_rne(summand: () -> Expression<FloatingPointSort>) =
    FPAdd(RNE, FloatingPointLiteral(this), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest away'. Converts [summand] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpadd_rna(summand: () -> Expression<FloatingPointSort>) =
    FPAdd(RNA, FloatingPointLiteral(this), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward positive'. Converts [summand] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpadd_rtp(summand: () -> Expression<FloatingPointSort>) =
    FPAdd(RTP, FloatingPointLiteral(this), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward negative'. Converts [summand] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpadd_rtn(summand: () -> Expression<FloatingPointSort>) =
    FPAdd(RTN, FloatingPointLiteral(this), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward zero'. Converts [summand] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpadd_rtz(summand: () -> Expression<FloatingPointSort>) =
    FPAdd(RTZ, FloatingPointLiteral(this), summand())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun Expression<FloatingPointSort>.fpsub(subtrahend: Expression<FloatingPointSort>) =
    this fpsub_rne subtrahend

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun Expression<FloatingPointSort>.fpsub_rne(subtrahend: Expression<FloatingPointSort>) =
    FPSub(RNE, this, subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun Expression<FloatingPointSort>.fpsub_rna(subtrahend: Expression<FloatingPointSort>) =
    FPSub(RNA, this, subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun Expression<FloatingPointSort>.fpsub_rtp(subtrahend: Expression<FloatingPointSort>) =
    FPSub(RTP, this, subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun Expression<FloatingPointSort>.fpsub_rtn(subtrahend: Expression<FloatingPointSort>) =
    FPSub(RTN, this, subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun Expression<FloatingPointSort>.fpsub_rtz(subtrahend: Expression<FloatingPointSort>) =
    FPSub(RTZ, this, subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun Expression<FloatingPointSort>.fpsub(subtrahend: () -> Expression<FloatingPointSort>) =
    this fpsub_rne subtrahend()

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun Expression<FloatingPointSort>.fpsub_rne(subtrahend: () -> Expression<FloatingPointSort>) =
    FPSub(RNE, this, subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun Expression<FloatingPointSort>.fpsub_rna(subtrahend: () -> Expression<FloatingPointSort>) =
    FPSub(RNA, this, subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun Expression<FloatingPointSort>.fpsub_rtp(subtrahend: () -> Expression<FloatingPointSort>) =
    FPSub(RTP, this, subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun Expression<FloatingPointSort>.fpsub_rtn(subtrahend: () -> Expression<FloatingPointSort>) =
    FPSub(RTN, this, subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun Expression<FloatingPointSort>.fpsub_rtz(subtrahend: () -> Expression<FloatingPointSort>) =
    FPSub(RTZ, this, subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpsub(subtrahend: Expression<FloatingPointSort>) =
    this() fpsub_rne subtrahend

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpsub_rne(
    subtrahend: Expression<FloatingPointSort>
) = FPSub(RNE, this(), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpsub_rna(
    subtrahend: Expression<FloatingPointSort>
) = FPSub(RNA, this(), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpsub_rtp(
    subtrahend: Expression<FloatingPointSort>
) = FPSub(RTP, this(), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpsub_rtn(
    subtrahend: Expression<FloatingPointSort>
) = FPSub(RTN, this(), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpsub_rtz(
    subtrahend: Expression<FloatingPointSort>
) = FPSub(RTZ, this(), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpsub(
    subtrahend: () -> Expression<FloatingPointSort>
) = this() fpsub_rne subtrahend()

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpsub_rne(
    subtrahend: () -> Expression<FloatingPointSort>
) = FPSub(RNE, this(), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpsub_rna(
    subtrahend: () -> Expression<FloatingPointSort>
) = FPSub(RNA, this(), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpsub_rtp(
    subtrahend: () -> Expression<FloatingPointSort>
) = FPSub(RTP, this(), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpsub_rtn(
    subtrahend: () -> Expression<FloatingPointSort>
) = FPSub(RTN, this(), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpsub_rtz(
    subtrahend: () -> Expression<FloatingPointSort>
) = FPSub(RTZ, this(), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [subtrahend] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FloatingPointSort>.fpsub(subtrahend: Float) =
    this fpsub_rne FloatingPointLiteral(subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest even'. Converts [subtrahend] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FloatingPointSort>.fpsub_rne(subtrahend: Float) =
    FPSub(RNE, this, FloatingPointLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest away'. Converts [subtrahend] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FloatingPointSort>.fpsub_rna(subtrahend: Float) =
    FPSub(RNA, this, FloatingPointLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward positive'. Converts [subtrahend] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FloatingPointSort>.fpsub_rtp(subtrahend: Float) =
    FPSub(RTP, this, FloatingPointLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward negative'. Converts [subtrahend] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FloatingPointSort>.fpsub_rtn(subtrahend: Float) =
    FPSub(RTN, this, FloatingPointLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward zero'. Converts [subtrahend] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FloatingPointSort>.fpsub_rtz(subtrahend: Float) =
    FPSub(RTZ, this, FloatingPointLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [subtrahend] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpsub(subtrahend: Float) =
    this() fpsub_rne FloatingPointLiteral(subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest even'. Converts [subtrahend] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpsub_rne(subtrahend: Float) =
    FPSub(RNE, this(), FloatingPointLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest away'. Converts [subtrahend] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpsub_rna(subtrahend: Float) =
    FPSub(RNA, this(), FloatingPointLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward positive'. Converts [subtrahend] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpsub_rtp(subtrahend: Float) =
    FPSub(RTP, this(), FloatingPointLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward negative'. Converts [subtrahend] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpsub_rtn(subtrahend: Float) =
    FPSub(RTN, this(), FloatingPointLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward zero'. Converts [subtrahend] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpsub_rtz(subtrahend: Float) =
    FPSub(RTZ, this(), FloatingPointLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [subtrahend] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpsub(subtrahend: Expression<FloatingPointSort>) =
    FloatingPointLiteral(this) fpsub_rne subtrahend

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest even'. Converts [subtrahend] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpsub_rne(subtrahend: Expression<FloatingPointSort>) =
    FPSub(RNE, FloatingPointLiteral(this), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest away'. Converts [subtrahend] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpsub_rna(subtrahend: Expression<FloatingPointSort>) =
    FPSub(RNA, FloatingPointLiteral(this), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward positive'. Converts [subtrahend] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpsub_rtp(subtrahend: Expression<FloatingPointSort>) =
    FPSub(RTP, FloatingPointLiteral(this), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward negative'. Converts [subtrahend] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpsub_rtn(subtrahend: Expression<FloatingPointSort>) =
    FPSub(RTN, FloatingPointLiteral(this), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward zero'. Converts [subtrahend] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpsub_rtz(subtrahend: Expression<FloatingPointSort>) =
    FPSub(RTZ, FloatingPointLiteral(this), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [subtrahend] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpsub(subtrahend: () -> Expression<FloatingPointSort>) =
    FloatingPointLiteral(this) fpsub_rne subtrahend()

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest even'. Converts [subtrahend] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpsub_rne(subtrahend: () -> Expression<FloatingPointSort>) =
    FPSub(RNE, FloatingPointLiteral(this), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest away'. Converts [subtrahend] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpsub_rna(subtrahend: () -> Expression<FloatingPointSort>) =
    FPSub(RNA, FloatingPointLiteral(this), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward positive'. Converts [subtrahend] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpsub_rtp(subtrahend: () -> Expression<FloatingPointSort>) =
    FPSub(RTP, FloatingPointLiteral(this), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward negative'. Converts [subtrahend] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpsub_rtn(subtrahend: () -> Expression<FloatingPointSort>) =
    FPSub(RTN, FloatingPointLiteral(this), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward zero'. Converts [subtrahend] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpsub_rtz(subtrahend: () -> Expression<FloatingPointSort>) =
    FPSub(RTZ, FloatingPointLiteral(this), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [subtrahend] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FloatingPointSort>.fpsub(subtrahend: Double) =
    this fpsub_rne FloatingPointLiteral(subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest even'. Converts [subtrahend] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FloatingPointSort>.fpsub_rne(subtrahend: Double) =
    FPSub(RNE, this, FloatingPointLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest away'. Converts [subtrahend] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FloatingPointSort>.fpsub_rna(subtrahend: Double) =
    FPSub(RNA, this, FloatingPointLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward positive'. Converts [subtrahend] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FloatingPointSort>.fpsub_rtp(subtrahend: Double) =
    FPSub(RTP, this, FloatingPointLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward negative'. Converts [subtrahend] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FloatingPointSort>.fpsub_rtn(subtrahend: Double) =
    FPSub(RTN, this, FloatingPointLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward zero'. Converts [subtrahend] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FloatingPointSort>.fpsub_rtz(subtrahend: Double) =
    FPSub(RTZ, this, FloatingPointLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [subtrahend] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpsub(subtrahend: Double) =
    this() fpsub_rne FloatingPointLiteral(subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest even'. Converts [subtrahend] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpsub_rne(subtrahend: Double) =
    FPSub(RNE, this(), FloatingPointLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest away'. Converts [subtrahend] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpsub_rna(subtrahend: Double) =
    FPSub(RNA, this(), FloatingPointLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward positive'. Converts [subtrahend] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpsub_rtp(subtrahend: Double) =
    FPSub(RTP, this(), FloatingPointLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward negative'. Converts [subtrahend] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpsub_rtn(subtrahend: Double) =
    FPSub(RTN, this(), FloatingPointLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward zero'. Converts [subtrahend] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpsub_rtz(subtrahend: Double) =
    FPSub(RTZ, this(), FloatingPointLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [subtrahend] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpsub(subtrahend: Expression<FloatingPointSort>) =
    FloatingPointLiteral(this) fpsub_rne subtrahend

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest even'. Converts [subtrahend] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpsub_rne(subtrahend: Expression<FloatingPointSort>) =
    FPSub(RNE, FloatingPointLiteral(this), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest away'. Converts [subtrahend] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpsub_rna(subtrahend: Expression<FloatingPointSort>) =
    FPSub(RNA, FloatingPointLiteral(this), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward positive'. Converts [subtrahend] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpsub_rtp(subtrahend: Expression<FloatingPointSort>) =
    FPSub(RTP, FloatingPointLiteral(this), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward negative'. Converts [subtrahend] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpsub_rtn(subtrahend: Expression<FloatingPointSort>) =
    FPSub(RTN, FloatingPointLiteral(this), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward zero'. Converts [subtrahend] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpsub_rtz(subtrahend: Expression<FloatingPointSort>) =
    FPSub(RTZ, FloatingPointLiteral(this), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [subtrahend] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpsub(subtrahend: () -> Expression<FloatingPointSort>) =
    FloatingPointLiteral(this) fpsub_rne subtrahend()

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest even'. Converts [subtrahend] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpsub_rne(subtrahend: () -> Expression<FloatingPointSort>) =
    FPSub(RNE, FloatingPointLiteral(this), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest away'. Converts [subtrahend] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpsub_rna(subtrahend: () -> Expression<FloatingPointSort>) =
    FPSub(RNA, FloatingPointLiteral(this), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward positive'. Converts [subtrahend] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpsub_rtp(subtrahend: () -> Expression<FloatingPointSort>) =
    FPSub(RTP, FloatingPointLiteral(this), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward negative'. Converts [subtrahend] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpsub_rtn(subtrahend: () -> Expression<FloatingPointSort>) =
    FPSub(RTN, FloatingPointLiteral(this), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward zero'. Converts [subtrahend] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpsub_rtz(subtrahend: () -> Expression<FloatingPointSort>) =
    FPSub(RTZ, FloatingPointLiteral(this), subtrahend())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun Expression<FloatingPointSort>.fpmul(multiplicant: Expression<FloatingPointSort>) =
    this fpmul_rne multiplicant

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun Expression<FloatingPointSort>.fpmul_rne(multiplicant: Expression<FloatingPointSort>) =
    FPMul(RNE, this, multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun Expression<FloatingPointSort>.fpmul_rna(multiplicant: Expression<FloatingPointSort>) =
    FPMul(RNA, this, multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun Expression<FloatingPointSort>.fpmul_rtp(multiplicant: Expression<FloatingPointSort>) =
    FPMul(RTP, this, multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun Expression<FloatingPointSort>.fpmul_rtn(multiplicant: Expression<FloatingPointSort>) =
    FPMul(RTN, this, multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun Expression<FloatingPointSort>.fpmul_rtz(multiplicant: Expression<FloatingPointSort>) =
    FPMul(RTZ, this, multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun Expression<FloatingPointSort>.fpmul(multiplicant: () -> Expression<FloatingPointSort>) =
    this fpmul_rne multiplicant()

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun Expression<FloatingPointSort>.fpmul_rne(
    multiplicant: () -> Expression<FloatingPointSort>
) = FPMul(RNE, this, multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun Expression<FloatingPointSort>.fpmul_rna(
    multiplicant: () -> Expression<FloatingPointSort>
) = FPMul(RNA, this, multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun Expression<FloatingPointSort>.fpmul_rtp(
    multiplicant: () -> Expression<FloatingPointSort>
) = FPMul(RTP, this, multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun Expression<FloatingPointSort>.fpmul_rtn(
    multiplicant: () -> Expression<FloatingPointSort>
) = FPMul(RTN, this, multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun Expression<FloatingPointSort>.fpmul_rtz(
    multiplicant: () -> Expression<FloatingPointSort>
) = FPMul(RTZ, this, multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpmul(multiplicant: Expression<FloatingPointSort>) =
    this() fpmul_rne multiplicant

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpmul_rne(
    multiplicant: Expression<FloatingPointSort>
) = FPMul(RNE, this(), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpmul_rna(
    multiplicant: Expression<FloatingPointSort>
) = FPMul(RNA, this(), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpmul_rtp(
    multiplicant: Expression<FloatingPointSort>
) = FPMul(RTP, this(), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpmul_rtn(
    multiplicant: Expression<FloatingPointSort>
) = FPMul(RTN, this(), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpmul_rtz(
    multiplicant: Expression<FloatingPointSort>
) = FPMul(RTZ, this(), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpmul(
    multiplicant: () -> Expression<FloatingPointSort>
) = this() fpmul_rne multiplicant()

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpmul_rne(
    multiplicant: () -> Expression<FloatingPointSort>
) = FPMul(RNE, this(), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpmul_rna(
    multiplicant: () -> Expression<FloatingPointSort>
) = FPMul(RNA, this(), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpmul_rtp(
    multiplicant: () -> Expression<FloatingPointSort>
) = FPMul(RTP, this(), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpmul_rtn(
    multiplicant: () -> Expression<FloatingPointSort>
) = FPMul(RTN, this(), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpmul_rtz(
    multiplicant: () -> Expression<FloatingPointSort>
) = FPMul(RTZ, this(), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [multiplicant] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FloatingPointSort>.fpmul(multiplicant: Float) =
    this fpmul_rne FloatingPointLiteral(multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest even'. Converts [multiplicant] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FloatingPointSort>.fpmul_rne(multiplicant: Float) =
    FPMul(RNE, this, FloatingPointLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest away'. Converts [multiplicant] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FloatingPointSort>.fpmul_rna(multiplicant: Float) =
    FPMul(RNA, this, FloatingPointLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward positive'. Converts [multiplicant] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FloatingPointSort>.fpmul_rtp(multiplicant: Float) =
    FPMul(RTP, this, FloatingPointLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward negative'. Converts [multiplicant] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FloatingPointSort>.fpmul_rtn(multiplicant: Float) =
    FPMul(RTN, this, FloatingPointLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward zero'. Converts [multiplicant] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FloatingPointSort>.fpmul_rtz(multiplicant: Float) =
    FPMul(RTZ, this, FloatingPointLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [multiplicant] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpmul(multiplicant: Float) =
    this() fpmul_rne FloatingPointLiteral(multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest even'. Converts [multiplicant] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpmul_rne(multiplicant: Float) =
    FPMul(RNE, this(), FloatingPointLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest away'. Converts [multiplicant] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpmul_rna(multiplicant: Float) =
    FPMul(RNA, this(), FloatingPointLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward positive'. Converts [multiplicant] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpmul_rtp(multiplicant: Float) =
    FPMul(RTP, this(), FloatingPointLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward negative'. Converts [multiplicant] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpmul_rtn(multiplicant: Float) =
    FPMul(RTN, this(), FloatingPointLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward zero'. Converts [multiplicant] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpmul_rtz(multiplicant: Float) =
    FPMul(RTZ, this(), FloatingPointLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [multiplicant] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpmul(multiplicant: Expression<FloatingPointSort>) =
    FloatingPointLiteral(this) fpmul_rne multiplicant

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest even'. Converts [multiplicant] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpmul_rne(multiplicant: Expression<FloatingPointSort>) =
    FPMul(RNE, FloatingPointLiteral(this), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest away'. Converts [multiplicant] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpmul_rna(multiplicant: Expression<FloatingPointSort>) =
    FPMul(RNA, FloatingPointLiteral(this), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward positive'. Converts [multiplicant] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpmul_rtp(multiplicant: Expression<FloatingPointSort>) =
    FPMul(RTP, FloatingPointLiteral(this), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward negative'. Converts [multiplicant] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpmul_rtn(multiplicant: Expression<FloatingPointSort>) =
    FPMul(RTN, FloatingPointLiteral(this), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward zero'. Converts [multiplicant] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpmul_rtz(multiplicant: Expression<FloatingPointSort>) =
    FPMul(RTZ, FloatingPointLiteral(this), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [multiplicant] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpmul(multiplicant: () -> Expression<FloatingPointSort>) =
    FloatingPointLiteral(this) fpmul_rne multiplicant()

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest even'. Converts [multiplicant] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpmul_rne(multiplicant: () -> Expression<FloatingPointSort>) =
    FPMul(RNE, FloatingPointLiteral(this), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest away'. Converts [multiplicant] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpmul_rna(multiplicant: () -> Expression<FloatingPointSort>) =
    FPMul(RNA, FloatingPointLiteral(this), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward positive'. Converts [multiplicant] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpmul_rtp(multiplicant: () -> Expression<FloatingPointSort>) =
    FPMul(RTP, FloatingPointLiteral(this), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward negative'. Converts [multiplicant] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpmul_rtn(multiplicant: () -> Expression<FloatingPointSort>) =
    FPMul(RTN, FloatingPointLiteral(this), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward zero'. Converts [multiplicant] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpmul_rtz(multiplicant: () -> Expression<FloatingPointSort>) =
    FPMul(RTZ, FloatingPointLiteral(this), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [multiplicant] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FloatingPointSort>.fpmul(multiplicant: Double) =
    this fpmul_rne FloatingPointLiteral(multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest even'. Converts [multiplicant] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FloatingPointSort>.fpmul_rne(multiplicant: Double) =
    FPMul(RNE, this, FloatingPointLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest away'. Converts [multiplicant] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FloatingPointSort>.fpmul_rna(multiplicant: Double) =
    FPMul(RNA, this, FloatingPointLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward positive'. Converts [multiplicant] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FloatingPointSort>.fpmul_rtp(multiplicant: Double) =
    FPMul(RTP, this, FloatingPointLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward negative'. Converts [multiplicant] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FloatingPointSort>.fpmul_rtn(multiplicant: Double) =
    FPMul(RTN, this, FloatingPointLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward zero'. Converts [multiplicant] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FloatingPointSort>.fpmul_rtz(multiplicant: Double) =
    FPMul(RTZ, this, FloatingPointLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [multiplicant] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpmul(multiplicant: Double) =
    this() fpmul_rne FloatingPointLiteral(multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest even'. Converts [multiplicant] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpmul_rne(multiplicant: Double) =
    FPMul(RNE, this(), FloatingPointLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest away'. Converts [multiplicant] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpmul_rna(multiplicant: Double) =
    FPMul(RNA, this(), FloatingPointLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward positive'. Converts [multiplicant] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpmul_rtp(multiplicant: Double) =
    FPMul(RTP, this(), FloatingPointLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward negative'. Converts [multiplicant] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpmul_rtn(multiplicant: Double) =
    FPMul(RTN, this(), FloatingPointLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward zero'. Converts [multiplicant] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpmul_rtz(multiplicant: Double) =
    FPMul(RTZ, this(), FloatingPointLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [multiplicant] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpmul(multiplicant: Expression<FloatingPointSort>) =
    FloatingPointLiteral(this) fpmul_rne multiplicant

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest even'. Converts [multiplicant] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpmul_rne(multiplicant: Expression<FloatingPointSort>) =
    FPMul(RNE, FloatingPointLiteral(this), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest away'. Converts [multiplicant] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpmul_rna(multiplicant: Expression<FloatingPointSort>) =
    FPMul(RNA, FloatingPointLiteral(this), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward positive'. Converts [multiplicant] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpmul_rtp(multiplicant: Expression<FloatingPointSort>) =
    FPMul(RTP, FloatingPointLiteral(this), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward negative'. Converts [multiplicant] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpmul_rtn(multiplicant: Expression<FloatingPointSort>) =
    FPMul(RTN, FloatingPointLiteral(this), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward zero'. Converts [multiplicant] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpmul_rtz(multiplicant: Expression<FloatingPointSort>) =
    FPMul(RTZ, FloatingPointLiteral(this), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [multiplicant] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpmul(multiplicant: () -> Expression<FloatingPointSort>) =
    FloatingPointLiteral(this) fpmul_rne multiplicant()

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest even'. Converts [multiplicant] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpmul_rne(multiplicant: () -> Expression<FloatingPointSort>) =
    FPMul(RNE, FloatingPointLiteral(this), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest away'. Converts [multiplicant] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpmul_rna(multiplicant: () -> Expression<FloatingPointSort>) =
    FPMul(RNA, FloatingPointLiteral(this), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward positive'. Converts [multiplicant] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpmul_rtp(multiplicant: () -> Expression<FloatingPointSort>) =
    FPMul(RTP, FloatingPointLiteral(this), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward negative'. Converts [multiplicant] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpmul_rtn(multiplicant: () -> Expression<FloatingPointSort>) =
    FPMul(RTN, FloatingPointLiteral(this), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward zero'. Converts [multiplicant] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpmul_rtz(multiplicant: () -> Expression<FloatingPointSort>) =
    FPMul(RTZ, FloatingPointLiteral(this), multiplicant())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun Expression<FloatingPointSort>.fpdiv(divisor: Expression<FloatingPointSort>) =
    this fpdiv_rne divisor

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun Expression<FloatingPointSort>.fpdiv_rne(divisor: Expression<FloatingPointSort>) =
    FPDiv(RNE, this, divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun Expression<FloatingPointSort>.fpdiv_rna(divisor: Expression<FloatingPointSort>) =
    FPDiv(RNA, this, divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun Expression<FloatingPointSort>.fpdiv_rtp(divisor: Expression<FloatingPointSort>) =
    FPDiv(RTP, this, divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun Expression<FloatingPointSort>.fpdiv_rtn(divisor: Expression<FloatingPointSort>) =
    FPDiv(RTN, this, divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun Expression<FloatingPointSort>.fpdiv_rtz(divisor: Expression<FloatingPointSort>) =
    FPDiv(RTZ, this, divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun Expression<FloatingPointSort>.fpdiv(divisor: () -> Expression<FloatingPointSort>) =
    this fpdiv_rne divisor()

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun Expression<FloatingPointSort>.fpdiv_rne(divisor: () -> Expression<FloatingPointSort>) =
    FPDiv(RNE, this, divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun Expression<FloatingPointSort>.fpdiv_rna(divisor: () -> Expression<FloatingPointSort>) =
    FPDiv(RNA, this, divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun Expression<FloatingPointSort>.fpdiv_rtp(divisor: () -> Expression<FloatingPointSort>) =
    FPDiv(RTP, this, divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun Expression<FloatingPointSort>.fpdiv_rtn(divisor: () -> Expression<FloatingPointSort>) =
    FPDiv(RTN, this, divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun Expression<FloatingPointSort>.fpdiv_rtz(divisor: () -> Expression<FloatingPointSort>) =
    FPDiv(RTZ, this, divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpdiv(divisor: Expression<FloatingPointSort>) =
    this() fpdiv_rne divisor

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpdiv_rne(divisor: Expression<FloatingPointSort>) =
    FPDiv(RNE, this(), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpdiv_rna(divisor: Expression<FloatingPointSort>) =
    FPDiv(RNA, this(), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpdiv_rtp(divisor: Expression<FloatingPointSort>) =
    FPDiv(RTP, this(), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpdiv_rtn(divisor: Expression<FloatingPointSort>) =
    FPDiv(RTN, this(), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpdiv_rtz(divisor: Expression<FloatingPointSort>) =
    FPDiv(RTZ, this(), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpdiv(
    divisor: () -> Expression<FloatingPointSort>
) = this() fpdiv_rne divisor()

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpdiv_rne(
    divisor: () -> Expression<FloatingPointSort>
) = FPDiv(RNE, this(), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpdiv_rna(
    divisor: () -> Expression<FloatingPointSort>
) = FPDiv(RNA, this(), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpdiv_rtp(
    divisor: () -> Expression<FloatingPointSort>
) = FPDiv(RTP, this(), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpdiv_rtn(
    divisor: () -> Expression<FloatingPointSort>
) = FPDiv(RTN, this(), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun (() -> Expression<FloatingPointSort>).fpdiv_rtz(
    divisor: () -> Expression<FloatingPointSort>
) = FPDiv(RTZ, this(), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [divisor] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FloatingPointSort>.fpdiv(divisor: Float) =
    this fpdiv_rne FloatingPointLiteral(divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest even'. Converts [divisor] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FloatingPointSort>.fpdiv_rne(divisor: Float) =
    FPDiv(RNE, this, FloatingPointLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest away'. Converts [divisor] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FloatingPointSort>.fpdiv_rna(divisor: Float) =
    FPDiv(RNA, this, FloatingPointLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward positive'. Converts [divisor] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FloatingPointSort>.fpdiv_rtp(divisor: Float) =
    FPDiv(RTP, this, FloatingPointLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward negative'. Converts [divisor] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FloatingPointSort>.fpdiv_rtn(divisor: Float) =
    FPDiv(RTN, this, FloatingPointLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward zero'. Converts [divisor] from [Float] to [FloatingPointLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FloatingPointSort>.fpdiv_rtz(divisor: Float) =
    FPDiv(RTZ, this, FloatingPointLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [divisor] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpdiv(divisor: Float) =
    this() fpdiv_rne FloatingPointLiteral(divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest even'. Converts [divisor] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpdiv_rne(divisor: Float) =
    FPDiv(RNE, this(), FloatingPointLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest away'. Converts [divisor] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpdiv_rna(divisor: Float) =
    FPDiv(RNA, this(), FloatingPointLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward positive'. Converts [divisor] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpdiv_rtp(divisor: Float) =
    FPDiv(RTP, this(), FloatingPointLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward negative'. Converts [divisor] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpdiv_rtn(divisor: Float) =
    FPDiv(RTN, this(), FloatingPointLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward zero'. Converts [divisor] from [Float] to [FloatingPointLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpdiv_rtz(divisor: Float) =
    FPDiv(RTZ, this(), FloatingPointLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [divisor] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpdiv(divisor: Expression<FloatingPointSort>) =
    FloatingPointLiteral(this) fpdiv_rne divisor

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest even'. Converts [divisor] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpdiv_rne(divisor: Expression<FloatingPointSort>) =
    FPDiv(RNE, FloatingPointLiteral(this), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest away'. Converts [divisor] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpdiv_rna(divisor: Expression<FloatingPointSort>) =
    FPDiv(RNA, FloatingPointLiteral(this), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward positive'. Converts [divisor] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpdiv_rtp(divisor: Expression<FloatingPointSort>) =
    FPDiv(RTP, FloatingPointLiteral(this), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward negative'. Converts [divisor] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpdiv_rtn(divisor: Expression<FloatingPointSort>) =
    FPDiv(RTN, FloatingPointLiteral(this), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward zero'. Converts [divisor] from [Float] to [FloatingPointLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpdiv_rtz(divisor: Expression<FloatingPointSort>) =
    FPDiv(RTZ, FloatingPointLiteral(this), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [divisor] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpdiv(divisor: () -> Expression<FloatingPointSort>) =
    FloatingPointLiteral(this) fpdiv_rne divisor()

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest even'. Converts [divisor] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpdiv_rne(divisor: () -> Expression<FloatingPointSort>) =
    FPDiv(RNE, FloatingPointLiteral(this), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest away'. Converts [divisor] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpdiv_rna(divisor: () -> Expression<FloatingPointSort>) =
    FPDiv(RNA, FloatingPointLiteral(this), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward positive'. Converts [divisor] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpdiv_rtp(divisor: () -> Expression<FloatingPointSort>) =
    FPDiv(RTP, FloatingPointLiteral(this), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward negative'. Converts [divisor] from [Float] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpdiv_rtn(divisor: () -> Expression<FloatingPointSort>) =
    FPDiv(RTN, FloatingPointLiteral(this), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward zero'. Converts [divisor] from [Float] to [FloatingPointLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpdiv_rtz(divisor: () -> Expression<FloatingPointSort>) =
    FPDiv(RTZ, FloatingPointLiteral(this), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [divisor] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FloatingPointSort>.fpdiv(divisor: Double) =
    this fpdiv_rne FloatingPointLiteral(divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest even'. Converts [divisor] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FloatingPointSort>.fpdiv_rne(divisor: Double) =
    FPDiv(RNE, this, FloatingPointLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest away'. Converts [divisor] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FloatingPointSort>.fpdiv_rna(divisor: Double) =
    FPDiv(RNA, this, FloatingPointLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward positive'. Converts [divisor] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FloatingPointSort>.fpdiv_rtp(divisor: Double) =
    FPDiv(RTP, this, FloatingPointLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward negative'. Converts [divisor] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FloatingPointSort>.fpdiv_rtn(divisor: Double) =
    FPDiv(RTN, this, FloatingPointLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward zero'. Converts [divisor] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FloatingPointSort>.fpdiv_rtz(divisor: Double) =
    FPDiv(RTZ, this, FloatingPointLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [divisor] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpdiv(divisor: Double) =
    this() fpdiv_rne FloatingPointLiteral(divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest even'. Converts [divisor] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpdiv_rne(divisor: Double) =
    FPDiv(RNE, this(), FloatingPointLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest away'. Converts [divisor] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpdiv_rna(divisor: Double) =
    FPDiv(RNA, this(), FloatingPointLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward positive'. Converts [divisor] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpdiv_rtp(divisor: Double) =
    FPDiv(RTP, this(), FloatingPointLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward negative'. Converts [divisor] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpdiv_rtn(divisor: Double) =
    FPDiv(RTN, this(), FloatingPointLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward zero'. Converts [divisor] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FloatingPointSort>).fpdiv_rtz(divisor: Double) =
    FPDiv(RTZ, this(), FloatingPointLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [divisor] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpdiv(divisor: Expression<FloatingPointSort>) =
    FloatingPointLiteral(this) fpdiv_rne divisor

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest even'. Converts [divisor] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpdiv_rne(divisor: Expression<FloatingPointSort>) =
    FPDiv(RNE, FloatingPointLiteral(this), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest away'. Converts [divisor] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpdiv_rna(divisor: Expression<FloatingPointSort>) =
    FPDiv(RNA, FloatingPointLiteral(this), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward positive'. Converts [divisor] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpdiv_rtp(divisor: Expression<FloatingPointSort>) =
    FPDiv(RTP, FloatingPointLiteral(this), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward negative'. Converts [divisor] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpdiv_rtn(divisor: Expression<FloatingPointSort>) =
    FPDiv(RTN, FloatingPointLiteral(this), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward zero'. Converts [divisor] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpdiv_rtz(divisor: Expression<FloatingPointSort>) =
    FPDiv(RTZ, FloatingPointLiteral(this), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [divisor] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpdiv(divisor: () -> Expression<FloatingPointSort>) =
    FloatingPointLiteral(this) fpdiv_rne divisor()

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest even'. Converts [divisor] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpdiv_rne(divisor: () -> Expression<FloatingPointSort>) =
    FPDiv(RNE, FloatingPointLiteral(this), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest away'. Converts [divisor] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpdiv_rna(divisor: () -> Expression<FloatingPointSort>) =
    FPDiv(RNA, FloatingPointLiteral(this), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward positive'. Converts [divisor] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpdiv_rtp(divisor: () -> Expression<FloatingPointSort>) =
    FPDiv(RTP, FloatingPointLiteral(this), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward negative'. Converts [divisor] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpdiv_rtn(divisor: () -> Expression<FloatingPointSort>) =
    FPDiv(RTN, FloatingPointLiteral(this), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward zero'. Converts [divisor] from [Double] to
 * [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpdiv_rtz(divisor: () -> Expression<FloatingPointSort>) =
    FPDiv(RTZ, FloatingPointLiteral(this), divisor())

/**
 * Remainder operator for FPSort expressions: [this] - [divisor] * n, where n in Z is closest to
 * [this]/[divisor].
 */
infix fun Expression<FloatingPointSort>.fprem(divisor: Expression<FloatingPointSort>) =
    FPRem(this, divisor)

/**
 * Remainder operator for FPSort expressions: [this] - [divisor] * n, where n in Z is closest to
 * [this]/[divisor].
 */
infix fun Expression<FloatingPointSort>.fprem(divisor: () -> Expression<FloatingPointSort>) =
    FPRem(this, divisor())

/**
 * Remainder operator for FPSort expressions: [this] - [divisor] * n, where n in Z is closest to
 * [this]/[divisor].
 */
infix fun (() -> Expression<FloatingPointSort>).fprem(divisor: Expression<FloatingPointSort>) =
    FPRem(this(), divisor)

/**
 * Remainder operator for FPSort expressions: [this] - [divisor] * n, where n in Z is closest to
 * [this]/[divisor].
 */
infix fun (() -> Expression<FloatingPointSort>).fprem(
    divisor: () -> Expression<FloatingPointSort>
) = FPRem(this(), divisor())

/**
 * Remainder operator for FPSort expressions: [this] - [divisor] * n, where n in Z is closest to
 * [this]/[divisor].
 *
 * Converts [this] from [Float] to [FloatingPointLiteral] with sort (_ FloatingPoint 8 24).
 */
infix fun Float.fprem(divisor: Expression<FloatingPointSort>) =
    FPRem(FloatingPointLiteral(this), divisor)

/**
 * Remainder operator for FPSort expressions: [this] - [divisor] * n, where n in Z is closest to
 * [this]/[divisor].
 *
 * Converts [this] from [Float] to [FloatingPointLiteral] with sort (_ FloatingPoint 8 24).
 */
infix fun Float.fprem(divisor: () -> Expression<FloatingPointSort>) =
    FPRem(FloatingPointLiteral(this), divisor())

/**
 * Remainder operator for FPSort expressions: [this] - [divisor] * n, where n in Z is closest to
 * [this]/[divisor].
 *
 * Converts [divisor] from [Float] to [FloatingPointLiteral] with sort (_ FloatingPoint 8 24).
 */
infix fun Expression<FloatingPointSort>.fprem(divisor: Float) =
    FPRem(this, FloatingPointLiteral(divisor))

/**
 * Remainder operator for FPSort expressions: [this] - [divisor] * n, where n in Z is closest to
 * [this]/[divisor].
 *
 * Converts [divisor] from [Float] to [FloatingPointLiteral] with sort (_ FloatingPoint 8 24).
 */
infix fun (() -> Expression<FloatingPointSort>).fprem(divisor: Float) =
    FPRem(this(), FloatingPointLiteral(divisor))

/**
 * Remainder operator for FPSort expressions: [this] - [divisor] * n, where n in Z is closest to
 * [this]/[divisor].
 *
 * Converts [this] from [Double] to [FloatingPointLiteral] with sort (_ FloatingPoint 11 53).
 */
infix fun Double.fprem(divisor: Expression<FloatingPointSort>) =
    FPRem(FloatingPointLiteral(this), divisor)

/**
 * Remainder operator for FPSort expressions: [this] - [divisor] * n, where n in Z is closest to
 * [this]/[divisor].
 *
 * Converts [this] from [Double] to [FloatingPointLiteral] with sort (_ FloatingPoint 11 53).
 */
infix fun Double.fprem(divisor: () -> Expression<FloatingPointSort>) =
    FPRem(FloatingPointLiteral(this), divisor())

/**
 * Remainder operator for FPSort expressions: [this] - [divisor] * n, where n in Z is closest to
 * [this]/[divisor].
 *
 * Converts [divisor] from [Double] to [FloatingPointLiteral] with sort (_ FloatingPoint 11 53).
 */
infix fun Expression<FloatingPointSort>.fprem(divisor: Double) =
    FPRem(this, FloatingPointLiteral(divisor))

/**
 * Remainder operator for FPSort expressions: [this] - [divisor] * n, where n in Z is closest to
 * [this]/[divisor].
 *
 * Converts [divisor] from [Double] to [FloatingPointLiteral] with sort (_ FloatingPoint 11 53).
 */
infix fun (() -> Expression<FloatingPointSort>).fprem(divisor: Double) =
    FPRem(this(), FloatingPointLiteral(divisor))

/*
 * unary floating-point operations
 */

/** Square root operator for FPSort expressions. */
fun fpsqrt(
    roundingMode: Expression<RoundingModeSort> = RNE,
    block: () -> Expression<FloatingPointSort>,
) = FPSqrt(roundingMode, block())

/** Square root operator for FPSort expressions. */
fun fpsqrt(roundingMode: Expression<RoundingModeSort> = RNE, expr: Expression<FloatingPointSort>) =
    FPSqrt(roundingMode, expr)

/**
 * Square root operator for FPSort expressions.
 *
 * Converts [expr] from [Float] to [FloatingPointLiteral] with sort (_ FloatingPoint 8 24).
 */
fun fpsqrt(roundingMode: Expression<RoundingModeSort> = RNE, expr: Float) =
    FPSqrt(roundingMode, FloatingPointLiteral(expr))

/**
 * Square root operator for FPSort expressions.
 *
 * Converts [expr] from [Double] to [FloatingPointLiteral] with sort (_ FloatingPoint 11 53).
 */
fun fpsqrt(roundingMode: Expression<RoundingModeSort> = RNE, expr: Double) =
    FPSqrt(roundingMode, FloatingPointLiteral(expr))

/** Round to integral operator for FPSort expressions. */
fun fproundToIntegral(
    roundingMode: Expression<RoundingModeSort> = RNE,
    block: () -> Expression<FloatingPointSort>,
) = FPRoundToIntegral(roundingMode, block())

/** Round to integral operator for FPSort expressions. */
fun fproundToIntegral(
    roundingMode: Expression<RoundingModeSort> = RNE,
    expr: Expression<FloatingPointSort>,
) = FPRoundToIntegral(roundingMode, expr)

/**
 * Round to integral operator for FPSort expressions.
 *
 * Converts [expr] from [Float] to [FloatingPointLiteral] with sort (_ FloatingPoint 8 24).
 */
fun fproundToIntegral(roundingMode: Expression<RoundingModeSort> = RNE, expr: Float) =
    FPRoundToIntegral(roundingMode, FloatingPointLiteral(expr))

/**
 * Round to integral operator for FPSort expressions.
 *
 * Converts [expr] from [Double] to [FloatingPointLiteral] with sort (_ FloatingPoint 11 53).
 */
fun fproundToIntegral(roundingMode: Expression<RoundingModeSort> = RNE, expr: Double) =
    FPRoundToIntegral(roundingMode, FloatingPointLiteral(expr))

/*
 * floating-point comparison operators
 */

/** Min operator for FPSort expressions. */
fun fpmin(lhs: Expression<FloatingPointSort>, rhs: Expression<FloatingPointSort>) = FPMin(lhs, rhs)

/** Min operator for FPSort expressions. */
fun fpmin(lhs: Expression<FloatingPointSort>, rhs: () -> Expression<FloatingPointSort>) =
    FPMin(lhs, rhs())

/** Min operator for FPSort expressions. */
fun fpmin(lhs: () -> Expression<FloatingPointSort>, rhs: Expression<FloatingPointSort>) =
    FPMin(lhs(), rhs)

/** Min operator for FPSort expressions. */
fun fpmin(lhs: () -> Expression<FloatingPointSort>, rhs: () -> Expression<FloatingPointSort>) =
    FPMin(lhs(), rhs())

/**
 * Min operator for FPSort expressions.
 *
 * Converts [rhs] from [Float] to [FloatingPointLiteral] with sort (_ FloatingPoint 4 24).
 */
fun fpmin(lhs: Expression<FloatingPointSort>, rhs: Float) = FPMin(lhs, FloatingPointLiteral(rhs))

/**
 * Min operator for FPSort expressions.
 *
 * Converts [rhs] from [Double] to [FloatingPointLiteral] with sort (_ FloatingPoint 11 53).
 */
fun fpmin(lhs: Expression<FloatingPointSort>, rhs: Double) = FPMin(lhs, FloatingPointLiteral(rhs))

/**
 * Min operator for FPSort expressions.
 *
 * Converts [lhs] from [Float] to [FloatingPointLiteral] with sort (_ FloatingPoint 4 24).
 */
fun fpmin(lhs: Float, rhs: Expression<FloatingPointSort>) = FPMin(FloatingPointLiteral(lhs), rhs)

/**
 * Min operator for FPSort expressions.
 *
 * Converts [lhs] from [Double] to [FloatingPointLiteral] with sort (_ FloatingPoint 11 53).
 */
fun fpmin(lhs: Double, rhs: Expression<FloatingPointSort>) = FPMin(FloatingPointLiteral(lhs), rhs)

/** Max operator for FPSort expressions. */
fun fpmax(lhs: Expression<FloatingPointSort>, rhs: Expression<FloatingPointSort>) = FPMax(lhs, rhs)

/** Max operator for FPSort expressions. */
fun fpmax(lhs: Expression<FloatingPointSort>, rhs: () -> Expression<FloatingPointSort>) =
    FPMax(lhs, rhs())

/** Max operator for FPSort expressions. */
fun fpmax(lhs: () -> Expression<FloatingPointSort>, rhs: Expression<FloatingPointSort>) =
    FPMax(lhs(), rhs)

/** Max operator for FPSort expressions. */
fun fpmax(lhs: () -> Expression<FloatingPointSort>, rhs: () -> Expression<FloatingPointSort>) =
    FPMax(lhs(), rhs())

/**
 * Max operator for FPSort expressions.
 *
 * Converts [rhs] from [Float] to [FloatingPointLiteral] with sort (_ FloatingPoint 4 24).
 */
fun fpmax(lhs: Expression<FloatingPointSort>, rhs: Float) = FPMax(lhs, FloatingPointLiteral(rhs))

/**
 * Max operator for FPSort expressions.
 *
 * Converts [rhs] from [Double] to [FloatingPointLiteral] with sort (_ FloatingPoint 11 53).
 */
fun fpmax(lhs: Expression<FloatingPointSort>, rhs: Double) = FPMax(lhs, FloatingPointLiteral(rhs))

/**
 * Max operator for FPSort expressions.
 *
 * Converts [lhs] from [Float] to [FloatingPointLiteral] with sort (_ FloatingPoint 4 24).
 */
fun fpmax(lhs: Float, rhs: Expression<FloatingPointSort>) = FPMax(FloatingPointLiteral(lhs), rhs)

/**
 * Max operator for FPSort expressions.
 *
 * Converts [lhs] from [Double] to [FloatingPointLiteral] with sort (_ FloatingPoint 11 53).
 */
fun fpmax(lhs: Double, rhs: Expression<FloatingPointSort>) = FPMax(FloatingPointLiteral(lhs), rhs)

/** Less equals operator for FPSort expressions: [this] <= [rhs]. */
infix fun Expression<FloatingPointSort>.fpleq(rhs: Expression<FloatingPointSort>) = FPLeq(this, rhs)

/** Less than operator for FPSort expressions: [this] < [rhs]. */
infix fun Expression<FloatingPointSort>.fplt(rhs: Expression<FloatingPointSort>) = FPLt(this, rhs)

/** Greater equals operator for FPSort expressions: [this] >= [rhs]. */
infix fun Expression<FloatingPointSort>.fpgeq(rhs: Expression<FloatingPointSort>) = FPGeq(this, rhs)

/** Greater than operator for FPSort expressions: [this] > [rhs]. */
infix fun Expression<FloatingPointSort>.fpgt(rhs: Expression<FloatingPointSort>) = FPGt(this, rhs)

/** Equals operator for FPSort expressions: [this] = [rhs]. */
infix fun Expression<FloatingPointSort>.fpeq(rhs: Expression<FloatingPointSort>) = FPEq(this, rhs)

/** Less equals operator for FPSort expressions: [this] <= [rhs]. */
infix fun Expression<FloatingPointSort>.fpleq(rhs: () -> Expression<FloatingPointSort>) =
    FPLeq(this, rhs())

/** Less than operator for FPSort expressions: [this] < [rhs]. */
infix fun Expression<FloatingPointSort>.fplt(rhs: () -> Expression<FloatingPointSort>) =
    FPLt(this, rhs())

/** Greater equals operator for FPSort expressions: [this] >= [rhs]. */
infix fun Expression<FloatingPointSort>.fpgeq(rhs: () -> Expression<FloatingPointSort>) =
    FPGeq(this, rhs())

/** Greater than operator for FPSort expressions: [this] > [rhs]. */
infix fun Expression<FloatingPointSort>.fpgt(rhs: () -> Expression<FloatingPointSort>) =
    FPGt(this, rhs())

/** Equals operator for FPSort expressions: [this] = [rhs]. */
infix fun Expression<FloatingPointSort>.fpeq(rhs: () -> Expression<FloatingPointSort>) =
    FPEq(this, rhs())

/** Less equals operator for FPSort expressions: [this] <= [rhs]. */
@JvmName("fpleq_expr")
infix fun (() -> Expression<FloatingPointSort>).fpleq(rhs: Expression<FloatingPointSort>) =
    FPLeq(this(), rhs)

/** Less than operator for FPSort expressions: [this] < [rhs]. */
@JvmName("fplt_expr")
infix fun (() -> Expression<FloatingPointSort>).fplt(rhs: Expression<FloatingPointSort>) =
    FPLt(this(), rhs)

/** Greater equals operator for FPSort expressions: [this] >= [rhs]. */
@JvmName("fpgeq_expr")
infix fun (() -> Expression<FloatingPointSort>).fpgeq(rhs: Expression<FloatingPointSort>) =
    FPGeq(this(), rhs)

/** Greater than operator for FPSort expressions: [this] > [rhs]. */
@JvmName("fpgt_expr")
infix fun (() -> Expression<FloatingPointSort>).fpgt(rhs: Expression<FloatingPointSort>) =
    FPGt(this(), rhs)

/** Equals operator for FPSort expressions: [this] = [rhs]. */
@JvmName("fpeq_expr")
infix fun (() -> Expression<FloatingPointSort>).fpeq(rhs: Expression<FloatingPointSort>) =
    FPEq(this(), rhs)

/** Less equals operator for FPSort expressions: [this] <= [rhs]. */
@JvmName("fpleq_lambda")
infix fun (() -> Expression<FloatingPointSort>).fpleq(rhs: () -> Expression<FloatingPointSort>) =
    FPLeq(this(), rhs())

/** Less than operator for FPSort expressions: [this] < [rhs]. */
@JvmName("fplt_lambda")
infix fun (() -> Expression<FloatingPointSort>).fplt(rhs: () -> Expression<FloatingPointSort>) =
    FPLt(this(), rhs())

/** Greater equals operator for FPSort expressions: [this] >= [rhs]. */
@JvmName("fpgeq_lambda")
infix fun (() -> Expression<FloatingPointSort>).fpgeq(rhs: () -> Expression<FloatingPointSort>) =
    FPGeq(this(), rhs())

/** Greater than operator for FPSort expressions: [this] > [rhs]. */
@JvmName("fpgt_lambda")
infix fun (() -> Expression<FloatingPointSort>).fpgt(rhs: () -> Expression<FloatingPointSort>) =
    FPGt(this(), rhs())

/** Equals operator for FPSort expressions: [this] = [rhs]. */
@JvmName("fpeq_lambda")
infix fun (() -> Expression<FloatingPointSort>).fpeq(rhs: () -> Expression<FloatingPointSort>) =
    FPEq(this(), rhs())

/** Less equals operator for FPSort expressions: [this] <= [rhs]. */
infix fun FPLeq.fpleq(rhs: Expression<FloatingPointSort>) = FPLeq(this.children + rhs)

/** Less than operator for FPSort expressions: [this] < [rhs]. */
infix fun FPLt.fplt(rhs: Expression<FloatingPointSort>) = FPLt(this.children + rhs)

/** Greater equals operator for FPSort expressions: [this] >= [rhs]. */
infix fun FPGeq.fpgeq(rhs: Expression<FloatingPointSort>) = FPGeq(this.children + rhs)

/** Greater than operator for FPSort expressions: [this] > [rhs]. */
infix fun FPGt.fpgt(rhs: Expression<FloatingPointSort>) = FPGt(this.children + rhs)

/** Equals operator for FPSort expressions: [this] = [rhs]. */
infix fun FPEq.fpeq(rhs: Expression<FloatingPointSort>) = FPEq(this.children + rhs)

/** Less equals operator for FPSort expressions: [this] <= [rhs]. */
infix fun FPLeq.fpleq(rhs: () -> Expression<FloatingPointSort>) = FPLeq(this.children + rhs())

/** Less than operator for FPSort expressions: [this] < [rhs]. */
infix fun FPLt.fplt(rhs: () -> Expression<FloatingPointSort>) = FPLt(this.children + rhs())

/** Greater equals operator for FPSort expressions: [this] >= [rhs]. */
infix fun FPGeq.fpgeq(rhs: () -> Expression<FloatingPointSort>) = FPGeq(this.children + rhs())

/** Greater than operator for FPSort expressions: [this] > [rhs]. */
infix fun FPGt.fpgt(rhs: () -> Expression<FloatingPointSort>) = FPGt(this.children + rhs())

/** Equals operator for FPSort expressions: [this] = [rhs]. */
infix fun FPEq.fpeq(rhs: () -> Expression<FloatingPointSort>) = FPEq(this.children + rhs())

/** Less equals operator for FPSort expressions: [this] <= [rhs]. */
infix fun (() -> FPLeq).fpleq(rhs: Expression<FloatingPointSort>) = FPLeq(this().children + rhs)

/** Less than operator for FPSort expressions: [this] < [rhs]. */
infix fun (() -> FPLt).fplt(rhs: Expression<FloatingPointSort>) = FPLt(this().children + rhs)

/** Greater equals operator for FPSort expressions: [this] >= [rhs]. */
infix fun (() -> FPGeq).fpgeq(rhs: Expression<FloatingPointSort>) = FPGeq(this().children + rhs)

/** Greater than operator for FPSort expressions: [this] > [rhs]. */
infix fun (() -> FPGt).fpgt(rhs: Expression<FloatingPointSort>) = FPGt(this().children + rhs)

/** Equals operator for FPSort expressions: [this] = [rhs]. */
infix fun (() -> FPEq).fpeq(rhs: Expression<FloatingPointSort>) = FPEq(this().children + rhs)

/** Less equals operator for FPSort expressions: [this] <= [rhs]. */
infix fun (() -> FPLeq).fpleq(rhs: () -> Expression<FloatingPointSort>) =
    FPLeq(this().children + rhs())

/** Less than operator for FPSort expressions: [this] < [rhs]. */
infix fun (() -> FPLt).fplt(rhs: () -> Expression<FloatingPointSort>) =
    FPLt(this().children + rhs())

/** Greater equals operator for FPSort expressions: [this] >= [rhs]. */
infix fun (() -> FPGeq).fpgeq(rhs: () -> Expression<FloatingPointSort>) =
    FPGeq(this().children + rhs())

/** Greater than operator for FPSort expressions: [this] > [rhs]. */
infix fun (() -> FPGt).fpgt(rhs: () -> Expression<FloatingPointSort>) =
    FPGt(this().children + rhs())

/** Equals operator for FPSort expressions: [this] = [rhs]. */
infix fun (() -> FPEq).fpeq(rhs: () -> Expression<FloatingPointSort>) =
    FPEq(this().children + rhs())

/**
 * Less equals operator for FPSort expressions: [this] <= [rhs].
 *
 * Converts [rhs] from [Float] to [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Expression<FloatingPointSort>.fpleq(rhs: Float) = FPLeq(this, FloatingPointLiteral(rhs))

/**
 * Less equals operator for FPSort expressions: [this] <= [rhs].
 *
 * Converts [rhs] from [Double] to [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Expression<FloatingPointSort>.fpleq(rhs: Double) = FPLeq(this, FloatingPointLiteral(rhs))

/**
 * Less than operator for FPSort expressions: [this] < [rhs].
 *
 * Converts [rhs] from [Float] to [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Expression<FloatingPointSort>.fplt(rhs: Float) = FPLt(this, FloatingPointLiteral(rhs))

/**
 * Less than operator for FPSort expressions: [this] < [rhs].
 *
 * Converts [rhs] from [Double] to [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Expression<FloatingPointSort>.fplt(rhs: Double) = FPLt(this, FloatingPointLiteral(rhs))

/**
 * Greater equals operator for FPSort expressions: [this] >= [rhs].
 *
 * Converts [rhs] from [Float] to [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Expression<FloatingPointSort>.fpgeq(rhs: Float) = FPGeq(this, FloatingPointLiteral(rhs))

/**
 * Greater equals operator for FPSort expressions: [this] >= [rhs].
 *
 * Converts [rhs] from [Double] to [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Expression<FloatingPointSort>.fpgeq(rhs: Double) = FPGeq(this, FloatingPointLiteral(rhs))

/**
 * Greater than operator for FPSort expressions: [this] > [rhs].
 *
 * Converts [rhs] from [Float] to [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Expression<FloatingPointSort>.fpgt(rhs: Float) = FPGt(this, FloatingPointLiteral(rhs))

/**
 * Greater than operator for FPSort expressions: [this] > [rhs].
 *
 * Converts [rhs] from [Double] to [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Expression<FloatingPointSort>.fpgt(rhs: Double) = FPGt(this, FloatingPointLiteral(rhs))

/**
 * Equals operator for FPSort expressions: [this] = [rhs].
 *
 * Converts [rhs] from [Float] to [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Expression<FloatingPointSort>.fpeq(rhs: Float) = FPEq(this, FloatingPointLiteral(rhs))

/**
 * Equals operator for FPSort expressions: [this] = [rhs].
 *
 * Converts [rhs] from [Double] to [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Expression<FloatingPointSort>.fpeq(rhs: Double) = FPEq(this, FloatingPointLiteral(rhs))

/**
 * Less equals operator for FPSort expressions: [this] <= [rhs].
 *
 * Converts [rhs] from [Float] to [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun (() -> Expression<FloatingPointSort>).fpleq(rhs: Float) =
    FPLeq(this(), FloatingPointLiteral(rhs))

/**
 * Less equals operator for FPSort expressions: [this] <= [rhs].
 *
 * Converts [rhs] from [Double] to [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun (() -> Expression<FloatingPointSort>).fpleq(rhs: Double) =
    FPLeq(this(), FloatingPointLiteral(rhs))

/**
 * Less than operator for FPSort expressions: [this] < [rhs].
 *
 * Converts [rhs] from [Float] to [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun (() -> Expression<FloatingPointSort>).fplt(rhs: Float) =
    FPLt(this(), FloatingPointLiteral(rhs))

/**
 * Less than operator for FPSort expressions: [this] < [rhs].
 *
 * Converts [rhs] from [Double] to [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun (() -> Expression<FloatingPointSort>).fplt(rhs: Double) =
    FPLt(this(), FloatingPointLiteral(rhs))

/**
 * Greater equals operator for FPSort expressions: [this] >= [rhs].
 *
 * Converts [rhs] from [Float] to [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun (() -> Expression<FloatingPointSort>).fpgeq(rhs: Float) =
    FPGeq(this(), FloatingPointLiteral(rhs))

/**
 * Greater equals operator for FPSort expressions: [this] >= [rhs].
 *
 * Converts [rhs] from [Double] to [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun (() -> Expression<FloatingPointSort>).fpgeq(rhs: Double) =
    FPGeq(this(), FloatingPointLiteral(rhs))

/**
 * Greater than operator for FPSort expressions: [this] > [rhs].
 *
 * Converts [rhs] from [Float] to [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun (() -> Expression<FloatingPointSort>).fpgt(rhs: Float) =
    FPGt(this(), FloatingPointLiteral(rhs))

/**
 * Greater than operator for FPSort expressions: [this] > [rhs].
 *
 * Converts [rhs] from [Double] to [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun (() -> Expression<FloatingPointSort>).fpgt(rhs: Double) =
    FPGt(this(), FloatingPointLiteral(rhs))

/**
 * Equals operator for FPSort expressions: [this] = [rhs].
 *
 * Converts [rhs] from [Float] to [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun (() -> Expression<FloatingPointSort>).fpeq(rhs: Float) =
    FPEq(this(), FloatingPointLiteral(rhs))

/**
 * Equals operator for FPSort expressions: [this] = [rhs].
 *
 * Converts [rhs] from [Double] to [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun (() -> Expression<FloatingPointSort>).fpeq(rhs: Double) =
    FPEq(this(), FloatingPointLiteral(rhs))

/**
 * Less equals operator for FPSort expressions: [this] <= [rhs].
 *
 * Converts [rhs] from [Float] to [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Float.fpleq(rhs: Expression<FloatingPointSort>) = FPLeq(FloatingPointLiteral(this), rhs)

/**
 * Less equals operator for FPSort expressions: [this] <= [rhs].
 *
 * Converts [rhs] from [Double] to [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Double.fpleq(rhs: Expression<FloatingPointSort>) = FPLeq(FloatingPointLiteral(this), rhs)

/**
 * Less than operator for FPSort expressions: [this] < [rhs].
 *
 * Converts [rhs] from [Float] to [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Float.fplt(rhs: Expression<FloatingPointSort>) = FPLt(FloatingPointLiteral(this), rhs)

/**
 * Less than operator for FPSort expressions: [this] < [rhs].
 *
 * Converts [rhs] from [Double] to [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Double.fplt(rhs: Expression<FloatingPointSort>) = FPLt(FloatingPointLiteral(this), rhs)

/**
 * Greater equals operator for FPSort expressions: [this] >= [rhs].
 *
 * Converts [rhs] from [Float] to [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Float.fpgeq(rhs: Expression<FloatingPointSort>) = FPGeq(FloatingPointLiteral(this), rhs)

/**
 * Greater equals operator for FPSort expressions: [this] >= [rhs].
 *
 * Converts [rhs] from [Double] to [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Double.fpgeq(rhs: Expression<FloatingPointSort>) = FPGeq(FloatingPointLiteral(this), rhs)

/**
 * Greater than operator for FPSort expressions: [this] > [rhs].
 *
 * Converts [rhs] from [Float] to [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Float.fpgt(rhs: Expression<FloatingPointSort>) = FPGt(FloatingPointLiteral(this), rhs)

/**
 * Greater than operator for FPSort expressions: [this] > [rhs].
 *
 * Converts [rhs] from [Double] to [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Double.fpgt(rhs: Expression<FloatingPointSort>) = FPGt(FloatingPointLiteral(this), rhs)

/**
 * Equals operator for FPSort expressions: [this] = [rhs].
 *
 * Converts [rhs] from [Float] to [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Float.fpeq(rhs: Expression<FloatingPointSort>) = FPEq(FloatingPointLiteral(this), rhs)

/**
 * Equals operator for FPSort expressions: [this] = [rhs].
 *
 * Converts [rhs] from [Double] to [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Double.fpeq(rhs: Expression<FloatingPointSort>) = FPEq(FloatingPointLiteral(this), rhs)

/**
 * Less equals operator for FPSort expressions: [this] <= [rhs].
 *
 * Converts [rhs] from [Float] to [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Float.fpleq(rhs: () -> Expression<FloatingPointSort>) =
    FPLeq(FloatingPointLiteral(this), rhs())

/**
 * Less equals operator for FPSort expressions: [this] <= [rhs].
 *
 * Converts [rhs] from [Double] to [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Double.fpleq(rhs: () -> Expression<FloatingPointSort>) =
    FPLeq(FloatingPointLiteral(this), rhs())

/**
 * Less than operator for FPSort expressions: [this] < [rhs].
 *
 * Converts [rhs] from [Float] to [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Float.fplt(rhs: () -> Expression<FloatingPointSort>) =
    FPLt(FloatingPointLiteral(this), rhs())

/**
 * Less than operator for FPSort expressions: [this] < [rhs].
 *
 * Converts [rhs] from [Double] to [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Double.fplt(rhs: () -> Expression<FloatingPointSort>) =
    FPLt(FloatingPointLiteral(this), rhs())

/**
 * Greater equals operator for FPSort expressions: [this] >= [rhs].
 *
 * Converts [rhs] from [Float] to [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Float.fpgeq(rhs: () -> Expression<FloatingPointSort>) =
    FPGeq(FloatingPointLiteral(this), rhs())

/**
 * Greater equals operator for FPSort expressions: [this] >= [rhs].
 *
 * Converts [rhs] from [Double] to [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Double.fpgeq(rhs: () -> Expression<FloatingPointSort>) =
    FPGeq(FloatingPointLiteral(this), rhs())

/**
 * Greater than operator for FPSort expressions: [this] > [rhs].
 *
 * Converts [rhs] from [Float] to [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Float.fpgt(rhs: () -> Expression<FloatingPointSort>) =
    FPGt(FloatingPointLiteral(this), rhs())

/**
 * Greater than operator for FPSort expressions: [this] > [rhs].
 *
 * Converts [rhs] from [Double] to [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Double.fpgt(rhs: () -> Expression<FloatingPointSort>) =
    FPGt(FloatingPointLiteral(this), rhs())

/**
 * Equals operator for FPSort expressions: [this] = [rhs].
 *
 * Converts [rhs] from [Float] to [FloatingPointLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Float.fpeq(rhs: () -> Expression<FloatingPointSort>) =
    FPEq(FloatingPointLiteral(this), rhs())

/**
 * Equals operator for FPSort expressions: [this] = [rhs].
 *
 * Converts [rhs] from [Double] to [FloatingPointLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Double.fpeq(rhs: () -> Expression<FloatingPointSort>) =
    FPEq(FloatingPointLiteral(this), rhs())

/*
 * floating-point conversion operations
 */

/**
 * Conversion operator from single bitstring representation in IEEE 754-2008 interchange format to
 * floating point.
 */
@JvmName("BVToFP")
fun toFP(eb: Int, sb: Int, block: () -> Expression<BitVecSort>) = BitVecToFP(block(), eb, sb)

/**
 * Conversion operator from single bitstring representation in IEEE 754-2008 interchange format to
 * floating point.
 */
@JvmName("BVToFP")
fun toFP(eb: Int, sb: Int, expr: Expression<BitVecSort>) = BitVecToFP(expr, eb, sb)

/**
 * Conversion operator from single bitstring representation in IEEE 754-2008 interchange format to
 * floating point.
 */
fun Expression<BitVecSort>.toFP(eb: Int, sb: Int) = BitVecToFP(this, eb, sb)

/**
 * Conversion operator from single bitstring representation in IEEE 754-2008 interchange format to
 * floating point.
 */
fun Expression<BitVecSort>.toFP(sort: FloatingPointSort) = BitVecToFP(this, sort)

/** Conversion operator from another floating point sort to floating point sort. */
@JvmName("FPToFP")
fun toFP(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingModeSort> = RNE,
    block: () -> Expression<FloatingPointSort>,
) = FPToFP(roundingMode, block(), eb, sb)

/** Conversion operator from another floating point sort to floating point sort. */
@JvmName("FPToFP")
fun toFP(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingModeSort> = RNE,
    expr: Expression<FloatingPointSort>,
) = FPToFP(roundingMode, expr, eb, sb)

/** Conversion operator from another floating point sort to floating point sort. */
fun Expression<FloatingPointSort>.toFP(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingModeSort> = RNE,
) = FPToFP(roundingMode, this, eb, sb)

/** Conversion operator from another floating point sort to floating point sort. */
fun Expression<FloatingPointSort>.toFP(
    sort: FloatingPointSort,
    roundingMode: Expression<RoundingModeSort> = RNE,
) = FPToFP(roundingMode, this, sort)

/** Conversion operator from real sort to floating point sort. */
@JvmName("RealToFP")
fun toFP(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingModeSort> = RNE,
    block: () -> Expression<RealSort>,
) = RealToFP(roundingMode, block(), eb, sb)

/** Conversion operator from real sort to floating point sort. */
@JvmName("RealToFP")
fun toFP(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingModeSort> = RNE,
    expr: Expression<RealSort>,
) = RealToFP(roundingMode, expr, eb, sb)

/** Conversion operator from real sort to floating point sort. */
fun Expression<RealSort>.toFP(eb: Int, sb: Int, roundingMode: Expression<RoundingModeSort> = RNE) =
    RealToFP(roundingMode, this, eb, sb)

/** Conversion operator from real sort to floating point sort. */
fun Expression<RealSort>.toFP(
    sort: FloatingPointSort,
    roundingMode: Expression<RoundingModeSort> = RNE,
) = RealToFP(roundingMode, this, sort)

/**
 * Conversion operator from signed machine integer, represented as a 2's complement bit vector to
 * floating point.
 */
@JvmName("SBVToFP")
fun toFPSigned(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingModeSort> = RNE,
    block: () -> Expression<BitVecSort>,
) = SBitVecToFP(roundingMode, block(), eb, sb)

/**
 * Conversion operator from signed machine integer, represented as a 2's complement bit vector to
 * floating point.
 */
@JvmName("SBVToFP")
fun toFPSigned(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingModeSort> = RNE,
    expr: Expression<BitVecSort>,
) = SBitVecToFP(roundingMode, expr, eb, sb)

/**
 * Conversion operator from signed machine integer, represented as a 2's complement bit vector to
 * floating point.
 */
fun Expression<BitVecSort>.toFPSigned(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingModeSort>,
) = SBitVecToFP(roundingMode, this, eb, sb)

/**
 * Conversion operator from signed machine integer, represented as a 2's complement bit vector to
 * floating point.
 */
fun Expression<BitVecSort>.toFPSigned(
    sort: FloatingPointSort,
    roundingMode: Expression<RoundingModeSort>,
) = SBitVecToFP(roundingMode, this, sort)

/**
 * Conversion operator from unsigned machine integer, represented as a 2's complement bit vector to
 * floating point.
 */
@JvmName("UBVToFP")
fun toFPUnsigned(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingModeSort> = RNE,
    block: () -> Expression<BitVecSort>,
) = UBitVecToFP(roundingMode, block(), eb, sb)

/**
 * Conversion operator from unsigned machine integer, represented as a 2's complement bit vector to
 * floating point.
 */
@JvmName("UBVToFP")
fun toFPUnsigned(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingModeSort> = RNE,
    expr: Expression<BitVecSort>,
) = UBitVecToFP(roundingMode, expr, eb, sb)

/**
 * Conversion operator from unsigned machine integer, represented as a 2's complement bit vector to
 * floating point.
 */
fun Expression<BitVecSort>.toFPUnsigned(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingModeSort>,
) = UBitVecToFP(roundingMode, this, eb, sb)

/**
 * Conversion operator from unsigned machine integer, represented as a 2's complement bit vector to
 * floating point.
 */
fun Expression<BitVecSort>.toFPUnsigned(
    sort: FloatingPointSort,
    roundingMode: Expression<RoundingModeSort>,
) = UBitVecToFP(roundingMode, this, sort)

/**
 * Conversion operator to unsigned machine integer, represented as a bit vector (_ BitVec [bits]).
 */
fun toUBV(
    bits: Int,
    roundingMode: Expression<RoundingModeSort> = RNE,
    block: () -> Expression<FloatingPointSort>,
) = FPToUBitVec(roundingMode, block(), bits)

/**
 * Conversion operator to unsigned machine integer, represented as a bit vector (_ BitVec [bits]).
 */
fun toUBV(
    bits: Int,
    roundingMode: Expression<RoundingModeSort> = RNE,
    expr: Expression<FloatingPointSort>,
) = FPToUBitVec(roundingMode, expr, bits)

/**
 * Conversion operator to unsigned machine integer, represented as a bit vector (_ BitVec [bits]).
 */
fun Expression<FloatingPointSort>.toUBV(
    bits: Int,
    roundingMode: Expression<RoundingModeSort> = RNE,
) = FPToUBitVec(roundingMode, this, bits)

/** Conversion operator to unsigned machine integer, represented as a bit vector [sort]. */
fun Expression<FloatingPointSort>.toUBV(
    sort: BitVecSort,
    roundingMode: Expression<RoundingModeSort> = RNE,
) = FPToUBitVec(roundingMode, this, sort.bits)

/**
 * Conversion operator to signed machine integer, represented as a 2's complement bit vector (_
 * BitVec [bits]).
 */
fun toSBV(
    bits: Int,
    roundingMode: Expression<RoundingModeSort> = RNE,
    block: () -> Expression<FloatingPointSort>,
) = FPToSBitVec(roundingMode, block(), bits)

/**
 * Conversion operator to signed machine integer, represented as a 2's complement bit vector (_
 * BitVec [bits]).
 */
fun toSBV(
    bits: Int,
    roundingMode: Expression<RoundingModeSort> = RNE,
    expr: Expression<FloatingPointSort>,
) = FPToSBitVec(roundingMode, expr, bits)

/**
 * Conversion operator to signed machine integer, represented as a 2's complement bit vector (_
 * BitVec [bits]).
 */
fun Expression<FloatingPointSort>.toSBV(
    bits: Int,
    roundingMode: Expression<RoundingModeSort> = RNE,
) = FPToSBitVec(roundingMode, this, bits)

/**
 * Conversion operator to signed machine integer, represented as a 2's complement bit vector (_
 * BitVec [sort.bits]).
 */
fun Expression<FloatingPointSort>.toSBV(
    sort: BitVecSort,
    roundingMode: Expression<RoundingModeSort> = RNE,
) = FPToSBitVec(roundingMode, this, sort.bits)

/** Conversion operator to real sort. */
fun toReal(block: () -> Expression<FloatingPointSort>) = FPToReal(block())

/** Conversion operator to real sort. */
@JvmName("toReal1") fun toReal(expr: Expression<FloatingPointSort>) = FPToReal(expr)

/** Conversion operator to real sort. */
@JvmName("toReal2") fun Expression<FloatingPointSort>.toReal() = FPToReal(this)

/*
 * fpfma
 */

/**
 * Fused multiplication addition operator ([multiplier] * multiplicand + summand) for FPSort
 * expressions. Must be followed by [FPFMA1.mul] and [FPFMA2.add].
 *
 * @param roundingMode: floating point rounding mode.
 */
@JvmName("fpfmaFPSortExpr")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
fun fpfma(
    roundingMode: Expression<RoundingModeSort> = RNE,
    multiplier: () -> Expression<FloatingPointSort>,
) = FPFMA1(roundingMode, multiplier())

/**
 * Fused multiplication addition operator ([multiplier] * multiplicand + summand) for FPSort
 * expressions. Must be followed by [FPFMA1.mul] and [FPFMA2.add].
 *
 * @param roundingMode: floating point rounding mode.
 */
@JvmName("fpfmaFloat")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
fun fpfma(roundingMode: Expression<RoundingModeSort> = RNE, multiplier: () -> Float) =
    FPFMA1(roundingMode, FloatingPointLiteral(multiplier()))

/**
 * Fused multiplication addition operator ([multiplier] * multiplicand + summand) for FPSort
 * expressions. Must be followed by [FPFMA1.mul] and [FPFMA2.add].
 *
 * @param roundingMode: floating point rounding mode.
 */
@JvmName("fpfmaDouble")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
fun fpfma(roundingMode: Expression<RoundingModeSort> = RNE, multiplier: () -> Double) =
    FPFMA1(roundingMode, FloatingPointLiteral(multiplier()))

/**
 * Fused multiplication addition operator ([multiplier] * multiplicand + summand) for FPSort
 * expressions. Must be followed by [FPFMA1.mul] and [FPFMA2.add].
 *
 * @param roundingMode: floating point rounding mode.
 */
fun fpfma(
    roundingMode: Expression<RoundingModeSort> = RNE,
    multiplier: Expression<FloatingPointSort>,
) = FPFMA1(roundingMode, multiplier)

/**
 * Fused multiplication addition operator ([multiplier] * multiplicand + summand) for FPSort
 * expressions. Must be followed by [FPFMA1.mul] and [FPFMA2.add].
 *
 * @param roundingMode: floating point rounding mode.
 */
fun fpfma(roundingMode: Expression<RoundingModeSort> = RNE, multiplier: Float) =
    FPFMA1(roundingMode, FloatingPointLiteral(multiplier))

/**
 * Fused multiplication addition operator ([multiplier] * multiplicand + summand) for FPSort
 * expressions. Must be followed by [FPFMA1.mul] and [FPFMA2.add].
 *
 * @param roundingMode: floating point rounding mode.
 */
fun fpfma(roundingMode: Expression<RoundingModeSort> = RNE, multiplier: Double) =
    FPFMA1(roundingMode, FloatingPointLiteral(multiplier))

/**
 * Multiplication stage of fp.fma.
 *
 * Must be followed by [FPFMA2].
 */
class FPFMA1(
    val roundingMode: Expression<RoundingModeSort>,
    val multiplier: Expression<FloatingPointSort>,
) {

  /**
   * Fused multiplication addition operator (multiplier * [multiplicand] + summand) for FPSort
   * expressions.
   *
   * Must be followed by [FPFMA2.add].
   */
  infix fun mul(multiplicand: Expression<FloatingPointSort>) =
      FPFMA2(roundingMode, multiplier, multiplicand)

  /**
   * Fused multiplication addition operator (multiplier * [multiplicand] + summand) for FPSort
   * expressions.
   *
   * Must be followed by [FPFMA2.add].
   */
  infix fun mul(multiplicand: Float) =
      FPFMA2(roundingMode, multiplier, FloatingPointLiteral(multiplicand))

  /**
   * Fused multiplication addition operator (multiplier * [multiplicand] + summand) for FPSort
   * expressions.
   *
   * Must be followed by [FPFMA2.add].
   */
  infix fun mul(multiplicand: Double) =
      FPFMA2(roundingMode, multiplier, FloatingPointLiteral(multiplicand))

  /**
   * Fused multiplication addition operator (multiplier * [multiplicand] + summand) for FPSort
   * expressions.
   *
   * Must be followed by [FPFMA2.add].
   */
  @JvmName("mulFPSortExpr")
  @OptIn(ExperimentalTypeInference::class)
  @OverloadResolutionByLambdaReturnType
  infix fun mul(multiplicand: () -> Expression<FloatingPointSort>) =
      FPFMA2(roundingMode, multiplier, multiplicand())

  /**
   * Fused multiplication addition operator (multiplier * [multiplicand] + summand) for FPSort
   * expressions.
   *
   * Must be followed by [FPFMA2.add].
   */
  @JvmName("mulFloat")
  @OptIn(ExperimentalTypeInference::class)
  @OverloadResolutionByLambdaReturnType
  infix fun mul(multiplicand: () -> Float) =
      FPFMA2(roundingMode, multiplier, FloatingPointLiteral(multiplicand()))

  /**
   * Fused multiplication addition operator (multiplier * [multiplicand] + summand) for FPSort
   * expressions.
   *
   * Must be followed by [FPFMA2.add].
   */
  @JvmName("mulDouble")
  @OptIn(ExperimentalTypeInference::class)
  @OverloadResolutionByLambdaReturnType
  infix fun mul(multiplicand: () -> Double) =
      FPFMA2(roundingMode, multiplier, FloatingPointLiteral(multiplicand()))
}

/** Addition stage of fp.fma. */
class FPFMA2(
    val roundingMode: Expression<RoundingModeSort>,
    val multiplier: Expression<FloatingPointSort>,
    val multiplicand: Expression<FloatingPointSort>,
) {

  /**
   * Fused multiplication addition operator (multiplier * multiplicand + [summand]) for FPSort
   * expressions.
   */
  infix fun add(summand: Expression<FloatingPointSort>) =
      FPFma(roundingMode, multiplier, multiplicand, summand)

  /**
   * Fused multiplication addition operator (multiplier * multiplicand + [summand]) for FPSort
   * expressions.
   */
  infix fun add(summand: Float) =
      FPFma(roundingMode, multiplier, multiplicand, FloatingPointLiteral(summand))

  /**
   * Fused multiplication addition operator (multiplier * multiplicand + [summand]) for FPSort
   * expressions.
   */
  infix fun add(summand: Double) =
      FPFma(roundingMode, multiplier, multiplicand, FloatingPointLiteral(summand))

  /**
   * Fused multiplication addition operator (multiplier * multiplicand + [summand]) for FPSort
   * expressions.
   */
  @JvmName("addFPExpr")
  @OptIn(ExperimentalTypeInference::class)
  @OverloadResolutionByLambdaReturnType
  infix fun add(summand: () -> Expression<FloatingPointSort>) =
      FPFma(roundingMode, multiplier, multiplicand, summand())

  /**
   * Fused multiplication addition operator (multiplier * multiplicand + [summand]) for FPSort
   * expressions.
   */
  @JvmName("addFloat")
  @OptIn(ExperimentalTypeInference::class)
  @OverloadResolutionByLambdaReturnType
  infix fun add(summand: () -> Float) =
      FPFma(roundingMode, multiplier, multiplicand, FloatingPointLiteral(summand()))

  /**
   * Fused multiplication addition operator (multiplier * multiplicand + [summand]) for FPSort
   * expressions.
   */
  @JvmName("addDouble")
  @OptIn(ExperimentalTypeInference::class)
  @OverloadResolutionByLambdaReturnType
  infix fun add(summand: () -> Double) =
      FPFma(roundingMode, multiplier, multiplicand, FloatingPointLiteral(summand()))
}

/** Implements floating point isNormal operation. */
fun isNormal(expr: Expression<FloatingPointSort>) = FPIsNormal(expr)

/** Implements floating point isNormal operation. */
fun isNormal(expr: Float) = FPIsNormal(FloatingPointLiteral(expr))

/** Implements floating point isNormal operation. */
fun isNormal(expr: Double) = FPIsNormal(FloatingPointLiteral(expr))

/** Implements floating point isNormal operation. */
@JvmName("isNormalFPExpr")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
fun isNormal(block: () -> Expression<FloatingPointSort>) = FPIsNormal(block())

/** Implements floating point isNormal operation. */
@JvmName("isNormalFloat")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
fun isNormal(expr: () -> Float) = FPIsNormal(FloatingPointLiteral(expr()))

/** Implements floating point isNormal operation. */
@JvmName("isNormalDouble")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
fun isNormal(expr: () -> Double) = FPIsNormal(FloatingPointLiteral(expr()))

/** Implements floating point isSubnormal operation. */
fun isSubnormal(expr: Expression<FloatingPointSort>) = FPIsSubnormal(expr)

/** Implements floating point isNormal operation. */
fun isSubnormal(expr: Float) = FPIsSubnormal(FloatingPointLiteral(expr))

/** Implements floating point isNormal operation. */
fun isSubnormal(expr: Double) = FPIsSubnormal(FloatingPointLiteral(expr))

/** Implements floating point isSubnormal operation. */
@JvmName("isSubnormalFPExpr")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
fun isSubnormal(block: () -> Expression<FloatingPointSort>) = FPIsSubnormal(block())

/** Implements floating point isNormal operation. */
@JvmName("isSubnormalFloat")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
fun isSubnormal(expr: () -> Float) = FPIsSubnormal(FloatingPointLiteral(expr()))

/** Implements floating point isNormal operation. */
@JvmName("isSubnormalDouble")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
fun isSubnormal(expr: () -> Double) = FPIsSubnormal(FloatingPointLiteral(expr()))

/** Implements floating point isZero operation. */
fun isZero(expr: Expression<FloatingPointSort>) = FPIsZero(expr)

/** Implements floating point isNormal operation. */
fun isZero(expr: Float) = FPIsZero(FloatingPointLiteral(expr))

/** Implements floating point isNormal operation. */
fun isZero(expr: Double) = FPIsZero(FloatingPointLiteral(expr))

/** Implements floating point isZero operation. */
@JvmName("isZeroFPExpr")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
fun isZero(block: () -> Expression<FloatingPointSort>) = FPIsZero(block())

/** Implements floating point isNormal operation. */
@JvmName("isZeroFloat")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
fun isZero(expr: () -> Float) = FPIsZero(FloatingPointLiteral(expr()))

/** Implements floating point isNormal operation. */
@JvmName("isZeroDouble")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
fun isZero(expr: () -> Double) = FPIsZero(FloatingPointLiteral(expr()))

/** Implements floating point isInfinite operation. */
fun isInfinite(expr: Expression<FloatingPointSort>) = FPIsInfinite(expr)

/** Implements floating point isNormal operation. */
fun isInfinite(expr: Float) = FPIsInfinite(FloatingPointLiteral(expr))

/** Implements floating point isNormal operation. */
fun isInfinite(expr: Double) = FPIsInfinite(FloatingPointLiteral(expr))

/** Implements floating point isInfinite operation. */
@JvmName("isInfiniteFPExpr")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
fun isInfinite(block: () -> Expression<FloatingPointSort>) = FPIsInfinite(block())

/** Implements floating point isNormal operation. */
@JvmName("isInfiniteFloat")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
fun isInfinite(expr: () -> Float) = FPIsInfinite(FloatingPointLiteral(expr()))

/** Implements floating point isNormal operation. */
@JvmName("isInfiniteDouble")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
fun isInfinite(expr: () -> Double) = FPIsInfinite(FloatingPointLiteral(expr()))

/** Implements floating point isNaN operation. */
fun isNaN(expr: Expression<FloatingPointSort>) = FPIsNaN(expr)

/** Implements floating point isNormal operation. */
fun isNaN(expr: Float) = FPIsNaN(FloatingPointLiteral(expr))

/** Implements floating point isNormal operation. */
fun isNaN(expr: Double) = FPIsNaN(FloatingPointLiteral(expr))

/** Implements floating point isNaN operation. */
@JvmName("isNaNFPExpr")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
fun isNaN(block: () -> Expression<FloatingPointSort>) = FPIsNaN(block())

/** Implements floating point isNormal operation. */
@JvmName("isNaNFloat")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
fun isNaN(expr: () -> Float) = FPIsNaN(FloatingPointLiteral(expr()))

/** Implements floating point isNormal operation. */
@JvmName("isNaNDouble")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
fun isNaN(expr: () -> Double) = FPIsNaN(FloatingPointLiteral(expr()))

/** Implements floating point isNegative operation. */
fun isNegative(expr: Expression<FloatingPointSort>) = FPIsNegative(expr)

/** Implements floating point isNormal operation. */
fun isNegative(expr: Float) = FPIsNegative(FloatingPointLiteral(expr))

/** Implements floating point isNormal operation. */
fun isNegative(expr: Double) = FPIsNegative(FloatingPointLiteral(expr))

/** Implements floating point isNegative operation. */
@JvmName("isNegativeFPExpr")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
fun isNegative(block: () -> Expression<FloatingPointSort>) = FPIsNegative(block())

/** Implements floating point isNormal operation. */
@JvmName("isNegativeFloat")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
fun isNegative(expr: () -> Float) = FPIsNegative(FloatingPointLiteral(expr()))

/** Implements floating point isNormal operation. */
@JvmName("isNegativeDouble")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
fun isNegative(expr: () -> Double) = FPIsNegative(FloatingPointLiteral(expr()))

/** Implements floating point isPositive operation. */
fun isPositive(expr: Expression<FloatingPointSort>) = FPIsPositive(expr)

/** Implements floating point isNormal operation. */
fun isPositive(expr: Float) = FPIsPositive(FloatingPointLiteral(expr))

/** Implements floating point isNormal operation. */
fun isPositive(expr: Double) = FPIsPositive(FloatingPointLiteral(expr))

/** Implements floating point isPositive operation. */
@JvmName("isPositiveFPExpr")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
fun isPositive(block: () -> Expression<FloatingPointSort>) = FPIsPositive(block())

/** Implements floating point isNormal operation. */
@JvmName("isPositiveFloat")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
fun isPositive(expr: () -> Float) = FPIsPositive(FloatingPointLiteral(expr()))

/** Implements floating point isNormal operation. */
@JvmName("isPositiveDouble")
@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
fun isPositive(expr: () -> Double) = FPIsPositive(FloatingPointLiteral(expr()))

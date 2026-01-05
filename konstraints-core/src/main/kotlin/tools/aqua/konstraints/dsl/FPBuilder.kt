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

import tools.aqua.konstraints.smt.BVSort
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
import tools.aqua.konstraints.smt.FPLiteral
import tools.aqua.konstraints.smt.FPLt
import tools.aqua.konstraints.smt.FPMax
import tools.aqua.konstraints.smt.FPMin
import tools.aqua.konstraints.smt.FPMul
import tools.aqua.konstraints.smt.FPRem
import tools.aqua.konstraints.smt.FPRoundToIntegral
import tools.aqua.konstraints.smt.FPSort
import tools.aqua.konstraints.smt.FPSqrt
import tools.aqua.konstraints.smt.FPSub
import tools.aqua.konstraints.smt.FPToFP
import tools.aqua.konstraints.smt.FPToReal
import tools.aqua.konstraints.smt.FPToSBitVec
import tools.aqua.konstraints.smt.FPToUBitVec
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
infix fun Expression<FPSort>.fpadd(summand: Expression<FPSort>) = this fpadd_rne summand

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun Expression<FPSort>.fpadd_rne(summand: Expression<FPSort>) = FPAdd(RNE, this, summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun Expression<FPSort>.fpadd_rna(summand: Expression<FPSort>) = FPAdd(RNA, this, summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun Expression<FPSort>.fpadd_rtp(summand: Expression<FPSort>) = FPAdd(RTP, this, summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun Expression<FPSort>.fpadd_rtn(summand: Expression<FPSort>) = FPAdd(RTN, this, summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun Expression<FPSort>.fpadd_rtz(summand: Expression<FPSort>) = FPAdd(RTZ, this, summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun Expression<FPSort>.fpadd(summand: () -> Expression<FPSort>) = this fpadd_rne summand()

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun Expression<FPSort>.fpadd_rne(summand: () -> Expression<FPSort>) =
    FPAdd(RNE, this, summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun Expression<FPSort>.fpadd_rna(summand: () -> Expression<FPSort>) =
    FPAdd(RNA, this, summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun Expression<FPSort>.fpadd_rtp(summand: () -> Expression<FPSort>) =
    FPAdd(RTP, this, summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun Expression<FPSort>.fpadd_rtn(summand: () -> Expression<FPSort>) =
    FPAdd(RTN, this, summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun Expression<FPSort>.fpadd_rtz(summand: () -> Expression<FPSort>) =
    FPAdd(RTZ, this, summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FPSort>).fpadd(summand: Expression<FPSort>) = this() fpadd_rne summand

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FPSort>).fpadd_rne(summand: Expression<FPSort>) =
    FPAdd(RNE, this(), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun (() -> Expression<FPSort>).fpadd_rna(summand: Expression<FPSort>) =
    FPAdd(RNA, this(), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun (() -> Expression<FPSort>).fpadd_rtp(summand: Expression<FPSort>) =
    FPAdd(RTP, this(), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun (() -> Expression<FPSort>).fpadd_rtn(summand: Expression<FPSort>) =
    FPAdd(RTN, this(), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun (() -> Expression<FPSort>).fpadd_rtz(summand: Expression<FPSort>) =
    FPAdd(RTZ, this(), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FPSort>).fpadd(summand: () -> Expression<FPSort>) =
    this() fpadd_rne summand()

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FPSort>).fpadd_rne(summand: () -> Expression<FPSort>) =
    FPAdd(RNE, this(), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun (() -> Expression<FPSort>).fpadd_rna(summand: () -> Expression<FPSort>) =
    FPAdd(RNA, this(), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun (() -> Expression<FPSort>).fpadd_rtp(summand: () -> Expression<FPSort>) =
    FPAdd(RTP, this(), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun (() -> Expression<FPSort>).fpadd_rtn(summand: () -> Expression<FPSort>) =
    FPAdd(RTN, this(), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun (() -> Expression<FPSort>).fpadd_rtz(summand: () -> Expression<FPSort>) =
    FPAdd(RTZ, this(), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [summand] from [Float] to
 * [tools.aqua.konstraints.smt.FPLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FPSort>.fpadd(summand: Float) = this fpadd_rne FPLiteral(summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest even'. Converts [summand] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FPSort>.fpadd_rne(summand: Float) = FPAdd(RNE, this, FPLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest away'. Converts [summand] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FPSort>.fpadd_rna(summand: Float) = FPAdd(RNA, this, FPLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward positive'. Converts [summand] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FPSort>.fpadd_rtp(summand: Float) = FPAdd(RTP, this, FPLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward negative'. Converts [summand] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FPSort>.fpadd_rtn(summand: Float) = FPAdd(RTN, this, FPLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward zero'. Converts [summand] from [Float] to [FPLiteral] with sort
 * [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FPSort>.fpadd_rtz(summand: Float) = FPAdd(RTZ, this, FPLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [summand] from [Float] to
 * [FPLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FPSort>).fpadd(summand: Float) = this() fpadd_rne FPLiteral(summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest even'. Converts [summand] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FPSort>).fpadd_rne(summand: Float) =
    FPAdd(RNE, this(), FPLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest away'. Converts [summand] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FPSort>).fpadd_rna(summand: Float) =
    FPAdd(RNA, this(), FPLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward positive'. Converts [summand] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FPSort>).fpadd_rtp(summand: Float) =
    FPAdd(RTP, this(), FPLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward negative'. Converts [summand] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FPSort>).fpadd_rtn(summand: Float) =
    FPAdd(RTN, this(), FPLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward zero'. Converts [summand] from [Float] to [FPLiteral] with sort
 * [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FPSort>).fpadd_rtz(summand: Float) =
    FPAdd(RTZ, this(), FPLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [summand] from [Float] to
 * [FPLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpadd(summand: Expression<FPSort>) = FPLiteral(this) fpadd_rne summand

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest even'. Converts [summand] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpadd_rne(summand: Expression<FPSort>) = FPAdd(RNE, FPLiteral(this), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest away'. Converts [summand] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpadd_rna(summand: Expression<FPSort>) = FPAdd(RNA, FPLiteral(this), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward positive'. Converts [summand] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpadd_rtp(summand: Expression<FPSort>) = FPAdd(RTP, FPLiteral(this), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward negative'. Converts [summand] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpadd_rtn(summand: Expression<FPSort>) = FPAdd(RTN, FPLiteral(this), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward zero'. Converts [summand] from [Float] to [FPLiteral] with sort
 * [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpadd_rtz(summand: Expression<FPSort>) = FPAdd(RTZ, FPLiteral(this), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [summand] from [Float] to
 * [FPLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpadd(summand: () -> Expression<FPSort>) = FPLiteral(this) fpadd_rne summand()

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest even'. Converts [summand] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpadd_rne(summand: () -> Expression<FPSort>) =
    FPAdd(RNE, FPLiteral(this), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest away'. Converts [summand] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpadd_rna(summand: () -> Expression<FPSort>) =
    FPAdd(RNA, FPLiteral(this), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward positive'. Converts [summand] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpadd_rtp(summand: () -> Expression<FPSort>) =
    FPAdd(RTP, FPLiteral(this), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward negative'. Converts [summand] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpadd_rtn(summand: () -> Expression<FPSort>) =
    FPAdd(RTN, FPLiteral(this), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward zero'. Converts [summand] from [Float] to [FPLiteral] with sort
 * [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpadd_rtz(summand: () -> Expression<FPSort>) =
    FPAdd(RTZ, FPLiteral(this), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [summand] from [Double] to
 * [FPLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FPSort>.fpadd(summand: Double) = this fpadd_rne FPLiteral(summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest even'. Converts [summand] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FPSort>.fpadd_rne(summand: Double) = FPAdd(RNE, this, FPLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest away'. Converts [summand] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FPSort>.fpadd_rna(summand: Double) = FPAdd(RNA, this, FPLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward positive'. Converts [summand] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FPSort>.fpadd_rtp(summand: Double) = FPAdd(RTP, this, FPLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward negative'. Converts [summand] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FPSort>.fpadd_rtn(summand: Double) = FPAdd(RTN, this, FPLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward zero'. Converts [summand] from [Double] to [FPLiteral] with sort
 * [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FPSort>.fpadd_rtz(summand: Double) = FPAdd(RTZ, this, FPLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [summand] from [Double] to
 * [FPLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FPSort>).fpadd(summand: Double) = this() fpadd_rne FPLiteral(summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest even'. Converts [summand] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FPSort>).fpadd_rne(summand: Double) =
    FPAdd(RNE, this(), FPLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest away'. Converts [summand] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FPSort>).fpadd_rna(summand: Double) =
    FPAdd(RNA, this(), FPLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward positive'. Converts [summand] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FPSort>).fpadd_rtp(summand: Double) =
    FPAdd(RTP, this(), FPLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward negative'. Converts [summand] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FPSort>).fpadd_rtn(summand: Double) =
    FPAdd(RTN, this(), FPLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward zero'. Converts [summand] from [Double] to [FPLiteral] with sort
 * [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FPSort>).fpadd_rtz(summand: Double) =
    FPAdd(RTZ, this(), FPLiteral(summand))

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [summand] from [Double] to
 * [FPLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpadd(summand: Expression<FPSort>) = FPLiteral(this) fpadd_rne summand

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest even'. Converts [summand] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpadd_rne(summand: Expression<FPSort>) = FPAdd(RNE, FPLiteral(this), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest away'. Converts [summand] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpadd_rna(summand: Expression<FPSort>) = FPAdd(RNA, FPLiteral(this), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward positive'. Converts [summand] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpadd_rtp(summand: Expression<FPSort>) = FPAdd(RTP, FPLiteral(this), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward negative'. Converts [summand] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpadd_rtn(summand: Expression<FPSort>) = FPAdd(RTN, FPLiteral(this), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward zero'. Converts [summand] from [Double] to [FPLiteral] with sort
 * [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpadd_rtz(summand: Expression<FPSort>) = FPAdd(RTZ, FPLiteral(this), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [summand] from [Double] to
 * [FPLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpadd(summand: () -> Expression<FPSort>) = FPLiteral(this) fpadd_rne summand()

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest even'. Converts [summand] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpadd_rne(summand: () -> Expression<FPSort>) =
    FPAdd(RNE, FPLiteral(this), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest away'. Converts [summand] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpadd_rna(summand: () -> Expression<FPSort>) =
    FPAdd(RNA, FPLiteral(this), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward positive'. Converts [summand] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpadd_rtp(summand: () -> Expression<FPSort>) =
    FPAdd(RTP, FPLiteral(this), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward negative'. Converts [summand] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpadd_rtn(summand: () -> Expression<FPSort>) =
    FPAdd(RTN, FPLiteral(this), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward zero'. Converts [summand] from [Double] to [FPLiteral] with sort
 * [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpadd_rtz(summand: () -> Expression<FPSort>) =
    FPAdd(RTZ, FPLiteral(this), summand())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun Expression<FPSort>.fpsub(subtrahend: Expression<FPSort>) = this fpsub_rne subtrahend

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun Expression<FPSort>.fpsub_rne(subtrahend: Expression<FPSort>) =
    FPSub(RNE, this, subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun Expression<FPSort>.fpsub_rna(subtrahend: Expression<FPSort>) =
    FPSub(RNA, this, subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun Expression<FPSort>.fpsub_rtp(subtrahend: Expression<FPSort>) =
    FPSub(RTP, this, subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun Expression<FPSort>.fpsub_rtn(subtrahend: Expression<FPSort>) =
    FPSub(RTN, this, subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun Expression<FPSort>.fpsub_rtz(subtrahend: Expression<FPSort>) =
    FPSub(RTZ, this, subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun Expression<FPSort>.fpsub(subtrahend: () -> Expression<FPSort>) =
    this fpsub_rne subtrahend()

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun Expression<FPSort>.fpsub_rne(subtrahend: () -> Expression<FPSort>) =
    FPSub(RNE, this, subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun Expression<FPSort>.fpsub_rna(subtrahend: () -> Expression<FPSort>) =
    FPSub(RNA, this, subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun Expression<FPSort>.fpsub_rtp(subtrahend: () -> Expression<FPSort>) =
    FPSub(RTP, this, subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun Expression<FPSort>.fpsub_rtn(subtrahend: () -> Expression<FPSort>) =
    FPSub(RTN, this, subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun Expression<FPSort>.fpsub_rtz(subtrahend: () -> Expression<FPSort>) =
    FPSub(RTZ, this, subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FPSort>).fpsub(subtrahend: Expression<FPSort>) =
    this() fpsub_rne subtrahend

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FPSort>).fpsub_rne(subtrahend: Expression<FPSort>) =
    FPSub(RNE, this(), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun (() -> Expression<FPSort>).fpsub_rna(subtrahend: Expression<FPSort>) =
    FPSub(RNA, this(), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun (() -> Expression<FPSort>).fpsub_rtp(subtrahend: Expression<FPSort>) =
    FPSub(RTP, this(), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun (() -> Expression<FPSort>).fpsub_rtn(subtrahend: Expression<FPSort>) =
    FPSub(RTN, this(), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun (() -> Expression<FPSort>).fpsub_rtz(subtrahend: Expression<FPSort>) =
    FPSub(RTZ, this(), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FPSort>).fpsub(subtrahend: () -> Expression<FPSort>) =
    this() fpsub_rne subtrahend()

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FPSort>).fpsub_rne(subtrahend: () -> Expression<FPSort>) =
    FPSub(RNE, this(), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun (() -> Expression<FPSort>).fpsub_rna(subtrahend: () -> Expression<FPSort>) =
    FPSub(RNA, this(), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun (() -> Expression<FPSort>).fpsub_rtp(subtrahend: () -> Expression<FPSort>) =
    FPSub(RTP, this(), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun (() -> Expression<FPSort>).fpsub_rtn(subtrahend: () -> Expression<FPSort>) =
    FPSub(RTN, this(), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun (() -> Expression<FPSort>).fpsub_rtz(subtrahend: () -> Expression<FPSort>) =
    FPSub(RTZ, this(), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [subtrahend] from [Float] to
 * [FPLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FPSort>.fpsub(subtrahend: Float) = this fpsub_rne FPLiteral(subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest even'. Converts [subtrahend] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FPSort>.fpsub_rne(subtrahend: Float) = FPSub(RNE, this, FPLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest away'. Converts [subtrahend] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FPSort>.fpsub_rna(subtrahend: Float) = FPSub(RNA, this, FPLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward positive'. Converts [subtrahend] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FPSort>.fpsub_rtp(subtrahend: Float) = FPSub(RTP, this, FPLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward negative'. Converts [subtrahend] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FPSort>.fpsub_rtn(subtrahend: Float) = FPSub(RTN, this, FPLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward zero'. Converts [subtrahend] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FPSort>.fpsub_rtz(subtrahend: Float) = FPSub(RTZ, this, FPLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [subtrahend] from [Float] to
 * [FPLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FPSort>).fpsub(subtrahend: Float) =
    this() fpsub_rne FPLiteral(subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest even'. Converts [subtrahend] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FPSort>).fpsub_rne(subtrahend: Float) =
    FPSub(RNE, this(), FPLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest away'. Converts [subtrahend] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FPSort>).fpsub_rna(subtrahend: Float) =
    FPSub(RNA, this(), FPLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward positive'. Converts [subtrahend] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FPSort>).fpsub_rtp(subtrahend: Float) =
    FPSub(RTP, this(), FPLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward negative'. Converts [subtrahend] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FPSort>).fpsub_rtn(subtrahend: Float) =
    FPSub(RTN, this(), FPLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward zero'. Converts [subtrahend] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FPSort>).fpsub_rtz(subtrahend: Float) =
    FPSub(RTZ, this(), FPLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [subtrahend] from [Float] to
 * [FPLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpsub(subtrahend: Expression<FPSort>) = FPLiteral(this) fpsub_rne subtrahend

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest even'. Converts [subtrahend] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpsub_rne(subtrahend: Expression<FPSort>) = FPSub(RNE, FPLiteral(this), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest away'. Converts [subtrahend] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpsub_rna(subtrahend: Expression<FPSort>) = FPSub(RNA, FPLiteral(this), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward positive'. Converts [subtrahend] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpsub_rtp(subtrahend: Expression<FPSort>) = FPSub(RTP, FPLiteral(this), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward negative'. Converts [subtrahend] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpsub_rtn(subtrahend: Expression<FPSort>) = FPSub(RTN, FPLiteral(this), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward zero'. Converts [subtrahend] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpsub_rtz(subtrahend: Expression<FPSort>) = FPSub(RTZ, FPLiteral(this), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [subtrahend] from [Float] to
 * [FPLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpsub(subtrahend: () -> Expression<FPSort>) = FPLiteral(this) fpsub_rne subtrahend()

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest even'. Converts [subtrahend] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpsub_rne(subtrahend: () -> Expression<FPSort>) =
    FPSub(RNE, FPLiteral(this), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest away'. Converts [subtrahend] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpsub_rna(subtrahend: () -> Expression<FPSort>) =
    FPSub(RNA, FPLiteral(this), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward positive'. Converts [subtrahend] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpsub_rtp(subtrahend: () -> Expression<FPSort>) =
    FPSub(RTP, FPLiteral(this), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward negative'. Converts [subtrahend] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpsub_rtn(subtrahend: () -> Expression<FPSort>) =
    FPSub(RTN, FPLiteral(this), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward zero'. Converts [subtrahend] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpsub_rtz(subtrahend: () -> Expression<FPSort>) =
    FPSub(RTZ, FPLiteral(this), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [subtrahend] from [Double] to
 * [FPLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FPSort>.fpsub(subtrahend: Double) = this fpsub_rne FPLiteral(subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest even'. Converts [subtrahend] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FPSort>.fpsub_rne(subtrahend: Double) = FPSub(RNE, this, FPLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest away'. Converts [subtrahend] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FPSort>.fpsub_rna(subtrahend: Double) = FPSub(RNA, this, FPLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward positive'. Converts [subtrahend] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FPSort>.fpsub_rtp(subtrahend: Double) = FPSub(RTP, this, FPLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward negative'. Converts [subtrahend] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FPSort>.fpsub_rtn(subtrahend: Double) = FPSub(RTN, this, FPLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward zero'. Converts [subtrahend] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FPSort>.fpsub_rtz(subtrahend: Double) = FPSub(RTZ, this, FPLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [subtrahend] from [Double] to
 * [FPLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FPSort>).fpsub(subtrahend: Double) =
    this() fpsub_rne FPLiteral(subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest even'. Converts [subtrahend] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FPSort>).fpsub_rne(subtrahend: Double) =
    FPSub(RNE, this(), FPLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest away'. Converts [subtrahend] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FPSort>).fpsub_rna(subtrahend: Double) =
    FPSub(RNA, this(), FPLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward positive'. Converts [subtrahend] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FPSort>).fpsub_rtp(subtrahend: Double) =
    FPSub(RTP, this(), FPLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward negative'. Converts [subtrahend] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FPSort>).fpsub_rtn(subtrahend: Double) =
    FPSub(RTN, this(), FPLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward zero'. Converts [subtrahend] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FPSort>).fpsub_rtz(subtrahend: Double) =
    FPSub(RTZ, this(), FPLiteral(subtrahend))

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [subtrahend] from [Double] to
 * [FPLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpsub(subtrahend: Expression<FPSort>) = FPLiteral(this) fpsub_rne subtrahend

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest even'. Converts [subtrahend] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpsub_rne(subtrahend: Expression<FPSort>) = FPSub(RNE, FPLiteral(this), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest away'. Converts [subtrahend] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpsub_rna(subtrahend: Expression<FPSort>) = FPSub(RNA, FPLiteral(this), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward positive'. Converts [subtrahend] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpsub_rtp(subtrahend: Expression<FPSort>) = FPSub(RTP, FPLiteral(this), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward negative'. Converts [subtrahend] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpsub_rtn(subtrahend: Expression<FPSort>) = FPSub(RTN, FPLiteral(this), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward zero'. Converts [subtrahend] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpsub_rtz(subtrahend: Expression<FPSort>) = FPSub(RTZ, FPLiteral(this), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [subtrahend] from [Double] to
 * [FPLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpsub(subtrahend: () -> Expression<FPSort>) =
    FPLiteral(this) fpsub_rne subtrahend()

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest even'. Converts [subtrahend] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpsub_rne(subtrahend: () -> Expression<FPSort>) =
    FPSub(RNE, FPLiteral(this), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest away'. Converts [subtrahend] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpsub_rna(subtrahend: () -> Expression<FPSort>) =
    FPSub(RNA, FPLiteral(this), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward positive'. Converts [subtrahend] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpsub_rtp(subtrahend: () -> Expression<FPSort>) =
    FPSub(RTP, FPLiteral(this), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward negative'. Converts [subtrahend] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpsub_rtn(subtrahend: () -> Expression<FPSort>) =
    FPSub(RTN, FPLiteral(this), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward zero'. Converts [subtrahend] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpsub_rtz(subtrahend: () -> Expression<FPSort>) =
    FPSub(RTZ, FPLiteral(this), subtrahend())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun Expression<FPSort>.fpmul(multiplicant: Expression<FPSort>) = this fpmul_rne multiplicant

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun Expression<FPSort>.fpmul_rne(multiplicant: Expression<FPSort>) =
    FPMul(RNE, this, multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun Expression<FPSort>.fpmul_rna(multiplicant: Expression<FPSort>) =
    FPMul(RNA, this, multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun Expression<FPSort>.fpmul_rtp(multiplicant: Expression<FPSort>) =
    FPMul(RTP, this, multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun Expression<FPSort>.fpmul_rtn(multiplicant: Expression<FPSort>) =
    FPMul(RTN, this, multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun Expression<FPSort>.fpmul_rtz(multiplicant: Expression<FPSort>) =
    FPMul(RTZ, this, multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun Expression<FPSort>.fpmul(multiplicant: () -> Expression<FPSort>) =
    this fpmul_rne multiplicant()

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun Expression<FPSort>.fpmul_rne(multiplicant: () -> Expression<FPSort>) =
    FPMul(RNE, this, multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun Expression<FPSort>.fpmul_rna(multiplicant: () -> Expression<FPSort>) =
    FPMul(RNA, this, multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun Expression<FPSort>.fpmul_rtp(multiplicant: () -> Expression<FPSort>) =
    FPMul(RTP, this, multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun Expression<FPSort>.fpmul_rtn(multiplicant: () -> Expression<FPSort>) =
    FPMul(RTN, this, multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun Expression<FPSort>.fpmul_rtz(multiplicant: () -> Expression<FPSort>) =
    FPMul(RTZ, this, multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FPSort>).fpmul(multiplicant: Expression<FPSort>) =
    this() fpmul_rne multiplicant

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FPSort>).fpmul_rne(multiplicant: Expression<FPSort>) =
    FPMul(RNE, this(), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun (() -> Expression<FPSort>).fpmul_rna(multiplicant: Expression<FPSort>) =
    FPMul(RNA, this(), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun (() -> Expression<FPSort>).fpmul_rtp(multiplicant: Expression<FPSort>) =
    FPMul(RTP, this(), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun (() -> Expression<FPSort>).fpmul_rtn(multiplicant: Expression<FPSort>) =
    FPMul(RTN, this(), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun (() -> Expression<FPSort>).fpmul_rtz(multiplicant: Expression<FPSort>) =
    FPMul(RTZ, this(), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FPSort>).fpmul(multiplicant: () -> Expression<FPSort>) =
    this() fpmul_rne multiplicant()

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FPSort>).fpmul_rne(multiplicant: () -> Expression<FPSort>) =
    FPMul(RNE, this(), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun (() -> Expression<FPSort>).fpmul_rna(multiplicant: () -> Expression<FPSort>) =
    FPMul(RNA, this(), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun (() -> Expression<FPSort>).fpmul_rtp(multiplicant: () -> Expression<FPSort>) =
    FPMul(RTP, this(), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun (() -> Expression<FPSort>).fpmul_rtn(multiplicant: () -> Expression<FPSort>) =
    FPMul(RTN, this(), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun (() -> Expression<FPSort>).fpmul_rtz(multiplicant: () -> Expression<FPSort>) =
    FPMul(RTZ, this(), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [multiplicant] from [Float] to
 * [FPLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FPSort>.fpmul(multiplicant: Float) = this fpmul_rne FPLiteral(multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest even'. Converts [multiplicant] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FPSort>.fpmul_rne(multiplicant: Float) =
    FPMul(RNE, this, FPLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest away'. Converts [multiplicant] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FPSort>.fpmul_rna(multiplicant: Float) =
    FPMul(RNA, this, FPLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward positive'. Converts [multiplicant] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FPSort>.fpmul_rtp(multiplicant: Float) =
    FPMul(RTP, this, FPLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward negative'. Converts [multiplicant] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FPSort>.fpmul_rtn(multiplicant: Float) =
    FPMul(RTN, this, FPLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward zero'. Converts [multiplicant] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FPSort>.fpmul_rtz(multiplicant: Float) =
    FPMul(RTZ, this, FPLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [multiplicant] from [Float] to
 * [FPLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FPSort>).fpmul(multiplicant: Float) =
    this() fpmul_rne FPLiteral(multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest even'. Converts [multiplicant] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FPSort>).fpmul_rne(multiplicant: Float) =
    FPMul(RNE, this(), FPLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest away'. Converts [multiplicant] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FPSort>).fpmul_rna(multiplicant: Float) =
    FPMul(RNA, this(), FPLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward positive'. Converts [multiplicant] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FPSort>).fpmul_rtp(multiplicant: Float) =
    FPMul(RTP, this(), FPLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward negative'. Converts [multiplicant] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FPSort>).fpmul_rtn(multiplicant: Float) =
    FPMul(RTN, this(), FPLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward zero'. Converts [multiplicant] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FPSort>).fpmul_rtz(multiplicant: Float) =
    FPMul(RTZ, this(), FPLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [multiplicant] from [Float] to
 * [FPLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpmul(multiplicant: Expression<FPSort>) = FPLiteral(this) fpmul_rne multiplicant

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest even'. Converts [multiplicant] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpmul_rne(multiplicant: Expression<FPSort>) =
    FPMul(RNE, FPLiteral(this), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest away'. Converts [multiplicant] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpmul_rna(multiplicant: Expression<FPSort>) =
    FPMul(RNA, FPLiteral(this), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward positive'. Converts [multiplicant] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpmul_rtp(multiplicant: Expression<FPSort>) =
    FPMul(RTP, FPLiteral(this), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward negative'. Converts [multiplicant] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpmul_rtn(multiplicant: Expression<FPSort>) =
    FPMul(RTN, FPLiteral(this), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward zero'. Converts [multiplicant] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpmul_rtz(multiplicant: Expression<FPSort>) =
    FPMul(RTZ, FPLiteral(this), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [multiplicant] from [Float] to
 * [FPLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpmul(multiplicant: () -> Expression<FPSort>) =
    FPLiteral(this) fpmul_rne multiplicant()

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest even'. Converts [multiplicant] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpmul_rne(multiplicant: () -> Expression<FPSort>) =
    FPMul(RNE, FPLiteral(this), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest away'. Converts [multiplicant] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpmul_rna(multiplicant: () -> Expression<FPSort>) =
    FPMul(RNA, FPLiteral(this), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward positive'. Converts [multiplicant] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpmul_rtp(multiplicant: () -> Expression<FPSort>) =
    FPMul(RTP, FPLiteral(this), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward negative'. Converts [multiplicant] from [Float] to [FPLiteral]
 * with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpmul_rtn(multiplicant: () -> Expression<FPSort>) =
    FPMul(RTN, FPLiteral(this), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward zero'. Converts [multiplicant] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpmul_rtz(multiplicant: () -> Expression<FPSort>) =
    FPMul(RTZ, FPLiteral(this), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [multiplicant] from [Double] to
 * [FPLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FPSort>.fpmul(multiplicant: Double) = this fpmul_rne FPLiteral(multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest even'. Converts [multiplicant] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FPSort>.fpmul_rne(multiplicant: Double) =
    FPMul(RNE, this, FPLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest away'. Converts [multiplicant] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FPSort>.fpmul_rna(multiplicant: Double) =
    FPMul(RNA, this, FPLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward positive'. Converts [multiplicant] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FPSort>.fpmul_rtp(multiplicant: Double) =
    FPMul(RTP, this, FPLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward negative'. Converts [multiplicant] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FPSort>.fpmul_rtn(multiplicant: Double) =
    FPMul(RTN, this, FPLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward zero'. Converts [multiplicant] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FPSort>.fpmul_rtz(multiplicant: Double) =
    FPMul(RTZ, this, FPLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [multiplicant] from [Double] to
 * [FPLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FPSort>).fpmul(multiplicant: Double) =
    this() fpmul_rne FPLiteral(multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest even'. Converts [multiplicant] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FPSort>).fpmul_rne(multiplicant: Double) =
    FPMul(RNE, this(), FPLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest away'. Converts [multiplicant] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FPSort>).fpmul_rna(multiplicant: Double) =
    FPMul(RNA, this(), FPLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward positive'. Converts [multiplicant] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FPSort>).fpmul_rtp(multiplicant: Double) =
    FPMul(RTP, this(), FPLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward negative'. Converts [multiplicant] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FPSort>).fpmul_rtn(multiplicant: Double) =
    FPMul(RTN, this(), FPLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward zero'. Converts [multiplicant] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FPSort>).fpmul_rtz(multiplicant: Double) =
    FPMul(RTZ, this(), FPLiteral(multiplicant))

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [multiplicant] from [Double] to
 * [FPLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpmul(multiplicant: Expression<FPSort>) = FPLiteral(this) fpmul_rne multiplicant

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest even'. Converts [multiplicant] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpmul_rne(multiplicant: Expression<FPSort>) =
    FPMul(RNE, FPLiteral(this), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest away'. Converts [multiplicant] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpmul_rna(multiplicant: Expression<FPSort>) =
    FPMul(RNA, FPLiteral(this), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward positive'. Converts [multiplicant] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpmul_rtp(multiplicant: Expression<FPSort>) =
    FPMul(RTP, FPLiteral(this), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward negative'. Converts [multiplicant] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpmul_rtn(multiplicant: Expression<FPSort>) =
    FPMul(RTN, FPLiteral(this), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward zero'. Converts [multiplicant] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpmul_rtz(multiplicant: Expression<FPSort>) =
    FPMul(RTZ, FPLiteral(this), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [multiplicant] from [Double] to
 * [FPLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpmul(multiplicant: () -> Expression<FPSort>) =
    FPLiteral(this) fpmul_rne multiplicant()

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest even'. Converts [multiplicant] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpmul_rne(multiplicant: () -> Expression<FPSort>) =
    FPMul(RNE, FPLiteral(this), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest away'. Converts [multiplicant] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpmul_rna(multiplicant: () -> Expression<FPSort>) =
    FPMul(RNA, FPLiteral(this), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward positive'. Converts [multiplicant] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpmul_rtp(multiplicant: () -> Expression<FPSort>) =
    FPMul(RTP, FPLiteral(this), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward negative'. Converts [multiplicant] from [Double] to [FPLiteral]
 * with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpmul_rtn(multiplicant: () -> Expression<FPSort>) =
    FPMul(RTN, FPLiteral(this), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward zero'. Converts [multiplicant] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpmul_rtz(multiplicant: () -> Expression<FPSort>) =
    FPMul(RTZ, FPLiteral(this), multiplicant())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun Expression<FPSort>.fpdiv(divisor: Expression<FPSort>) = this fpdiv_rne divisor

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun Expression<FPSort>.fpdiv_rne(divisor: Expression<FPSort>) = FPDiv(RNE, this, divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun Expression<FPSort>.fpdiv_rna(divisor: Expression<FPSort>) = FPDiv(RNA, this, divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun Expression<FPSort>.fpdiv_rtp(divisor: Expression<FPSort>) = FPDiv(RTP, this, divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun Expression<FPSort>.fpdiv_rtn(divisor: Expression<FPSort>) = FPDiv(RTN, this, divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun Expression<FPSort>.fpdiv_rtz(divisor: Expression<FPSort>) = FPDiv(RTZ, this, divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun Expression<FPSort>.fpdiv(divisor: () -> Expression<FPSort>) = this fpdiv_rne divisor()

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun Expression<FPSort>.fpdiv_rne(divisor: () -> Expression<FPSort>) =
    FPDiv(RNE, this, divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun Expression<FPSort>.fpdiv_rna(divisor: () -> Expression<FPSort>) =
    FPDiv(RNA, this, divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun Expression<FPSort>.fpdiv_rtp(divisor: () -> Expression<FPSort>) =
    FPDiv(RTP, this, divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun Expression<FPSort>.fpdiv_rtn(divisor: () -> Expression<FPSort>) =
    FPDiv(RTN, this, divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun Expression<FPSort>.fpdiv_rtz(divisor: () -> Expression<FPSort>) =
    FPDiv(RTZ, this, divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FPSort>).fpdiv(divisor: Expression<FPSort>) = this() fpdiv_rne divisor

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FPSort>).fpdiv_rne(divisor: Expression<FPSort>) =
    FPDiv(RNE, this(), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun (() -> Expression<FPSort>).fpdiv_rna(divisor: Expression<FPSort>) =
    FPDiv(RNA, this(), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun (() -> Expression<FPSort>).fpdiv_rtp(divisor: Expression<FPSort>) =
    FPDiv(RTP, this(), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun (() -> Expression<FPSort>).fpdiv_rtn(divisor: Expression<FPSort>) =
    FPDiv(RTN, this(), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun (() -> Expression<FPSort>).fpdiv_rtz(divisor: Expression<FPSort>) =
    FPDiv(RTZ, this(), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FPSort>).fpdiv(divisor: () -> Expression<FPSort>) =
    this() fpdiv_rne divisor()

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FPSort>).fpdiv_rne(divisor: () -> Expression<FPSort>) =
    FPDiv(RNE, this(), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun (() -> Expression<FPSort>).fpdiv_rna(divisor: () -> Expression<FPSort>) =
    FPDiv(RNA, this(), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun (() -> Expression<FPSort>).fpdiv_rtp(divisor: () -> Expression<FPSort>) =
    FPDiv(RTP, this(), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun (() -> Expression<FPSort>).fpdiv_rtn(divisor: () -> Expression<FPSort>) =
    FPDiv(RTN, this(), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun (() -> Expression<FPSort>).fpdiv_rtz(divisor: () -> Expression<FPSort>) =
    FPDiv(RTZ, this(), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [divisor] from [Float] to
 * [FPLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FPSort>.fpdiv(divisor: Float) = this fpdiv_rne FPLiteral(divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest even'. Converts [divisor] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FPSort>.fpdiv_rne(divisor: Float) = FPDiv(RNE, this, FPLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest away'. Converts [divisor] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FPSort>.fpdiv_rna(divisor: Float) = FPDiv(RNA, this, FPLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward positive'. Converts [divisor] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FPSort>.fpdiv_rtp(divisor: Float) = FPDiv(RTP, this, FPLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward negative'. Converts [divisor] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FPSort>.fpdiv_rtn(divisor: Float) = FPDiv(RTN, this, FPLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward zero'. Converts [divisor] from [Float] to [FPLiteral] with sort
 * [(_ FloatingPoint 8 24)]
 */
infix fun Expression<FPSort>.fpdiv_rtz(divisor: Float) = FPDiv(RTZ, this, FPLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [divisor] from [Float] to
 * [FPLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FPSort>).fpdiv(divisor: Float) = this() fpdiv_rne FPLiteral(divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest even'. Converts [divisor] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FPSort>).fpdiv_rne(divisor: Float) =
    FPDiv(RNE, this(), FPLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest away'. Converts [divisor] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FPSort>).fpdiv_rna(divisor: Float) =
    FPDiv(RNA, this(), FPLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward positive'. Converts [divisor] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FPSort>).fpdiv_rtp(divisor: Float) =
    FPDiv(RTP, this(), FPLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward negative'. Converts [divisor] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FPSort>).fpdiv_rtn(divisor: Float) =
    FPDiv(RTN, this(), FPLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward zero'. Converts [divisor] from [Float] to [FPLiteral] with sort
 * [(_ FloatingPoint 8 24)]
 */
infix fun (() -> Expression<FPSort>).fpdiv_rtz(divisor: Float) =
    FPDiv(RTZ, this(), FPLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [divisor] from [Float] to
 * [FPLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpdiv(divisor: Expression<FPSort>) = FPLiteral(this) fpdiv_rne divisor

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest even'. Converts [divisor] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpdiv_rne(divisor: Expression<FPSort>) = FPDiv(RNE, FPLiteral(this), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest away'. Converts [divisor] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpdiv_rna(divisor: Expression<FPSort>) = FPDiv(RNA, FPLiteral(this), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward positive'. Converts [divisor] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpdiv_rtp(divisor: Expression<FPSort>) = FPDiv(RTP, FPLiteral(this), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward negative'. Converts [divisor] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpdiv_rtn(divisor: Expression<FPSort>) = FPDiv(RTN, FPLiteral(this), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward zero'. Converts [divisor] from [Float] to [FPLiteral] with sort
 * [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpdiv_rtz(divisor: Expression<FPSort>) = FPDiv(RTZ, FPLiteral(this), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [divisor] from [Float] to
 * [FPLiteral] with sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpdiv(divisor: () -> Expression<FPSort>) = FPLiteral(this) fpdiv_rne divisor()

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest even'. Converts [divisor] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpdiv_rne(divisor: () -> Expression<FPSort>) =
    FPDiv(RNE, FPLiteral(this), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest away'. Converts [divisor] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpdiv_rna(divisor: () -> Expression<FPSort>) =
    FPDiv(RNA, FPLiteral(this), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward positive'. Converts [divisor] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpdiv_rtp(divisor: () -> Expression<FPSort>) =
    FPDiv(RTP, FPLiteral(this), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward negative'. Converts [divisor] from [Float] to [FPLiteral] with
 * sort [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpdiv_rtn(divisor: () -> Expression<FPSort>) =
    FPDiv(RTN, FPLiteral(this), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward zero'. Converts [divisor] from [Float] to [FPLiteral] with sort
 * [(_ FloatingPoint 8 24)]
 */
infix fun Float.fpdiv_rtz(divisor: () -> Expression<FPSort>) =
    FPDiv(RTZ, FPLiteral(this), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [divisor] from [Double] to
 * [FPLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FPSort>.fpdiv(divisor: Double) = this fpdiv_rne FPLiteral(divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest even'. Converts [divisor] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FPSort>.fpdiv_rne(divisor: Double) = FPDiv(RNE, this, FPLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest away'. Converts [divisor] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FPSort>.fpdiv_rna(divisor: Double) = FPDiv(RNA, this, FPLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward positive'. Converts [divisor] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FPSort>.fpdiv_rtp(divisor: Double) = FPDiv(RTP, this, FPLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward negative'. Converts [divisor] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FPSort>.fpdiv_rtn(divisor: Double) = FPDiv(RTN, this, FPLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward zero'. Converts [divisor] from [Double] to [FPLiteral] with sort
 * [(_ FloatingPoint 11 53)]
 */
infix fun Expression<FPSort>.fpdiv_rtz(divisor: Double) = FPDiv(RTZ, this, FPLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [divisor] from [Double] to
 * [FPLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FPSort>).fpdiv(divisor: Double) = this() fpdiv_rne FPLiteral(divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest even'. Converts [divisor] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FPSort>).fpdiv_rne(divisor: Double) =
    FPDiv(RNE, this(), FPLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest away'. Converts [divisor] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FPSort>).fpdiv_rna(divisor: Double) =
    FPDiv(RNA, this(), FPLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward positive'. Converts [divisor] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FPSort>).fpdiv_rtp(divisor: Double) =
    FPDiv(RTP, this(), FPLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward negative'. Converts [divisor] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FPSort>).fpdiv_rtn(divisor: Double) =
    FPDiv(RTN, this(), FPLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward zero'. Converts [divisor] from [Double] to [FPLiteral] with sort
 * [(_ FloatingPoint 11 53)]
 */
infix fun (() -> Expression<FPSort>).fpdiv_rtz(divisor: Double) =
    FPDiv(RTZ, this(), FPLiteral(divisor))

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [divisor] from [Double] to
 * [FPLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpdiv(divisor: Expression<FPSort>) = FPLiteral(this) fpdiv_rne divisor

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest even'. Converts [divisor] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpdiv_rne(divisor: Expression<FPSort>) = FPDiv(RNE, FPLiteral(this), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest away'. Converts [divisor] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpdiv_rna(divisor: Expression<FPSort>) = FPDiv(RNA, FPLiteral(this), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward positive'. Converts [divisor] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpdiv_rtp(divisor: Expression<FPSort>) = FPDiv(RTP, FPLiteral(this), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward negative'. Converts [divisor] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpdiv_rtn(divisor: Expression<FPSort>) = FPDiv(RTN, FPLiteral(this), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward zero'. Converts [divisor] from [Double] to [FPLiteral] with sort
 * [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpdiv_rtz(divisor: Expression<FPSort>) = FPDiv(RTZ, FPLiteral(this), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses default rounding mode 'round to nearest even'. Converts [divisor] from [Double] to
 * [FPLiteral] with sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpdiv(divisor: () -> Expression<FPSort>) = FPLiteral(this) fpdiv_rne divisor()

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest even'. Converts [divisor] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpdiv_rne(divisor: () -> Expression<FPSort>) =
    FPDiv(RNE, FPLiteral(this), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest away'. Converts [divisor] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpdiv_rna(divisor: () -> Expression<FPSort>) =
    FPDiv(RNA, FPLiteral(this), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward positive'. Converts [divisor] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpdiv_rtp(divisor: () -> Expression<FPSort>) =
    FPDiv(RTP, FPLiteral(this), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward negative'. Converts [divisor] from [Double] to [FPLiteral] with
 * sort [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpdiv_rtn(divisor: () -> Expression<FPSort>) =
    FPDiv(RTN, FPLiteral(this), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward zero'. Converts [divisor] from [Double] to [FPLiteral] with sort
 * [(_ FloatingPoint 11 53)]
 */
infix fun Double.fpdiv_rtz(divisor: () -> Expression<FPSort>) =
    FPDiv(RTZ, FPLiteral(this), divisor())

/**
 * Remainder operator for FPSort expressions: [this] - [divisor] * n, where n in Z is closest to
 * [this]/[divisor].
 */
infix fun Expression<FPSort>.fprem(divisor: Expression<FPSort>) = FPRem(this, divisor)

/**
 * Remainder operator for FPSort expressions: [this] - [divisor] * n, where n in Z is closest to
 * [this]/[divisor].
 */
infix fun Expression<FPSort>.fprem(divisor: () -> Expression<FPSort>) = FPRem(this, divisor())

/**
 * Remainder operator for FPSort expressions: [this] - [divisor] * n, where n in Z is closest to
 * [this]/[divisor].
 */
infix fun (() -> Expression<FPSort>).fprem(divisor: Expression<FPSort>) = FPRem(this(), divisor)

/**
 * Remainder operator for FPSort expressions: [this] - [divisor] * n, where n in Z is closest to
 * [this]/[divisor].
 */
infix fun (() -> Expression<FPSort>).fprem(divisor: () -> Expression<FPSort>) =
    FPRem(this(), divisor())

/**
 * Remainder operator for FPSort expressions: [this] - [divisor] * n, where n in Z is closest to
 * [this]/[divisor].
 *
 * Converts [this] from [Float] to [FPLiteral] with sort (_ FloatingPoint 8 24).
 */
infix fun Float.fprem(divisor: Expression<FPSort>) = FPRem(FPLiteral(this), divisor)

/**
 * Remainder operator for FPSort expressions: [this] - [divisor] * n, where n in Z is closest to
 * [this]/[divisor].
 *
 * Converts [this] from [Float] to [FPLiteral] with sort (_ FloatingPoint 8 24).
 */
infix fun Float.fprem(divisor: () -> Expression<FPSort>) = FPRem(FPLiteral(this), divisor())

/**
 * Remainder operator for FPSort expressions: [this] - [divisor] * n, where n in Z is closest to
 * [this]/[divisor].
 *
 * Converts [divisor] from [Float] to [FPLiteral] with sort (_ FloatingPoint 8 24).
 */
infix fun Expression<FPSort>.fprem(divisor: Float) = FPRem(this, FPLiteral(divisor))

/**
 * Remainder operator for FPSort expressions: [this] - [divisor] * n, where n in Z is closest to
 * [this]/[divisor].
 *
 * Converts [divisor] from [Float] to [FPLiteral] with sort (_ FloatingPoint 8 24).
 */
infix fun (() -> Expression<FPSort>).fprem(divisor: Float) = FPRem(this(), FPLiteral(divisor))

/**
 * Remainder operator for FPSort expressions: [this] - [divisor] * n, where n in Z is closest to
 * [this]/[divisor].
 *
 * Converts [this] from [Double] to [FPLiteral] with sort (_ FloatingPoint 11 53).
 */
infix fun Double.fprem(divisor: Expression<FPSort>) = FPRem(FPLiteral(this), divisor)

/**
 * Remainder operator for FPSort expressions: [this] - [divisor] * n, where n in Z is closest to
 * [this]/[divisor].
 *
 * Converts [this] from [Double] to [FPLiteral] with sort (_ FloatingPoint 11 53).
 */
infix fun Double.fprem(divisor: () -> Expression<FPSort>) = FPRem(FPLiteral(this), divisor())

/**
 * Remainder operator for FPSort expressions: [this] - [divisor] * n, where n in Z is closest to
 * [this]/[divisor].
 *
 * Converts [divisor] from [Double] to [FPLiteral] with sort (_ FloatingPoint 11 53).
 */
infix fun Expression<FPSort>.fprem(divisor: Double) = FPRem(this, FPLiteral(divisor))

/**
 * Remainder operator for FPSort expressions: [this] - [divisor] * n, where n in Z is closest to
 * [this]/[divisor].
 *
 * Converts [divisor] from [Double] to [FPLiteral] with sort (_ FloatingPoint 11 53).
 */
infix fun (() -> Expression<FPSort>).fprem(divisor: Double) = FPRem(this(), FPLiteral(divisor))

/*
 * unary floating-point operations
 */

/** Square root operator for FPSort expressions. */
fun fpsqrt(roundingMode: Expression<RoundingModeSort> = RNE, block: () -> Expression<FPSort>) =
    FPSqrt(roundingMode, block())

/** Square root operator for FPSort expressions. */
fun fpsqrt(roundingMode: Expression<RoundingModeSort> = RNE, expr: Expression<FPSort>) =
    FPSqrt(roundingMode, expr)

/**
 * Square root operator for FPSort expressions.
 *
 * Converts [expr] from [Float] to [FPLiteral] with sort (_ FloatingPoint 8 24).
 */
fun fpsqrt(roundingMode: Expression<RoundingModeSort> = RNE, expr: Float) =
    FPSqrt(roundingMode, FPLiteral(expr))

/**
 * Square root operator for FPSort expressions.
 *
 * Converts [expr] from [Double] to [FPLiteral] with sort (_ FloatingPoint 11 53).
 */
fun fpsqrt(roundingMode: Expression<RoundingModeSort> = RNE, expr: Double) =
    FPSqrt(roundingMode, FPLiteral(expr))

/** Round to integral operator for FPSort expressions. */
fun fproundToIntegral(
    roundingMode: Expression<RoundingModeSort> = RNE,
    block: () -> Expression<FPSort>,
) = FPRoundToIntegral(roundingMode, block())

/** Round to integral operator for FPSort expressions. */
fun fproundToIntegral(roundingMode: Expression<RoundingModeSort> = RNE, expr: Expression<FPSort>) =
    FPRoundToIntegral(roundingMode, expr)

/**
 * Round to integral operator for FPSort expressions.
 *
 * Converts [expr] from [Float] to [FPLiteral] with sort (_ FloatingPoint 8 24).
 */
fun fproundToIntegral(roundingMode: Expression<RoundingModeSort> = RNE, expr: Float) =
    FPRoundToIntegral(roundingMode, FPLiteral(expr))

/**
 * Round to integral operator for FPSort expressions.
 *
 * Converts [expr] from [Double] to [FPLiteral] with sort (_ FloatingPoint 11 53).
 */
fun fproundToIntegral(roundingMode: Expression<RoundingModeSort> = RNE, expr: Double) =
    FPRoundToIntegral(roundingMode, FPLiteral(expr))

/*
 * floating-point comparison operators
 */

/** Min operator for FPSort expressions. */
fun fpmin(lhs: Expression<FPSort>, rhs: Expression<FPSort>) = FPMin(lhs, rhs)

/** Min operator for FPSort expressions. */
fun fpmin(lhs: Expression<FPSort>, rhs: () -> Expression<FPSort>) = FPMin(lhs, rhs())

/** Min operator for FPSort expressions. */
fun fpmin(lhs: () -> Expression<FPSort>, rhs: Expression<FPSort>) = FPMin(lhs(), rhs)

/** Min operator for FPSort expressions. */
fun fpmin(lhs: () -> Expression<FPSort>, rhs: () -> Expression<FPSort>) = FPMin(lhs(), rhs())

/**
 * Min operator for FPSort expressions.
 *
 * Converts [rhs] from [Float] to [FPLiteral] with sort (_ FloatingPoint 4 24).
 */
fun fpmin(lhs: Expression<FPSort>, rhs: Float) = FPMin(lhs, FPLiteral(rhs))

/**
 * Min operator for FPSort expressions.
 *
 * Converts [rhs] from [Double] to [FPLiteral] with sort (_ FloatingPoint 11 53).
 */
fun fpmin(lhs: Expression<FPSort>, rhs: Double) = FPMin(lhs, FPLiteral(rhs))

/**
 * Min operator for FPSort expressions.
 *
 * Converts [lhs] from [Float] to [FPLiteral] with sort (_ FloatingPoint 4 24).
 */
fun fpmin(lhs: Float, rhs: Expression<FPSort>) = FPMin(FPLiteral(lhs), rhs)

/**
 * Min operator for FPSort expressions.
 *
 * Converts [lhs] from [Double] to [FPLiteral] with sort (_ FloatingPoint 11 53).
 */
fun fpmin(lhs: Double, rhs: Expression<FPSort>) = FPMin(FPLiteral(lhs), rhs)

/** Max operator for FPSort expressions. */
fun fpmax(lhs: Expression<FPSort>, rhs: Expression<FPSort>) = FPMax(lhs, rhs)

/** Max operator for FPSort expressions. */
fun fpmax(lhs: Expression<FPSort>, rhs: () -> Expression<FPSort>) = FPMax(lhs, rhs())

/** Max operator for FPSort expressions. */
fun fpmax(lhs: () -> Expression<FPSort>, rhs: Expression<FPSort>) = FPMax(lhs(), rhs)

/** Max operator for FPSort expressions. */
fun fpmax(lhs: () -> Expression<FPSort>, rhs: () -> Expression<FPSort>) = FPMax(lhs(), rhs())

/**
 * Max operator for FPSort expressions.
 *
 * Converts [rhs] from [Float] to [FPLiteral] with sort (_ FloatingPoint 4 24).
 */
fun fpmax(lhs: Expression<FPSort>, rhs: Float) = FPMax(lhs, FPLiteral(rhs))

/**
 * Max operator for FPSort expressions.
 *
 * Converts [rhs] from [Double] to [FPLiteral] with sort (_ FloatingPoint 11 53).
 */
fun fpmax(lhs: Expression<FPSort>, rhs: Double) = FPMax(lhs, FPLiteral(rhs))

/**
 * Max operator for FPSort expressions.
 *
 * Converts [lhs] from [Float] to [FPLiteral] with sort (_ FloatingPoint 4 24).
 */
fun fpmax(lhs: Float, rhs: Expression<FPSort>) = FPMax(FPLiteral(lhs), rhs)

/**
 * Max operator for FPSort expressions.
 *
 * Converts [lhs] from [Double] to [FPLiteral] with sort (_ FloatingPoint 11 53).
 */
fun fpmax(lhs: Double, rhs: Expression<FPSort>) = FPMax(FPLiteral(lhs), rhs)

/** Less equals operator for FPSort expressions: [this] <= [rhs]. */
infix fun Expression<FPSort>.fpleq(rhs: Expression<FPSort>) = FPLeq(this, rhs)

/** Less than operator for FPSort expressions: [this] < [rhs]. */
infix fun Expression<FPSort>.fplt(rhs: Expression<FPSort>) = FPLt(this, rhs)

/** Greater equals operator for FPSort expressions: [this] >= [rhs]. */
infix fun Expression<FPSort>.fpgeq(rhs: Expression<FPSort>) = FPGeq(this, rhs)

/** Greater than operator for FPSort expressions: [this] > [rhs]. */
infix fun Expression<FPSort>.fpgt(rhs: Expression<FPSort>) = FPGt(this, rhs)

/** Equals operator for FPSort expressions: [this] = [rhs]. */
infix fun Expression<FPSort>.fpeq(rhs: Expression<FPSort>) = FPEq(this, rhs)

/** Less equals operator for FPSort expressions: [this] <= [rhs]. */
infix fun Expression<FPSort>.fpleq(rhs: () -> Expression<FPSort>) = FPLeq(this, rhs())

/** Less than operator for FPSort expressions: [this] < [rhs]. */
infix fun Expression<FPSort>.fplt(rhs: () -> Expression<FPSort>) = FPLt(this, rhs())

/** Greater equals operator for FPSort expressions: [this] >= [rhs]. */
infix fun Expression<FPSort>.fpgeq(rhs: () -> Expression<FPSort>) = FPGeq(this, rhs())

/** Greater than operator for FPSort expressions: [this] > [rhs]. */
infix fun Expression<FPSort>.fpgt(rhs: () -> Expression<FPSort>) = FPGt(this, rhs())

/** Equals operator for FPSort expressions: [this] = [rhs]. */
infix fun Expression<FPSort>.fpeq(rhs: () -> Expression<FPSort>) = FPEq(this, rhs())

/** Less equals operator for FPSort expressions: [this] <= [rhs]. */
@JvmName("fpleq_expr")
infix fun (() -> Expression<FPSort>).fpleq(rhs: Expression<FPSort>) = FPLeq(this(), rhs)

/** Less than operator for FPSort expressions: [this] < [rhs]. */
@JvmName("fplt_expr")
infix fun (() -> Expression<FPSort>).fplt(rhs: Expression<FPSort>) = FPLt(this(), rhs)

/** Greater equals operator for FPSort expressions: [this] >= [rhs]. */
@JvmName("fpgeq_expr")
infix fun (() -> Expression<FPSort>).fpgeq(rhs: Expression<FPSort>) = FPGeq(this(), rhs)

/** Greater than operator for FPSort expressions: [this] > [rhs]. */
@JvmName("fpgt_expr")
infix fun (() -> Expression<FPSort>).fpgt(rhs: Expression<FPSort>) = FPGt(this(), rhs)

/** Equals operator for FPSort expressions: [this] = [rhs]. */
@JvmName("fpeq_expr")
infix fun (() -> Expression<FPSort>).fpeq(rhs: Expression<FPSort>) = FPEq(this(), rhs)

/** Less equals operator for FPSort expressions: [this] <= [rhs]. */
@JvmName("fpleq_lambda")
infix fun (() -> Expression<FPSort>).fpleq(rhs: () -> Expression<FPSort>) = FPLeq(this(), rhs())

/** Less than operator for FPSort expressions: [this] < [rhs]. */
@JvmName("fplt_lambda")
infix fun (() -> Expression<FPSort>).fplt(rhs: () -> Expression<FPSort>) = FPLt(this(), rhs())

/** Greater equals operator for FPSort expressions: [this] >= [rhs]. */
@JvmName("fpgeq_lambda")
infix fun (() -> Expression<FPSort>).fpgeq(rhs: () -> Expression<FPSort>) = FPGeq(this(), rhs())

/** Greater than operator for FPSort expressions: [this] > [rhs]. */
@JvmName("fpgt_lambda")
infix fun (() -> Expression<FPSort>).fpgt(rhs: () -> Expression<FPSort>) = FPGt(this(), rhs())

/** Equals operator for FPSort expressions: [this] = [rhs]. */
@JvmName("fpeq_lambda")
infix fun (() -> Expression<FPSort>).fpeq(rhs: () -> Expression<FPSort>) = FPEq(this(), rhs())

/** Less equals operator for FPSort expressions: [this] <= [rhs]. */
infix fun FPLeq.fpleq(rhs: Expression<FPSort>) = FPLeq(this.children + rhs)

/** Less than operator for FPSort expressions: [this] < [rhs]. */
infix fun FPLt.fplt(rhs: Expression<FPSort>) = FPLt(this.children + rhs)

/** Greater equals operator for FPSort expressions: [this] >= [rhs]. */
infix fun FPGeq.fpgeq(rhs: Expression<FPSort>) = FPGeq(this.children + rhs)

/** Greater than operator for FPSort expressions: [this] > [rhs]. */
infix fun FPGt.fpgt(rhs: Expression<FPSort>) = FPGt(this.children + rhs)

/** Equals operator for FPSort expressions: [this] = [rhs]. */
infix fun FPEq.fpeq(rhs: Expression<FPSort>) = FPEq(this.children + rhs)

/** Less equals operator for FPSort expressions: [this] <= [rhs]. */
infix fun FPLeq.fpleq(rhs: () -> Expression<FPSort>) = FPLeq(this.children + rhs())

/** Less than operator for FPSort expressions: [this] < [rhs]. */
infix fun FPLt.fplt(rhs: () -> Expression<FPSort>) = FPLt(this.children + rhs())

/** Greater equals operator for FPSort expressions: [this] >= [rhs]. */
infix fun FPGeq.fpgeq(rhs: () -> Expression<FPSort>) = FPGeq(this.children + rhs())

/** Greater than operator for FPSort expressions: [this] > [rhs]. */
infix fun FPGt.fpgt(rhs: () -> Expression<FPSort>) = FPGt(this.children + rhs())

/** Equals operator for FPSort expressions: [this] = [rhs]. */
infix fun FPEq.fpeq(rhs: () -> Expression<FPSort>) = FPEq(this.children + rhs())

/** Less equals operator for FPSort expressions: [this] <= [rhs]. */
infix fun (() -> FPLeq).fpleq(rhs: Expression<FPSort>) = FPLeq(this().children + rhs)

/** Less than operator for FPSort expressions: [this] < [rhs]. */
infix fun (() -> FPLt).fplt(rhs: Expression<FPSort>) = FPLt(this().children + rhs)

/** Greater equals operator for FPSort expressions: [this] >= [rhs]. */
infix fun (() -> FPGeq).fpgeq(rhs: Expression<FPSort>) = FPGeq(this().children + rhs)

/** Greater than operator for FPSort expressions: [this] > [rhs]. */
infix fun (() -> FPGt).fpgt(rhs: Expression<FPSort>) = FPGt(this().children + rhs)

/** Equals operator for FPSort expressions: [this] = [rhs]. */
infix fun (() -> FPEq).fpeq(rhs: Expression<FPSort>) = FPEq(this().children + rhs)

/** Less equals operator for FPSort expressions: [this] <= [rhs]. */
infix fun (() -> FPLeq).fpleq(rhs: () -> Expression<FPSort>) = FPLeq(this().children + rhs())

/** Less than operator for FPSort expressions: [this] < [rhs]. */
infix fun (() -> FPLt).fplt(rhs: () -> Expression<FPSort>) = FPLt(this().children + rhs())

/** Greater equals operator for FPSort expressions: [this] >= [rhs]. */
infix fun (() -> FPGeq).fpgeq(rhs: () -> Expression<FPSort>) = FPGeq(this().children + rhs())

/** Greater than operator for FPSort expressions: [this] > [rhs]. */
infix fun (() -> FPGt).fpgt(rhs: () -> Expression<FPSort>) = FPGt(this().children + rhs())

/** Equals operator for FPSort expressions: [this] = [rhs]. */
infix fun (() -> FPEq).fpeq(rhs: () -> Expression<FPSort>) = FPEq(this().children + rhs())

/**
 * Less equals operator for FPSort expressions: [this] <= [rhs].
 *
 * Converts [rhs] from [Float] to [FPLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Expression<FPSort>.fpleq(rhs: Float) = FPLeq(this, FPLiteral(rhs))

/**
 * Less equals operator for FPSort expressions: [this] <= [rhs].
 *
 * Converts [rhs] from [Double] to [FPLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Expression<FPSort>.fpleq(rhs: Double) = FPLeq(this, FPLiteral(rhs))

/**
 * Less than operator for FPSort expressions: [this] < [rhs].
 *
 * Converts [rhs] from [Float] to [FPLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Expression<FPSort>.fplt(rhs: Float) = FPLt(this, FPLiteral(rhs))

/**
 * Less than operator for FPSort expressions: [this] < [rhs].
 *
 * Converts [rhs] from [Double] to [FPLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Expression<FPSort>.fplt(rhs: Double) = FPLt(this, FPLiteral(rhs))

/**
 * Greater equals operator for FPSort expressions: [this] >= [rhs].
 *
 * Converts [rhs] from [Float] to [FPLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Expression<FPSort>.fpgeq(rhs: Float) = FPGeq(this, FPLiteral(rhs))

/**
 * Greater equals operator for FPSort expressions: [this] >= [rhs].
 *
 * Converts [rhs] from [Double] to [FPLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Expression<FPSort>.fpgeq(rhs: Double) = FPGeq(this, FPLiteral(rhs))

/**
 * Greater than operator for FPSort expressions: [this] > [rhs].
 *
 * Converts [rhs] from [Float] to [FPLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Expression<FPSort>.fpgt(rhs: Float) = FPGt(this, FPLiteral(rhs))

/**
 * Greater than operator for FPSort expressions: [this] > [rhs].
 *
 * Converts [rhs] from [Double] to [FPLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Expression<FPSort>.fpgt(rhs: Double) = FPGt(this, FPLiteral(rhs))

/**
 * Equals operator for FPSort expressions: [this] = [rhs].
 *
 * Converts [rhs] from [Float] to [FPLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Expression<FPSort>.fpeq(rhs: Float) = FPEq(this, FPLiteral(rhs))

/**
 * Equals operator for FPSort expressions: [this] = [rhs].
 *
 * Converts [rhs] from [Double] to [FPLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Expression<FPSort>.fpeq(rhs: Double) = FPEq(this, FPLiteral(rhs))

/**
 * Less equals operator for FPSort expressions: [this] <= [rhs].
 *
 * Converts [rhs] from [Float] to [FPLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun (() -> Expression<FPSort>).fpleq(rhs: Float) = FPLeq(this(), FPLiteral(rhs))

/**
 * Less equals operator for FPSort expressions: [this] <= [rhs].
 *
 * Converts [rhs] from [Double] to [FPLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun (() -> Expression<FPSort>).fpleq(rhs: Double) = FPLeq(this(), FPLiteral(rhs))

/**
 * Less than operator for FPSort expressions: [this] < [rhs].
 *
 * Converts [rhs] from [Float] to [FPLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun (() -> Expression<FPSort>).fplt(rhs: Float) = FPLt(this(), FPLiteral(rhs))

/**
 * Less than operator for FPSort expressions: [this] < [rhs].
 *
 * Converts [rhs] from [Double] to [FPLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun (() -> Expression<FPSort>).fplt(rhs: Double) = FPLt(this(), FPLiteral(rhs))

/**
 * Greater equals operator for FPSort expressions: [this] >= [rhs].
 *
 * Converts [rhs] from [Float] to [FPLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun (() -> Expression<FPSort>).fpgeq(rhs: Float) = FPGeq(this(), FPLiteral(rhs))

/**
 * Greater equals operator for FPSort expressions: [this] >= [rhs].
 *
 * Converts [rhs] from [Double] to [FPLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun (() -> Expression<FPSort>).fpgeq(rhs: Double) = FPGeq(this(), FPLiteral(rhs))

/**
 * Greater than operator for FPSort expressions: [this] > [rhs].
 *
 * Converts [rhs] from [Float] to [FPLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun (() -> Expression<FPSort>).fpgt(rhs: Float) = FPGt(this(), FPLiteral(rhs))

/**
 * Greater than operator for FPSort expressions: [this] > [rhs].
 *
 * Converts [rhs] from [Double] to [FPLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun (() -> Expression<FPSort>).fpgt(rhs: Double) = FPGt(this(), FPLiteral(rhs))

/**
 * Equals operator for FPSort expressions: [this] = [rhs].
 *
 * Converts [rhs] from [Float] to [FPLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun (() -> Expression<FPSort>).fpeq(rhs: Float) = FPEq(this(), FPLiteral(rhs))

/**
 * Equals operator for FPSort expressions: [this] = [rhs].
 *
 * Converts [rhs] from [Double] to [FPLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun (() -> Expression<FPSort>).fpeq(rhs: Double) = FPEq(this(), FPLiteral(rhs))

/**
 * Less equals operator for FPSort expressions: [this] <= [rhs].
 *
 * Converts [rhs] from [Float] to [FPLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Float.fpleq(rhs: Expression<FPSort>) = FPLeq(FPLiteral(this), rhs)

/**
 * Less equals operator for FPSort expressions: [this] <= [rhs].
 *
 * Converts [rhs] from [Double] to [FPLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Double.fpleq(rhs: Expression<FPSort>) = FPLeq(FPLiteral(this), rhs)

/**
 * Less than operator for FPSort expressions: [this] < [rhs].
 *
 * Converts [rhs] from [Float] to [FPLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Float.fplt(rhs: Expression<FPSort>) = FPLt(FPLiteral(this), rhs)

/**
 * Less than operator for FPSort expressions: [this] < [rhs].
 *
 * Converts [rhs] from [Double] to [FPLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Double.fplt(rhs: Expression<FPSort>) = FPLt(FPLiteral(this), rhs)

/**
 * Greater equals operator for FPSort expressions: [this] >= [rhs].
 *
 * Converts [rhs] from [Float] to [FPLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Float.fpgeq(rhs: Expression<FPSort>) = FPGeq(FPLiteral(this), rhs)

/**
 * Greater equals operator for FPSort expressions: [this] >= [rhs].
 *
 * Converts [rhs] from [Double] to [FPLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Double.fpgeq(rhs: Expression<FPSort>) = FPGeq(FPLiteral(this), rhs)

/**
 * Greater than operator for FPSort expressions: [this] > [rhs].
 *
 * Converts [rhs] from [Float] to [FPLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Float.fpgt(rhs: Expression<FPSort>) = FPGt(FPLiteral(this), rhs)

/**
 * Greater than operator for FPSort expressions: [this] > [rhs].
 *
 * Converts [rhs] from [Double] to [FPLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Double.fpgt(rhs: Expression<FPSort>) = FPGt(FPLiteral(this), rhs)

/**
 * Equals operator for FPSort expressions: [this] = [rhs].
 *
 * Converts [rhs] from [Float] to [FPLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Float.fpeq(rhs: Expression<FPSort>) = FPEq(FPLiteral(this), rhs)

/**
 * Equals operator for FPSort expressions: [this] = [rhs].
 *
 * Converts [rhs] from [Double] to [FPLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Double.fpeq(rhs: Expression<FPSort>) = FPEq(FPLiteral(this), rhs)

/**
 * Less equals operator for FPSort expressions: [this] <= [rhs].
 *
 * Converts [rhs] from [Float] to [FPLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Float.fpleq(rhs: () -> Expression<FPSort>) = FPLeq(FPLiteral(this), rhs())

/**
 * Less equals operator for FPSort expressions: [this] <= [rhs].
 *
 * Converts [rhs] from [Double] to [FPLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Double.fpleq(rhs: () -> Expression<FPSort>) = FPLeq(FPLiteral(this), rhs())

/**
 * Less than operator for FPSort expressions: [this] < [rhs].
 *
 * Converts [rhs] from [Float] to [FPLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Float.fplt(rhs: () -> Expression<FPSort>) = FPLt(FPLiteral(this), rhs())

/**
 * Less than operator for FPSort expressions: [this] < [rhs].
 *
 * Converts [rhs] from [Double] to [FPLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Double.fplt(rhs: () -> Expression<FPSort>) = FPLt(FPLiteral(this), rhs())

/**
 * Greater equals operator for FPSort expressions: [this] >= [rhs].
 *
 * Converts [rhs] from [Float] to [FPLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Float.fpgeq(rhs: () -> Expression<FPSort>) = FPGeq(FPLiteral(this), rhs())

/**
 * Greater equals operator for FPSort expressions: [this] >= [rhs].
 *
 * Converts [rhs] from [Double] to [FPLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Double.fpgeq(rhs: () -> Expression<FPSort>) = FPGeq(FPLiteral(this), rhs())

/**
 * Greater than operator for FPSort expressions: [this] > [rhs].
 *
 * Converts [rhs] from [Float] to [FPLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Float.fpgt(rhs: () -> Expression<FPSort>) = FPGt(FPLiteral(this), rhs())

/**
 * Greater than operator for FPSort expressions: [this] > [rhs].
 *
 * Converts [rhs] from [Double] to [FPLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Double.fpgt(rhs: () -> Expression<FPSort>) = FPGt(FPLiteral(this), rhs())

/**
 * Equals operator for FPSort expressions: [this] = [rhs].
 *
 * Converts [rhs] from [Float] to [FPLiteral] with sort [(_ FloatingPoint 8 24)].
 */
infix fun Float.fpeq(rhs: () -> Expression<FPSort>) = FPEq(FPLiteral(this), rhs())

/**
 * Equals operator for FPSort expressions: [this] = [rhs].
 *
 * Converts [rhs] from [Double] to [FPLiteral] with sort [(_ FloatingPoint 11 53)].
 */
infix fun Double.fpeq(rhs: () -> Expression<FPSort>) = FPEq(FPLiteral(this), rhs())

/*
 * floating-point conversion operations
 */

/**
 * Conversion operator from single bitstring representation in IEEE 754-2008 interchange format to
 * floating point.
 */
@JvmName("BVToFP")
fun toFP(eb: Int, sb: Int, block: () -> Expression<BVSort>) = BitVecToFP(block(), eb, sb)

/**
 * Conversion operator from single bitstring representation in IEEE 754-2008 interchange format to
 * floating point.
 */
@JvmName("BVToFP") fun toFP(eb: Int, sb: Int, expr: Expression<BVSort>) = BitVecToFP(expr, eb, sb)

/**
 * Conversion operator from single bitstring representation in IEEE 754-2008 interchange format to
 * floating point.
 */
fun Expression<BVSort>.toFP(eb: Int, sb: Int) = BitVecToFP(this, eb, sb)

/**
 * Conversion operator from single bitstring representation in IEEE 754-2008 interchange format to
 * floating point.
 */
fun Expression<BVSort>.toFP(sort: FPSort) = BitVecToFP(this, sort)

/** Conversion operator from another floating point sort to floating point sort. */
@JvmName("FPToFP")
fun toFP(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingModeSort> = RNE,
    block: () -> Expression<FPSort>,
) = FPToFP(roundingMode, block(), eb, sb)

/** Conversion operator from another floating point sort to floating point sort. */
@JvmName("FPToFP")
fun toFP(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingModeSort> = RNE,
    expr: Expression<FPSort>,
) = FPToFP(roundingMode, expr, eb, sb)

/** Conversion operator from another floating point sort to floating point sort. */
fun Expression<FPSort>.toFP(eb: Int, sb: Int, roundingMode: Expression<RoundingModeSort> = RNE) =
    FPToFP(roundingMode, this, eb, sb)

/** Conversion operator from another floating point sort to floating point sort. */
fun Expression<FPSort>.toFP(sort: FPSort, roundingMode: Expression<RoundingModeSort> = RNE) =
    FPToFP(roundingMode, this, sort)

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
fun Expression<RealSort>.toFP(sort: FPSort, roundingMode: Expression<RoundingModeSort> = RNE) =
    RealToFP(roundingMode, this, sort)

/**
 * Conversion operator from signed machine integer, represented as a 2's complement bit vector to
 * floating point.
 */
@JvmName("SBVToFP")
fun toFPSigned(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingModeSort> = RNE,
    block: () -> Expression<BVSort>,
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
    expr: Expression<BVSort>,
) = SBitVecToFP(roundingMode, expr, eb, sb)

/**
 * Conversion operator from signed machine integer, represented as a 2's complement bit vector to
 * floating point.
 */
fun Expression<BVSort>.toFPSigned(eb: Int, sb: Int, roundingMode: Expression<RoundingModeSort>) =
    SBitVecToFP(roundingMode, this, eb, sb)

/**
 * Conversion operator from signed machine integer, represented as a 2's complement bit vector to
 * floating point.
 */
fun Expression<BVSort>.toFPSigned(sort: FPSort, roundingMode: Expression<RoundingModeSort>) =
    SBitVecToFP(roundingMode, this, sort)

/**
 * Conversion operator from unsigned machine integer, represented as a 2's complement bit vector to
 * floating point.
 */
@JvmName("UBVToFP")
fun toFPUnsigned(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingModeSort> = RNE,
    block: () -> Expression<BVSort>,
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
    expr: Expression<BVSort>,
) = UBitVecToFP(roundingMode, expr, eb, sb)

/**
 * Conversion operator from unsigned machine integer, represented as a 2's complement bit vector to
 * floating point.
 */
fun Expression<BVSort>.toFPUnsigned(eb: Int, sb: Int, roundingMode: Expression<RoundingModeSort>) =
    UBitVecToFP(roundingMode, this, eb, sb)

/**
 * Conversion operator from unsigned machine integer, represented as a 2's complement bit vector to
 * floating point.
 */
fun Expression<BVSort>.toFPUnsigned(sort: FPSort, roundingMode: Expression<RoundingModeSort>) =
    UBitVecToFP(roundingMode, this, sort)

/**
 * Conversion operator to unsigned machine integer, represented as a bit vector (_ BitVec [bits]).
 */
fun toUBV(
    bits: Int,
    roundingMode: Expression<RoundingModeSort> = RNE,
    block: () -> Expression<FPSort>,
) = FPToUBitVec(roundingMode, block(), bits)

/**
 * Conversion operator to unsigned machine integer, represented as a bit vector (_ BitVec [bits]).
 */
fun toUBV(bits: Int, roundingMode: Expression<RoundingModeSort> = RNE, expr: Expression<FPSort>) =
    FPToUBitVec(roundingMode, expr, bits)

/**
 * Conversion operator to unsigned machine integer, represented as a bit vector (_ BitVec [bits]).
 */
fun Expression<FPSort>.toUBV(bits: Int, roundingMode: Expression<RoundingModeSort> = RNE) =
    FPToUBitVec(roundingMode, this, bits)

/** Conversion operator to unsigned machine integer, represented as a bit vector [sort]. */
fun Expression<FPSort>.toUBV(sort: BVSort, roundingMode: Expression<RoundingModeSort> = RNE) =
    FPToUBitVec(roundingMode, this, sort.bits)

/**
 * Conversion operator to signed machine integer, represented as a 2's complement bit vector (_
 * BitVec [bits]).
 */
fun toSBV(
    bits: Int,
    roundingMode: Expression<RoundingModeSort> = RNE,
    block: () -> Expression<FPSort>,
) = FPToSBitVec(roundingMode, block(), bits)

/**
 * Conversion operator to signed machine integer, represented as a 2's complement bit vector (_
 * BitVec [bits]).
 */
fun toSBV(bits: Int, roundingMode: Expression<RoundingModeSort> = RNE, expr: Expression<FPSort>) =
    FPToSBitVec(roundingMode, expr, bits)

/**
 * Conversion operator to signed machine integer, represented as a 2's complement bit vector (_
 * BitVec [bits]).
 */
fun Expression<FPSort>.toSBV(bits: Int, roundingMode: Expression<RoundingModeSort> = RNE) =
    FPToSBitVec(roundingMode, this, bits)

/**
 * Conversion operator to signed machine integer, represented as a 2's complement bit vector (_
 * BitVec [sort.bits]).
 */
fun Expression<FPSort>.toSBV(sort: BVSort, roundingMode: Expression<RoundingModeSort> = RNE) =
    FPToSBitVec(roundingMode, this, sort.bits)

/** Conversion operator to real sort. */
fun toReal(block: () -> Expression<FPSort>) = FPToReal(block())

/** Conversion operator to real sort. */
@JvmName("toReal1") fun toReal(expr: Expression<FPSort>) = FPToReal(expr)

/** Conversion operator to real sort. */
@JvmName("toReal2") fun Expression<FPSort>.toReal() = FPToReal(this)

/*
 * fpfma
 */

/**
 * Fused multiplication addition operator ([multiplier] * multiplicand + summand) for FPSort
 * expressions. Must be followed by [FPFMA1.mul] and [FPFMA2.add].
 *
 * @param roundingMode: floating point rounding mode.
 */
fun fpfma(roundingMode: Expression<RoundingModeSort> = RNE, multiplier: () -> Expression<FPSort>) =
    FPFMA1(roundingMode, multiplier())

/**
 * Fused multiplication addition operator ([multiplier] * multiplicand + summand) for FPSort
 * expressions. Must be followed by [FPFMA1.mul] and [FPFMA2.add].
 *
 * @param roundingMode: floating point rounding mode.
 */
fun fpfma(roundingMode: Expression<RoundingModeSort> = RNE, multiplier: Expression<FPSort>) =
    FPFMA1(roundingMode, multiplier)

/**
 * Multiplication stage of fp.fma.
 *
 * Must be followed by [FPFMA2].
 */
class FPFMA1(val roundingMode: Expression<RoundingModeSort>, val multiplier: Expression<FPSort>) {

  /**
   * Fused multiplication addition operator (multiplier * [multiplicand] + summand) for FPSort
   * expressions.
   *
   * Must be followed by [FPFMA2.add].
   */
  infix fun mul(multiplicand: Expression<FPSort>) = FPFMA2(roundingMode, multiplier, multiplicand)

  /**
   * Fused multiplication addition operator (multiplier * [multiplicand] + summand) for FPSort
   * expressions.
   *
   * Must be followed by [FPFMA2.add].
   */
  infix fun mul(multiplicand: () -> Expression<FPSort>) =
      FPFMA2(roundingMode, multiplier, multiplicand())
}

/** Addition stage of fp.fma. */
class FPFMA2(
    val roundingMode: Expression<RoundingModeSort>,
    val multiplier: Expression<FPSort>,
    val multiplicand: Expression<FPSort>,
) {

  /**
   * Fused multiplication addition operator (multiplier * multiplicand + [summand]) for FPSort
   * expressions.
   */
  infix fun add(summand: Expression<FPSort>) =
      FPFma(roundingMode, multiplier, multiplicand, summand)

  /**
   * Fused multiplication addition operator (multiplier * multiplicand + [summand]) for FPSort
   * expressions.
   */
  infix fun add(summand: () -> Expression<FPSort>) =
      FPFma(roundingMode, multiplier, multiplicand, summand())
}

/** Implements floating point isNormal operation. */
fun isNormal(expr: Expression<FPSort>) = FPIsNormal(expr)

/** Implements floating point isNormal operation. */
fun isNormal(block: () -> Expression<FPSort>) = FPIsNormal(block())

/** Implements floating point isSubnormal operation. */
fun isSubnormal(expr: Expression<FPSort>) = FPIsSubnormal(expr)

/** Implements floating point isSubnormal operation. */
fun isSubnormal(block: () -> Expression<FPSort>) = FPIsSubnormal(block())

/** Implements floating point isZero operation. */
fun isZero(expr: Expression<FPSort>) = FPIsZero(expr)

/** Implements floating point isZero operation. */
fun isZero(block: () -> Expression<FPSort>) = FPIsZero(block())

/** Implements floating point isInfinite operation. */
fun isInfinite(expr: Expression<FPSort>) = FPIsInfinite(expr)

/** Implements floating point isInfinite operation. */
fun isInfinite(block: () -> Expression<FPSort>) = FPIsInfinite(block())

/** Implements floating point isNaN operation. */
fun isNaN(expr: Expression<FPSort>) = FPIsNaN(expr)

/** Implements floating point isNaN operation. */
fun isNaN(block: () -> Expression<FPSort>) = FPIsNaN(block())

/** Implements floating point isNegative operation. */
fun isNegative(expr: Expression<FPSort>) = FPIsNegative(expr)

/** Implements floating point isNegative operation. */
fun isNegative(block: () -> Expression<FPSort>) = FPIsNegative(block())

/** Implements floating point isPositive operation. */
fun isPositive(expr: Expression<FPSort>) = FPIsPositive(expr)

/** Implements floating point isPositive operation. */
fun isPositive(block: () -> Expression<FPSort>) = FPIsPositive(block())

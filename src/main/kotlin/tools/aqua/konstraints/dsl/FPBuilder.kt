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
infix fun Expression<FPSort>.fpadd_rne(summand: () -> Expression<FPSort>) = FPAdd(RNE, this, summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun Expression<FPSort>.fpadd_rna(summand: () -> Expression<FPSort>) = FPAdd(RNA, this, summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun Expression<FPSort>.fpadd_rtp(summand: () -> Expression<FPSort>) = FPAdd(RTP, this, summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun Expression<FPSort>.fpadd_rtn(summand: () -> Expression<FPSort>) = FPAdd(RTN, this, summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun Expression<FPSort>.fpadd_rtz(summand: () -> Expression<FPSort>) = FPAdd(RTZ, this, summand())


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
infix fun (() -> Expression<FPSort>).fpadd_rne(summand: Expression<FPSort>) = FPAdd(RNE, this(), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun (() -> Expression<FPSort>).fpadd_rna(summand: Expression<FPSort>) = FPAdd(RNA, this(), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun (() -> Expression<FPSort>).fpadd_rtp(summand: Expression<FPSort>) = FPAdd(RTP, this(), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun (() -> Expression<FPSort>).fpadd_rtn(summand: Expression<FPSort>) = FPAdd(RTN, this(), summand)

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun (() -> Expression<FPSort>).fpadd_rtz(summand: Expression<FPSort>) = FPAdd(RTZ, this(), summand)


/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FPSort>).fpadd(summand: () -> Expression<FPSort>) = this() fpadd_rne summand()
/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FPSort>).fpadd_rne(summand: () -> Expression<FPSort>) = FPAdd(RNE, this(), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun (() -> Expression<FPSort>).fpadd_rna(summand: () -> Expression<FPSort>) = FPAdd(RNA, this(), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun (() -> Expression<FPSort>).fpadd_rtp(summand: () -> Expression<FPSort>) = FPAdd(RTP, this(), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun (() -> Expression<FPSort>).fpadd_rtn(summand: () -> Expression<FPSort>) = FPAdd(RTN, this(), summand())

/**
 * Addition operator for FPSort expressions: [this] + [summand].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun (() -> Expression<FPSort>).fpadd_rtz(summand: () -> Expression<FPSort>) = FPAdd(RTZ, this(), summand())


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
infix fun Expression<FPSort>.fpsub_rne(subtrahend: Expression<FPSort>) = FPSub(RNE, this, subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun Expression<FPSort>.fpsub_rna(subtrahend: Expression<FPSort>) = FPSub(RNA, this, subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun Expression<FPSort>.fpsub_rtp(subtrahend: Expression<FPSort>) = FPSub(RTP, this, subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun Expression<FPSort>.fpsub_rtn(subtrahend: Expression<FPSort>) = FPSub(RTN, this, subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun Expression<FPSort>.fpsub_rtz(subtrahend: Expression<FPSort>) = FPSub(RTZ, this, subtrahend)


/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun Expression<FPSort>.fpsub(subtrahend: () -> Expression<FPSort>) = this fpsub_rne subtrahend()
/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun Expression<FPSort>.fpsub_rne(subtrahend: () -> Expression<FPSort>) = FPSub(RNE, this, subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun Expression<FPSort>.fpsub_rna(subtrahend: () -> Expression<FPSort>) = FPSub(RNA, this, subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun Expression<FPSort>.fpsub_rtp(subtrahend: () -> Expression<FPSort>) = FPSub(RTP, this, subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun Expression<FPSort>.fpsub_rtn(subtrahend: () -> Expression<FPSort>) = FPSub(RTN, this, subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun Expression<FPSort>.fpsub_rtz(subtrahend: () -> Expression<FPSort>) = FPSub(RTZ, this, subtrahend())


/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FPSort>).fpsub(subtrahend: Expression<FPSort>) = this() fpsub_rne subtrahend
/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FPSort>).fpsub_rne(subtrahend: Expression<FPSort>) = FPSub(RNE, this(), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun (() -> Expression<FPSort>).fpsub_rna(subtrahend: Expression<FPSort>) = FPSub(RNA, this(), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun (() -> Expression<FPSort>).fpsub_rtp(subtrahend: Expression<FPSort>) = FPSub(RTP, this(), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun (() -> Expression<FPSort>).fpsub_rtn(subtrahend: Expression<FPSort>) = FPSub(RTN, this(), subtrahend)

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun (() -> Expression<FPSort>).fpsub_rtz(subtrahend: Expression<FPSort>) = FPSub(RTZ, this(), subtrahend)


/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FPSort>).fpsub(subtrahend: () -> Expression<FPSort>) = this() fpsub_rne subtrahend()
/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FPSort>).fpsub_rne(subtrahend: () -> Expression<FPSort>) = FPSub(RNE, this(), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun (() -> Expression<FPSort>).fpsub_rna(subtrahend: () -> Expression<FPSort>) = FPSub(RNA, this(), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun (() -> Expression<FPSort>).fpsub_rtp(subtrahend: () -> Expression<FPSort>) = FPSub(RTP, this(), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun (() -> Expression<FPSort>).fpsub_rtn(subtrahend: () -> Expression<FPSort>) = FPSub(RTN, this(), subtrahend())

/**
 * Subtraction operator for FPSort expressions: [this] - [subtrahend].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun (() -> Expression<FPSort>).fpsub_rtz(subtrahend: () -> Expression<FPSort>) = FPSub(RTZ, this(), subtrahend())


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
infix fun Expression<FPSort>.fpmul_rne(multiplicant: Expression<FPSort>) = FPMul(RNE, this, multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun Expression<FPSort>.fpmul_rna(multiplicant: Expression<FPSort>) = FPMul(RNA, this, multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun Expression<FPSort>.fpmul_rtp(multiplicant: Expression<FPSort>) = FPMul(RTP, this, multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun Expression<FPSort>.fpmul_rtn(multiplicant: Expression<FPSort>) = FPMul(RTN, this, multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun Expression<FPSort>.fpmul_rtz(multiplicant: Expression<FPSort>) = FPMul(RTZ, this, multiplicant)


/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun Expression<FPSort>.fpmul(multiplicant: () -> Expression<FPSort>) = this fpmul_rne multiplicant()
/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun Expression<FPSort>.fpmul_rne(multiplicant: () -> Expression<FPSort>) = FPMul(RNE, this, multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun Expression<FPSort>.fpmul_rna(multiplicant: () -> Expression<FPSort>) = FPMul(RNA, this, multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun Expression<FPSort>.fpmul_rtp(multiplicant: () -> Expression<FPSort>) = FPMul(RTP, this, multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun Expression<FPSort>.fpmul_rtn(multiplicant: () -> Expression<FPSort>) = FPMul(RTN, this, multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun Expression<FPSort>.fpmul_rtz(multiplicant: () -> Expression<FPSort>) = FPMul(RTZ, this, multiplicant())


/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FPSort>).fpmul(multiplicant: Expression<FPSort>) = this() fpmul_rne multiplicant
/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FPSort>).fpmul_rne(multiplicant: Expression<FPSort>) = FPMul(RNE, this(), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun (() -> Expression<FPSort>).fpmul_rna(multiplicant: Expression<FPSort>) = FPMul(RNA, this(), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun (() -> Expression<FPSort>).fpmul_rtp(multiplicant: Expression<FPSort>) = FPMul(RTP, this(), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun (() -> Expression<FPSort>).fpmul_rtn(multiplicant: Expression<FPSort>) = FPMul(RTN, this(), multiplicant)

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun (() -> Expression<FPSort>).fpmul_rtz(multiplicant: Expression<FPSort>) = FPMul(RTZ, this(), multiplicant)


/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FPSort>).fpmul(multiplicant: () -> Expression<FPSort>) = this() fpmul_rne multiplicant()
/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FPSort>).fpmul_rne(multiplicant: () -> Expression<FPSort>) = FPMul(RNE, this(), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun (() -> Expression<FPSort>).fpmul_rna(multiplicant: () -> Expression<FPSort>) = FPMul(RNA, this(), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun (() -> Expression<FPSort>).fpmul_rtp(multiplicant: () -> Expression<FPSort>) = FPMul(RTP, this(), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun (() -> Expression<FPSort>).fpmul_rtn(multiplicant: () -> Expression<FPSort>) = FPMul(RTN, this(), multiplicant())

/**
 * Multiplication operator for FPSort expressions: [this] * [multiplicant].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun (() -> Expression<FPSort>).fpmul_rtz(multiplicant: () -> Expression<FPSort>) = FPMul(RTZ, this(), multiplicant())


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
infix fun Expression<FPSort>.fpdiv_rne(divisor: () -> Expression<FPSort>) = FPDiv(RNE, this, divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun Expression<FPSort>.fpdiv_rna(divisor: () -> Expression<FPSort>) = FPDiv(RNA, this, divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun Expression<FPSort>.fpdiv_rtp(divisor: () -> Expression<FPSort>) = FPDiv(RTP, this, divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun Expression<FPSort>.fpdiv_rtn(divisor: () -> Expression<FPSort>) = FPDiv(RTN, this, divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun Expression<FPSort>.fpdiv_rtz(divisor: () -> Expression<FPSort>) = FPDiv(RTZ, this, divisor())


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
infix fun (() -> Expression<FPSort>).fpdiv_rne(divisor: Expression<FPSort>) = FPDiv(RNE, this(), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun (() -> Expression<FPSort>).fpdiv_rna(divisor: Expression<FPSort>) = FPDiv(RNA, this(), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun (() -> Expression<FPSort>).fpdiv_rtp(divisor: Expression<FPSort>) = FPDiv(RTP, this(), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun (() -> Expression<FPSort>).fpdiv_rtn(divisor: Expression<FPSort>) = FPDiv(RTN, this(), divisor)

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun (() -> Expression<FPSort>).fpdiv_rtz(divisor: Expression<FPSort>) = FPDiv(RTZ, this(), divisor)


/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses default rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FPSort>).fpdiv(divisor: () -> Expression<FPSort>) = this() fpdiv_rne divisor()
/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest even'.
 */
infix fun (() -> Expression<FPSort>).fpdiv_rne(divisor: () -> Expression<FPSort>) = FPDiv(RNE, this(), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round to nearest away'.
 */
infix fun (() -> Expression<FPSort>).fpdiv_rna(divisor: () -> Expression<FPSort>) = FPDiv(RNA, this(), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward positive'.
 */
infix fun (() -> Expression<FPSort>).fpdiv_rtp(divisor: () -> Expression<FPSort>) = FPDiv(RTP, this(), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward negative'.
 */
infix fun (() -> Expression<FPSort>).fpdiv_rtn(divisor: () -> Expression<FPSort>) = FPDiv(RTN, this(), divisor())

/**
 * Division operator for FPSort expressions: [this] / [divisor].
 *
 * Uses rounding mode 'round toward zero'.
 */
infix fun (() -> Expression<FPSort>).fpdiv_rtz(divisor: () -> Expression<FPSort>) = FPDiv(RTZ, this(), divisor())

/**
 * Remainder operator for FPSort expressions: [this] - [divisor] * n, where n in Z is closest to [this]/[divisor].
 */
infix fun Expression<FPSort>.fprem(divisor: Expression<FPSort>) = FPRem(this, divisor)

/**
 * Remainder operator for FPSort expressions: [this] - [divisor] * n, where n in Z is closest to [this]/[divisor].
 */
infix fun Expression<FPSort>.fprem(divisor: () -> Expression<FPSort>) = FPRem(this, divisor())

/**
 * Remainder operator for FPSort expressions: [this] - [divisor] * n, where n in Z is closest to [this]/[divisor].
 */
infix fun (() -> Expression<FPSort>).fprem(divisor: Expression<FPSort>) = FPRem(this(), divisor)

/**
 * Remainder operator for FPSort expressions: [this] - [divisor] * n, where n in Z is closest to [this]/[divisor].
 */
infix fun (() -> Expression<FPSort>).fprem(divisor: () -> Expression<FPSort>) = FPRem(this(), divisor())

/*
 * unary floating-point operations
 */


/**
 * Square root operator for FPSort expressions.
 */
fun fpsqrt(roundingMode: Expression<RoundingMode> = RNE, block: () -> Expression<FPSort>) =
    FPSqrt(roundingMode, block())

/**
 * Square root operator for FPSort expressions.
 */
fun fpsqrt(roundingMode: Expression<RoundingMode> = RNE, expr: Expression<FPSort>) =
    FPSqrt(roundingMode, expr)

/**
 * Round to integral operator for FPSort expressions.
 */
fun fproundToIntegral(
    roundingMode: Expression<RoundingMode> = RNE,
    block: () -> Expression<FPSort>
) = FPRoundToIntegral(roundingMode, block())

/**
 * Round to integral operator for FPSort expressions.
 */
fun fproundToIntegral(roundingMode: Expression<RoundingMode> = RNE, expr: Expression<FPSort>) =
    FPRoundToIntegral(roundingMode, expr)

/*
 * floating-point comparison operators
 */


/**
 * Min operator for FPSort expressions.
 */
fun fpmin(rhs: Expression<FPSort>, lhs: Expression<FPSort>) = FPMin(rhs, lhs)

/**
 * Min operator for FPSort expressions.
 */
fun fpmin(rhs: Expression<FPSort>, lhs: () -> Expression<FPSort>) = FPMin(rhs, lhs())

/**
 * Min operator for FPSort expressions.
 */
fun fpmin(rhs: () -> Expression<FPSort>, lhs: Expression<FPSort>) = FPMin(rhs(), lhs)

/**
 * Min operator for FPSort expressions.
 */
fun fpmin(rhs: () -> Expression<FPSort>, lhs: () -> Expression<FPSort>) = FPMin(rhs(), lhs())

/**
 * Max operator for FPSort expressions.
 */
fun fpmax(rhs: Expression<FPSort>, lhs: Expression<FPSort>) = FPMax(rhs, lhs)

/**
 * Max operator for FPSort expressions.
 */
fun fpmax(rhs: Expression<FPSort>, lhs: () -> Expression<FPSort>) = FPMax(rhs, lhs())

/**
 * Max operator for FPSort expressions.
 */
fun fpmax(rhs: () -> Expression<FPSort>, lhs: Expression<FPSort>) = FPMax(rhs(), lhs)

/**
 * Max operator for FPSort expressions.
 */
fun fpmax(rhs: () -> Expression<FPSort>, lhs: () -> Expression<FPSort>) = FPMax(rhs(), lhs())

/**
 * Less equals operator for FPSort expressions: [this] <= [rhs].
 */
infix fun Expression<FPSort>.fpleq(rhs: Expression<FPSort>) = FPLeq(this, rhs)

/**
 * Less than operator for FPSort expressions: [this] < [rhs].
 */
infix fun Expression<FPSort>.fplt(rhs: Expression<FPSort>) = FPLt(this, rhs)

/**
 * Greater equals operator for FPSort expressions: [this] >= [rhs].
 */
infix fun Expression<FPSort>.fpgeq(rhs: Expression<FPSort>) = FPGeq(this, rhs)

/**
 * Greater than operator for FPSort expressions: [this] > [rhs].
 */
infix fun Expression<FPSort>.fpgt(rhs: Expression<FPSort>) = FPGt(this, rhs)

/**
 * Equals operator for FPSort expressions: [this] = [rhs].
 */
infix fun Expression<FPSort>.fpeq(rhs: Expression<FPSort>) = FPEq(this, rhs)


/**
 * Less equals operator for FPSort expressions: [this] <= [rhs].
 */
infix fun Expression<FPSort>.fpleq(rhs: () -> Expression<FPSort>) = FPLeq(this, rhs())

/**
 * Less than operator for FPSort expressions: [this] < [rhs].
 */
infix fun Expression<FPSort>.fplt(rhs: () -> Expression<FPSort>) = FPLt(this, rhs())

/**
 * Greater equals operator for FPSort expressions: [this] >= [rhs].
 */
infix fun Expression<FPSort>.fpgeq(rhs: () -> Expression<FPSort>) = FPGeq(this, rhs())

/**
 * Greater than operator for FPSort expressions: [this] > [rhs].
 */
infix fun Expression<FPSort>.fpgt(rhs: () -> Expression<FPSort>) = FPGt(this, rhs())

/**
 * Equals operator for FPSort expressions: [this] = [rhs].
 */
infix fun Expression<FPSort>.fpeq(rhs: () -> Expression<FPSort>) = FPEq(this, rhs())


/**
 * Less equals operator for FPSort expressions: [this] <= [rhs].
 */
infix fun (() -> Expression<FPSort>).fpleq(rhs: Expression<FPSort>) = FPLeq(this(), rhs)

/**
 * Less than operator for FPSort expressions: [this] < [rhs].
 */
infix fun (() -> Expression<FPSort>).fplt(rhs: Expression<FPSort>) = FPLt(this(), rhs)

/**
 * Greater equals operator for FPSort expressions: [this] >= [rhs].
 */
infix fun (() -> Expression<FPSort>).fpgeq(rhs: Expression<FPSort>) = FPGeq(this(), rhs)

/**
 * Greater than operator for FPSort expressions: [this] > [rhs].
 */
infix fun (() -> Expression<FPSort>).fpgt(rhs: Expression<FPSort>) = FPGt(this(), rhs)

/**
 * Equals operator for FPSort expressions: [this] = [rhs].
 */
infix fun (() -> Expression<FPSort>).fpeq(rhs: Expression<FPSort>) = FPEq(this(), rhs)


/**
 * Less equals operator for FPSort expressions: [this] <= [rhs].
 */
infix fun (() -> Expression<FPSort>).fpleq(rhs: () -> Expression<FPSort>) = FPLeq(this(), rhs())

/**
 * Less than operator for FPSort expressions: [this] < [rhs].
 */
infix fun (() -> Expression<FPSort>).fplt(rhs: () -> Expression<FPSort>) = FPLt(this(), rhs())

/**
 * Greater equals operator for FPSort expressions: [this] >= [rhs].
 */
infix fun (() -> Expression<FPSort>).fpgeq(rhs: () -> Expression<FPSort>) = FPGeq(this(), rhs())

/**
 * Greater than operator for FPSort expressions: [this] > [rhs].
 */
infix fun (() -> Expression<FPSort>).fpgt(rhs: () -> Expression<FPSort>) = FPGt(this(), rhs())

/**
 * Equals operator for FPSort expressions: [this] = [rhs].
 */
infix fun (() -> Expression<FPSort>).fpeq(rhs: () -> Expression<FPSort>) = FPEq(this(), rhs())


/**
 * Less equals operator for FPSort expressions: [this] <= [rhs].
 */
infix fun FPLeq.fpleq(rhs: Expression<FPSort>) = FPLeq(this.children + rhs)

/**
 * Less than operator for FPSort expressions: [this] < [rhs].
 */
infix fun FPLt.fplt(rhs: Expression<FPSort>) = FPLt(this.children + rhs)

/**
 * Greater equals operator for FPSort expressions: [this] >= [rhs].
 */
infix fun FPGeq.fpgeq(rhs: Expression<FPSort>) = FPGeq(this.children + rhs)

/**
 * Greater than operator for FPSort expressions: [this] > [rhs].
 */
infix fun FPGt.fpgt(rhs: Expression<FPSort>) = FPGt(this.children + rhs)

/**
 * Equals operator for FPSort expressions: [this] = [rhs].
 */
infix fun FPEq.fpeq(rhs: Expression<FPSort>) = FPEq(this.children + rhs)


/**
 * Less equals operator for FPSort expressions: [this] <= [rhs].
 */
infix fun FPLeq.fpleq(rhs: () -> Expression<FPSort>) = FPLeq(this.children + rhs())

/**
 * Less than operator for FPSort expressions: [this] < [rhs].
 */
infix fun FPLt.fplt(rhs: () -> Expression<FPSort>) = FPLt(this.children + rhs())

/**
 * Greater equals operator for FPSort expressions: [this] >= [rhs].
 */
infix fun FPGeq.fpgeq(rhs: () -> Expression<FPSort>) = FPGeq(this.children + rhs())

/**
 * Greater than operator for FPSort expressions: [this] > [rhs].
 */
infix fun FPGt.fpgt(rhs: () -> Expression<FPSort>) = FPGt(this.children + rhs())

/**
 * Equals operator for FPSort expressions: [this] = [rhs].
 */
infix fun FPEq.fpeq(rhs: () -> Expression<FPSort>) = FPEq(this.children + rhs())


/**
 * Less equals operator for FPSort expressions: [this] <= [rhs].
 */
infix fun (() -> FPLeq).fpleq(rhs: Expression<FPSort>) = FPLeq(this().children + rhs)

/**
 * Less than operator for FPSort expressions: [this] < [rhs].
 */
infix fun (() -> FPLt).fplt(rhs: Expression<FPSort>) = FPLt(this().children + rhs)

/**
 * Greater equals operator for FPSort expressions: [this] >= [rhs].
 */
infix fun (() -> FPGeq).fpgeq(rhs: Expression<FPSort>) = FPGeq(this().children + rhs)

/**
 * Greater than operator for FPSort expressions: [this] > [rhs].
 */
infix fun (() -> FPGt).fpgt(rhs: Expression<FPSort>) = FPGt(this().children + rhs)

/**
 * Equals operator for FPSort expressions: [this] = [rhs].
 */
infix fun (() -> FPEq).fpeq(rhs: Expression<FPSort>) = FPEq(this().children + rhs)


/**
 * Less equals operator for FPSort expressions: [this] <= [rhs].
 */
infix fun (() -> FPLeq).fpleq(rhs: () -> Expression<FPSort>) = FPLeq(this().children + rhs())

/**
 * Less than operator for FPSort expressions: [this] < [rhs].
 */
infix fun (() -> FPLt).fplt(rhs: () -> Expression<FPSort>) = FPLt(this().children + rhs())

/**
 * Greater equals operator for FPSort expressions: [this] >= [rhs].
 */
infix fun (() -> FPGeq).fpgeq(rhs: () -> Expression<FPSort>) = FPGeq(this().children + rhs())

/**
 * Greater than operator for FPSort expressions: [this] > [rhs].
 */
infix fun (() -> FPGt).fpgt(rhs: () -> Expression<FPSort>) = FPGt(this().children + rhs())

/**
 * Equals operator for FPSort expressions: [this] = [rhs].
 */
infix fun (() -> FPEq).fpeq(rhs: () -> Expression<FPSort>) = FPEq(this().children + rhs())

/*
 * floating-point conversion operations
 */

/**
 * Conversion operator from single bitstring representation in IEEE 754-2008 interchange format to floating point.
 */
@JvmName("BVToFP")
fun toFP(eb: Int, sb: Int, block: () -> Expression<BVSort>) = BitVecToFP(block(), eb, sb)

/**
 * Conversion operator from single bitstring representation in IEEE 754-2008 interchange format to floating point.
 */
@JvmName("BVToFP")
fun toFP(eb: Int, sb: Int, expr: Expression<BVSort>) = BitVecToFP(expr, eb, sb)

/**
 * Conversion operator from single bitstring representation in IEEE 754-2008 interchange format to floating point.
 */
fun Expression<BVSort>.toFP(eb: Int, sb: Int) = BitVecToFP(this, eb, sb)

/**
 * Conversion operator from single bitstring representation in IEEE 754-2008 interchange format to floating point.
 */
fun Expression<BVSort>.toFP(sort: FPSort) = BitVecToFP(this, sort)

/**
 * Conversion operator from another floating point sort to floating point sort.
 */
@JvmName("FPToFP")
fun toFP(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingMode> = RNE,
    block: () -> Expression<FPSort>
) = FPToFP(roundingMode, block(), eb, sb)

/**
 * Conversion operator from another floating point sort to floating point sort.
 */
@JvmName("FPToFP")
fun toFP(eb: Int, sb: Int, roundingMode: Expression<RoundingMode> = RNE, expr: Expression<FPSort>) =
    FPToFP(roundingMode, expr, eb, sb)

/**
 * Conversion operator from another floating point sort to floating point sort.
 */
fun Expression<FPSort>.toFP(eb : Int, sb : Int, roundingMode: Expression<RoundingMode> = RNE) = FPToFP(roundingMode, this, eb, sb)

/**
 * Conversion operator from another floating point sort to floating point sort.
 */
fun Expression<FPSort>.toFP(sort: FPSort, roundingMode: Expression<RoundingMode> = RNE) = FPToFP(roundingMode, this, sort)

/**
 * Conversion operator from real sort to floating point sort.
 */
@JvmName("RealToFP")
fun toFP(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingMode> = RNE,
    block: () -> Expression<RealSort>
) = RealToFP(roundingMode, block(), eb, sb)

/**
 * Conversion operator from real sort to floating point sort.
 */
@JvmName("RealToFP")
fun toFP(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingMode> = RNE,
    expr: Expression<RealSort>
) = RealToFP(roundingMode, expr, eb, sb)

/**
 * Conversion operator from real sort to floating point sort.
 */
fun Expression<RealSort>.toFP(eb: Int, sb: Int, roundingMode: Expression<RoundingMode> = RNE) = RealToFP(roundingMode, this, eb, sb)

/**
 * Conversion operator from real sort to floating point sort.
 */
fun Expression<RealSort>.toFP(sort: FPSort, roundingMode: Expression<RoundingMode> = RNE) = RealToFP(roundingMode, this, sort)

/**
 * Conversion operator from signed machine integer, represented as a 2's complement bit vector to floating point.
 */
@JvmName("SBVToFP")
fun toFPSigned(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingMode> = RNE,
    block: () -> Expression<BVSort>
) = SBitVecToFP(roundingMode, block(), eb, sb)

/**
 * Conversion operator from signed machine integer, represented as a 2's complement bit vector to floating point.
 */
@JvmName("SBVToFP")
fun toFPSigned(eb: Int, sb: Int, roundingMode: Expression<RoundingMode> = RNE, expr: Expression<BVSort>) =
    SBitVecToFP(roundingMode, expr, eb, sb)

/**
 * Conversion operator from signed machine integer, represented as a 2's complement bit vector to floating point.
 */
fun Expression<BVSort>.toFPSigned(eb: Int, sb: Int, roundingMode: Expression<RoundingMode>) = SBitVecToFP(roundingMode, this, eb, sb)

/**
 * Conversion operator from signed machine integer, represented as a 2's complement bit vector to floating point.
 */
fun Expression<BVSort>.toFPSigned(sort: FPSort, roundingMode: Expression<RoundingMode>) = SBitVecToFP(roundingMode, this, sort)

/**
 * Conversion operator from unsigned machine integer, represented as a 2's complement bit vector to floating point.
 */
@JvmName("UBVToFP")
fun toFPUnsigned(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingMode> = RNE,
    block: () -> Expression<BVSort>
) = UBitVecToFP(roundingMode, block(), eb, sb)

/**
 * Conversion operator from unsigned machine integer, represented as a 2's complement bit vector to floating point.
 */
@JvmName("UBVToFP")
fun toFPUnsigned(
    eb: Int,
    sb: Int,
    roundingMode: Expression<RoundingMode> = RNE,
    expr: Expression<BVSort>
) = UBitVecToFP(roundingMode, expr, eb, sb)

/**
 * Conversion operator from unsigned machine integer, represented as a 2's complement bit vector to floating point.
 */
fun Expression<BVSort>.toFPUnsigned(eb: Int, sb: Int, roundingMode: Expression<RoundingMode>) = UBitVecToFP(roundingMode, this, eb, sb)

/**
 * Conversion operator from unsigned machine integer, represented as a 2's complement bit vector to floating point.
 */
fun Expression<BVSort>.toFPUnsigned(sort: FPSort, roundingMode: Expression<RoundingMode>) = UBitVecToFP(roundingMode, this, sort)

/**
 * Conversion operator to unsigned machine integer, represented as a bit vector (_ BitVec [bits])
 */
fun toUBV(bits: Int, roundingMode: Expression<RoundingMode> = RNE, block: () -> Expression<FPSort>) =
    FPToUBitVec(roundingMode, block(), bits)

/**
 * Conversion operator to unsigned machine integer, represented as a bit vector (_ BitVec [bits])
 */
fun toUBV(bits: Int, roundingMode: Expression<RoundingMode> = RNE, expr: Expression<FPSort>) =
    FPToUBitVec(roundingMode, expr, bits)

/**
 * Conversion operator to unsigned machine integer, represented as a bit vector (_ BitVec [bits])
 */
fun Expression<FPSort>.toUBV(bits: Int, roundingMode: Expression<RoundingMode> = RNE) = FPToUBitVec(roundingMode, this, bits)

/**
 * Conversion operator to unsigned machine integer, represented as a bit vector [sort]
 */
fun Expression<FPSort>.toUBV(sort: BVSort, roundingMode: Expression<RoundingMode> = RNE) = FPToUBitVec(roundingMode, this, sort.bits)

/**
 * Conversion operator to signed machine integer, represented as a 2's complement bit vector (_ BitVec [bits])
 */
fun toSBV(bits: Int, roundingMode: Expression<RoundingMode> = RNE, block: () -> Expression<FPSort>) =
    FPToSBitVec(roundingMode, block(), bits)

/**
 * Conversion operator to signed machine integer, represented as a 2's complement bit vector (_ BitVec [bits])
 */
fun toSBV(bits: Int, roundingMode: Expression<RoundingMode> = RNE, expr: Expression<FPSort>) =
    FPToSBitVec(roundingMode, expr, bits)

/**
 * Conversion operator to signed machine integer, represented as a 2's complement bit vector (_ BitVec [bits])
 */
fun Expression<FPSort>.toSBV(bits: Int, roundingMode: Expression<RoundingMode> = RNE) = FPToSBitVec(roundingMode, this, bits)

/**
 * Conversion operator to signed machine integer, represented as a 2's complement bit vector (_ BitVec [bits])
 */
fun Expression<FPSort>.toSBV(sort: BVSort, roundingMode: Expression<RoundingMode> = RNE) = FPToSBitVec(roundingMode, this, sort.bits)


/**
 * Conversion operator to real sort
 */
fun toReal(block: () -> Expression<FPSort>) = FPToReal(block())

/**
 * Conversion operator to real sort
 */
fun toReal(expr: Expression<FPSort>) = FPToReal(expr)

/**
 * Conversion operator to real sort
 */
fun Expression<FPSort>.toReal() = FPToReal(this)

/*
 * fpfma
 */

/**
 * Fused multiplication addition operator ([multiplier] * multiplicand + summand) for FPSort expressions.
 * Must be followed by [FPFMA1.mul] and [FPFMA2.add].
 *
 * @param roundingMode: floating point rounding mode.
 */
fun fpfma(
    roundingMode: Expression<RoundingMode> = RNE,
    multiplier: () -> Expression<FPSort>
) = FPFMA1(roundingMode, multiplier())

/**
 * Fused multiplication addition operator ([multiplier] * multiplicand + summand) for FPSort expressions.
 * Must be followed by [FPFMA1.mul] and [FPFMA2.add].
 *
 * @param roundingMode: floating point rounding mode.
 */
fun fpfma(
    roundingMode: Expression<RoundingMode> = RNE,
    multiplier: Expression<FPSort>
) = FPFMA1(roundingMode, multiplier)

class FPFMA1(val roundingMode: Expression<RoundingMode>, val multiplier: Expression<FPSort>) {

    /**
     * Fused multiplication addition operator (multiplier * [multiplicand] + summand) for FPSort expressions.
     *
     * Must be followed by [FPFMA2.add].
     */
  infix fun mul(multiplicand: Expression<FPSort>) = FPFMA2(roundingMode, multiplier, multiplicand)

    /**
     * Fused multiplication addition operator (multiplier * [multiplicand] + summand) for FPSort expressions.
     *
     * Must be followed by [FPFMA2.add].
     */
  infix fun mul(multiplicand: () -> Expression<FPSort>) = FPFMA2(roundingMode, multiplier, multiplicand())
}

class FPFMA2(
    val roundingMode: Expression<RoundingMode>,
    val multiplier: Expression<FPSort>,
    val multiplicand: Expression<FPSort>
) {

    /**
     * Fused multiplication addition operator (multiplier * multiplicand +  [summand]) for FPSort expressions.
     */
  infix fun add(summand: Expression<FPSort>) = FPFma(roundingMode, multiplier, multiplicand, summand)

    /**
     * Fused multiplication addition operator (multiplier * multiplicand + [summand]) for FPSort expressions.
     */
  infix fun add(summand: () -> Expression<FPSort>) = FPFma(roundingMode, multiplier, multiplicand, summand())
}

/** Implements floating point isNormal operation */
fun isNormal(expr: Expression<FPSort>) = FPIsNormal(expr)

/** Implements floating point isNormal operation */
fun isNormal(block: () -> Expression<FPSort>) = FPIsNormal(block())

/** Implements floating point isSubnormal operation */
fun isSubnormal(expr: Expression<FPSort>) = FPIsSubnormal(expr)

/** Implements floating point isSubnormal operation */
fun isSubnormal(block: () -> Expression<FPSort>) = FPIsSubnormal(block())

/** Implements floating point isZero operation */
fun isZero(expr: Expression<FPSort>) = FPIsZero(expr)

/** Implements floating point isZero operation */
fun isZero(block: () -> Expression<FPSort>) = FPIsZero(block())

/** Implements floating point isInfinite operation */
fun isInfinite(expr: Expression<FPSort>) = FPIsInfinite(expr)

/** Implements floating point isInfinite operation */
fun isInfinite(block: () -> Expression<FPSort>) = FPIsInfinite(block())

/** Implements floating point isNaN operation */
fun isNaN(expr: Expression<FPSort>) = FPIsNaN(expr)

/** Implements floating point isNaN operation */
fun isNaN(block: () -> Expression<FPSort>) = FPIsNaN(block())

/** Implements floating point isNegative operation */
fun isNegative(expr: Expression<FPSort>) = FPIsNegative(expr)

/** Implements floating point isNegative operation */
fun isNegative(block: () -> Expression<FPSort>) = FPIsNegative(block())

/** Implements floating point isPositive operation */
fun isPositive(expr: Expression<FPSort>) = FPIsPositive(expr)

/** Implements floating point isPositive operation */
fun isPositive(block: () -> Expression<FPSort>) = FPIsPositive(block())
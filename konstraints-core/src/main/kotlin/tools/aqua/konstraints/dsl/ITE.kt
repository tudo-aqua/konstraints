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

package tools.aqua.konstraints.dsl

import java.math.BigDecimal
import java.math.BigInteger
import tools.aqua.konstraints.smt.BoolSort
import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.smt.FPLiteral
import tools.aqua.konstraints.smt.FPSort
import tools.aqua.konstraints.smt.IntLiteral
import tools.aqua.konstraints.smt.IntSort
import tools.aqua.konstraints.smt.Ite
import tools.aqua.konstraints.smt.RealLiteral
import tools.aqua.konstraints.smt.RealSort
import tools.aqua.konstraints.smt.RegLanSort
import tools.aqua.konstraints.smt.Sort
import tools.aqua.konstraints.smt.StrToRe
import tools.aqua.konstraints.smt.StringLiteral
import tools.aqua.konstraints.smt.StringSort

@SMTDSL
class ITE1(val condition: Expression<BoolSort>) {
  /**
   * Value of the if-statement, when [condition] is true.
   *
   * Must be followed by an [ITE2.otherwise].
   *
   * @param expr: Value of the if-statement, when [condition] is true.
   */
  infix fun <T : Sort> then(expr: Expression<T>): ITE2<T> = ITE2(condition, expr)

  /**
   * Value of the if-statement, when [condition] is true.
   *
   * Must be followed by an [ITE2.otherwise].
   *
   * @param block: Value of the if-statement, when [condition] is true.
   */
  infix fun <T : Sort> then(block: () -> Expression<T>): ITE2<T> = ITE2(condition, block())

  infix fun then(numeral: Int) = IntITE2(condition, numeral)
}

class ITE2<T : Sort>(val condition: Expression<BoolSort>, val then: Expression<T>) {

  /**
   * Value of the if-statement, when [condition] is false.
   *
   * @param expr: Value of the if-statement, when [condition] is true.
   */
  infix fun otherwise(expr: Expression<T>): Ite<T> = Ite(condition, then, expr)

  /**
   * Value of the if-statement, when [condition] is false.
   *
   * @param block: Value of the if-statement, when [condition] is true.
   */
  infix fun otherwise(block: () -> Expression<T>): Ite<T> = Ite(condition, then, block())
}

/**
 * Temporary class holding temporary ite [condition] and [numeral] value. [numeral] will later be
 * converted to an appropriate [Literal] depending on the value of [otherwise]
 */
class ByteITE2(val condition: Expression<BoolSort>, val numeral: Byte) {
  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [numeral] is converted to [IntLiteral]
   */
  @JvmName("ByteOtherwiseIntSort")
  infix fun otherwise(expr: Expression<IntSort>) = Ite(condition, IntLiteral(numeral), expr)

  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [numeral] is converted to [IntLiteral]
   */
  @JvmName("ByteOtherwiseIntSortLambda")
  infix fun otherwise(expr: (() -> Expression<IntSort>)) =
      Ite(condition, IntLiteral(numeral), expr())

  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [numeral] is converted to [RealLiteral]
   */
  @JvmName("ByteOtherwiseRealSort")
  infix fun otherwise(expr: Expression<RealSort>) = Ite(condition, RealLiteral(numeral), expr)

  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [numeral] is converted to [RealLiteral]
   */
  @JvmName("ByteOtherwiseRealSortLambda")
  infix fun otherwise(expr: (() -> Expression<RealSort>)) =
      Ite(condition, RealLiteral(numeral), expr())
}

/**
 * Temporary class holding temporary ite [condition] and [numeral] value. [numeral] will later be
 * converted to an appropriate [Literal] depending on the value of [otherwise]
 */
class ShortITE2(val condition: Expression<BoolSort>, val numeral: Short) {
  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [numeral] is converted to [IntLiteral]
   */
  @JvmName("ShortOtherwiseIntSort")
  infix fun otherwise(expr: Expression<IntSort>) = Ite(condition, IntLiteral(numeral), expr)

  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [numeral] is converted to [IntLiteral]
   */
  @JvmName("ShortOtherwiseIntSortLambda")
  infix fun otherwise(expr: (() -> Expression<IntSort>)) =
      Ite(condition, IntLiteral(numeral), expr())

  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [numeral] is converted to [RealLiteral]
   */
  @JvmName("ShortOtherwiseRealSort")
  infix fun otherwise(expr: Expression<RealSort>) = Ite(condition, RealLiteral(numeral), expr)

  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [numeral] is converted to [RealLiteral]
   */
  @JvmName("ShortOtherwiseRealSortLambda")
  infix fun otherwise(expr: (() -> Expression<RealSort>)) =
      Ite(condition, RealLiteral(numeral), expr())
}

/**
 * Temporary class holding temporary ite [condition] and [numeral] value. [numeral] will later be
 * converted to an appropriate [Literal] depending on the value of [otherwise]
 */
class IntITE2(val condition: Expression<BoolSort>, val numeral: Int) {
  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [numeral] is converted to [IntLiteral]
   */
  @JvmName("IntOtherwiseIntSort")
  infix fun otherwise(expr: Expression<IntSort>) = Ite(condition, IntLiteral(numeral), expr)

  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [numeral] is converted to [IntLiteral]
   */
  @JvmName("IntOtherwiseIntSortLambda")
  infix fun otherwise(expr: (() -> Expression<IntSort>)) =
      Ite(condition, IntLiteral(numeral), expr())

  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [numeral] is converted to [RealLiteral]
   */
  @JvmName("IntOtherwiseRealSort")
  infix fun otherwise(expr: Expression<RealSort>) = Ite(condition, RealLiteral(numeral), expr)

  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [numeral] is converted to [RealLiteral]
   */
  @JvmName("IntOtherwiseRealSortLambda")
  infix fun otherwise(expr: (() -> Expression<RealSort>)) =
      Ite(condition, RealLiteral(numeral), expr())
}

/**
 * Temporary class holding temporary ite [condition] and [numeral] value. [numeral] will later be
 * converted to an appropriate [Literal] depending on the value of [otherwise]
 */
class LongITE2(val condition: Expression<BoolSort>, val numeral: Long) {
  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [numeral] is converted to [IntLiteral]
   */
  @JvmName("LongOtherwiseIntSort")
  infix fun otherwise(expr: Expression<IntSort>) = Ite(condition, IntLiteral(numeral), expr)

  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [numeral] is converted to [IntLiteral]
   */
  @JvmName("LongOtherwiseIntSortLambda")
  infix fun otherwise(expr: (() -> Expression<IntSort>)) =
      Ite(condition, IntLiteral(numeral), expr())

  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [numeral] is converted to [RealLiteral]
   */
  @JvmName("LongOtherwiseRealSort")
  infix fun otherwise(expr: Expression<RealSort>) = Ite(condition, RealLiteral(numeral), expr)

  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [numeral] is converted to [RealLiteral]
   */
  @JvmName("LongOtherwiseRealSortLambda")
  infix fun otherwise(expr: (() -> Expression<RealSort>)) =
      Ite(condition, RealLiteral(numeral), expr())
}

/**
 * Temporary class holding temporary ite [condition] and [numeral] value. [numeral] will later be
 * converted to an appropriate [Literal] depending on the value of [otherwise]
 */
class BigIntegerITE2(val condition: Expression<BoolSort>, val numeral: BigInteger) {
  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [numeral] is converted to [IntLiteral]
   */
  @JvmName("BigIntegerOtherwiseIntSort")
  infix fun otherwise(expr: Expression<IntSort>) = Ite(condition, IntLiteral(numeral), expr)

  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [numeral] is converted to [IntLiteral]
   */
  @JvmName("BigIntegerOtherwiseIntSortLambda")
  infix fun otherwise(expr: (() -> Expression<IntSort>)) =
      Ite(condition, IntLiteral(numeral), expr())

  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [numeral] is converted to [RealLiteral]
   */
  @JvmName("BigIntegerOtherwiseRealSort")
  infix fun otherwise(expr: Expression<RealSort>) = Ite(condition, RealLiteral(numeral), expr)

  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [numeral] is converted to [RealLiteral]
   */
  @JvmName("BigIntegerOtherwiseRealSortLambda")
  infix fun otherwise(expr: (() -> Expression<RealSort>)) =
      Ite(condition, RealLiteral(numeral), expr())
}

/**
 * Temporary class holding temporary ite [condition] and [numeral] value. [numeral] will later be
 * converted to an appropriate [Literal] depending on the value of [otherwise]
 */
class FloatITE2(val condition: Expression<BoolSort>, val numeral: Float) {
  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [numeral] is converted to [RealLiteral]
   */
  @JvmName("FloatOtherwiseRealSort")
  infix fun otherwise(expr: Expression<RealSort>) = Ite(condition, RealLiteral(numeral), expr)

  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [numeral] is converted to [RealLiteral]
   */
  @JvmName("FloatOtherwiseRealSortLambda")
  infix fun otherwise(expr: (() -> Expression<RealSort>)) =
      Ite(condition, RealLiteral(numeral), expr())
}

/**
 * Temporary class holding temporary ite [condition] and [numeral] value. [numeral] will later be
 * converted to an appropriate [Literal] depending on the value of [otherwise]
 */
class DoubleITE2(val condition: Expression<BoolSort>, val numeral: Double) {
  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [numeral] is converted to [RealLiteral]
   */
  @JvmName("DoubleOtherwiseRealSort")
  infix fun otherwise(expr: Expression<RealSort>) = Ite(condition, RealLiteral(numeral), expr)

  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [numeral] is converted to [RealLiteral]
   */
  @JvmName("DoubleOtherwiseRealSortLambda")
  infix fun otherwise(expr: (() -> Expression<RealSort>)) =
      Ite(condition, RealLiteral(numeral), expr())
}

/**
 * Temporary class holding temporary ite [condition] and [numeral] value. [numeral] will later be
 * converted to an appropriate [Literal] depending on the value of [otherwise]
 */
class BigDecimalITE2(val condition: Expression<BoolSort>, val numeral: BigDecimal) {
  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [numeral] is converted to [RealLiteral]
   */
  @JvmName("BigDecimalOtherwiseRealSort")
  infix fun otherwise(expr: Expression<RealSort>) = Ite(condition, RealLiteral(numeral), expr)

  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [numeral] is converted to [RealLiteral]
   */
  @JvmName("BigDecimalOtherwiseRealSortLambda")
  infix fun otherwise(expr: (() -> Expression<RealSort>)) =
      Ite(condition, RealLiteral(numeral), expr())
}

/**
 * Temporary class holding temporary ite [condition] and [string] value. [string] will later be
 * converted to an appropriate [Literal] depending on the value of [otherwise]
 */
class StringITE2(val condition: Expression<BoolSort>, val string: String) {
  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [string] is converted to [StringLiteral]
   */
  @JvmName("StringOtherwiseStringSort")
  infix fun otherwise(expr: Expression<StringSort>) = Ite(condition, StringLiteral(string), expr)

  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [string] is converted to [StringLiteral]
   */
  @JvmName("StringOtherwiseStringSortLambda")
  infix fun otherwise(expr: (() -> Expression<StringSort>)) =
      Ite(condition, StringLiteral(string), expr())
}

/**
 * Temporary class holding ite [condition] and [reglan] value. [reglan] will later be converted to
 * an appropriate [Literal] depending on the value of [otherwise]
 */
class RegLanITE2(val condition: Expression<BoolSort>, val reglan: String) {
  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [reglan] is converted to [StringLiteral]
   */
  @JvmName("StringOtherwiseRegLanSort")
  infix fun otherwise(expr: Expression<RegLanSort>) =
      Ite(condition, StrToRe(StringLiteral(reglan)), expr)

  /**
   * Evaluate if-statement to [expr], when [condition] is false.
   * - [reglan] is converted to [StringLiteral]
   */
  @JvmName("StringOtherwiseRegLanSortLambda")
  infix fun otherwise(expr: (() -> Expression<RegLanSort>)) =
      Ite(condition, StrToRe(StringLiteral(reglan)), expr())
}

/**
 * If-then-else operator.
 *
 * Must be followed by a [ITE1.then] and [ITE2.otherwise].
 *
 * @param condition: lambda yielding an Expression<BoolSort> used as condition for the if-statement.
 */
fun ite(condition: () -> Expression<BoolSort>): ITE1 = ITE1(condition())

/**
 * If-then-else operator.
 *
 * Must be followed by a [ITE1.then] and [ITE2.otherwise].
 *
 * @param condition: Expression<BoolSort> used as condition for the if-statement.
 */
fun ite(condition: Expression<BoolSort>): ITE1 = ITE1(condition)

// IntSort extensions
@JvmName("IntSortOtherwiseByte")
infix fun ITE2<IntSort>.otherwise(numeral: Byte) = otherwise(IntLiteral(numeral))

@JvmName("IntSortOtherwiseShort")
infix fun ITE2<IntSort>.otherwise(numeral: Short) = otherwise(IntLiteral(numeral))

@JvmName("IntSortOtherwiseInt")
infix fun ITE2<IntSort>.otherwise(numeral: Int) = otherwise(IntLiteral(numeral))

@JvmName("IntSortOtherwiseLong")
infix fun ITE2<IntSort>.otherwise(numeral: Long) = otherwise(IntLiteral(numeral))

@JvmName("IntSortOtherwiseBigInteger")
infix fun ITE2<IntSort>.otherwise(numeral: BigInteger) = otherwise(IntLiteral(numeral))

@JvmName("IntSortOtherwiseByteLambda")
infix fun ITE2<IntSort>.otherwise(numeral: (() -> Byte)) = otherwise(IntLiteral(numeral()))

@JvmName("IntSortOtherwiseShortLambda")
infix fun ITE2<IntSort>.otherwise(numeral: (() -> Short)) = otherwise(IntLiteral(numeral()))

@JvmName("IntSortOtherwiseIntLambda")
infix fun ITE2<IntSort>.otherwise(numeral: (() -> Int)) = otherwise(IntLiteral(numeral()))

@JvmName("IntSortOtherwiseLongLambda")
infix fun ITE2<IntSort>.otherwise(numeral: (() -> Long)) = otherwise(IntLiteral(numeral()))

@JvmName("IntSortOtherwiseBigIntegerLambda")
infix fun ITE2<IntSort>.otherwise(numeral: (() -> BigInteger)) = otherwise(IntLiteral(numeral()))

// RealSort extensions
@JvmName("RealSortOtherwiseByte")
infix fun ITE2<RealSort>.otherwise(numeral: Byte) = otherwise(RealLiteral(numeral))

@JvmName("RealSortOtherwiseShort")
infix fun ITE2<RealSort>.otherwise(numeral: Short) = otherwise(RealLiteral(numeral))

@JvmName("RealSortOtherwiseInt")
infix fun ITE2<RealSort>.otherwise(numeral: Int) = otherwise(RealLiteral(numeral))

@JvmName("RealSortOtherwiseLong")
infix fun ITE2<RealSort>.otherwise(numeral: Long) = otherwise(RealLiteral(numeral))

@JvmName("RealSortOtherwiseBigInteger")
infix fun ITE2<RealSort>.otherwise(numeral: BigInteger) = otherwise(RealLiteral(numeral))

@JvmName("RealSortOtherwiseFloat")
infix fun ITE2<RealSort>.otherwise(numeral: Float) = otherwise(RealLiteral(numeral))

@JvmName("RealSortOtherwiseBigDecimal")
infix fun ITE2<RealSort>.otherwise(numeral: BigDecimal) = otherwise(RealLiteral(numeral))

@JvmName("RealSortOtherwiseByteLambda")
infix fun ITE2<RealSort>.otherwise(numeral: (() -> Byte)) = otherwise(RealLiteral(numeral()))

@JvmName("RealSortOtherwiseShortLambda")
infix fun ITE2<RealSort>.otherwise(numeral: (() -> Short)) = otherwise(RealLiteral(numeral()))

@JvmName("RealSortOtherwiseIntLambda")
infix fun ITE2<RealSort>.otherwise(numeral: (() -> Int)) = otherwise(RealLiteral(numeral()))

@JvmName("RealSortOtherwiseLongLambda")
infix fun ITE2<RealSort>.otherwise(numeral: (() -> Long)) = otherwise(RealLiteral(numeral()))

@JvmName("RealSortOtherwiseBigIntegerLambda")
infix fun ITE2<RealSort>.otherwise(numeral: (() -> BigInteger)) = otherwise(RealLiteral(numeral()))

@JvmName("RealSortOtherwiseFloatLambda")
infix fun ITE2<RealSort>.otherwise(numeral: (() -> Float)) = otherwise(RealLiteral(numeral()))

@JvmName("RealSortOtherwiseBigDecimalLambda")
infix fun ITE2<RealSort>.otherwise(numeral: (() -> BigDecimal)) = otherwise(RealLiteral(numeral()))

// Float extensions
@JvmName("FloatingPointSortOtherwiseFloat")
infix fun ITE2<FPSort>.otherwise(numeral: Float) = otherwise(FPLiteral(numeral))

@JvmName("FloatingPointSortOtherwiseDouble")
infix fun ITE2<FPSort>.otherwise(numeral: Double) = otherwise(FPLiteral(numeral))

@JvmName("FloatingPointSortOtherwiseFloatLambda")
infix fun ITE2<FPSort>.otherwise(numeral: (() -> Float)) = otherwise(FPLiteral(numeral()))

@JvmName("FloatingPointSortOtherwiseDoubleLambda")
infix fun ITE2<FPSort>.otherwise(numeral: (() -> Double)) = otherwise(FPLiteral(numeral()))

// String extensions
@JvmName("StringSortOtherwiseString")
infix fun ITE2<StringSort>.otherwise(string: String) = otherwise(StringLiteral(string))

@JvmName("StringSortOtherwiseStringLambda")
infix fun ITE2<StringSort>.otherwise(string: (() -> String)) = otherwise(StringLiteral(string()))

// RegLan extensions
@JvmName("RegLanSortOtherwiseString")
infix fun ITE2<RegLanSort>.otherwise(reglan: String) = otherwise(StrToRe(StringLiteral(reglan)))

@JvmName("RegLanSortOtherwiseStringLambda")
infix fun ITE2<RegLanSort>.otherwise(reglan: (() -> String)) =
    otherwise(StrToRe(StringLiteral(reglan())))

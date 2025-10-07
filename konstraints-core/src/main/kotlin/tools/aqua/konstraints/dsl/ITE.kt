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

import tools.aqua.konstraints.smt.BoolSort
import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.smt.FPLiteral
import tools.aqua.konstraints.smt.FPSort
import tools.aqua.konstraints.smt.True
import tools.aqua.konstraints.smt.IntLiteral
import tools.aqua.konstraints.smt.IntSort
import tools.aqua.konstraints.smt.Ite
import tools.aqua.konstraints.smt.RealLiteral
import tools.aqua.konstraints.smt.RealSort
import tools.aqua.konstraints.smt.Sort
import java.math.BigDecimal
import java.math.BigInteger

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

/*
// IntSort extensions
infix fun ITE2<IntSort>.otherwise(numeral: Byte) = otherwise(IntLiteral(numeral))
infix fun ITE2<IntSort>.otherwise(numeral: Short) = otherwise(IntLiteral(numeral))
infix fun ITE2<IntSort>.otherwise(numeral: Int) = otherwise(IntLiteral(numeral))
infix fun ITE2<IntSort>.otherwise(numeral: Long) = otherwise(IntLiteral(numeral))
infix fun ITE2<IntSort>.otherwise(numeral: BigInteger) = otherwise(IntLiteral(numeral))

//RealSort extensions
infix fun ITE2<RealSort>.otherwise(numeral: Byte) = otherwise(RealLiteral(numeral))
infix fun ITE2<RealSort>.otherwise(numeral: Short) = otherwise(RealLiteral(numeral))
infix fun ITE2<RealSort>.otherwise(numeral: Int) = otherwise(RealLiteral(numeral))
infix fun ITE2<RealSort>.otherwise(numeral: Long) = otherwise(RealLiteral(numeral))
infix fun ITE2<RealSort>.otherwise(numeral: BigInteger) = otherwise(RealLiteral(numeral))
infix fun ITE2<RealSort>.otherwise(numeral: Float) = otherwise(RealLiteral(numeral))
infix fun ITE2<RealSort>.otherwise(numeral: BigDecimal) = otherwise(RealLiteral(numeral))

//Float extensions
infix fun ITE2<FPSort>.otherwise(numeral: Float) = otherwise(FPLiteral(numeral))
infix fun ITE2<FPSort>.otherwise(numeral: Double) = otherwise(FPLiteral(numeral))

fun main(){
    val expr = IntLiteral(1)

    val cond = ite(True) then expr otherwise 2
    val cond2 = ite(True) then IntLiteral(2) otherwise expr
}
*/
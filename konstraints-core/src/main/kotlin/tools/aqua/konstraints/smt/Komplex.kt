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

package tools.aqua.konstraints.smt

import kotlin.math.sqrt
import tools.aqua.konstraints.dsl.UserDefinedSMTFunction1
import tools.aqua.konstraints.dsl.UserDefinedSMTFunction2
import tools.aqua.konstraints.dsl.cpxadd
import tools.aqua.konstraints.dsl.cpxmul
import tools.aqua.konstraints.dsl.eq

object ComplexSort :
    Datatype(
        0,
        "Complex".toSymbol(),
        listOf(
            ConstructorDecl(
                "C".toSymbol(),
                listOf(
                    SelectorDecl("re".toSymbol(), SMTReal),
                    SelectorDecl("im".toSymbol(), SMTReal),
                ),
            )
        ),
    ) {
  fun construct(re: Expression<RealSort>, im: Expression<RealSort>): Expression<ComplexSort> {
    return constructors[0].constructDynamic(listOf(re, im), emptyList()) as Expression<ComplexSort>
  }

  fun re(expr: Expression<ComplexSort>): Expression<RealSort> {
    return selectors[0].constructDynamic(listOf(expr), emptyList()) as Expression<RealSort>
  }

  fun im(expr: Expression<ComplexSort>): Expression<RealSort> {
    return selectors[1].constructDynamic(listOf(expr), emptyList()) as Expression<RealSort>
  }
}

fun Expression<ComplexSort>.re(): Expression<RealSort> {
  return ComplexSort.re(this)
}

fun Expression<ComplexSort>.im(): Expression<RealSort> {
  return ComplexSort.im(this)
}

object ComplexAddDecl :
    UserDefinedSMTFunction2<ComplexSort, ComplexSort, ComplexSort>(
        "cpx.add".toSymbol(),
        ComplexSort,
        SortedVar("x".toSymbol(), ComplexSort),
        SortedVar("y".toSymbol(), ComplexSort),
        { x: Expression<ComplexSort>, y: Expression<ComplexSort> ->
          ComplexSort.construct(RealAdd(x.re(), y.re()), RealAdd(x.im(), y.im()))
        },
    ) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<ComplexSort> {
    return ComplexMul(args[0] as Expression<ComplexSort>, args[1] as Expression<ComplexSort>)
  }
}

class ComplexAdd(
    override val lhs: Expression<ComplexSort>,
    override val rhs: Expression<ComplexSort>,
) : BinaryExpression<ComplexSort, ComplexSort, ComplexSort>("cpx.add".toSymbol(), ComplexSort) {
  override val theories: Set<Theories> = emptySet()
  override val func = ComplexAddDecl // this is important so the context finds the related function

  override fun copy(children: List<Expression<*>>): Expression<ComplexSort> {
    TODO("Not yet implemented")
  }
}

object ComplexSubDecl :
    UserDefinedSMTFunction2<ComplexSort, ComplexSort, ComplexSort>(
        "cpx.sub".toSymbol(),
        ComplexSort,
        SortedVar("x".toSymbol(), ComplexSort),
        SortedVar("y".toSymbol(), ComplexSort),
        { x: Expression<ComplexSort>, y: Expression<ComplexSort> ->
          ComplexSort.construct(RealSub(x.re(), y.re()), RealSub(x.im(), y.im()))
        },
    ) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<ComplexSort> {
    return ComplexSub(args[0] as Expression<ComplexSort>, args[1] as Expression<ComplexSort>)
  }
}

class ComplexSub(
    override val lhs: Expression<ComplexSort>,
    override val rhs: Expression<ComplexSort>,
) : BinaryExpression<ComplexSort, ComplexSort, ComplexSort>("cpx.sub".toSymbol(), ComplexSort) {
  override val theories: Set<Theories> = emptySet()
  override val func = ComplexSubDecl // this is important so the context finds the related function

  override fun copy(children: List<Expression<*>>): Expression<ComplexSort> {
    TODO("Not yet implemented")
  }
}

object ComplexMulDecl :
    UserDefinedSMTFunction2<ComplexSort, ComplexSort, ComplexSort>(
        "cpx.mul".toSymbol(),
        ComplexSort,
        SortedVar("x".toSymbol(), ComplexSort),
        SortedVar("y".toSymbol(), ComplexSort),
        { x: Expression<ComplexSort>, y: Expression<ComplexSort> ->
          ComplexSort.construct(
              RealSub(RealMul(x.re(), y.re()), RealMul(x.im(), y.im())),
              RealAdd(RealMul(x.re(), y.im()), RealMul(x.im(), y.re())),
          )
        },
    ) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<ComplexSort> {
    return ComplexMul(args[0] as Expression<ComplexSort>, args[1] as Expression<ComplexSort>)
  }
}

class ComplexMul(
    override val lhs: Expression<ComplexSort>,
    override val rhs: Expression<ComplexSort>,
) : BinaryExpression<ComplexSort, ComplexSort, ComplexSort>("cpx.mul".toSymbol(), ComplexSort) {
  override val theories: Set<Theories> = emptySet()
  override val func = ComplexMulDecl // this is important so the context finds the related function

  override fun copy(children: List<Expression<*>>): Expression<ComplexSort> {
    TODO("Not yet implemented")
  }
}

object ComplexDivDecl :
    UserDefinedSMTFunction2<ComplexSort, ComplexSort, ComplexSort>(
        "cpx.div".toSymbol(),
        ComplexSort,
        SortedVar("x".toSymbol(), ComplexSort),
        SortedVar("y".toSymbol(), ComplexSort),
        { x: Expression<ComplexSort>, y: Expression<ComplexSort> -> ComplexMul(x, ComplexInv(y)) },
    ) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<ComplexSort> {
    return ComplexDiv(args[0] as Expression<ComplexSort>, args[1] as Expression<ComplexSort>)
  }
}

class ComplexDiv(
    override val lhs: Expression<ComplexSort>,
    override val rhs: Expression<ComplexSort>,
) : BinaryExpression<ComplexSort, ComplexSort, ComplexSort>("cpx.div".toSymbol(), ComplexSort) {
  override val theories: Set<Theories> = emptySet()
  override val func = ComplexDivDecl // this is important so the context finds the related function

  override fun copy(children: List<Expression<*>>): Expression<ComplexSort> {
    TODO("Not yet implemented")
  }
}

object ComplexInvDecl :
    UserDefinedSMTFunction1<ComplexSort, ComplexSort>(
        "cpx.inv".toSymbol(),
        ComplexSort,
        SortedVar("x".toSymbol(), ComplexSort),
        { x: Expression<ComplexSort> ->
          ComplexSort.construct(
              RealDiv(x.re(), RealAdd(RealMul(x.re(), x.re()), RealMul(x.im(), x.im()))),
              RealNeg(RealDiv(x.im(), RealAdd(RealMul(x.re(), x.re()), RealMul(x.im(), x.im())))),
          )
        },
    ) {
  override fun constructDynamic(
      args: List<Expression<*>>,
      indices: List<Index>,
  ): Expression<ComplexSort> {
    return ComplexInv(args[0] as Expression<ComplexSort>)
  }
}

class ComplexInv(
    override val inner: Expression<ComplexSort>,
) : UnaryExpression<ComplexSort, ComplexSort>("cpx.inv".toSymbol(), ComplexSort) {
  override val theories: Set<Theories> = emptySet()
  override val func = ComplexInvDecl // this is important so the context finds the related function

  override fun copy(children: List<Expression<*>>): Expression<ComplexSort> {
    TODO("Not yet implemented")
  }
}

data class Complex(val re: Double, val im: Double) {
  /** Addition: (a + bi) + (c + di) = (a+c) + (b+d)i */
  operator fun plus(other: Complex): Complex = Complex(re + other.re, im + other.im)

  /** Subtraction: (a + bi) - (c + di) = (a-c) + (b-d)i */
  operator fun minus(other: Complex): Complex = Complex(re - other.re, im - other.im)

  /** Multiplication: (a + bi)(c + di) = (ac - bd) + (ad + bc)i */
  operator fun times(other: Complex): Complex =
      Complex(re * other.re - im * other.im, re * other.im + im * other.re)

  /** Conjugate: ([re] - [im]i) */
  fun conjugate(): Complex = Complex(re, -im)

  /** Magnitude squared: |z|² = [re]² + [im]² */
  fun magnitudeSquared(): Double = re * re + im * im

  fun magnitude(): Double = sqrt(magnitudeSquared())

  /** Complex inverse: 1 / ([re] + [im]i) = ([re] - [im]i) / ([re]² + [im]²) */
  fun inverse(): Complex {
    val denom = magnitudeSquared()
    require(denom != 0.0) { "Can not invert zero complex number" }
    return Complex(re / denom, -im / denom)
  }

  /**
   * Division using multiplication and inverse: [this][tools.aqua.komplex.Complex] / [other] =
   * [this][tools.aqua.komplex.Complex] * [other].[inverse]
   */
  operator fun div(other: Complex): Complex = this * other.inverse()
}

val Number.re: Complex
  get() = Complex(this.toDouble(), 0.0)

val Number.i: Complex
  get() = Complex(0.0, this.toDouble())

infix operator fun Number.plus(other: Complex): Complex = Complex(this.toDouble(), 0.0) + other

infix operator fun Complex.plus(other: Number): Complex = this + Complex(other.toDouble(), 0.0)

fun Complex.toExpression(): Expression<ComplexSort> =
    ComplexSort.construct(RealLiteral(re), RealLiteral(im))

fun main() {
  val program = MutableSMTProgram()
  program.setLogic(QF_RDL)
  program.declareDatatype(ComplexSort)
  program.defineFun(ComplexAddDecl)
  program.defineFun(ComplexMulDecl)
  val c0 = program.declareConst("C0".toSymbol(), ComplexSort).instance
  val c1 = program.declareConst("C1".toSymbol(), ComplexSort).instance
  val c2 = program.declareConst("C2".toSymbol(), ComplexSort).instance
  program.assert((c0 cpxmul c1) eq c2)
  program.assert((c0 cpxadd c1) eq c2)
  program.add(CheckSat)

  println(program.toSMTString(QuotingRule.SAME_AS_INPUT, false))
}

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

import tools.aqua.konstraints.dsl.UserDefinedSMTFunction1
import tools.aqua.konstraints.dsl.UserDefinedSMTFunction2

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
  override val func =
      ComplexAddDecl // this is important so the context finds the related function

  override fun copy(children: List<Expression<*>>): Expression<ComplexSort> {
    TODO("Not yet implemented")
  }
}

object ComplexSubDecl :
    UserDefinedSMTFunction2<ComplexSort, ComplexSort, ComplexSort>(
        "cpx.add".toSymbol(),
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
) : BinaryExpression<ComplexSort, ComplexSort, ComplexSort>("cpx.add".toSymbol(), ComplexSort) {
    override val theories: Set<Theories> = emptySet()
    override val func =
        ComplexSubDecl // this is important so the context finds the related function

    override fun copy(children: List<Expression<*>>): Expression<ComplexSort> {
        TODO("Not yet implemented")
    }
}

object ComplexMulDecl :
    UserDefinedSMTFunction2<ComplexSort, ComplexSort, ComplexSort>(
        "cpx.add".toSymbol(),
        ComplexSort,
        SortedVar("x".toSymbol(), ComplexSort),
        SortedVar("y".toSymbol(), ComplexSort),
        { x: Expression<ComplexSort>, y: Expression<ComplexSort> ->
            ComplexSort.construct(RealSub(RealMul(x.re(), y.re()), RealMul(x.im(), y.im())), RealAdd(RealMul(x.re(), y.im()), RealMul(x.im(), y.re())))
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
) : BinaryExpression<ComplexSort, ComplexSort, ComplexSort>("cpx.add".toSymbol(), ComplexSort) {
    override val theories: Set<Theories> = emptySet()
    override val func =
        ComplexMulDecl // this is important so the context finds the related function

    override fun copy(children: List<Expression<*>>): Expression<ComplexSort> {
        TODO("Not yet implemented")
    }
}

object ComplexDivDecl :
    UserDefinedSMTFunction2<ComplexSort, ComplexSort, ComplexSort>(
        "cpx.add".toSymbol(),
        ComplexSort,
        SortedVar("x".toSymbol(), ComplexSort),
        SortedVar("y".toSymbol(), ComplexSort),
        { x: Expression<ComplexSort>, y: Expression<ComplexSort> ->
            ComplexMul(x, ComplexInv(y))
        },
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
) : BinaryExpression<ComplexSort, ComplexSort, ComplexSort>("cpx.add".toSymbol(), ComplexSort) {
    override val theories: Set<Theories> = emptySet()
    override val func =
        ComplexDivDecl // this is important so the context finds the related function

    override fun copy(children: List<Expression<*>>): Expression<ComplexSort> {
        TODO("Not yet implemented")
    }
}

object ComplexInvDecl :
    UserDefinedSMTFunction1<ComplexSort, ComplexSort>(
        "cpx.add".toSymbol(),
        ComplexSort,
        SortedVar("x".toSymbol(), ComplexSort),
        { x: Expression<ComplexSort> ->
            ComplexSort.construct(
                RealDiv(x.re(), RealAdd(RealMul(x.re(), x.re()), RealMul(x.im(), x.im()))),
                RealNeg(RealDiv(x.im(), RealAdd(RealMul(x.re(), x.re()), RealMul(x.im(), x.im()))))
            )
        },
    ) {
    override fun constructDynamic(
        args: List<Expression<*>>,
        indices: List<Index>,
    ): Expression<ComplexSort> {
        return ComplexInv(args[0] as Expression<ComplexSort>, args[1] as Expression<ComplexSort>)
    }
}

class ComplexInv(
    override val lhs: Expression<ComplexSort>,
    override val rhs: Expression<ComplexSort>,
) : BinaryExpression<ComplexSort, ComplexSort, ComplexSort>("cpx.add".toSymbol(), ComplexSort) {
    override val theories: Set<Theories> = emptySet()
    override val func =
        ComplexInvDecl // this is important so the context finds the related function

    override fun copy(children: List<Expression<*>>): Expression<ComplexSort> {
        TODO("Not yet implemented")
    }
}

fun main() {
  val program = MutableSMTProgram()
  program.setLogic(QF_RDL)
  program.declareDatatype(ComplexSort)
  program.defineFun(ComplexAddDecl)
  val c0 = program.declareConst("C0".toSymbol(), ComplexSort).instance
  val c1 = program.declareConst("C1".toSymbol(), ComplexSort).instance
  val c2 = program.declareConst("C2".toSymbol(), ComplexSort).instance
  program.assert(Equals(ComplexMul(c0, c1), c2))
  program.add(CheckSat)

  println(program.toSMTString(QuotingRule.SAME_AS_INPUT, false))
}

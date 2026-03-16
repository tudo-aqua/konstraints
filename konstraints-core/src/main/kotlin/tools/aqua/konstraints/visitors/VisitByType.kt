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

package tools.aqua.konstraints.visitors

import tools.aqua.konstraints.smt.*

interface VisitByType<T> {
  fun visit(expr: Expression<*>): T =
      when (expr.sort) {
        is BoolSort -> visit(expr.cast<BoolSort>())
        is BitVecSort -> visit(expr.cast<BitVecSort>())
        is FPSort -> visit(expr.cast<FPSort>())
        is RoundingModeSort -> visit(expr.cast<RoundingModeSort>())
        is IntSort -> visit(expr.cast<IntSort>())
        is RealSort -> visit(expr.cast<RealSort>())
        is ArraySort<*, *> -> visit(expr.cast<ArraySort<*, *>>())
        is StringSort -> visit(expr.cast<StringSort>())
        is RegLanSort -> visit(expr.cast<RegLanSort>())
        is Datatype -> visit(expr.cast<Datatype>())
        is UserDeclaredSort -> visit(expr.cast<UserDeclaredSort>())
        is SortParameter -> TODO()
        NumeralSortInstance -> TODO()
      }

  fun visit(expr: Expression<BoolSort>): T =
      when (expr) {
        is AnnotatedExpression<BoolSort> -> visit(expr)
        is LocalExpression<BoolSort> -> visit(expr)
        is LetExpression<BoolSort> -> visit(expr)
        is ForallExpression -> visit(expr)
        is ExistsExpression -> visit(expr)
        is BoundVariable<BoolSort> -> visit(expr)
        is Ite<BoolSort> -> visit(expr)
        is True -> visit(expr)
        is False -> visit(expr)
        is Not -> visit(expr)
        is Implies -> visit(expr)
        is And -> visit(expr)
        is Or -> visit(expr)
        is XOr -> visit(expr)
        is Equals<*> -> visit(expr)
        is Distinct<*> -> visit(expr)
        is BVUlt -> visit(expr)
        is BVULe -> visit(expr)
        is BVUGt -> visit(expr)
        is BVUGe -> visit(expr)
        is BVSLt -> visit(expr)
        is BVSLe -> visit(expr)
        is BVSGt -> visit(expr)
        is BVSGe -> visit(expr)
        is IntLessEq -> visit(expr)
        is IntLess -> visit(expr)
        is IntGreaterEq -> visit(expr)
        is IntGreater -> visit(expr)
        is Divisible -> visit(expr)
        is RealLessEq -> visit(expr)
        is RealLess -> visit(expr)
        is RealGreaterEq -> visit(expr)
        is RealGreater -> visit(expr)
        is IsInt -> visit(expr)
        is FPLeq -> visit(expr)
        is FPLt -> visit(expr)
        is FPGeq -> visit(expr)
        is FPGt -> visit(expr)
        is FPEq -> visit(expr)
        is FPIsNormal -> visit(expr)
        is FPIsSubnormal -> visit(expr)
        is FPIsZero -> visit(expr)
        is FPIsInfinite -> visit(expr)
        is FPIsNaN -> visit(expr)
        is FPIsNegative -> visit(expr)
        is FPIsPositive -> visit(expr)
        is StrLexOrder -> visit(expr)
        is StrRefLexOrder -> visit(expr)
        is StrPrefixOf -> visit(expr)
        is StrSuffixOf -> visit(expr)
        is StrContains -> visit(expr)
        is StrIsDigit -> visit(expr)
        is StrInRe -> visit(expr)
        is ArraySelect<*, BoolSort> -> visit(expr)
        is BVNegO -> visit(expr)
        is BVUAddO -> visit(expr)
        is BVSAddO -> visit(expr)
        is BVUSubO -> visit(expr)
        is BVSSubO -> visit(expr)
        is BVUMulO -> visit(expr)
        is BVSMulO -> visit(expr)
        is BVSDivO -> visit(expr)
        is UserDeclaredExpression -> visit(expr)
        is UserDefinedExpression -> visit(expr)
        else ->
            throw IllegalArgumentException(
                "Can not visit expression $this with type ${expr.javaClass}!"
            )
      }

  fun visit(expr: AnnotatedExpression<BoolSort>): T

  fun visit(expr: LocalExpression<BoolSort>): T

  fun visit(expr: LetExpression<BoolSort>): T

  fun visit(expr: ForallExpression): T

  fun visit(expr: ExistsExpression): T

  fun visit(expr: BoundVariable<BoolSort>): T

  fun visit(expr: Ite<BoolSort>): T

  fun visit(expr: True): T

  fun visit(expr: False): T

  fun visit(expr: Not): T

  fun visit(expr: Implies): T

  fun visit(expr: And): T

  fun visit(expr: Or): T

  fun visit(expr: XOr): T

  fun visit(expr: Equals<*>): T

  fun visit(expr: Distinct<*>): T

  fun visit(expr: BVUlt): T

  fun visit(expr: BVULe): T

  fun visit(expr: BVUGt): T

  fun visit(expr: BVUGe): T

  fun visit(expr: BVSLt): T

  fun visit(expr: BVSLe): T

  fun visit(expr: BVSGt): T

  fun visit(expr: BVSGe): T

  fun visit(expr: IntLessEq): T

  fun visit(expr: IntLess): T

  fun visit(expr: IntGreaterEq): T

  fun visit(expr: IntGreater): T

  fun visit(expr: Divisible): T

  fun visit(expr: RealLessEq): T

  fun visit(expr: RealLess): T

  fun visit(expr: RealGreaterEq): T

  fun visit(expr: RealGreater): T

  fun visit(expr: IsInt): T

  fun visit(expr: FPLeq): T

  fun visit(expr: FPLt): T

  fun visit(expr: FPGeq): T

  fun visit(expr: FPGt): T

  fun visit(expr: FPEq): T

  fun visit(expr: FPIsNormal): T

  fun visit(expr: FPIsSubnormal): T

  fun visit(expr: FPIsZero): T

  fun visit(expr: FPIsInfinite): T

  fun visit(expr: FPIsNaN): T

  fun visit(expr: FPIsNegative): T

  fun visit(expr: FPIsPositive): T

  fun visit(expr: StrLexOrder): T

  fun visit(expr: StrRefLexOrder): T

  fun visit(expr: StrPrefixOf): T

  fun visit(expr: StrSuffixOf): T

  fun visit(expr: StrContains): T

  fun visit(expr: StrIsDigit): T

  fun visit(expr: StrInRe): T

  fun visit(expr: ArraySelect<*, BoolSort>): T

  fun visit(expr: BVNegO): T

  fun visit(expr: BVUAddO): T

  fun visit(expr: BVSAddO): T

  fun visit(expr: BVUSubO): T

  fun visit(expr: BVSSubO): T

  fun visit(expr: BVUMulO): T

  fun visit(expr: BVSMulO): T

  fun visit(expr: BVSDivO): T

  fun visit(expr: UserDeclaredExpression<BoolSort>): T

  fun visit(expr: UserDefinedExpression<BoolSort>): T

  fun visit(expr: Expression<BitVecSort>) =
      when (expr) {
        is LocalExpression -> visit(expr)
        is LetExpression -> visit(expr)
        is BoundVariable -> visit(expr)
        is Ite -> visit(expr)
        is BitVecLiteral -> visit(expr)
        is BVConcat -> visit(expr)
        is BVExtract -> visit(expr)
        is BVNot -> visit(expr)
        is BVNeg -> visit(expr)
        is BVAnd -> visit(expr)
        is BVOr -> visit(expr)
        is BVAdd -> visit(expr)
        is BVMul -> visit(expr)
        is BVUDiv -> visit(expr)
        is BVURem -> visit(expr)
        is BVShl -> visit(expr)
        is BVLShr -> visit(expr)
        is FPToUBitVec -> visit(expr)
        is FPToSBitVec -> visit(expr)
        is BVNAnd -> visit(expr)
        is BVNOr -> visit(expr)
        is BVXOr -> visit(expr)
        is BVXNOr -> visit(expr)
        is BVComp -> visit(expr)
        is BVSub -> visit(expr)
        is BVSDiv -> visit(expr)
        is BVSRem -> visit(expr)
        is BVSMod -> visit(expr)
        is BVAShr -> visit(expr)
        is Repeat -> visit(expr)
        is ZeroExtend -> visit(expr)
        is SignExtend -> visit(expr)
        is RotateRight -> visit(expr)
        is RotateLeft -> visit(expr)
        is ArraySelect<*, BitVecSort> -> visit(expr)
        is UserDeclaredExpression -> visit(expr)
        is UserDefinedExpression -> visit(expr)
        else ->
            throw IllegalArgumentException(
                "Can not visit expression $this with type ${expr.javaClass}!"
            )
      }

  fun visit(expr: LocalExpression<BitVecSort>): T

  fun visit(expr: LetExpression<BitVecSort>): T

  fun visit(expr: BoundVariable<BitVecSort>): T

  fun visit(expr: Ite<BitVecSort>): T

  fun visit(expr: BitVecLiteral): T

  fun visit(expr: BVConcat): T

  fun visit(expr: BVExtract): T

  fun visit(expr: BVNot): T

  fun visit(expr: BVNeg): T

  fun visit(expr: BVAnd): T

  fun visit(expr: BVOr): T

  fun visit(expr: BVAdd): T

  fun visit(expr: BVMul): T

  fun visit(expr: BVUDiv): T

  fun visit(expr: BVURem): T

  fun visit(expr: BVShl): T

  fun visit(expr: BVLShr): T

  fun visit(expr: FPToUBitVec): T

  fun visit(expr: FPToSBitVec): T

  fun visit(expr: BVNAnd): T

  fun visit(expr: BVNOr): T

  fun visit(expr: BVXOr): T

  fun visit(expr: BVXNOr): T

  fun visit(expr: BVComp): T

  fun visit(expr: BVSub): T

  fun visit(expr: BVSDiv): T

  fun visit(expr: BVSRem): T

  fun visit(expr: BVSMod): T

  fun visit(expr: BVAShr): T

  fun visit(expr: Repeat): T

  fun visit(expr: ZeroExtend): T

  fun visit(expr: SignExtend): T

  fun visit(expr: RotateRight): T

  fun visit(expr: RotateLeft): T

  fun visit(expr: ArraySelect<*, BitVecSort>): T

  fun visit(expr: UserDeclaredExpression<BitVecSort>): T

  fun visit(expr: UserDefinedExpression<BitVecSort>): T

  fun visit(expr: Expression<IntSort>): T =
      when (expr) {
        is LocalExpression -> visit(expr)
        is LetExpression -> visit(expr)
        is BoundVariable -> visit(expr)
        is Ite -> visit(expr)
        is IntLiteral -> visit(expr)
        is IntNeg -> visit(expr)
        is IntSub -> visit(expr)
        is IntAdd -> visit(expr)
        is IntMul -> visit(expr)
        is IntDiv -> visit(expr)
        is Mod -> visit(expr)
        is Abs -> visit(expr)
        is ToInt -> visit(expr)
        is StrLength -> visit(expr)
        is StrIndexOf -> visit(expr)
        is StrToCode -> visit(expr)
        is StrToInt -> visit(expr)
        is ArraySelect<*, IntSort> -> visit(expr)
        is UserDeclaredExpression -> visit(expr)
        is UserDefinedExpression -> visit(expr)
        else ->
            throw IllegalArgumentException(
                "Can not visit expression $this with type ${expr.javaClass}!"
            )
      }

  fun visit(expr: LocalExpression<IntSort>): T

  fun visit(expr: LetExpression<IntSort>): T

  fun visit(expr: BoundVariable<IntSort>): T

  fun visit(expr: Ite<IntSort>): T

  fun visit(expr: IntLiteral): T

  fun visit(expr: IntNeg): T

  fun visit(expr: IntSub): T

  fun visit(expr: IntAdd): T

  fun visit(expr: IntMul): T

  fun visit(expr: IntDiv): T

  fun visit(expr: Mod): T

  fun visit(expr: Abs): T

  fun visit(expr: ToInt): T

  fun visit(expr: StrLength): T

  fun visit(expr: StrIndexOf): T

  fun visit(expr: StrToCode): T

  fun visit(expr: StrToInt): T

  fun visit(expr: ArraySelect<*, IntSort>): T

  fun visit(expr: UserDeclaredExpression<IntSort>): T

  fun visit(expr: UserDefinedExpression<IntSort>): T

  fun visit(expr: Expression<RealSort>): T =
      when (expr) {
        is LocalExpression -> visit(expr)
        is LetExpression -> visit(expr)
        is BoundVariable -> visit(expr)
        is Ite -> visit(expr)
        is RealLiteral -> visit(expr)
        is RealNeg -> visit(expr)
        is RealSub -> visit(expr)
        is RealAdd -> visit(expr)
        is RealMul -> visit(expr)
        is RealDiv -> visit(expr)
        is ToReal -> visit(expr)
        is FPToReal -> visit(expr)
        is ArraySelect<*, RealSort> -> visit(expr)
        is UserDeclaredExpression -> visit(expr)
        is UserDefinedExpression -> visit(expr)
        else ->
            throw IllegalArgumentException(
                "Can not visit expression $this with type ${expr.javaClass}!"
            )
      }

  fun visit(expr: LocalExpression<RealSort>): T

  fun visit(expr: LetExpression<RealSort>): T

  fun visit(expr: BoundVariable<RealSort>): T

  fun visit(expr: Ite<RealSort>): T

  fun visit(expr: RealLiteral): T

  fun visit(expr: RealNeg): T

  fun visit(expr: RealSub): T

  fun visit(expr: RealAdd): T

  fun visit(expr: RealMul): T

  fun visit(expr: RealDiv): T

  fun visit(expr: ToReal): T

  fun visit(expr: FPToReal): T

  fun visit(expr: ArraySelect<*, RealSort>): T

  fun visit(expr: UserDeclaredExpression<RealSort>): T

  fun visit(expr: UserDefinedExpression<RealSort>): T

  fun visit(expr: Expression<FPSort>): T =
      when (expr) {
        is LocalExpression -> visit(expr)
        is LetExpression -> visit(expr)
        is BoundVariable -> visit(expr)
        is Ite -> visit(expr)
        is FloatingPointLiteral -> visit(expr)
        is FPInfinity -> visit(expr)
        is FPMinusInfinity -> visit(expr)
        is FPZero -> visit(expr)
        is FPMinusZero -> visit(expr)
        is FPNaN -> visit(expr)
        is FPAbs -> visit(expr)
        is FPNeg -> visit(expr)
        is FPAdd -> visit(expr)
        is FPSub -> visit(expr)
        is FPMul -> visit(expr)
        is FPDiv -> visit(expr)
        is FPFma -> visit(expr)
        is FPSqrt -> visit(expr)
        is FPRem -> visit(expr)
        is FPRoundToIntegral -> visit(expr)
        is FPMin -> visit(expr)
        is FPMax -> visit(expr)
        is BitVecToFP -> visit(expr)
        is FPToFP -> visit(expr)
        is RealToFP -> visit(expr)
        is SBitVecToFP -> visit(expr)
        is UBitVecToFP -> visit(expr)
        is ArraySelect<*, FPSort> -> visit(expr)
        is UserDeclaredExpression -> visit(expr)
        is UserDefinedExpression -> visit(expr)
        else ->
            throw IllegalArgumentException(
                "Can not visit expression $this with type ${expr.javaClass}!"
            )
      }

  fun visit(expr: LocalExpression<FPSort>): T

  fun visit(expr: LetExpression<FPSort>): T

  fun visit(expr: BoundVariable<FPSort>): T

  fun visit(expr: Ite<FPSort>): T

  fun visit(expr: FloatingPointLiteral): T

  fun visit(expr: FPInfinity): T

  fun visit(expr: FPMinusInfinity): T

  fun visit(expr: FPZero): T

  fun visit(expr: FPMinusZero): T

  fun visit(expr: FPNaN): T

  fun visit(expr: FPAbs): T

  fun visit(expr: FPNeg): T

  fun visit(expr: FPAdd): T

  fun visit(expr: FPSub): T

  fun visit(expr: FPMul): T

  fun visit(expr: FPDiv): T

  fun visit(expr: FPFma): T

  fun visit(expr: FPSqrt): T

  fun visit(expr: FPRem): T

  fun visit(expr: FPRoundToIntegral): T

  fun visit(expr: FPMin): T

  fun visit(expr: FPMax): T

  fun visit(expr: BitVecToFP): T

  fun visit(expr: FPToFP): T

  fun visit(expr: RealToFP): T

  fun visit(expr: SBitVecToFP): T

  fun visit(expr: UBitVecToFP): T

  fun visit(expr: ArraySelect<*, FPSort>): T

  fun visit(expr: UserDeclaredExpression<FPSort>): T

  fun visit(expr: UserDefinedExpression<FPSort>): T

  fun visit(expr: Expression<RoundingModeSort>): T =
      when (expr) {
        is LocalExpression -> visit(expr)
        is LetExpression -> visit(expr)
        is BoundVariable -> visit(expr)
        is Ite -> visit(expr)
        is RoundNearestTiesToEven -> visit(expr)
        is RNE -> visit(expr)
        is RoundNearestTiesToAway -> visit(expr)
        is RNA -> visit(expr)
        is RoundTowardPositive -> visit(expr)
        is RTP -> visit(expr)
        is RoundTowardNegative -> visit(expr)
        is RTN -> visit(expr)
        is RoundTowardZero -> visit(expr)
        is RTZ -> visit(expr)
        is ArraySelect<*, RoundingModeSort> -> visit(expr)
        is UserDeclaredExpression -> visit(expr)
        is UserDefinedExpression -> visit(expr)
        else ->
            throw IllegalArgumentException(
                "Can not visit expression $this with type ${expr.javaClass}!"
            )
      }

  fun visit(expr: LocalExpression<RoundingModeSort>): T

  fun visit(expr: LetExpression<RoundingModeSort>): T

  fun visit(expr: BoundVariable<RoundingModeSort>): T

  fun visit(expr: Ite<RoundingModeSort>): T

  fun visit(expr: RoundNearestTiesToEven): T

  fun visit(expr: RNE): T

  fun visit(expr: RoundNearestTiesToAway): T

  fun visit(expr: RNA): T

  fun visit(expr: RoundTowardPositive): T

  fun visit(expr: RTP): T

  fun visit(expr: RoundTowardNegative): T

  fun visit(expr: RTN): T

  fun visit(expr: RoundTowardZero): T

  fun visit(expr: RTZ): T

  fun visit(expr: ArraySelect<*, RoundingModeSort>): T

  fun visit(expr: UserDeclaredExpression<RoundingModeSort>): T

  fun visit(expr: UserDefinedExpression<RoundingModeSort>): T

  fun visit(expr: Expression<StringSort>): T =
      when (expr) {
        is LocalExpression -> visit(expr)
        is LetExpression -> visit(expr)
        is BoundVariable -> visit(expr)
        is Ite -> visit(expr)
        is StringLiteral -> visit(expr)
        is StrConcat -> visit(expr)
        is StrAt -> visit(expr)
        is StrSubstring -> visit(expr)
        is StrReplace -> visit(expr)
        is StrReplaceAll -> visit(expr)
        is StrReplaceRegex -> visit(expr)
        is StrReplaceAllRegex -> visit(expr)
        is StrFromCode -> visit(expr)
        is StrFromInt -> visit(expr)
        is ArraySelect<*, StringSort> -> visit(expr)
        is UserDeclaredExpression -> visit(expr)
        is UserDefinedExpression -> visit(expr)
        else ->
            throw IllegalArgumentException(
                "Can not visit expression $this with type ${expr.javaClass}!"
            )
      }

  fun visit(expr: LocalExpression<StringSort>): T

  fun visit(expr: LetExpression<StringSort>): T

  fun visit(expr: BoundVariable<StringSort>): T

  fun visit(expr: Ite<StringSort>): T

  fun visit(expr: StringLiteral): T

  fun visit(expr: StrConcat): T

  fun visit(expr: StrAt): T

  fun visit(expr: StrSubstring): T

  fun visit(expr: StrReplace): T

  fun visit(expr: StrReplaceAll): T

  fun visit(expr: StrReplaceRegex): T

  fun visit(expr: StrReplaceAllRegex): T

  fun visit(expr: StrFromCode): T

  fun visit(expr: StrFromInt): T

  fun visit(expr: ArraySelect<*, StringSort>): T

  fun visit(expr: UserDeclaredExpression<StringSort>): T

  fun visit(expr: UserDefinedExpression<StringSort>): T

  fun visit(expr: Expression<RegLanSort>): T =
      when (expr) {
        is LocalExpression -> visit(expr)
        is LetExpression -> visit(expr)
        is BoundVariable -> visit(expr)
        is StrToRe -> visit(expr)
        is RegexNone -> visit(expr)
        is RegexAll -> visit(expr)
        is RegexAllChar -> visit(expr)
        is RegexConcat -> visit(expr)
        is RegexUnion -> visit(expr)
        is RegexIntersec -> visit(expr)
        is RegexStar -> visit(expr)
        is RegexComp -> visit(expr)
        is RegexDiff -> visit(expr)
        is RegexPlus -> visit(expr)
        is RegexOption -> visit(expr)
        is RegexRange -> visit(expr)
        is RegexPower -> visit(expr)
        is RegexLoop -> visit(expr)
        is ArraySelect<*, RegLanSort> -> visit(expr)
        is UserDeclaredExpression -> visit(expr)
        is UserDefinedExpression -> visit(expr)
        else ->
            throw IllegalArgumentException(
                "Can not visit expression $this with type ${expr.javaClass}!"
            )
      }

  fun visit(expr: LocalExpression<RegLanSort>): T

  fun visit(expr: LetExpression<RegLanSort>): T

  fun visit(expr: BoundVariable<RegLanSort>): T

  fun visit(expr: StrToRe): T

  fun visit(expr: RegexNone): T

  fun visit(expr: RegexAll): T

  fun visit(expr: RegexAllChar): T

  fun visit(expr: RegexConcat): T

  fun visit(expr: RegexUnion): T

  fun visit(expr: RegexIntersec): T

  fun visit(expr: RegexStar): T

  fun visit(expr: RegexComp): T

  fun visit(expr: RegexDiff): T

  fun visit(expr: RegexPlus): T

  fun visit(expr: RegexOption): T

  fun visit(expr: RegexRange): T

  fun visit(expr: RegexPower): T

  fun visit(expr: RegexLoop): T

  fun visit(expr: ArraySelect<*, RegLanSort>): T

  fun visit(expr: UserDeclaredExpression<RegLanSort>): T

  fun visit(expr: UserDefinedExpression<RegLanSort>): T

  fun visit(expr: Expression<ArraySort<*, *>>): T =
      when (expr) {
        is Ite -> visit(expr)
        is LocalExpression -> visit(expr)
        is LetExpression -> visit(expr)
        is ArrayStore -> visit(expr)
        is ArraySelect<*, ArraySort<*, *>> -> visit(expr)
        is UserDeclaredExpression -> visit(expr)
        is UserDefinedExpression -> visit(expr)
        else ->
            throw IllegalArgumentException(
                "Can not visit expression $this with type ${expr.javaClass}!"
            )
      }

  fun visit(expr: Ite<ArraySort<*, *>>): T

  fun visit(expr: LocalExpression<ArraySort<*, *>>): T

  fun visit(expr: LetExpression<ArraySort<*, *>>): T

  fun visit(expr: ArrayStore<*, *>): T

  fun visit(expr: ArraySelect<*, ArraySort<*, *>>): T

  fun visit(expr: UserDeclaredExpression<ArraySort<*, *>>): T

  fun visit(expr: UserDefinedExpression<ArraySort<*, *>>): T

  fun visit(expr: Expression<Datatype>): T =
      when (expr) {
        is Ite -> visit(expr)
        is LocalExpression -> visit(expr)
        is LetExpression -> visit(expr)
        is ArraySelect<*, Datatype> -> visit(expr)
        is UserDeclaredExpression -> visit(expr)
        is UserDefinedExpression -> visit(expr)
        else ->
            throw IllegalArgumentException(
                "Can not visit expression $this with type ${expr.javaClass}!"
            )
      }

  fun visit(expr: Ite<Datatype>): T

  fun visit(expr: LocalExpression<Datatype>): T

  fun visit(expr: LetExpression<Datatype>): T

  fun visit(expr: ArraySelect<*, Datatype>): T

  fun visit(expr: UserDeclaredExpression<Datatype>): T

  fun visit(expr: UserDefinedExpression<Datatype>): T

  fun visit(expr: Expression<UserDeclaredSort>): T =
      when (expr) {
        is Ite -> visit(expr)
        is LocalExpression -> visit(expr)
        is LetExpression -> visit(expr)
        is ArraySelect<*, UserDeclaredSort> -> visit(expr)
        is UserDeclaredExpression -> visit(expr)
        is UserDefinedExpression -> visit(expr)
        else ->
            throw IllegalArgumentException(
                "Can not visit expression $this with type ${expr.javaClass}!"
            )
      }

  fun visit(expr: Ite<UserDeclaredSort>): T

  fun visit(expr: LocalExpression<UserDeclaredSort>): T

  fun visit(expr: LetExpression<UserDeclaredSort>): T

  fun visit(expr: ArraySelect<*, UserDeclaredSort>): T

  fun visit(expr: UserDeclaredExpression<UserDeclaredSort>): T

  fun visit(expr: UserDefinedExpression<UserDeclaredSort>): T
}

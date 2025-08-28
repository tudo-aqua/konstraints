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

package tools.aqua.konstraints.solvers.z3

import com.microsoft.z3.ArrayExpr
import com.microsoft.z3.ArraySort as Z3ArraySort
import com.microsoft.z3.BitVecExpr
import com.microsoft.z3.BitVecNum
import com.microsoft.z3.BitVecSort
import com.microsoft.z3.BoolExpr
import com.microsoft.z3.CharSort
import com.microsoft.z3.BoolSort as Z3BoolSort
import com.microsoft.z3.Expr
import com.microsoft.z3.FPExpr
import com.microsoft.z3.FPNum
import com.microsoft.z3.FPRMExpr
import com.microsoft.z3.FPRMSort as Z3RMSort
import com.microsoft.z3.FPSort as Z3FPSort
import com.microsoft.z3.IntExpr
import com.microsoft.z3.IntNum
import com.microsoft.z3.ReExpr
import com.microsoft.z3.IntSort as Z3IntSort
import com.microsoft.z3.RealExpr
import com.microsoft.z3.SeqExpr
import com.microsoft.z3.SeqSort
import com.microsoft.z3.RealSort as Z3RealSort
import com.microsoft.z3.Sort as Z3Sort
import com.microsoft.z3.enumerations.Z3_decl_kind
import tools.aqua.konstraints.smt.*

fun Z3Sort.aquaify(): Sort =
    when (this) {
      is Z3BoolSort -> Bool
      is Z3IntSort -> SMTInt
      is Z3RealSort -> Real
      is BitVecSort -> BVSort(size)
      is Z3FPSort -> FloatingPoint(eBits, sBits)
      is Z3RMSort -> RoundingMode
      is Z3ArraySort<*, *> -> SMTArray(domain.aquaify(), range.aquaify())
      else -> throw RuntimeException("Unknown or unsupported Z3 sort $this")
    }

@JvmName("aquaifyAny")
fun Expr<*>.aquaify(): Expression<*> =
    @Suppress("UNCHECKED_CAST")
    when (this) {
      is BoolExpr -> this.aquaify()
      is IntExpr -> this.aquaify()
      is RealExpr -> this.aquaify()
      is BitVecExpr -> this.aquaify()
      is FPExpr -> this.aquaify()
      is FPRMExpr -> this.aquaify()
      is ArrayExpr<*, *> -> this.aquaify()
        is ReExpr<*> -> this.aquaify()
        is SeqExpr<*> -> if(sort.toString() == "String") {
            this.aquaify()
        } else {
            throw RuntimeException("Unknown or unsupported Z3 sort $sort")
        }
      else -> throw RuntimeException("Unknown or unsupported Z3 sort $sort")
    }

@JvmName("aquaifyBool")
fun BoolExpr.aquaify(): Expression<BoolSort> =
    if (isTrue) {
      True
    } else if (isFalse) {
      False
    } else if (isNot) {
      Not(args[0].aquaify().cast())
    } else if (isImplies) {
      Implies(args.map { expr -> expr.aquaify().cast() })
    } else if (isAnd) {
      And(args.map { expr -> expr.aquaify().cast() })
    } else if (isOr) {
      Or(args.map { expr -> expr.aquaify().cast() })
    } else if (isXor) {
      XOr(args.map { expr -> expr.aquaify().cast() })
    } else if (isEq) {
      Equals(args.map { it.aquaify() })
    } else if (isDistinct) {
      Distinct(args.map { expr -> expr.aquaify().cast() })
    } else if (isITE) {
      Ite(args[0].aquaify().cast(), args[1].aquaify().cast(), args[2].aquaify().cast())
    } else if (isLT) {
      // z3 does not differentiate between Int and Real operations
      if (isInt) {
        IntLess(args.map { expr -> expr.aquaify().cast() })
      } else {
        RealLess(args.map { expr -> expr.aquaify().cast() })
      }
    } else if (isLE) {
      // z3 does not differentiate between Int and Real operations
      if (isInt) {
        IntLessEq(args.map { expr -> expr.aquaify().cast() })
      } else {
        RealLessEq(args.map { expr -> expr.aquaify().cast() })
      }
    } else if (isGT) {
      // z3 does not differentiate between Int and Real operations
      if (isInt) {
        IntGreater(args.map { expr -> expr.aquaify().cast() })
      } else {
        RealGreater(args.map { expr -> expr.aquaify().cast() })
      }
    } else if (isGE) {
      // z3 does not differentiate between Int and Real operations
      if (isInt) {
        IntGreaterEq(args.map { expr -> expr.aquaify().cast() })
      } else {
        RealGreaterEq(args.map { expr -> expr.aquaify().cast() })
      }
    } else if (isBVULT) {
      BVUlt(args[0].aquaify().cast(), args[1].aquaify().cast())
    } else if (isBVULE) {
      BVULe(args[0].aquaify().cast(), args[1].aquaify().cast())
    } else if (isBVUGT) {
      BVUGt(args[0].aquaify().cast(), args[1].aquaify().cast())
    } else if (isBVUGE) {
      BVUGe(args[0].aquaify().cast(), args[1].aquaify().cast())
    } else if (isBVSLT) {
      BVSLt(args[0].aquaify().cast(), args[1].aquaify().cast())
    } else if (isBVSLE) {
      BVSLe(args[0].aquaify().cast(), args[1].aquaify().cast())
    } else if (isBVSGT) {
      BVSGt(args[0].aquaify().cast(), args[1].aquaify().cast())
    } else if (isBVSGE) {
      BVSGe(args[0].aquaify().cast(), args[1].aquaify().cast())
    } else if (funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_LE) {
      FPLeq(args.map { expr -> expr.aquaify().cast() })
    } else if (funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_LT) {
      FPLt(args.map { expr -> expr.aquaify().cast() })
    } else if (funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_GE) {
      FPGeq(args.map { expr -> expr.aquaify().cast() })
    } else if (funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_GT) {
      FPGt(args.map { expr -> expr.aquaify().cast() })
    } else if (funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_EQ) {
      FPEq(args.map { expr -> expr.aquaify().cast() })
    } else if (funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_IS_NORMAL) {
      FPIsNormal(args[0].aquaify().cast())
    } else if (funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_IS_SUBNORMAL) {
      FPIsSubnormal(args[0].aquaify().cast())
    } else if (funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_IS_ZERO) {
      FPIsZero(args[0].aquaify().cast())
    } else if (funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_IS_INF) {
      FPIsInfinite(args[0].aquaify().cast())
    } else if (funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_IS_NAN) {
      FPIsNaN(args[0].aquaify().cast())
    } else if (funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_IS_NEGATIVE) {
      FPIsNegative(args[0].aquaify().cast())
    } else if (funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_IS_POSITIVE) {
      FPIsPositive(args[0].aquaify().cast())
    } else {
      throw RuntimeException("Unknown or unsupported bool expression $this")
    }

@JvmName("aquaifyInt")
fun IntExpr.aquaify(): Expression<IntSort> =
    if (isUMinus) {
      IntNeg(args[0].aquaify().cast())
    } else if (isSub) {
      IntSub(args.map { expr -> expr.aquaify().cast() })
    } else if (isAdd) {
      IntAdd(args.map { expr -> expr.aquaify().cast() })
    } else if (isMul) {
      IntMul(args.map { expr -> expr.aquaify().cast() })
    } else if (isDiv) {
      IntDiv(args.map { expr -> expr.aquaify().cast() })
    } else if (isModulus) {
      Mod(args[0].aquaify().cast(), args[1].aquaify().cast())
    } else if (isIntNum) {
      IntLiteral((this as IntNum).bigInteger)
    } else if (isRealToInt) {
      ToInt(args[0].aquaify().cast())
    } else if (isBVToInt) {
      TODO("Missing")
    } else {
      throw RuntimeException("Unknown or unsupported int expression $this")
    }

@JvmName("aquaifyReal")
fun RealExpr.aquaify(): Expression<RealSort> =
    if (isUMinus) {
      RealNeg(args[0].aquaify().cast())
    } else if (isSub) {
      RealSub(args.map { expr -> expr.aquaify().cast() })
    } else if (isAdd) {
      RealAdd(args.map { expr -> expr.aquaify().cast() })
    } else if (isMul) {
      RealMul(args.map { expr -> expr.aquaify().cast() })
    } else if (isDiv) {
      RealDiv(args.map { expr -> expr.aquaify().cast() })
    } else if (isIntNum) {
      RealLiteral((this as IntNum).bigInteger)
    } else if (isIntToReal) {
      ToReal(args[0].aquaify().cast())
    } else if (funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_TO_REAL) {
      FPToReal(args[0].aquaify().cast())
    } else {
      throw RuntimeException("Unknown or unsupported real expression $this")
    }

@JvmName("aquaifyBitVec")
fun BitVecExpr.aquaify(): Expression<BVSort> =
    if (isBVNOT) {
      BVNot(args[0].aquaify().cast())
    } else if (isBVAND) {
      BVAnd(args.map { expr -> expr.aquaify().cast() })
    } else if (isBVOR) {
      BVOr(args.map { expr -> expr.aquaify().cast() })
    } else if (isBVAdd) {
      BVAdd(args.map { expr -> expr.aquaify().cast() })
    } else if (isBVMul) {
      BVMul(args.map { expr -> expr.aquaify().cast() })
    } else if (isBVUDiv) {
      BVUDiv(args[0].aquaify().cast(), args[1].aquaify().cast())
    } else if (isBVURem) {
      BVURem(args[0].aquaify().cast(), args[1].aquaify().cast())
    } else if (isBVShiftLeft) {
      BVShl(args[0].aquaify().cast(), args[1].aquaify().cast())
    } else if (isBVShiftRightLogical) {
      BVLShr(args[0].aquaify().cast(), args[1].aquaify().cast())
    } else if (isConcat) {
      BVConcat(args[0].aquaify().cast(), args[1].aquaify().cast())
    } else if (isBVExtract) {
      BVExtract(funcDecl.parameters[0].int, funcDecl.parameters[1].int, args[0].aquaify().cast())
    } else if (isBVNAND) {
      BVNAnd(args[0].aquaify().cast(), args[1].aquaify().cast())
    } else if (isBVNOR) {
      BVNOr(args[0].aquaify().cast(), args[1].aquaify().cast())
    } else if (isBVXOR) {
      BVXOr(args[0].aquaify().cast(), args[1].aquaify().cast())
    } else if (isBVXNOR) {
      BVXNOr(args[0].aquaify().cast(), args[1].aquaify().cast())
    } else if (isBVComp) {
      BVComp(args[0].aquaify().cast(), args[1].aquaify().cast())
    } else if (isBVSub) {
      BVSub(args[0].aquaify().cast(), args[1].aquaify().cast())
    } else if (isBVSDiv) {
      BVSDiv(args[0].aquaify().cast(), args[1].aquaify().cast())
    } else if (isBVSRem) {
      BVSRem(args[0].aquaify().cast(), args[1].aquaify().cast())
    } else if (isBVSMod) {
      BVSMod(args[0].aquaify().cast(), args[1].aquaify().cast())
    } else if (isBVShiftRightArithmetic) {
      BVAShr(args[0].aquaify().cast(), args[1].aquaify().cast())
    } else if (isBVRepeat) {
      Repeat(funcDecl.parameters[0].int, args[0].aquaify().cast())
    } else if (isBVZeroExtension) {
      ZeroExtend(funcDecl.parameters[0].int, args[0].aquaify().cast())
    } else if (isBVSignExtension) {
      SignExtend(funcDecl.parameters[0].int, args[0].aquaify().cast())
    } else if (isBVRotateLeft) {
      RotateLeft(funcDecl.parameters[0].int, args[0].aquaify().cast())
    } else if (isBVRotateRight) {
      RotateRight(funcDecl.parameters[0].int, args[0].aquaify().cast())
    } else if (funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_TO_UBV) {
      FPToUBitVec(args[0].aquaify().cast(), args[1].aquaify().cast(), funcDecl.parameters[0].int)
    } else if (funcDecl.declKind == Z3_decl_kind.Z3_OP_FPA_TO_SBV) {
      FPToSBitVec(args[0].aquaify().cast(), args[1].aquaify().cast(), funcDecl.parameters[0].int)
    } else if (this is BitVecNum) {
      // its important that we pass the number of bits here to ensure sort compatibility with the
      // declared function
      BVLiteral("#x${bigInteger.toString(16)}", sort.size)
    } else if (funcDecl.declKind == Z3_decl_kind.Z3_OP_BNUM) {
      BVLiteral(toString(), sort.size)
    } else {
      throw RuntimeException("Unknown or unsupported bitvec expression $this")
    }

@JvmName("aquaifyFloatingPoint")
fun FPExpr.aquaify(): Expression<FPSort> =
    when (funcDecl.declKind) {
      Z3_decl_kind.Z3_OP_FPA_NUM ->
          (this as FPNum).let { fpNum ->
            FPLiteral(
                fpNum.signBV.aquaify().cast(),
                fpNum.getExponentBV(false).aquaify().cast(),
                fpNum.significandBV.aquaify().cast())
          }
      Z3_decl_kind.Z3_OP_FPA_FP ->
          FPLiteral(args[0].aquaify().cast(), args[1].aquaify().cast(), args[2].aquaify().cast())
      Z3_decl_kind.Z3_OP_FPA_PLUS_INF -> FPInfinity(sort.eBits, sort.sBits)
      Z3_decl_kind.Z3_OP_FPA_MINUS_INF -> FPMinusInfinity(sort.eBits, sort.sBits)
      Z3_decl_kind.Z3_OP_FPA_PLUS_ZERO -> FPZero(sort.eBits, sort.sBits)
      Z3_decl_kind.Z3_OP_FPA_MINUS_ZERO -> FPMinusZero(sort.eBits, sort.sBits)
      Z3_decl_kind.Z3_OP_FPA_NAN -> FPNaN(sort.eBits, sort.sBits)
      Z3_decl_kind.Z3_OP_FPA_ABS -> FPAbs(args[0].aquaify().cast())
      Z3_decl_kind.Z3_OP_FPA_NEG -> FPNeg(args[0].aquaify().cast())
      Z3_decl_kind.Z3_OP_FPA_ADD ->
          FPAdd(args[0].aquaify().cast(), args[1].aquaify().cast(), args[2].aquaify().cast())
      Z3_decl_kind.Z3_OP_FPA_SUB ->
          FPSub(args[0].aquaify().cast(), args[1].aquaify().cast(), args[2].aquaify().cast())
      Z3_decl_kind.Z3_OP_FPA_MUL ->
          FPMul(args[0].aquaify().cast(), args[1].aquaify().cast(), args[2].aquaify().cast())
      Z3_decl_kind.Z3_OP_FPA_DIV ->
          FPDiv(args[0].aquaify().cast(), args[1].aquaify().cast(), args[2].aquaify().cast())
      Z3_decl_kind.Z3_OP_FPA_FMA ->
          FPFma(
              args[0].aquaify().cast(),
              args[1].aquaify().cast(),
              args[2].aquaify().cast(),
              args[3].aquaify().cast())
      Z3_decl_kind.Z3_OP_FPA_SQRT -> FPSqrt(args[0].aquaify().cast(), args[1].aquaify().cast())
      Z3_decl_kind.Z3_OP_FPA_REM -> FPRem(args[0].aquaify().cast(), args[1].aquaify().cast())
      Z3_decl_kind.Z3_OP_FPA_ROUND_TO_INTEGRAL ->
          FPRoundToIntegral(args[0].aquaify().cast(), args[1].aquaify().cast())
      Z3_decl_kind.Z3_OP_FPA_MIN -> FPMin(args[0].aquaify().cast(), args[1].aquaify().cast())
      Z3_decl_kind.Z3_OP_FPA_MAX -> FPMax(args[0].aquaify().cast(), args[1].aquaify().cast())
      Z3_decl_kind.Z3_OP_FPA_TO_FP -> {
        val inner = args[1].aquaify()

        if (args.size == 1) {
          BitVecToFP(args[0].aquaify().cast(), sort.aquaify() as FPSort)
        } else if (inner.sort is FPSort) {
          FPToFP(args[0].aquaify().cast(), inner.cast(), sort.aquaify() as FPSort)
        } else if (inner.sort is RealSort) {
          RealToFP(args[0].aquaify().cast(), inner.cast(), sort.aquaify() as FPSort)
        } else if (inner.sort is BVSort) {
          SBitVecToFP(args[0].aquaify().cast(), inner.cast(), sort.aquaify() as FPSort)
        } else {
          throw IllegalStateException()
        }
      }
      Z3_decl_kind.Z3_OP_FPA_TO_FP_UNSIGNED ->
          SBitVecToFP(args[0].aquaify().cast(), args[1].aquaify().cast(), sort.aquaify() as FPSort)
      else ->
          throw RuntimeException(
              "Unknown or unsupported floating point expression $this (decl kind ${this.funcDecl.declKind})")
    }

@JvmName("aquaifyRoundingMode")
fun FPRMExpr.aquaify(): Expression<RoundingModeSort> =
    when (funcDecl.declKind) {
      Z3_decl_kind.Z3_OP_FPA_RM_TOWARD_ZERO -> RoundTowardZero
      Z3_decl_kind.Z3_OP_FPA_RM_TOWARD_NEGATIVE -> RoundTowardNegative
      Z3_decl_kind.Z3_OP_FPA_RM_TOWARD_POSITIVE -> RoundTowardPositive
      Z3_decl_kind.Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY -> RoundNearestTiesToAway
      Z3_decl_kind.Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN -> RoundNearestTiesToEven
      else -> throw RuntimeException("Unknown or unsupported rounding mode expression $this.")
    }

@JvmName("aquaifyArraysEx")
fun ArrayExpr<*, *>.aquaify(): Expression<ArraySort<*, *>> =
    if (isStore) {
      ArrayStore(args[0].aquaify().cast(), args[1].aquaify().cast(), args[2].aquaify().cast())
    } else if (isSelect) {
      ArraySelect(args[0].aquaify().cast(), args[1].aquaify().cast())
    } else {
      throw RuntimeException("Unknown or unsupported array expression $this")
    }

@JvmName("aquaifyString")
fun SeqExpr<SeqSort<CharSort>>.aquaify(): Expression<StringSort> =
    when(funcDecl.declKind) {
        Z3_decl_kind.Z3_OP_SEQ_AT -> TODO()
        Z3_decl_kind.Z3_OP_SEQ_MAP -> TODO()

    }

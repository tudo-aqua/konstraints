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

package tools.aqua.konstraints.solvers.Z3

import com.microsoft.z3.BitVecNum
import com.microsoft.z3.BitVecSort
import com.microsoft.z3.BoolSort as Z3BoolSort
import com.microsoft.z3.Expr
import com.microsoft.z3.IntNum
import com.microsoft.z3.IntSort as Z3IntSort
import com.microsoft.z3.Sort as Z3Sort
import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.smt.Sort
import tools.aqua.konstraints.theories.*
import tools.aqua.konstraints.theories.BVSort
import tools.aqua.konstraints.theories.BoolSort

fun Z3Sort.aquaify(): Sort =
    when (this) {
      is Z3BoolSort -> BoolSort
      is Z3IntSort -> IntSort
      is BitVecSort -> BVSort(this.size)
      else -> throw RuntimeException("Unknown or unsupported Z3 sort $this")
    }

@JvmName("aquaifyAny")
fun Expr<*>.aquaify(): Expression<*> =
    when (this.sort) {
      is Z3BoolSort -> (this as Expr<Z3BoolSort>).aquaify() as Expression<Sort>
      is Z3IntSort -> (this as Expr<Z3IntSort>).aquaify() as Expression<Sort>
      is BitVecSort -> (this as Expr<BitVecSort>).aquaify() as Expression<Sort>
      else -> throw RuntimeException("Unknown or unsupported Z3 sort ${this.sort}")
    }

@JvmName("aquaifyBool")
fun Expr<Z3BoolSort>.aquaify(): Expression<BoolSort> =
    if (isTrue) {
      True
    } else if (isFalse) {
      False
    } else if (isEq) {
      Equals(*this.args.map { it.aquaify() }.toTypedArray())
    } else {
      throw RuntimeException("Unknown or unsupported bool expression $this")
    }

@JvmName("aquaifyInt")
fun Expr<Z3IntSort>.aquaify(): Expression<IntSort> =
    if (isUMinus) {
      IntNeg(this.args[0].aquaify() as Expression<IntSort>)
    } else if (isIntNum) {
      IntLiteral((this as IntNum).int)
    } else {
      throw RuntimeException("Unknown or unsupported int expression $this")
    }

@JvmName("aquaifyBitVec")
fun Expr<BitVecSort>.aquaify(): Expression<BVSort> =
    if (isBVNOT) {
      BVNot(this.args[0].aquaify() as Expression<BVSort>)
    } else if (this is BitVecNum) {
      BVLiteral("#x${this.bigInteger.toString(16)}")
    } else {
      throw RuntimeException("Unknown or unsupported bitvec expression $this")
    }

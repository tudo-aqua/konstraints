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

import com.microsoft.z3.BitVecNum
import com.microsoft.z3.BitVecSort
import com.microsoft.z3.BoolSort as Z3BoolSort
import com.microsoft.z3.Expr
import com.microsoft.z3.IntNum
import com.microsoft.z3.IntSort as Z3IntSort
import com.microsoft.z3.Sort as Z3Sort
import tools.aqua.konstraints.smt.BVLiteral
import tools.aqua.konstraints.smt.BVNot
import tools.aqua.konstraints.smt.BVSort
import tools.aqua.konstraints.smt.Bool
import tools.aqua.konstraints.smt.BoolSort
import tools.aqua.konstraints.smt.Equals
import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.smt.False
import tools.aqua.konstraints.smt.IntLiteral
import tools.aqua.konstraints.smt.IntNeg
import tools.aqua.konstraints.smt.IntSort
import tools.aqua.konstraints.smt.SMTInt
import tools.aqua.konstraints.smt.Sort
import tools.aqua.konstraints.smt.True

fun Z3Sort.aquaify(): Sort =
    when (this) {
      is Z3BoolSort -> Bool
      is Z3IntSort -> SMTInt
      is BitVecSort -> BVSort(this.size)
      else -> throw RuntimeException("Unknown or unsupported Z3 sort $this")
    }

@JvmName("aquaifyAny")
fun Expr<*>.aquaify(): Expression<*> =
    @Suppress("UNCHECKED_CAST")
    when (this.sort) {
      is Z3BoolSort -> (this as Expr<Z3BoolSort>).aquaify()
      is Z3IntSort -> (this as Expr<Z3IntSort>).aquaify()
      is BitVecSort -> (this as Expr<BitVecSort>).aquaify()
      else -> throw RuntimeException("Unknown or unsupported Z3 sort ${this.sort}")
    }

@JvmName("aquaifyBool")
fun Expr<Z3BoolSort>.aquaify(): Expression<BoolSort> =
    if (isTrue) {
      True
    } else if (isFalse) {
      False
    } else if (isEq) {
      Equals(this.args.map { it.aquaify() })
    } else {
      throw RuntimeException("Unknown or unsupported bool expression $this")
    }

@JvmName("aquaifyInt")
fun Expr<Z3IntSort>.aquaify(): Expression<IntSort> =
    if (isUMinus) {
      IntNeg(this.args[0].aquaify() as Expression<IntSort>)
    } else if (isIntNum) {
      IntLiteral((this as IntNum).bigInteger)
    } else {
      throw RuntimeException("Unknown or unsupported int expression $this")
    }

@JvmName("aquaifyBitVec")
fun Expr<BitVecSort>.aquaify(): Expression<BVSort> =
    if (isBVNOT) {
      BVNot(this.args[0].aquaify() as Expression<BVSort>)
    } else if (this is BitVecNum) {
      // its important that we pass the number of bits here to ensure sort compatibility with the
      // declared function
      BVLiteral("#x${this.bigInteger.toString(16)}", this.sort.size)
    } else {
      throw RuntimeException("Unknown or unsupported bitvec expression $this")
    }

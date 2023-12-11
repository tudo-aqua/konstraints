/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2023 The Konstraints Authors
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

package tools.aqua.konstraints.visitors.Z3

import com.microsoft.z3.BitVecSort
import com.microsoft.z3.Context
import com.microsoft.z3.Expr
import tools.aqua.konstraints.*
import tools.aqua.konstraints.visitors.AssociativeVisitor
import tools.aqua.konstraints.visitors.FSBVVisitor

class Z3BitVecVisitor(val context: Context) : FSBVVisitor<Expr<*>>, AssociativeVisitor {
  override fun visit(bvLiteral: BVLiteral): Expr<*> {
    return context.mkBV(bvLiteral.value, bvLiteral.bits)
  }

  override fun visit(bvConcat: BVConcat): Expr<*> {
    return context.mkConcat(
        visit(bvConcat.lhs) as Expr<BitVecSort>, visit(bvConcat.rhs) as Expr<BitVecSort>)
  }

  override fun visit(bvExtract: BVExtract): Expr<*> {
    return context.mkExtract(bvExtract.i, bvExtract.j, visit(bvExtract.inner) as Expr<BitVecSort>)
  }

  override fun visit(bvNot: BVNot): Expr<*> {
    return context.mkBVNot(visit(bvNot.inner) as Expr<BitVecSort>)
  }

  override fun visit(bvNeg: BVNeg): Expr<*> {
    return context.mkBVNot(visit(bvNeg.inner) as Expr<BitVecSort>)
  }

  override fun visit(bvAnd: BVAnd): Expr<*> {
    return makeLeftAssoc(bvAnd.conjuncts, { expr -> visit(expr) }) { lhs, rhs ->
      context.mkBVAND(lhs, rhs)
    }
  }

  override fun visit(bvOr: BVOr): Expr<*> {
    return makeLeftAssoc(bvOr.disjuncts, { expr -> visit(expr) }) { lhs, rhs ->
      context.mkBVOR(lhs, rhs)
    }
  }

  override fun visit(bvAdd: BVAdd): Expr<*> {
    return makeLeftAssoc(bvAdd.summands, { expr -> visit(expr) }) { lhs, rhs ->
      context.mkBVAdd(lhs, rhs)
    }
  }

  override fun visit(bvMul: BVMul): Expr<*> {
    return makeLeftAssoc(bvMul.factors, { expr -> visit(expr) }) { lhs, rhs ->
      context.mkBVMul(lhs, rhs)
    }
  }

  override fun visit(bvuDiv: BVUDiv): Expr<*> {
    return context.mkBVUDiv(
        visit(bvuDiv.numerator) as Expr<BitVecSort>, visit(bvuDiv.denominator) as Expr<BitVecSort>)
  }

  override fun visit(bvuRem: BVURem): Expr<*> {
    return context.mkBVURem(
        visit(bvuRem.numerator) as Expr<BitVecSort>, visit(bvuRem.denominator) as Expr<BitVecSort>)
  }

  override fun visit(bvShl: BVShl): Expr<*> {
    return context.mkBVSHL(
        visit(bvShl.value) as Expr<BitVecSort>, visit(bvShl.distance) as Expr<BitVecSort>)
  }

  override fun visit(bvlShr: BVLShr): Expr<*> {
    return context.mkBVLSHR(
        visit(bvlShr.value) as Expr<BitVecSort>, visit(bvlShr.distance) as Expr<BitVecSort>)
  }

  override fun visit(bvUlt: BVUlt): Expr<*> {
    return context.mkBVULT(visit(bvUlt.lhs) as Expr<BitVecSort>, visit(bvUlt) as Expr<BitVecSort>)
  }
}

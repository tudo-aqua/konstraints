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

import com.microsoft.z3.*
import com.microsoft.z3.BoolSort
import com.microsoft.z3.Sort
import tools.aqua.konstraints.*
import tools.aqua.konstraints.visitors.CommandVisitor

class Z3Solver : CommandVisitor<Unit>, AutoCloseable {
  val context = Context()
  val solver = context.mkSolver()
  val expressionGenerator = Z3ExpressionGenerator(this)

  internal var status = ""

  internal val constants = HashMap<String, Expr<*>>()
  internal val functions = HashMap<String, FuncDecl<*>>()
  internal val sorts = HashMap<tools.aqua.konstraints.Sort, com.microsoft.z3.Sort>()

  override fun visit(assert: Assert) {
    solver.add(expressionGenerator.visit(assert.expression) as Expr<BoolSort>)
    println(solver.assertions.last())
  }

  override fun visit(declareConst: DeclareConst) {
    TODO("Not yet implemented")
  }

  override fun visit(declareFun: DeclareFun) {
    if (declareFun.parameters.isNotEmpty()) {
      functions[declareFun.name.toString()]?.let { error("function already declared.") }
      functions[declareFun.name.toString()] =
          context.mkFuncDecl(
              declareFun.name.toSMTString(),
              declareFun.parameters.map { getOrCreateSort(it) }.toTypedArray(),
              getOrCreateSort(declareFun.sort))
    } else {
      constants[declareFun.name.toString()]?.let { error("constant already declared.") }
      constants[declareFun.name.toString()] =
          when (declareFun.sort) {
            is tools.aqua.konstraints.BoolSort -> context.mkBoolConst(declareFun.name.toSMTString())
            is BVSort -> context.mkBVConst(declareFun.name.toSMTString(), declareFun.sort.bits)
            else -> error("Sort ${declareFun.sort} not supported.")
          }
    }
  }

  private fun getOrCreateSort(sort: tools.aqua.konstraints.Sort): Sort {
    sorts[sort]?.let {
      return sorts[sort]!!
    }
    sorts[sort] =
        when (sort) {
          is BoolSort -> context.mkBoolSort()
          is IntSort -> context.mkIntSort()
          else -> error("unsupported sort $sort")
        }
    return sorts[sort]!!
  }

  override fun visit(checkSat: CheckSat) {
    return when (solver.check()) {
      Status.UNSATISFIABLE -> status = "unsat"
      Status.UNKNOWN -> status = "DontKnow"
      Status.SATISFIABLE -> status = "sat"
    }
  }

  override fun close() {
    solver.reset()
    context.close()
  }
}

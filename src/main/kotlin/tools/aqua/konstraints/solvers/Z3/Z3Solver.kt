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

package tools.aqua.konstraints.solvers.Z3

import com.microsoft.z3.BoolSort
import com.microsoft.z3.IntSort
import com.microsoft.z3.Sort
import com.microsoft.z3.Status
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.visitors.CommandVisitor

class Z3Solver : CommandVisitor<Unit>, AutoCloseable {
  val context = Z3Context()

  internal var status = ""

  override fun visit(assert: Assert) {
    val assertion = assert.expression.z3ify(context)
    println(assertion)
    context.solver.add(assertion)
  }

  override fun visit(declareConst: DeclareConst) {
    TODO("Not yet implemented")
  }

  override fun visit(declareFun: DeclareFun) {
    if (declareFun.parameters.isNotEmpty()) {
      context.functions[declareFun.name.toString()]?.let { error("function already declared.") }
      context.functions[declareFun.name.toString()] =
          context.context.mkFuncDecl(
              declareFun.name.toSMTString(),
              declareFun.parameters.map { getOrCreateSort(it) }.toTypedArray(),
              getOrCreateSort(declareFun.sort))
    } else {
      context.constants[declareFun.name.toString()]?.let { error("constant already declared.") }
      context.constants[declareFun.name.toString()] =
          when (declareFun.sort) {
            is tools.aqua.konstraints.smt.BoolSort ->
                context.context.mkBoolConst(declareFun.name.toSMTString())
            is BVSort ->
                context.context.mkBVConst(declareFun.name.toSMTString(), declareFun.sort.bits)
            is tools.aqua.konstraints.theories.IntSort ->
                context.context.mkIntConst(declareFun.name.toSMTString())
            is tools.aqua.konstraints.theories.RealSort ->
                context.context.mkRealConst(declareFun.name.toSMTString())
            else -> error("Sort ${declareFun.sort} not supported.")
          }
    }
  }

  private fun getOrCreateSort(sort: tools.aqua.konstraints.smt.Sort): Sort {
    context.sorts[sort]?.let {
      return context.sorts[sort]!!
    }
    context.sorts[sort] =
        when (sort) {
          is BoolSort -> context.context.mkBoolSort()
          is IntSort -> context.context.mkIntSort()
          else -> error("unsupported sort $sort")
        }
    return context.sorts[sort]!!
  }

  override fun visit(checkSat: CheckSat) {
    return when (context.solver.check()) {
      Status.UNSATISFIABLE -> status = "unsat"
      Status.UNKNOWN -> status = "DontKnow"
      Status.SATISFIABLE -> status = "sat"
    }
  }

  override fun visit(exit: Exit) {}

  override fun visit(setInfo: SetInfo) {}

  override fun visit(setOption: SetOption) {}

  override fun visit(setLogic: SetLogic) {}

  override fun close() {
    context.solver.reset()
    context.context.close()
  }
}

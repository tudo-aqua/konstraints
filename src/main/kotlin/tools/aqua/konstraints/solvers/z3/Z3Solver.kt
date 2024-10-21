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

package tools.aqua.konstraints.solvers.z3

import com.microsoft.z3.Model as Z3Model
import com.microsoft.z3.Sort
import com.microsoft.z3.Status
import tools.aqua.konstraints.parser.SortedVar
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.solvers.Solver
import tools.aqua.konstraints.theories.*
import tools.aqua.konstraints.visitors.CommandVisitor

class Z3Solver : CommandVisitor<Unit>, Solver {
  val context = Z3Context()
  val solver: com.microsoft.z3.Solver = context.context.mkSolver()

  internal var status: SatStatus = SatStatus.PENDING

  private var model: Z3Model? = null

  fun solve(terms: List<Expression<BoolSort>>): SatStatus {
    val declarations = mutableListOf<DeclareFun>()
    terms.forEach { base ->
      base.forEach {
        if (it is UserDeclaredExpression<*> &&
            declarations.find { decl -> decl.name == it.name } == null) {
          declarations.add(DeclareFun(it.name, it.children.map { it.sort }, it.sort))
        }
      }
    }

    declarations.forEach { visit(it) }
    terms.forEach { visit(Assert(it)) }
    visit(CheckSat)

    return status
  }

  override fun solve(program: SMTProgram): SatStatus {
    program.commands.forEach { visit(it) }

    return status
  }

  override fun getModelOrNull(): Model? {
    return if (model != null) {
      getModel()
    } else {
      return null
    }
  }

  override fun getModel(): Model {
    requireNotNull(model)

    return Model(model!!)
  }

  override fun isModelAvailable(): Boolean {
    return model != null
  }

  override fun visit(assert: Assert) {
    val assertion = assert.expression.z3ify(context)

    solver.add(assertion)
  }

  override fun visit(declareConst: DeclareConst) {
    context.constants[declareConst.name.toString()]?.let { error("constant already declared.") }
    context.constants[declareConst.name.toString()] =
        context.context
            .mkConstDecl(declareConst.name.toSMTString(), getOrCreateSort(declareConst.sort))
            .apply()
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
          context.context
              .mkConstDecl(declareFun.name.toSMTString(), getOrCreateSort(declareFun.sort))
              .apply()
    }
  }

  private fun getOrCreateSort(sort: tools.aqua.konstraints.smt.Sort): Sort {
    context.sorts[sort]?.let {
      return context.sorts[sort]!!
    }
    context.sorts[sort] =
        when (sort) {
          is BoolSort -> context.context.mkBoolSort()
          is BVSort -> context.context.mkBitVecSort(sort.bits)
          is IntSort -> context.context.mkIntSort()
          is RealSort -> context.context.mkRealSort()
          is RoundingMode -> context.context.mkFPRoundingModeSort()
          is FPSort -> context.context.mkFPSort(sort.exponentBits, sort.significantBits)
          is FP16 -> context.context.mkFPSort16()
          is FP32 -> context.context.mkFPSort32()
          is FP64 -> context.context.mkFPSort64()
          is FP128 -> context.context.mkFPSort128()
          is ArraySort<*, *> ->
              context.context.mkArraySort(getOrCreateSort(sort.x), getOrCreateSort(sort.y))
          else -> context.context.mkUninterpretedSort(sort.toSMTString())
        }
    return context.sorts[sort]!!
  }

  override fun visit(checkSat: CheckSat) {
    return when (solver.check()) {
      Status.UNSATISFIABLE -> status = SatStatus.UNSAT
      Status.UNKNOWN -> status = SatStatus.UNKNOWN
      Status.SATISFIABLE -> status = SatStatus.SAT
      null -> throw RuntimeException("z3 solver status was null")
    }
  }

  override fun visit(exit: Exit) {}

  override fun visit(setInfo: SetInfo) {}

  override fun visit(setOption: SetOption) {}

  override fun visit(setLogic: SetLogic) {}

  override fun visit(declareSort: DeclareSort) {
    context.context.mkUninterpretedSort(declareSort.name.toSMTString())
  }

  override fun visit(getModel: GetModel) {
    model = solver.model
  }

  override fun visit(defineFun: DefineFun) {
    // this is empty as we do not need to do any work when seeing a "defineFun"
    // Z3 has no concept of function definitions, we replace function created via define-fun
    // "on the fly" while converting the expression tree into z3 objects
  }

  override fun visit(push: Push) {
    (0 ..< push.n).forEach { _ -> solver.push() }
  }

  override fun visit(pop: Pop) {
    solver.pop(pop.n)
  }

  // this should later be part of solver interface
  override fun close() {
    solver.reset()
    context.context.close()
  }
}

/**
 * Extension function creating a model from a z3 model obtained from solver.model this extends the
 * invoke function of the companion object to emulate constructor syntax
 */
operator fun Model.Companion.invoke(model: Z3Model): Model {
  // TODO implement handling of uninterpreted sorts from model.sorts

  val temp = mutableListOf<FunctionDef<*>>()

  temp.addAll(
      model.constDecls.map { decl ->
        FunctionDef(
            decl.name.toString().symbol(),
            emptyList(),
            decl.range.aquaify(),
            model.getConstInterp(decl).aquaify() castTo decl.range.aquaify())
      })

  temp.addAll(
      model.funcDecls.map { decl ->
        FunctionDef(
            decl.name.toString().symbol(),
            (decl.domain zip 0 ..< decl.domainSize).map { (sort, index) ->
              SortedVar("x$index".symbol(), sort.aquaify())
            },
            decl.range.aquaify(),
            model.getFuncInterp(decl).`else`.aquaify() castTo decl.range.aquaify())
      })

  return Model(temp)
}

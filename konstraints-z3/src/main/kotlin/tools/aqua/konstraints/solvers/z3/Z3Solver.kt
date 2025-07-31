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

import com.microsoft.z3.Model as Z3Model
import com.microsoft.z3.Sort
import com.microsoft.z3.Status
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.solvers.Solver
import tools.aqua.konstraints.util.computeIfAbsentAndMerge
import tools.aqua.konstraints.visitors.CommandVisitor

class Z3Solver : CommandVisitor<Unit>, Solver {
  val context = Z3Context()
  val solver: com.microsoft.z3.Solver = context.context.mkSolver()

  var status: SatStatus = SatStatus.PENDING

  private var z3model: Z3Model? = null

  fun solve(terms: List<Expression<BoolSort>>): SatStatus {
    val declarationsByName = mutableMapOf<Symbol, DeclareFun>()
    terms.forEach { base ->
      base.asSequence().filterIsInstance<UserDeclaredExpression<*>>().forEach { expr ->
        declarationsByName.computeIfAbsentAndMerge(expr.name) { _ ->
          DeclareFun(expr.name, expr.children.map(Expression<*>::sort), expr.sort)
        }
      }
    }

    declarationsByName.values.forEach { visit(it) }
    terms.forEach { visit(Assert(it)) }
    visit(CheckSat)

    return status
  }

  override fun solve(program: SMTProgram): SatStatus {
    program.commands.forEach { visit(it) }
    program.status = status

    return status
  }

  fun simplify(term: Expression<BoolSort>): Expression<BoolSort> {
    val declarationsByName = mutableMapOf<Symbol, DeclareFun>()
    term.asSequence().filterIsInstance<UserDeclaredExpression<*>>().forEach { expr ->
      declarationsByName.computeIfAbsentAndMerge(expr.name) { _ ->
        DeclareFun(expr.name, expr.children.map(Expression<*>::sort), expr.sort)
      }
    }

    declarationsByName.values.forEach { visit(it) }
    val termSimplified = term.z3ify(context).simplify().aquaify()

    return termSimplified
  }

  override val modelOrNull: Model?
    get() = z3model?.let { Model(it) }

  override val isModelAvailable: Boolean
    get() = z3model != null

  override fun visit(assert: Assert) {
    val assertion = assert.expr.z3ify(context)

    solver.add(assertion)
  }


  override fun visit(declareConst: DeclareConst) {
    val name = declareConst.name.toString()
    require(name !in context.constants) { "constant $declareConst already declared." }
    context.constants[name] =
        context.context
            .mkConstDecl(declareConst.name.toSMTString(), getOrCreateSort(declareConst.sort))
            .apply()
  }

  override fun visit(declareFun: DeclareFun) {
    if (declareFun.parameters.isEmpty()) {
      return visit(DeclareConst(declareFun.name, declareFun.sort))
    }

    val name = declareFun.name.toString()
    require(name !in context.functions) { "function $declareFun already declared." }
    context.functions[name] =
        context.context.mkFuncDecl(
            declareFun.name.toSMTString(),
            declareFun.parameters.map { getOrCreateSort(it) }.toTypedArray(),
            getOrCreateSort(declareFun.sort))
  }

  private fun getOrCreateSort(sort: tools.aqua.konstraints.smt.Sort): Sort =
      context.sorts.computeIfAbsentAndMerge(sort) { _ ->
        when (sort) {
          is BoolSort -> context.context.mkBoolSort()
          is BVSort -> context.context.mkBitVecSort(sort.bits)
          is IntSort -> context.context.mkIntSort()
          is RealSort -> context.context.mkRealSort()
          is RoundingModeSort -> context.context.mkFPRoundingModeSort()
          is FPSort -> context.context.mkFPSort(sort.exponentBits, sort.significantBits)
          is FP16 -> context.context.mkFPSort16()
          is FP32 -> context.context.mkFPSort32()
          is FP64 -> context.context.mkFPSort64()
          is FP128 -> context.context.mkFPSort128()
          is ArraySort<*, *> ->
              context.context.mkArraySort(getOrCreateSort(sort.x), getOrCreateSort(sort.y))
          else -> context.context.mkUninterpretedSort(sort.toSMTString())
        }
      }

  override fun visit(checkSat: CheckSat): Unit =
      when (solver.check()) {
        Status.UNSATISFIABLE -> status = SatStatus.UNSAT
        Status.UNKNOWN -> status = SatStatus.UNKNOWN
        Status.SATISFIABLE -> status = SatStatus.SAT
      }

  override fun visit(exit: Exit) {}

  override fun visit(setInfo: SetInfo) {}

  override fun visit(setOption: SetOption) {}

  override fun visit(setLogic: SetLogic) {}

  override fun visit(declareSort: DeclareSort) {
    context.context.mkUninterpretedSort(declareSort.name.toSMTString())
  }

  override fun visit(getModel: GetModel) {
    z3model = solver.model
  }

  override fun visit(defineConst: DefineConst) {
    TODO("Not yet implemented")
  }

  override fun visit(defineFun: DefineFun) {
    // this is empty as we do not need to do any work when seeing a "defineFun"
    // Z3 has no concept of function definitions, we replace function created via define-fun
    // "on the fly" while converting the expression tree into z3 objects
  }

  override fun visit(push: Push) {
    repeat(push.n) { _ -> solver.push() }
  }

  override fun visit(pop: Pop) {
    solver.pop(pop.n)
  }

  override fun visit(defineSort: DefineSort) {
    // empty
  }

  fun reset() {
    solver.reset()
    context.reset()
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
            decl.name.toString().toSymbolWithQuotes(),
            emptyList(),
            decl.range.aquaify(),
            model.getConstInterp(decl).aquaify())
      })

  temp.addAll(
      model.funcDecls.map { decl ->
        FunctionDef(
            decl.name.toString().toSymbolWithQuotes(),
            (decl.domain zip 0..<decl.domainSize).map { (sort, index) ->
              SortedVar("x$index".toSymbolWithQuotes(), sort.aquaify())
            },
            decl.range.aquaify(),
            model.getFuncInterp(decl).`else`.aquaify())
      })

  return Model(temp)
}

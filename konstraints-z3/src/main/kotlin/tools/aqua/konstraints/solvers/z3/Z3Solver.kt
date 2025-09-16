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
import tools.aqua.konstraints.dsl.UserDeclaredSMTFunctionN
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
    val declarationsByName = mutableMapOf<Symbol, DeclareFun<*>>()
    terms.forEach { base ->
      base.asSequence().filterIsInstance<UserDeclaredExpression<*>>().forEach { expr ->
        declarationsByName.computeIfAbsentAndMerge(expr.name) { _ ->
          DeclareFun(
              UserDeclaredSMTFunctionN(
                  expr.name, expr.sort, expr.children.map(Expression<*>::sort)))
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

  override val modelOrNull: Model?
    get() = z3model?.let { Model(it, context) }

  override val isModelAvailable: Boolean
    get() = z3model != null

  override fun visit(assert: Assert) {
    val assertion = assert.expr.z3ify(context)

    solver.add(assertion)
  }

  override fun visit(declareConst: DeclareConst<*>) {
    if (context.functions.put(
        declareConst.func,
        context.context.mkConstDecl(
            declareConst.name.toSMTString(), getOrCreateSort(declareConst.sort))) != null) {
      /*
       * if the smt program we are solving is correct (which we assume since otherwise there is a bug somewhere
       * in the construction of the program) this exception SHOULD never be reached
       */

      throw IllegalStateException("Function ${declareConst.func} was already declared!")
    }
  }

  override fun visit(declareFun: DeclareFun<*>) {
    if (context.functions.put(
        declareFun.func,
        context.context.mkFuncDecl(
            declareFun.name.toSMTString(),
            declareFun.parameters.map { getOrCreateSort(it) }.toTypedArray(),
            getOrCreateSort(declareFun.sort))) != null) {
      /*
       * if the smt program we are solving is correct (which we assume since otherwise there is a bug somewhere
       * in the construction of the program) this exception SHOULD never be reached
       */

      throw IllegalStateException("Function ${declareFun.func} was already declared!")
    }
  }

  private fun getOrCreateSort(sort: tools.aqua.konstraints.smt.Sort): Sort =
      context.sorts.computeIfAbsentAndMerge(sort) { _ ->
        when (sort) {
          is BoolSort -> context.context.mkBoolSort()
          is BVSort -> context.context.mkBitVecSort(sort.bits)
          is IntSort -> context.context.mkIntSort()
          is RealSort -> context.context.mkRealSort()
          is RoundingModeSort -> context.context.mkFPRoundingModeSort()
          /* specialized floating point sorts need to be checked first as they are all FPSorts */
          is FP16 -> context.context.mkFPSort16()
          is FP32 -> context.context.mkFPSort32()
          is FP64 -> context.context.mkFPSort64()
          is FP128 -> context.context.mkFPSort128()
          is FPSort -> context.context.mkFPSort(sort.exponentBits, sort.significantBits)
          is ArraySort<*, *> ->
              context.context.mkArraySort(getOrCreateSort(sort.x), getOrCreateSort(sort.y))
          is StringSort -> context.context.mkStringSort()
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

  override fun close() {
    solver.reset()
    context.context.close()
  }
}

/**
 * Extension function creating a model from a z3 model obtained from solver.model this extends the
 * invoke function of the companion object to emulate constructor syntax
 */
// TODO implement handling of uninterpreted sorts from model.sorts
operator fun Model.Companion.invoke(model: Z3Model, context: Z3Context) =
    Model(
        context.constants.map { (aqua, z3) ->
          FunctionDef(
              aqua.name as Symbol, emptyList(), aqua.sort, model.getConstInterp(z3).aquaify())
        } +
            context.functions.map { (aqua, z3) ->
              if (aqua.parameters.isEmpty()) {
                FunctionDef(aqua.symbol, emptyList(), aqua.sort, model.getConstInterp(z3).aquaify())
              } else {
                model.getFuncInterp(z3).let { interp ->
                  // construct sorted vars that are needed for the function definition
                  val arguments =
                      aqua.parameters.mapIndexed { i, sort ->
                        SortedVar("|x!$i|".toSymbolWithQuotes(), sort)
                      }

                  // build the chained ITE that z3 gives as interpretation for functions with arity
                  // > 0
                  // example interpretation for a function (declare-fun foo (Int Int) Int)
                  //   (define-fun foo ((x!0 Int) (x!1 Int)) Int
                  //    (ite (and (= x!0 1) (= x!1 0)) 1
                  //    (ite (and (= x!0 0) (= x!1 0)) 0
                  //    (ite (and (= x!0 2) (= x!1 1)) 3
                  //    (ite (and (= x!0 0) (= x!1 1)) 1
                  //      2)))))
                  val term =
                      interp.entries
                          .map { entry ->
                            // if the condition has more than two arguments chain them by using and
                            if (entry.numArgs >= 2) {
                              And(
                                  // build the equality conditions
                                  (arguments zip entry.args).map { (local, value) ->
                                    Equals(local.instance, value.aquaify())
                                  }) to entry.value.aquaify()
                            } else {
                              // we only have a single condition here since the functions is arity 1
                              Equals(arguments.single().instance, entry.args.single().aquaify()) to
                                  entry.value.aquaify()
                            }
                          }
                          // build the chain 'bottom up' to get the same order as Z3
                          .reversed()
                          // fold the list of condition, value pairs into ITE where the 'else' is
                          // the next
                          // ITE in the chain
                          .fold(interp.`else`.aquaify()) { acc, (condition, value) ->
                            Ite(condition, value, acc)
                          }

                  // finally construct the function definition
                  FunctionDef(aqua.symbol, arguments, aqua.sort, term)
                }
              }
            })

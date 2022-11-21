package tools.aqua.constraints.runner


/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2022 The jConstraints Authors
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

import gov.nasa.jpf.constraints.api.ConstraintSolver
import gov.nasa.jpf.constraints.api.SolverContext
import gov.nasa.jpf.constraints.api.Valuation
import gov.nasa.jpf.constraints.exceptions.UndecidedBooleanExeception
import gov.nasa.jpf.constraints.smtlibUtility.SMTProblem
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory
import jdk.internal.org.jline.reader.impl.DefaultParser
import org.apache.commons.cli.CommandLine
import org.apache.commons.cli.CommandLineParser
import org.apache.commons.cli.Option
import org.apache.commons.cli.Options
import org.apache.commons.cli.ParseException
import structuralEquivalence.Processor
import java.io.File


class KonstraintsRunner {
    private fun runProgram(cmd: CommandLine) {
        val filepath: String = cmd.getOptionValue("smt")
        val solver: String = cmd.getOptionValue("s")
        if (solver.equals("z3", ignoreCase = true)
            || solver.equals("cvc5", ignoreCase = true)
            || solver.equals("multi", ignoreCase = true)
        ) {
            val constraintSolver: ConstraintSolver = ConstraintSolverFactory.createSolver(solver)
            val problem: SMTProblem = Processor.parseFile(File(filepath))
            val ctx: SolverContext = constraintSolver.createContext()
            val valuation = Valuation()
            ctx.add(problem.assertions)
            val res: ConstraintSolver.Result = ctx.solve(valuation`)
            println("RESULT: $res")
            if (res === ConstraintSolver.Result.SAT) {
                var evaluated = false
                try {
                    System.out.println("Valuation: " + valuation.toString())
                    evaluated = problem.getAllAssertionsAsConjunction().evaluateSMT(valuation)
                } catch (e: UndecidedBooleanExeception) {
                    evaluated = true
                } catch (t: Throwable) {
                    t.printStackTrace()
                    println("VALUATIONERROR")
                }
                println("EVALUATED: $evaluated")
            }
        }
        System.exit(0)
    }

    companion object {
        @JvmStatic
        fun main(args: Array<String>) {
            val parser: CommandLineParser = DefaultParser()
            try {
                val cmd: CommandLine = parser.parse(setupOptions(), args)
                KonstraintsRunner().runProgram(cmd)
            } catch (e: ParseException) {
                e.printStackTrace()
            }
        }

        private fun setupOptions(): Options {
            val smtRootFolder: Option = Option.builder("smt").longOpt("smt_file").hasArg().required().build()
            val solver: Option = Option.builder("s").longOpt("solver").hasArg().required().build()
            val checkerOptions = Options()
            checkerOptions.addOption(smtRootFolder)
            checkerOptions.addOption(solver)
            return checkerOptions
        }
    }
}
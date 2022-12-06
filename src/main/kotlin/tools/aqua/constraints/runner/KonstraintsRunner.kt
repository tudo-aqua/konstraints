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

import com.github.h0tk3y.betterParse.grammar.parseToEnd
import org.apache.commons.cli.CommandLine
import org.apache.commons.cli.DefaultParser
import org.apache.commons.cli.Option
import org.apache.commons.cli.Options
import tools.aqua.constraints.smtlib.SMTLibParser
import tools.aqua.constraints.z3.Z3SMTLibSolver
import java.io.File

fun main(args: Array<String>) {
    val parser = DefaultParser()
    val cmd: CommandLine = parser.parse(setupOptions(), args)
    runProgram(cmd)
}

fun runProgram(cmd: CommandLine) {
    val parser = SMTLibParser()
    val filepath: String = cmd.getOptionValue("smt")
    val solver: String = cmd.getOptionValue("s")
    val smtProblem = File(filepath).readText()

    if (solver.equals("z3", ignoreCase = true)) {
        val constraintSolver = Z3SMTLibSolver()
        println(smtProblem)
        val problem = parser.parseToEnd(smtProblem)
        val solverResult = problem.execute(constraintSolver).toString()

        println("RESULT: $solverResult")
    } else if (solver.equals("multi", ignoreCase = true)) {
        println("Not yet supported for multi.")
    } else if (solver.equals("cvc5", ignoreCase = true)) {
        println("Not yet supported for cvc5.")
    }
    System.exit(0)
}


fun setupOptions(): Options {
    val smtRootFolder: Option = Option.builder("smt").longOpt("smt_file").hasArg().required().build()
    val solver: Option = Option.builder("s").longOpt("solver").hasArg().required().build()
    val checkerOptions = Options()
    checkerOptions.addOption(smtRootFolder)
    checkerOptions.addOption(solver)
    return checkerOptions
}




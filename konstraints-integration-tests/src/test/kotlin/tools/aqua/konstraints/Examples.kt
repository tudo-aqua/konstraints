/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2026 The Konstraints Authors
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

package tools.aqua.konstraints

import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import tools.aqua.konstraints.dsl.*
import tools.aqua.konstraints.smt.QF_BV
import tools.aqua.konstraints.smt.QF_NIRA
import tools.aqua.konstraints.smt.SMTBitVec
import tools.aqua.konstraints.smt.SMTInt
import tools.aqua.konstraints.smt.SMTReal
import tools.aqua.konstraints.smt.SatStatus
import tools.aqua.konstraints.solvers.z3.Z3Solver

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class Examples {
  @Test
  fun simpleProgram() {
    // entry point for smt dsl
    // a logic needs to be specified when creating a program
    // we will be using QF_BV here
    val program =
        smt(QF_BV) {
          // all info flags can be set via the setInfo block
          setInfo {
            // for each standard flag described on p.74 of the smt-lib manual
            // there is a function to set the flag
            smtLibVersion("2.6")
            source("|An examples program to show the usage of the konstraints dsl.|")
            category(BenchmarkCategory.CRAFTED)
            status(SatStatus.SAT)

            // custom flags can be set via <flag> set_to <value>
            "CustomIntFlag" set_to 1

            // for hexadecimal or binary values use set_to_hex and set_to_bin respectively
            // note that hex and bin strings have to follow the smt-lib format of #x or #b
            // respectively
            "CustomHexFlag" set_to_hex "#xFF"
          }

          // solver options can similarly be set via a setOptions block
          setOptions {
            // for each solver option on p. 60 of the smt-lib manual this block provides a setter
            // function
            printSuccess(true)

            // so we can later inspect the model returned by z3
            produceModels(true)

            // none standard solver options may be set via the set_to infix function
            "CustomIntOption" set_to 1
          }

          // there are several ways of introducing new function symbols
          // note that these will be named like the kotlin field on the smt side
          // directly creating a constant will return the created expression that can directly be
          // used
          val u by declaringConst(SMTBitVec(32))

          // creating a function requires instantiating the function to retrieve the expression
          val v by declaring(SMTBitVec(32))

          // we can declare a function that takes two bitvectors and returns a bitvector as follows
          val f by declaring(SMTBitVec(32), SMTBitVec(32), SMTBitVec(32))

          // to build constraints over the terms we created the infix operators can be used
          // note that we need to either use invoke or .instance to retrieve the expression from v
          // as v was declared as a function of arity 0
          val sum = u bvadd v()

          // we can now assert that our mistery function f produces results smaller than the sum of
          // its arguments
          assert(f(u, v()) bvult sum)

          // when we added all assertions we can get the sat status as follows

          val solver = Z3Solver()

          // to automatically close solver resources once finished we solve inside this use block
          solver.use { solver ->
            // we may save the status here however it will also be stored at the program.status
            // field for later use
            val status = checkSat(solver)
            println(status)

            // we can also inspect the model here
            println(solver.model)
          }

          // note that calling checkSat without a solver argument only
          // indicates that we want to get the sat status
          // in this location the program will not be solver yet
          // to actually solve the program we later need to call Solver.solve (see example. ?)
        }
  }

  @Test
  fun quantifierProgram() {
    // entry point for smt dsl
    // a logic needs to be specified when creating a program
    // we will be using QF_BV here
    val program =
        smt(QF_BV) {
          // all info flags can be set via the setInfo block
          setInfo {
            // for each standard flag described on p.74 of the smt-lib manual
            // there is a function to set the flag
            smtLibVersion("2.6")
            source("|An examples program to show the usage of the konstraints dsl.|")
            category(BenchmarkCategory.CRAFTED)
            status(SatStatus.UNSAT)

            // custom flags can be set via <flag> set_to <value>
            "CustomIntFlag" set_to 1

            // for hexadecimal or binary values use set_to_hex and set_to_bin respectively
            // note that hex and bin strings have to follow the smt-lib format of #x or #b
            // respectively
            "CustomHexFlag" set_to_hex "#xFF"
          }

          // solver options can similarly be set via a setOptions block
          setOptions {
            // for each solver option on p. 60 of the smt-lib manual this block provides a setter
            // function
            printSuccess(true)

            // so we can later inspect the model returned by z3
            produceModels(true)

            // none standard solver options may be set via the set_to infix function
            "CustomIntOption" set_to 1
          }

          val f by declaring(SMTBitVec(32), SMTBitVec(32), SMTBitVec(32))

          // we use the forall function to generate an all quantified expression over two bitvectors
          // x and y
          // x and y are only valid within the scope of the lambda
          // we could also store the all quantified expression by writing val qExpr = forall(...)
          assert(forall(SMTBitVec(32), SMTBitVec(32)) { x, y -> f(x, y) bvult (x bvadd y) })

          val solver = Z3Solver()

          // to automatically close solver resources once finished we solve inside this use block
          solver.use { solver ->
            // we may save the status here however it will also be stored at the program.status
            // field for later use
            val status = checkSat(solver)
            println(status)
          }
        }
  }

  @Test
  fun kotlinPrimitivesProgram() {
    // entry point for smt dsl
    // a logic needs to be specified when creating a program
    // we will be using QF_BV here
    val program =
        smt(QF_NIRA) {
          // all info flags can be set via the setInfo block
          setInfo {
            // for each standard flag described on p.74 of the smt-lib manual
            // there is a function to set the flag
            smtLibVersion("2.6")
            source("|An examples program to show the usage of the konstraints dsl.|")
            category(BenchmarkCategory.CRAFTED)
            status(SatStatus.SAT)

            // custom flags can be set via <flag> set_to <value>
            "CustomIntFlag" set_to 1

            // for hexadecimal or binary values use set_to_hex and set_to_bin respectively
            // note that hex and bin strings have to follow the smt-lib format of #x or #b
            // respectively
            "CustomHexFlag" set_to_hex "#xFF"
          }

          // solver options can similarly be set via a setOptions block
          setOptions {
            // for each solver option on p. 60 of the smt-lib manual this block provides a setter
            // function
            printSuccess(true)

            // so we can later inspect the model returned by z3
            produceModels(true)

            // none standard solver options may be set via the set_to infix function
            "CustomIntOption" set_to 1
          }

          val u by declaringConst(SMTInt)
          val v by declaringConst(SMTReal)

          // the dsl also allows for easy use of kotlin primitives in smt programs
          // for IntSort terms any of the following may be used as its automatically converted to an
          // smt int literal
          // Byte, Short, Int, Long, BigInteger
          // for RealSort terms allow any type that can be converted to BigDecimal, however note
          // that when using
          // floating point types such as Float or Double there may be conversion or round errors
          // when numbers
          // can not be represented by a floating point type, its advised to use strings whenever
          // necessary
          // also note that when using RealsInts there are no 'mixed' operations so the user needs
          // to specify
          // if he wants to convert to IntSort or RealSort
          val sum = u.toReal() + v

          // three options to assert that sum is less than 0
          assert(sum leq 0)
          assert(sum leq 0.0)
          assert(sum leq "0.0")

          // when we added all assertions we can get the sat status as follows

          val solver = Z3Solver()

          // to automatically close solver resources once finished we solve inside this use block
          solver.use { solver ->
            // we may save the status here however it will also be stored at the program.status
            // field for later use
            val status = checkSat(solver)

            // we can also inspect the model here
            println(solver.model)
          }

          // note that calling checkSat without a solver argument only
          // indicates that we want to get the sat status
          // in this location the program will not be solver yet
          // to actually solve the program we later need to call Solver.solve (see example. ?)
        }

    println(program)
  }
}

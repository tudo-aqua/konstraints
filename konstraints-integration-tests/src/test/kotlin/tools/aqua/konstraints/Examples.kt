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

import kotlin.use
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import tools.aqua.konstraints.dsl.*
import tools.aqua.konstraints.smt.BV
import tools.aqua.konstraints.smt.BitVecSort
import tools.aqua.konstraints.smt.FPMul
import tools.aqua.konstraints.smt.QF_ASLIA
import tools.aqua.konstraints.smt.QF_BV
import tools.aqua.konstraints.smt.QF_FP
import tools.aqua.konstraints.smt.QF_IDL
import tools.aqua.konstraints.smt.QF_NIRA
import tools.aqua.konstraints.smt.SMTArray
import tools.aqua.konstraints.smt.SMTBitVec
import tools.aqua.konstraints.smt.SMTFP32
import tools.aqua.konstraints.smt.SMTFloatingPoint
import tools.aqua.konstraints.smt.SMTInt
import tools.aqua.konstraints.smt.SMTReal
import tools.aqua.konstraints.smt.SMTRoundingMode
import tools.aqua.konstraints.smt.SMTString
import tools.aqua.konstraints.smt.SatStatus
import tools.aqua.konstraints.smt.bitvec
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
        smt(BV) {
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
        }

    println(program)
  }

  @Test
  fun iteProgram() {
    val program =
        smt(QF_IDL) {
          setInfo {
            smtLibVersion("2.6")
            source("|An examples program to show the usage of the konstraints dsl.|")
            category(BenchmarkCategory.CRAFTED)
            status(SatStatus.SAT)
          }

          setOptions {
            printSuccess(true)
            produceModels(true)
          }

          val u by declaringConst(SMTInt)
          val v by declaringConst(SMTInt)

          // if-then-else conditions can be formulated in a kotlin-like syntax
          val simpleIf = ite(u gt v) then u otherwise v

          // else-if can also be emulated with a kotlin-like syntax note that the next ite in the
          // otherwise block
          // needs to be enclosed in rounded brackets
          val nestedIf = ite(u gt v) then u otherwise (ite(v gt 0) then v otherwise u)

          // for more complicated conditions or values that need to be computed in place an option
          // using lambdas is provided
          val lambdaIf = ite { u gt v } then { u } otherwise { v }

          // note that lambdas also work with kotlin primitives however there are 2 major
          // restrictions
          // 1. At least one of the ite values needs to be an expression with an explicit sort to
          // determine the overall sort of the ite
          // 2. If the then value is a kotlin primitive the otherwise gets restricted to only
          // applicable sort types
          // i.e. using a Float as then value restricts the otherwise to also only use floating
          // point sort while
          // using an Integer would restrict to any numeral type other than float
          // It is also allowed to use a Boolean expression that is evaluated by kotlin however any
          // information
          // about how the statement was evaluated is lost on the smt end as it is just converted to
          // a constant
          ite { javaClass.name.startsWith("tools.aqua") } then { 5L } otherwise { u }

          assert(simpleIf eq nestedIf eq lambdaIf)

          val solver = Z3Solver()

          solver.use { solver ->
            checkSat(solver)
            println(solver.model)
          }
        }

    println(program)
  }

  @Test
  fun bvsdiv8Program() {
    // this program showcases how a more complicated operation may be implemented in a read-able
    // manner using the dsl
    val program =
        smt(BV) {
          // all info flags can be set via the setInfo block
          setInfo {
            smtLibVersion("2.6")
            source("|An examples program to show the usage of the konstraints dsl.|")
            category(BenchmarkCategory.CRAFTED)
            status(SatStatus.SAT)
          }

          setOptions {
            printSuccess(true)
            produceModels(true)
          }

          // smt defines bvsdiv (signed bitvector division) as a shorthand extension of the
          // bitvector theory
          // in this example we build bvsdiv from standard bitvector operations as described in
          // https://smt-lib.org/logics-all.shtml#QF_BV
          // (bvsdiv s t) abbreviates
          //      (let ((?msb_s ((_ extract |m-1| |m-1|) s))
          //            (?msb_t ((_ extract |m-1| |m-1|) t)))
          //        (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
          //             (bvudiv s t)
          //        (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
          //             (bvneg (bvudiv (bvneg s) t))
          //        (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
          //             (bvneg (bvudiv s (bvneg t)))
          //             (bvudiv (bvneg s) (bvneg t))))))
          // this smt script can be expressed much more readable in the kotlin dsl
          // we define bvsdiv as an smt function taking two bitvectors of length 8, returning a
          // bitvector of length 8
          // also note that we can not name the kotlin val bvsdiv as this would lead to an illegal
          // shadowing of a theory symbol
          val bvsdiv8 by
              defining(SMTBitVec(8), SMTBitVec(8), SMTBitVec(8)) { s, t ->
                // we emulate let by storing the extract operation in a local variable
                val msb_s = extract(s.sort.bits - 1, s.sort.bits - 1) { s }
                val msb_t = extract(t.sort.bits - 1, t.sort.bits - 1) { t }

                // finally we build the nested ite
                ite { (msb_s eq "#b0".bitvec()) and (msb_t eq "#b0".bitvec()) } then
                    {
                      s bvudiv t
                    } otherwise
                    {
                      ite { (msb_s eq "#b1".bitvec()) and (msb_t eq "#b0".bitvec()) } then
                          {
                            bvneg { bvneg { s } bvudiv t }
                          } otherwise
                          {
                            ite { (msb_s eq "#b0".bitvec()) and (msb_t eq "#b1".bitvec()) } then
                                {
                                  bvneg { s bvudiv bvneg { t } }
                                } otherwise
                                {
                                  bvneg { s } bvudiv bvneg { t }
                                }
                          }
                    }
              }

          assert {
            // we use an all-quantified expression to verify that our bvsdiv behaves as expected
            forall(SMTBitVec(8), SMTBitVec(8)) { s, t -> (s bvsdiv t) eq bvsdiv8(s, t) }
          }

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

  @Test
  fun bvsdivnProgram() {
    // this program showcases how we can build a new smt operation on bitvectors of arbitrary but
    // fixed length
    val program =
        smt(BV) {
          // all info flags can be set via the setInfo block
          setInfo {
            smtLibVersion("2.6")
            source("|An examples program to show the usage of the konstraints dsl.|")
            category(BenchmarkCategory.CRAFTED)
            status(SatStatus.SAT)
          }

          setOptions {
            printSuccess(true)
            produceModels(true)
          }

          // smt defines bvsdiv (signed bitvector division) as a shorthand extension of the
          // bitvector theory
          // in this example we build bvsdiv from standard bitvector operations as described in
          // https://smt-lib.org/logics-all.shtml#QF_BV
          // (bvsdiv s t) abbreviates
          //      (let ((?msb_s ((_ extract |m-1| |m-1|) s))
          //            (?msb_t ((_ extract |m-1| |m-1|) t)))
          //        (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
          //             (bvudiv s t)
          //        (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
          //             (bvneg (bvudiv (bvneg s) t))
          //        (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
          //             (bvneg (bvudiv s (bvneg t)))
          //             (bvudiv (bvneg s) (bvneg t))))))
          // this smt script can be expressed much more readable in the kotlin dsl
          // we define bvsdiv as an smt function taking two bitvectors of length 8, returning a
          // bitvector of length 8
          // also note that we can not name the kotlin val bvsdiv as this would lead to an illegal
          // shadowing of a theory symbol

          // its important that this is a local function so we have access to the SMTProgramBuilder
          // functions
          fun bvsdivn(n: Int): UserDefinedSMTFunction2<BitVecSort, SMTBitVec, SMTBitVec> {
            require(n > 0)

            // note that we need to manually give a name here to avoid illegal shadowing
            val bvsdiv by
                defining("bvsdiv$n", SMTBitVec(n), SMTBitVec(n), SMTBitVec(n)) { s, t ->
                  // we emulate let by storing the extract operation in a local variable
                  val msb_s = extract(s.sort.bits - 1, s.sort.bits - 1) { s }
                  val msb_t = extract(t.sort.bits - 1, t.sort.bits - 1) { t }

                  // finally we build the nested ite
                  ite { (msb_s eq "#b0".bitvec()) and (msb_t eq "#b0".bitvec()) } then
                      {
                        s bvudiv t
                      } otherwise
                      {
                        ite { (msb_s eq "#b1".bitvec()) and (msb_t eq "#b0".bitvec()) } then
                            {
                              bvneg { bvneg { s } bvudiv t }
                            } otherwise
                            {
                              ite { (msb_s eq "#b0".bitvec()) and (msb_t eq "#b1".bitvec()) } then
                                  {
                                    bvneg { s bvudiv bvneg { t } }
                                  } otherwise
                                  {
                                    bvneg { s } bvudiv bvneg { t }
                                  }
                            }
                      }
                }

            return bvsdiv
          }

          // using the more generic version of bvsdiv defined above we can assert that it behaves
          // like the bvsdiv operator up to an arbitrary limit using a simple loop
          // verify that bvsdivn bahves correctly up to a bitvector length of 8
          for (i in 1..8) {
            // here we create the actual instance of bvsdivn
            // note that calling this function twice would register the same function again leading
            // to
            // multiple definitions and an illegal name shadowing
            val bvsdiv = bvsdivn(i)
            assert {
              // we use an all-quantified expression to verify that our bvsdiv behaves as expected
              forall(SMTBitVec(i), SMTBitVec(i)) { s, t -> (s bvsdiv t) eq bvsdiv(s, t) }
            }
          }

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

  @Test
  fun arrayProgram() {
    val program =
        smt(QF_ASLIA) {
          setInfo {
            smtLibVersion("2.6")
            source("|An examples program to show the usage of the konstraints dsl.|")
            category(BenchmarkCategory.CRAFTED)
            status(SatStatus.UNSAT)
          }

          setOptions {
            printSuccess(true)
            produceModels(true)
          }

          val intArray by declaringConst(SMTArray(SMTInt, SMTInt))
          val foo by declaringConst(SMTInt)

          // we can now store values in the array using any combination of integer primitives and
          // IntSort terms
          // by chaining store-at-then calls we can fill the array with an arbitrary number of
          // values
          val filledIntArray =
              intArray store
                  (foo at 0) then
                  (1 at foo) then
                  (2 at 2) then
                  ({
                    1
                  } at foo) then
                  ({
                    foo
                  } at 3) then
                  (foo at { 4 }) then
                  ({
                    foo
                  } at { 5 })

          // arrays can also use other kotlin primitives like strings
          val stringArray by declaringConst(SMTArray(SMTInt, SMTString))
          val filledStringArray =
              stringArray store ("foo" at 0) then ("bar" at 1) then ({ javaClass.name } at 2)

          // 'assign' an arbitrary value to foo
          assert(foo eq 1)
          assert((filledIntArray select 0) eq foo)
          assert((filledIntArray select foo) eq 5)
          assert(javaClass.name eq (filledStringArray select 2))

          val solver = Z3Solver()

          solver.use { solver ->
            val status = checkSat(solver)
            println(status)
          }
        }

    println(program)
  }

  @Test
  fun floatProgram() {
    val program =
        smt(QF_FP) {
          setInfo {
            smtLibVersion("2.6")
            source("|An examples program to show the usage of the konstraints dsl.|")
            category(BenchmarkCategory.CRAFTED)
            status(SatStatus.UNSAT)
          }

          setOptions {
            printSuccess(true)
            produceModels(true)
          }

          // be careful with floating point sorts and kotlin literals
          // Float will ALWAYS be converted to (_ FloatingPoint 8 24)
          // Double will ALWAYS be converted to (_ FloatingPoint 11 53)
          // there are no compile-time checks so its completely legal to mix
          // floating point types with different sizes however this will lead to runtime errors

          val foo by declaringConst(SMTFloatingPoint(8, 24))

          // the smt shorthand for Float32 can be used
          val bar by declaringConst(SMTFP32)

          // we can also declare a free function of rounding mode sort
          val rm by declaring(SMTRoundingMode)

          // infix operator exist in 2 variants the 'default' version without a name postfix
          // they use the default rounding mode rne (round nearest ties to even)
          val sum = foo fpadd bar

          // if a specific one must be used there is a version for each rounding mode
          val diff = foo fpsub_rtz bar

          // we can also use an expression of rounding mode sort however there are no infix
          // operators that exists for this case
          val prod = FPMul(rm.instance, foo, bar)

          // fused multiplication and addition can be used as a chain of infix functions
          // the intial function takes a rounding mode that is defaulted to rne and either an
          // expression
          // or a lambda that yields an expression
          val fma = fpfma { foo } mul bar add 4.2f

          assert(sum eq 3.14f)
          assert(diff eq 2.71f)

          val solver = Z3Solver()

          solver.use { solver ->
            val status = checkSat(solver)
            println(status)
          }
        }
  }
}

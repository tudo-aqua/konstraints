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

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.assertNotNull
import org.junit.jupiter.api.assertNull
import tools.aqua.konstraints.dsl.toInt
import tools.aqua.konstraints.smt.BVAdd
import tools.aqua.konstraints.smt.BitVecLiteral
import tools.aqua.konstraints.smt.BitVecSort
import tools.aqua.konstraints.smt.Equals
import tools.aqua.konstraints.smt.MutableSMTProgram
import tools.aqua.konstraints.smt.QF_UFBV
import tools.aqua.konstraints.smt.SMTBitVec
import tools.aqua.konstraints.smt.SatStatus
import tools.aqua.konstraints.smt.SortedVar
import tools.aqua.konstraints.smt.cast
import tools.aqua.konstraints.smt.toSymbol
import tools.aqua.konstraints.solvers.InteractiveZ3Solver

class PushTests {
  @Test
  fun test() {
    val program = MutableSMTProgram()
    program.setLogic(QF_UFBV)
    val foo = program.declareConst("foo".toSymbol(), SMTBitVec(8))

    program.assert(Equals(foo(), BitVecLiteral(8, 8)))

    InteractiveZ3Solver().use { solver ->
      solver.solve(program, true, 5000).let { (status, model) ->
        assertEquals(SatStatus.SAT, status)
        assertNotNull(model)
        assertEquals(8, model.getConstantValue(foo).toInt())
      }
    }

    val (status, model) =
        program.push(InteractiveZ3Solver(), true) {
          val bar = declareConst("bar".toSymbol(), SMTBitVec(8))
          assert(Equals(foo(), bar()))
        }

    assertEquals(SatStatus.SAT, status)
    assertNotNull(model)
    assertEquals(8, model.getConstantValue(foo).toInt())
    assertEquals(8, (model.getConstant("bar") as BitVecLiteral).value.toInt())

    // solve program without the pushed assertions again and verify bar is no longer in the model
    InteractiveZ3Solver().use { solver ->
      solver.solve(program, true, 5000).let { (status, model) ->
        assertEquals(SatStatus.SAT, status)
        assertNotNull(model)
        assertEquals(8, model.getConstantValue(foo).toInt())
        assertNull(model.getDefinitionOrNull("bar"))
      }
    }
  }

  @Test
  fun pushWithDefineFun() {
    val program = MutableSMTProgram()
    program.setLogic(QF_UFBV)
    val foo = program.declareConst("foo".toSymbol(), SMTBitVec(8))

    // add base assertions
    program.assert(Equals(foo(), BitVecLiteral(8, 8)))

    // push and solve
    val (status, model) =
      program.push(InteractiveZ3Solver(), true) {
        val bar = declareConst("bar".toSymbol(), SMTBitVec(8))
        val abc = defineFun(
          "func".toSymbol(),
          listOf(
            SortedVar("x".toSymbol(), SMTBitVec(8)),
            SortedVar("y".toSymbol(),SMTBitVec(8))
          ),
          SMTBitVec(8)) { params: List<SortedVar<*>> ->
          BVAdd(params[0].instance.cast(), params[1].instance.cast())
        }

        assert(Equals(foo(), bar()))
        assert(Equals(foo(), abc.constructDynamic(listOf(foo(), bar()), emptyList())))
      }

    assertEquals(SatStatus.UNSAT, status)
    assertNull(model)

    // solve program without the pushed assertions again and verify bar is no longer in the model
    InteractiveZ3Solver().use { solver ->
      solver.solve(program, true, 5000).let { (status, model) ->
        assertEquals(SatStatus.SAT, status)
        assertNotNull(model)
        assertEquals(8, model.getConstantValue(foo).toInt())
        assertNull(model.getDefinitionOrNull("bar"))
      }
    }
  }
}

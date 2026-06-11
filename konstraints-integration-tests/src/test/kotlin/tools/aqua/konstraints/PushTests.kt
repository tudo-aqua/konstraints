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

import java.io.IOException
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assumptions.assumeTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.assertNotNull
import org.junit.jupiter.api.assertNull
import tools.aqua.konstraints.dsl.declaring
import tools.aqua.konstraints.dsl.declaringConst
import tools.aqua.konstraints.dsl.eq
import tools.aqua.konstraints.dsl.plus
import tools.aqua.konstraints.dsl.smt
import tools.aqua.konstraints.dsl.toInt
import tools.aqua.konstraints.smt.ALL
import tools.aqua.konstraints.smt.And
import tools.aqua.konstraints.smt.BVAdd
import tools.aqua.konstraints.smt.BVSLe
import tools.aqua.konstraints.smt.BitVecLiteral
import tools.aqua.konstraints.smt.Equals
import tools.aqua.konstraints.smt.MutableSMTProgram
import tools.aqua.konstraints.smt.Not
import tools.aqua.konstraints.smt.Or
import tools.aqua.konstraints.smt.QF_UFBV
import tools.aqua.konstraints.smt.QF_UFLIA
import tools.aqua.konstraints.smt.SMTBitVec
import tools.aqua.konstraints.smt.SMTBool
import tools.aqua.konstraints.smt.SMTInt
import tools.aqua.konstraints.smt.SMTString
import tools.aqua.konstraints.smt.SatStatus
import tools.aqua.konstraints.smt.Sort
import tools.aqua.konstraints.smt.SortedVar
import tools.aqua.konstraints.smt.StringLiteral
import tools.aqua.konstraints.smt.StringSort
import tools.aqua.konstraints.smt.UserDeclaredSort
import tools.aqua.konstraints.smt.cast
import tools.aqua.konstraints.smt.toSymbol
import tools.aqua.konstraints.solvers.InteractiveZ3Solver
import tools.aqua.konstraints.solvers.z3.Z3Solver

class PushTests {
  private fun getSolver() =
      try {
        InteractiveZ3Solver()
      } catch (e: IOException) {
        assumeTrue(false)
      }
          as InteractiveZ3Solver

  @Test
  fun test() {
    val program = MutableSMTProgram()
    program.setLogic(QF_UFBV)
    val foo = program.declareConst("foo".toSymbol(), SMTBitVec(8))

    program.assert(Equals(foo(), BitVecLiteral(8, 8)))

    getSolver().use { solver ->
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
    getSolver().use { solver ->
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
        program.push(getSolver(), true) {
          val bar = declareConst("bar".toSymbol(), SMTBitVec(8))
          val abc =
              defineFun("func", listOf(SMTBitVec(8), SMTBitVec(8)), SMTBitVec(8)) {
                  params: List<SortedVar<*>> ->
                BVAdd(params[0].instance.cast(), params[1].instance.cast())
              }

          assert(Equals(foo(), bar()))
          assert(Equals(foo(), abc.constructDynamic(listOf(foo(), bar()), emptyList())))
        }

    assertEquals(SatStatus.UNSAT, status)
    assertNull(model)

    // solve program without the pushed assertions again and verify bar is no longer in the model
    getSolver().use { solver ->
      solver.solve(program, true, 5000).let { (status, model) ->
        assertEquals(SatStatus.SAT, status)
        assertNotNull(model)
        assertEquals(8, model.getConstantValue(foo).toInt())
        assertNull(model.getDefinitionOrNull("bar"))
      }
    }
  }
  @Test
  fun simpleGDartDSEExample() {
    val program = MutableSMTProgram()
    program.setLogic(ALL)

    // (declare-sort Object 0)
    program.declareSort("Object".toSymbol(), 0)
    val objectSort = UserDeclaredSort("Object".toSymbol(), emptyList())

    // (declare-fun null () Object)
    val nullConst = program.declareConst("null".toSymbol(), objectSort)

    // (define-fun obj.extends ((sub String) (sup String)) Bool ...)
    val objExtends =
        program.defineFun("obj.extends", listOf(SMTString, SMTString), SMTBool) { params ->
          val sub = params[0].instance.cast<StringSort>()
          val sup = params[1].instance.cast<StringSort>()
          Or(
              And(Equals(sub, StringLiteral("null")), Equals(sup, StringLiteral("LA;"))),
              And(Equals(sub, StringLiteral("null")), Equals(sup, StringLiteral("LB;"))),
              And(Equals(sub, StringLiteral("null")), Equals(sup, StringLiteral("LC;"))),
              And(Equals(sub, StringLiteral("null")), Equals(sup, StringLiteral("Ltest/D;"))),
              And(Equals(sub, StringLiteral("LA;")), Equals(sup, StringLiteral("LA;"))),
              And(Equals(sub, StringLiteral("LB;")), Equals(sup, StringLiteral("LB;"))),
              And(Equals(sub, StringLiteral("LB;")), Equals(sup, StringLiteral("LA;"))),
              And(Equals(sub, StringLiteral("LC;")), Equals(sup, StringLiteral("LC;"))),
              And(Equals(sub, StringLiteral("LC;")), Equals(sup, StringLiteral("LB;"))),
              And(Equals(sub, StringLiteral("LC;")), Equals(sup, StringLiteral("LA;"))),
              And(Equals(sub, StringLiteral("Ltest/D;")), Equals(sup, StringLiteral("Ltest/D;"))),
          )
        }

    // (define-fun obj.method.of ((cls String) (method String) (sig String) (implIn String)) Bool)
    val objMethodOf =
        program.defineFun(
            "obj.method.of",
            listOf(SMTString, SMTString, SMTString, SMTString),
            SMTBool,
        ) { params ->
          val cls = params[0].instance.cast<StringSort>()
          val method = params[1].instance.cast<StringSort>()
          val sig = params[2].instance.cast<StringSort>()
          val implIn = params[3].instance.cast<StringSort>()
          Or(
              And(
                  Equals(cls, StringLiteral("LA;")),
                  Equals(method, StringLiteral("foo")),
                  Equals(sig, StringLiteral("()V")),
                  Equals(implIn, StringLiteral("LA;")),
              ),
              And(
                  Equals(cls, StringLiteral("LB;")),
                  Equals(method, StringLiteral("foo")),
                  Equals(sig, StringLiteral("()V")),
                  Equals(implIn, StringLiteral("LA;")),
              ),
              And(
                  Equals(cls, StringLiteral("LC;")),
                  Equals(method, StringLiteral("foo")),
                  Equals(sig, StringLiteral("()V")),
                  Equals(implIn, StringLiteral("LA;")),
              ),
          )
        }

    // per-object vars
    val obj0 = program.declareConst("__object_0".toSymbol(), objectSort)
    val obj0cls = program.declareConst("__object_0.cls".toSymbol(), SMTString)
    val obj0x = program.declareConst("__object_0.x".toSymbol(), SMTBitVec(32))
    val obj0a = program.declareConst("__object_0.a".toSymbol(), objectSort)
    val obj0aCls = program.declareConst("__object_0.a.cls".toSymbol(), SMTString)
    val int0 = program.declareConst("__int_0".toSymbol(), SMTBitVec(32))
    val obj0init = program.declareConst("__object_0.init".toSymbol(), SMTString)
    val obj0err = program.declareConst("__object_0.err".toSymbol(), SMTString)

    // constructor-analysis assertion
    program.assert(
        Or(
            // case: null object
            And(
                Equals(obj0init(), StringLiteral("<>null|NULL")),
                Equals(obj0(), nullConst()),
                Equals(obj0err(), StringLiteral("")),
                Equals(obj0cls(), StringLiteral("null")),
            ),
            // case: new LA;(int)
            And(
                Equals(obj0init(), StringLiteral("<>LA;|(I)V|{__int_0}")),
                Not(Equals(obj0(), nullConst())),
                Equals(obj0err(), StringLiteral("")),
                Equals(obj0cls(), StringLiteral("LA;")),
                Equals(obj0x(), int0()),
            ),
            // case: new LB;()
            And(
                Equals(obj0init(), StringLiteral("<>LB;|()V|")),
                Not(Equals(obj0(), nullConst())),
                Equals(obj0err(), StringLiteral("")),
                Equals(obj0cls(), StringLiteral("LB;")),
                Equals(obj0x(), BitVecLiteral(0x64, 32)),
            ),
            // case: new LB;(int)
            And(
                Equals(obj0init(), StringLiteral("<>LB;|(I)V|{__int_0}")),
                Not(Equals(obj0(), nullConst())),
                Equals(obj0err(), StringLiteral("")),
                Equals(obj0cls(), StringLiteral("LB;")),
                Equals(obj0x(), int0()),
            ),
            // case: new LC;(int) — with assertion check (int != 1)
            And(
                Equals(obj0init(), StringLiteral("<>LC;|(I)V|{__int_0}")),
                Not(Equals(obj0(), nullConst())),
                Equals(obj0err(), StringLiteral("")),
                Not(Equals(BitVecLiteral(1, 32), int0())),
                Equals(obj0cls(), StringLiteral("LC;")),
                Equals(obj0x(), int0()),
                Equals(obj0a(), nullConst()),
                Equals(obj0aCls(), StringLiteral("null")),
            ),
            // case: new LC;(int) throws AssertionError (int == 1)
            And(
                Equals(
                    obj0init(),
                    StringLiteral("<java/lang/AssertionError>LC;|(I)V|{__int_0}"),
                ),
                Equals(obj0err(), StringLiteral("java/lang/AssertionError")),
                Equals(BitVecLiteral(1, 32), int0()),
            ),
            // case: new LC;(null)
            And(
                Equals(obj0init(), StringLiteral("<>LC;|(LA;)V|{null|NULL}")),
                Not(Equals(obj0(), nullConst())),
                Equals(obj0err(), StringLiteral("")),
                Equals(obj0cls(), StringLiteral("LC;")),
                Equals(obj0x(), BitVecLiteral(0, 32)),
                Equals(obj0a(), nullConst()),
                Equals(obj0aCls(), StringLiteral("null")),
            ),
        ))

    // push 1: negated — error must be non-empty (SAT: case AssertionError)
    program
        .push(getSolver(), false) { assert(Not(Equals(obj0err(), StringLiteral("")))) }
        .let { (status, _) -> assertEquals(SatStatus.SAT, status) }

    // push 2: err="" AND obj not-null AND extends LB (SAT)
    program
        .push(getSolver(), false) {
          assert(Equals(obj0err(), StringLiteral("")))
          assert(
              Not(
                  Not(
                      And(
                          Not(Equals(obj0(), nullConst())),
                          objExtends.constructDynamic(
                              listOf(obj0cls(), StringLiteral("LB;")), emptyList()),
                      ))))
        }
        .let { (status, _) -> assertEquals(SatStatus.SAT, status) }

    // push 3: err="" AND (not-null extends LB) AND NOT(not-null extends LA)
    // UNSAT: every class extending LB also extends LA in this hierarchy
    program
        .push(getSolver(), false) {
          assert(Equals(obj0err(), StringLiteral("")))
          assert(
              And(
                  Not(Equals(obj0(), nullConst())),
                  objExtends.constructDynamic(
                      listOf(obj0cls(), StringLiteral("LB;")), emptyList()),
              ))
          assert(
              Not(
                  And(
                      Not(Equals(obj0(), nullConst())),
                      objExtends.constructDynamic(
                          listOf(obj0cls(), StringLiteral("LA;")), emptyList()),
                  )))
        }
        .let { (status, _) -> assertEquals(SatStatus.UNSAT, status) }

    // push 4: err="" AND extends LB AND extends LA AND NOT extends LC (SAT: LB)
    program
        .push(getSolver(), false) {
          assert(Equals(obj0err(), StringLiteral("")))
          assert(
              And(
                  Not(Equals(obj0(), nullConst())),
                  objExtends.constructDynamic(
                      listOf(obj0cls(), StringLiteral("LB;")), emptyList()),
              ))
          assert(
              And(
                  Not(Equals(obj0(), nullConst())),
                  objExtends.constructDynamic(
                      listOf(obj0cls(), StringLiteral("LA;")), emptyList()),
              ))
          assert(
              Not(
                  objExtends.constructDynamic(
                      listOf(obj0cls(), StringLiteral("LC;")), emptyList())))
        }
        .let { (status, _) -> assertEquals(SatStatus.SAT, status) }

    // push 5: same + assert obj=null (contradicts not-null) (UNSAT)
    program
        .push(getSolver(), false) {
          assert(Equals(obj0err(), StringLiteral("")))
          assert(
              And(
                  Not(Equals(obj0(), nullConst())),
                  objExtends.constructDynamic(
                      listOf(obj0cls(), StringLiteral("LB;")), emptyList()),
              ))
          assert(
              And(
                  Not(Equals(obj0(), nullConst())),
                  objExtends.constructDynamic(
                      listOf(obj0cls(), StringLiteral("LA;")), emptyList()),
              ))
          assert(
              objExtends.constructDynamic(listOf(obj0cls(), StringLiteral("LC;")), emptyList()))
          assert(Not(Not(Equals(obj0(), nullConst()))))
        }
        .let { (status, _) -> assertEquals(SatStatus.UNSAT, status) }

    // push 6: same + not-null + assert obj=null (UNSAT)
    program
        .push(getSolver(), false) {
          assert(Equals(obj0err(), StringLiteral("")))
          assert(
              And(
                  Not(Equals(obj0(), nullConst())),
                  objExtends.constructDynamic(
                      listOf(obj0cls(), StringLiteral("LB;")), emptyList()),
              ))
          assert(
              And(
                  Not(Equals(obj0(), nullConst())),
                  objExtends.constructDynamic(
                      listOf(obj0cls(), StringLiteral("LA;")), emptyList()),
              ))
          assert(
              objExtends.constructDynamic(listOf(obj0cls(), StringLiteral("LC;")), emptyList()))
          assert(Not(Equals(obj0(), nullConst())))
          assert(Not(Not(Equals(obj0(), nullConst()))))
        }
        .let { (status, _) -> assertEquals(SatStatus.UNSAT, status) }

    // push 7: extends LC, not-null, NOT method.of (UNSAT: only LC satisfies, but method.of LC is true)
    program
        .push(getSolver(), false) {
          assert(Equals(obj0err(), StringLiteral("")))
          assert(
              And(
                  Not(Equals(obj0(), nullConst())),
                  objExtends.constructDynamic(
                      listOf(obj0cls(), StringLiteral("LB;")), emptyList()),
              ))
          assert(
              And(
                  Not(Equals(obj0(), nullConst())),
                  objExtends.constructDynamic(
                      listOf(obj0cls(), StringLiteral("LA;")), emptyList()),
              ))
          assert(
              objExtends.constructDynamic(listOf(obj0cls(), StringLiteral("LC;")), emptyList()))
          assert(Not(Equals(obj0(), nullConst())))
          assert(Not(Equals(obj0(), nullConst())))
          assert(
              Not(
                  objMethodOf.constructDynamic(
                      listOf(
                          obj0cls(),
                          StringLiteral("foo"),
                          StringLiteral("()V"),
                          StringLiteral("LA;"),
                      ),
                      emptyList(),
                  )))
        }
        .let { (status, _) -> assertEquals(SatStatus.UNSAT, status) }

    // push 8: extends LC, not-null, method.of, x > 0 (SAT)
    program
        .push(getSolver(), false) {
          assert(Equals(obj0err(), StringLiteral("")))
          assert(
              And(
                  Not(Equals(obj0(), nullConst())),
                  objExtends.constructDynamic(
                      listOf(obj0cls(), StringLiteral("LB;")), emptyList()),
              ))
          assert(
              And(
                  Not(Equals(obj0(), nullConst())),
                  objExtends.constructDynamic(
                      listOf(obj0cls(), StringLiteral("LA;")), emptyList()),
              ))
          assert(
              objExtends.constructDynamic(listOf(obj0cls(), StringLiteral("LC;")), emptyList()))
          assert(Not(Equals(obj0(), nullConst())))
          assert(Not(Equals(obj0(), nullConst())))
          assert(
              objMethodOf.constructDynamic(
                  listOf(
                      obj0cls(),
                      StringLiteral("foo"),
                      StringLiteral("()V"),
                      StringLiteral("LA;"),
                  ),
                  emptyList(),
              ))
          assert(Not(BVSLe(obj0x(), BitVecLiteral(0, 32))))
        }
        .let { (status, _) -> assertEquals(SatStatus.SAT, status) }
  }
}

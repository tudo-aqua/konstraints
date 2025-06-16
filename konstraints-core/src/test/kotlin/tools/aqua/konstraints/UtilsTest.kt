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

package tools.aqua.konstraints

import java.util.stream.Stream
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.assertThrows
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.Arguments.arguments
import org.junit.jupiter.params.provider.MethodSource
import tools.aqua.konstraints.parser.ArrayExTheory
import tools.aqua.konstraints.parser.BitVectorExpressionTheory
import tools.aqua.konstraints.parser.CoreTheory
import tools.aqua.konstraints.parser.FloatingPointTheory
import tools.aqua.konstraints.parser.IntsTheory
import tools.aqua.konstraints.parser.RealsIntsTheory
import tools.aqua.konstraints.parser.RealsTheory
import tools.aqua.konstraints.parser.StringsTheory
import tools.aqua.konstraints.smt.ABV
import tools.aqua.konstraints.smt.ABVFP
import tools.aqua.konstraints.smt.ABVFPLRA
import tools.aqua.konstraints.smt.ALIA
import tools.aqua.konstraints.smt.ANIA
import tools.aqua.konstraints.smt.AUFBV
import tools.aqua.konstraints.smt.AUFBVDTLIA
import tools.aqua.konstraints.smt.AUFBVDTNIA
import tools.aqua.konstraints.smt.AUFBVDTNIRA
import tools.aqua.konstraints.smt.AUFBVFP
import tools.aqua.konstraints.smt.AUFDTLIA
import tools.aqua.konstraints.smt.AUFDTLIRA
import tools.aqua.konstraints.smt.AUFDTNIRA
import tools.aqua.konstraints.smt.AUFFPDTNIRA
import tools.aqua.konstraints.smt.AUFLIA
import tools.aqua.konstraints.smt.AUFLIRA
import tools.aqua.konstraints.smt.AUFNIA
import tools.aqua.konstraints.smt.AUFNIRA
import tools.aqua.konstraints.smt.BV
import tools.aqua.konstraints.smt.BVFP
import tools.aqua.konstraints.smt.BVFPLRA
import tools.aqua.konstraints.smt.FP
import tools.aqua.konstraints.smt.FPLRA
import tools.aqua.konstraints.smt.LIA
import tools.aqua.konstraints.smt.LRA
import tools.aqua.konstraints.smt.Logic
import tools.aqua.konstraints.smt.NIA
import tools.aqua.konstraints.smt.NRA
import tools.aqua.konstraints.smt.QF_ABV
import tools.aqua.konstraints.smt.QF_ABVFP
import tools.aqua.konstraints.smt.QF_ABVFPLRA
import tools.aqua.konstraints.smt.QF_ALIA
import tools.aqua.konstraints.smt.QF_ANIA
import tools.aqua.konstraints.smt.QF_AUFBV
import tools.aqua.konstraints.smt.QF_AUFBVFP
import tools.aqua.konstraints.smt.QF_AUFLIA
import tools.aqua.konstraints.smt.QF_AUFNIA
import tools.aqua.konstraints.smt.QF_AX
import tools.aqua.konstraints.smt.QF_BV
import tools.aqua.konstraints.smt.QF_BVFP
import tools.aqua.konstraints.smt.QF_BVFPLRA
import tools.aqua.konstraints.smt.QF_DT
import tools.aqua.konstraints.smt.QF_FP
import tools.aqua.konstraints.smt.QF_FPLRA
import tools.aqua.konstraints.smt.QF_IDL
import tools.aqua.konstraints.smt.QF_LIA
import tools.aqua.konstraints.smt.QF_LIRA
import tools.aqua.konstraints.smt.QF_LRA
import tools.aqua.konstraints.smt.QF_NIA
import tools.aqua.konstraints.smt.QF_NIRA
import tools.aqua.konstraints.smt.QF_NRA
import tools.aqua.konstraints.smt.QF_RDL
import tools.aqua.konstraints.smt.QF_S
import tools.aqua.konstraints.smt.QF_SLIA
import tools.aqua.konstraints.smt.QF_SNIA
import tools.aqua.konstraints.smt.QF_UF
import tools.aqua.konstraints.smt.QF_UFBV
import tools.aqua.konstraints.smt.QF_UFBVDT
import tools.aqua.konstraints.smt.QF_UFDT
import tools.aqua.konstraints.smt.QF_UFDTLIA
import tools.aqua.konstraints.smt.QF_UFDTLIRA
import tools.aqua.konstraints.smt.QF_UFDTNIA
import tools.aqua.konstraints.smt.QF_UFFP
import tools.aqua.konstraints.smt.QF_UFFPDTNIRA
import tools.aqua.konstraints.smt.QF_UFIDL
import tools.aqua.konstraints.smt.QF_UFLIA
import tools.aqua.konstraints.smt.QF_UFLRA
import tools.aqua.konstraints.smt.QF_UFNIA
import tools.aqua.konstraints.smt.QF_UFNRA
import tools.aqua.konstraints.smt.Theories
import tools.aqua.konstraints.smt.UF
import tools.aqua.konstraints.smt.UFBV
import tools.aqua.konstraints.smt.UFBVDT
import tools.aqua.konstraints.smt.UFBVFP
import tools.aqua.konstraints.smt.UFBVLIA
import tools.aqua.konstraints.smt.UFDT
import tools.aqua.konstraints.smt.UFDTLIA
import tools.aqua.konstraints.smt.UFDTLIRA
import tools.aqua.konstraints.smt.UFDTNIA
import tools.aqua.konstraints.smt.UFDTNIRA
import tools.aqua.konstraints.smt.UFFPDTNIRA
import tools.aqua.konstraints.smt.UFIDL
import tools.aqua.konstraints.smt.UFLIA
import tools.aqua.konstraints.smt.UFLRA
import tools.aqua.konstraints.smt.UFNIA
import tools.aqua.konstraints.smt.UFNIRA
import tools.aqua.konstraints.util.zipWithSameLength

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class UtilsTest {
  @ParameterizedTest
  @MethodSource("getUnequalLengthLists")
  fun `test that zipWithSameLength throws for list with different size`(
      lhs: List<*>,
      rhs: List<*>
  ) {
    assertThrows<IllegalArgumentException> { lhs zipWithSameLength rhs }
  }

  private fun getUnequalLengthLists(): Stream<Arguments> {
    return Stream.of(
        arguments(listOf(1, 2, 3), listOf(1, 2)),
        arguments(listOf(1, 2), emptyList<Any>()),
        arguments(emptyList<Any>(), listOf(1, 2)),
    )
  }

  @ParameterizedTest
  @MethodSource("getEqualLengthList")
  fun `test that zipWithSameLength works like zip`(lhs: List<*>, rhs: List<*>) {
    assertEquals(lhs zip rhs, lhs zipWithSameLength rhs)
  }

  private fun getEqualLengthList(): Stream<Arguments> {
    return Stream.of(
        arguments(listOf(1, 2, 3), listOf(4, 5, 6)),
        arguments(listOf(1), listOf(2)),
        arguments(emptyList<Any>(), emptyList<Any>()),
    )
  }

  fun generate(logic: Logic) =
      "\"${logic.javaClass.name.removePrefix("tools.aqua.konstraints.smt.")}\":{ ${
            logic.theories.joinToString(", ") { theory ->
                when (theory) {
                    Theories.CORE -> CoreTheory
                    Theories.ARRAYS_EX -> ArrayExTheory
                    Theories.FIXED_SIZE_BIT_VECTORS -> BitVectorExpressionTheory
                    Theories.FLOATING_POINT -> FloatingPointTheory
                    Theories.INTS -> IntsTheory
                    Theories.REALS -> RealsTheory
                    Theories.REALS_INTS -> RealsIntsTheory
                    Theories.STRINGS -> StringsTheory
                }.functions.keys.joinToString(", ") { "\"${it}\"" }
            }
        } }"

  @Test
  fun test() {
    print(
        "logics = {\n${listOf(
            ABV,
            ABVFP,
            ABVFPLRA,
            ALIA,
            ANIA,
            AUFBV,
            AUFBVDTLIA,
            AUFBVDTNIA,
            AUFBVDTNIRA,
            AUFBVFP,
            AUFDTLIA,
            AUFDTLIRA,
            AUFDTNIRA,
            AUFFPDTNIRA,
            AUFLIA,
            AUFLIRA,
            AUFNIA,
            AUFNIRA,
            BV,
            BVFP,
            BVFPLRA,
            FP,
            FPLRA,
            LIA,
            LRA,
            NIA,
            NRA,
            QF_ABV,
            QF_ABVFP,
            QF_ABVFPLRA,
            QF_ALIA,
            QF_ANIA,
            QF_AUFBV,
            QF_AUFBVFP,
            QF_AUFLIA,
            QF_AUFNIA,
            QF_AX,
            QF_BV,
            QF_BVFP,
            QF_BVFPLRA,
            QF_DT,
            QF_FP,
            QF_FPLRA,
            QF_IDL,
            QF_LIA,
            QF_LIRA,
            QF_LRA,
            QF_NIA,
            QF_NIRA,
            QF_NRA,
            QF_RDL,
            QF_S,
            QF_SLIA,
            QF_SNIA,
            QF_UF,
            QF_UFBV,
            QF_UFBVDT,
            QF_UFDT,
            QF_UFDTLIA,
            QF_UFDTLIRA,
            QF_UFDTNIA,
            QF_UFFP,
            QF_UFFPDTNIRA,
            QF_UFIDL,
            QF_UFLIA,
            QF_UFLRA,
            QF_UFNIA,
            QF_UFNRA,
            UF,
            UFBV,
            UFBVDT,
            UFBVFP,
            UFBVLIA,
            UFDT,
            UFDTLIA,
            UFDTLIRA,
            UFDTNIA,
            UFDTNIRA,
            UFFPDTNIRA,
            UFIDL,
            UFLIA,
            UFLRA,
            UFNIA,
            UFNIRA,
        ).joinToString(",\n") {generate(it)}}\n}")
  }
}

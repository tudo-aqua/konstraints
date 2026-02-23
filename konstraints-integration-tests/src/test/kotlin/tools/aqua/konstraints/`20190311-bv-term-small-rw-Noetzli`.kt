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

import tools.aqua.konstraints.dsl.*
import tools.aqua.konstraints.smt.QF_BV
import tools.aqua.konstraints.smt.SMTBitVec
import tools.aqua.konstraints.smt.bitvec

class `20190311-bv-term-small-rw-Noetzli` {
  fun `bv-term-small-rw_1`() {
    smt(QF_BV) {
      val s by declaringConst(SMTBitVec(32))

      assert { not(s bvand s eq s) }
      checkSat()
    }
  }

  fun `bv-term-small-rw_2`() {
    smt(QF_BV) {
      val s by declaringConst(SMTBitVec(32))

      assert {
        not(s bvlshr s eq "#b0".bitvec(32))
        // not(s bvlshr s eq 0)
      }
      checkSat()
    }
  }

  fun `bv-term-small-rw_64`() {
    smt(QF_BV) {
      val s by declaringConst(SMTBitVec(32))
      val t by declaringConst(SMTBitVec(32))

      assert { not((s bvor (t bvor t)) eq (s bvor t)) }
      checkSat()
    }
  }

  fun `bv-term-small-rw_64-named-expressions`() {
    smt(QF_BV) {
      val s by declaringConst(SMTBitVec(32))
      val t by declaringConst(SMTBitVec(32))

      assert {
        val expr1 = s bvor (t bvor t)
        val expr2 = s bvor t
        not(expr1 eq expr2)
      }
      checkSat()
    }
  }
}

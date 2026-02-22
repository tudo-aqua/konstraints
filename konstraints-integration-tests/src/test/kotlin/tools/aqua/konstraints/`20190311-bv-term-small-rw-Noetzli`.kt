package tools.aqua.konstraints

import tools.aqua.konstraints.dsl.*
import tools.aqua.konstraints.smt.BitVec
import tools.aqua.konstraints.smt.QF_BV
import tools.aqua.konstraints.smt.bitvec

class `20190311-bv-term-small-rw-Noetzli` {
    fun `bv-term-small-rw_1`() {
        smt(QF_BV) {
            val s by declaringConst(BitVec(32))

            assert {
                not(s bvand s eq s)
            }
            checkSat()
        }
    }

    fun `bv-term-small-rw_2`() {
        smt(QF_BV) {
            val s by declaringConst(BitVec(32))

            assert {
                not(s bvlshr s eq "#b0".bitvec(32))
                // not(s bvlshr s eq 0)
            }
            checkSat()
        }
    }

    fun `bv-term-small-rw_64`() {
        smt(QF_BV) {
            val s by declaringConst(BitVec(32))
            val t by declaringConst(BitVec(32))

            assert {
                not((s bvor (t bvor t)) eq (s bvor t))
            }
            checkSat()
        }
    }

    fun `bv-term-small-rw_64-named-expressions`() {
        smt(QF_BV) {
            val s by declaringConst(BitVec(32))
            val t by declaringConst(BitVec(32))

            assert {
                val expr1 = s bvor (t bvor t)
                val expr2 = s bvor t
                not(expr1 eq expr2)
            }
            checkSat()
        }
    }
}
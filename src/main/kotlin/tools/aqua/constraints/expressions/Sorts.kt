package tools.aqua.constraints.expressions

// Basic Sort

interface Sort

// Unit

object NoSort : Sort

// Special Sorts

object BoolSort : Sort
object IntSort  : Sort
object RealSort : Sort

// Floating Point

open class FPSort(val eBits: Int, val mBits: Int) : Sort {
    override fun toString(): String = "(_ FloatingPoint $eBits $mBits)"
}

object Float16  : FPSort( 5,  11) { override fun toString(): String =  "Float16" }
object Float32  : FPSort( 8,  24) { override fun toString(): String =  "Float32" }
object Float64  : FPSort(11,  53) { override fun toString(): String =  "Float64" }
object Float128 : FPSort(15, 113) { override fun toString(): String = "Float128" }

// Bitvector

open class BVSort(val bits: Int) : Sort {
    override fun toString(): String = "(_ BitVec $bits)"
}

object BitVec8  : BVSort( 8) // not in SMTLib
object BitVec16 : BVSort(16) // not in SMTLib
object BitVec32 : BVSort(32) // not in SMTLib
object BitVec64 : BVSort(64) // not in SMTLib

// Custom Sorts

data class NamedSort(val name:String)
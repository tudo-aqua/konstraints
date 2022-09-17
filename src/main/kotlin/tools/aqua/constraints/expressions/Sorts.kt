package tools.aqua.constraints.expressions

/**
 * Basic marker interface for sorts
 */
interface Sort

/**
 * Shared marker for ints and reals
 */
interface NumericSort : Sort

/**
 * SMTLib Bool
 */
object BoolSort : Sort {
    override fun toString() = "Bool"
}

/**
 * SMTLib Int
 */
object IntSort  : NumericSort {
    override fun toString() = "Int"
}

/**
 * SMTLib Real
 */
object RealSort : NumericSort {
    override fun toString() = "Real"
}

/**
 * SMTLib floating point sort
 */
open class FPSort(val eBits: Int, val mBits: Int) : Sort {
    override fun toString(): String = "(_ FloatingPoint $eBits $mBits)"
}

/**
 * SMTLib Float16
 */
object Float16  : FPSort( 5,  11)

/**
 * SMTLib Float32
 */
object Float32  : FPSort( 8,  24)

/**
 * SMTLib Float64
 */
object Float64  : FPSort(11,  53)

/**
 * SMTLib Float128
 */
object Float128 : FPSort(15, 113)

/**
 * SMTLib BitVec
 */
open class BVSort(val bits: Int) : Sort {
    override fun toString(): String = "(_ BitVec $bits)"
}

/**
 * 8 bit. Not in SMTLib
 */
object BitVec8   : BVSort( 8)

/**
 * 16 bit. Not in SMTLib
 */
object BitVec16  : BVSort( 16)

/**
 * 32 bit. Not in SMTLib
 */
object BitVec32  : BVSort( 32)

/**
 * 64 bit. Not in SMTLib
 */
object BitVec64  : BVSort( 64)

/**
 * 128 bit. Not in SMTLib
 */
object BitVec128 : BVSort( 128)


/**
 * SMTLib String
 */
object StringSort : Sort {
    override fun toString() = "String"
}

/**
 * Function sort
 */
data class FunctionSort(val argTypes:List<Sort>, val returnType:Sort) : Sort {
    override fun toString() = "(${argTypes.joinToString(" ")}) $returnType"
}

/**
 * SMTLib named sort
 */
data class NamedSort(val name:String) : Sort {
        override fun toString() = name
}
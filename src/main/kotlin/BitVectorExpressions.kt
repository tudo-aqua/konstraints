/*abstract class BitVectorSort(arity: Int) : ParameterizedSort("BitVec", arity)

class BVAdd(summands: List<Expression<BitVectorSort>>) : Expression<BitVectorSort> {
    constructor(vararg summands: Expression<BitVectorSort>) : this(summands.toList())

    init {
        require(summands.isNotEmpty()) { "summand required" }
        val firstSort = summands.first().sort
        require(summands.all { it.sort == firstSort }) { "sort error" }
    }
}

sealed interface Identifier

data class SimpleIdentifier(val id: String) : Identifier

// and the other one

val String.id: SimpleIdentifier get() = SimpleIdentifier(this)
*/

//concat bvs
class BVConcat

//extract bits from bv
class BVExtract

//bitwise not
class BVNot<T : BVSort>(val inner : Expression<T>) : Expression<T> {

}

//negate bv
class BVNeg<T : BVSort>(val inner : Expression<T>) : Expression<T> {

}

//bitwise and
class BVAnd<T : BVSort>(conjuncts : List<Expression<T>>) : Expression<T> {
    constructor(vararg summands : Expression<T>) : this(summands.toList())
}

//bitwise or
class BVOr<T : BVSort>(disjuncts : List<Expression<T>>) : Expression<T> {
    constructor(vararg summands : Expression<T>) : this(summands.toList())
}

//addition
class BVAdd<T : BVSort>(summands : List<Expression<T>>) : Expression<T> {
    constructor(vararg summands : Expression<T>) : this(summands.toList())
}

//multiplication
class BVMul<T : BVSort>(factors : List<Expression<T>>) : Expression<T> {
    constructor(vararg summands : Expression<T>) : this(summands.toList())
}

//unsigned division
class BVUDiv<T : BVSort>(numeratos : Expression<T>, denominator : Expression<T>) {

}

//unsigned remainder
class BVURem<T : BVSort>(numeratos : Expression<T>, denominator : Expression<T>) {

}

//shift left
class BVShl<T : BVSort>(numeratos : Expression<T>, denominator : Expression<T>) {

}

//logical shift right
class BVLShr<T : BVSort>(numeratos : Expression<T>, denominator : Expression<T>) {

}

//unsigned less than
class BVUlt<T : BVSort>(val lhs : Expression<T>, val rhs : Expression<T>) : Expression<BoolSort> {

}
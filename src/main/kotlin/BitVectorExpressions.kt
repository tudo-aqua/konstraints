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
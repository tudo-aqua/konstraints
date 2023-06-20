/**
 * Data class representing an SMTSymbol
 * constructor checks if [symbol] is a valid simple symbol or quoted symbol
 * quotes symbol if needed, allows for explicit and implicit creation of quoted symbols
 * @throws [IllegalArgumentException] if [symbol] is not valid
 */
data class SMTSymbol(val symbol : String) {

    /**
     * Companion object to store [Regex]
     * so they don't need to be created everytime a Symbol is created
     */
    companion object Regex {
        val simple = Regex("""[a-zA-Z~!@$%^&*_\-+=<>.?/][0-9a-zA-Z~!@$%^&*_\-+=<>.?/]*""")
        val quoted = Regex("""\|(.|\n)*\|""")
    }

    /**
     * Check if [symbol] is a valid SMT Symbol by matching it
     * first with a simple symbol
     * second with a quoted symbol
     * third with a list of reserved words (TODO)
     * @throws IllegalArgumentException if [symbol] is not valid
     */
    init {
        require(symbol.matches(simple) || symbol.matches(quoted) || "|$symbol|".matches(quoted))

        //TODO("Check for reserved words in simple symbol")
    }

    /**
     * Serialization of SMTSymbol, quotes symbol if needed
     * @return a valid quoted or simple SMT Symbol
     */
    override fun toString() = if(symbol.matches(simple)) symbol else "|$symbol|"
}

/**
 * Identifiers of the form <identifier> ::= <symbol> | ( _ <symbol> <index>+ )
+ )
 */
class SMTIdentifier(symbol : SMTSymbol, varargs : List<String>) {
    constructor(symbol : SMTSymbol) : this(symbol, listOf())

    private val symbol : String = if(varargs.isEmpty()) symbol.toString()
    else "(_ $symbol ${varargs.joinToString(separator = " ")})"

    override fun toString() = symbol
}

/**
 * Basic marker interface for sorts
 */
open class Sort(val identifier : SMTIdentifier, val varargs : List<Sort>) {
    constructor(identifier : SMTIdentifier) : this(identifier, listOf())

    override fun toString() = if (varargs.isEmpty()) "$identifier" else "($identifier ${varargs.joinToString(separator = " ")})"
}

/**
 * SMTLib Bool
 */
object BoolSort : Sort(SMTIdentifier(SMTSymbol("Bool"))) {}

/**
 * SMTLib fixed size bitvector
 */
open class BVSort(val bits : Int) : Sort(SMTIdentifier(SMTSymbol("BitVec"), listOf("$bits"))) {}

object BVSort32 : BVSort(32)

/**
 * SMTLib String
 */
object StringSort : Sort(SMTIdentifier(SMTSymbol("String")))

object IntSort : Sort(SMTIdentifier(SMTSymbol("Int")))

object RealSort : Sort(SMTIdentifier(SMTSymbol("Real")))

object ExampleListSort : Sort(SMTIdentifier(SMTSymbol("List")),
    listOf(Sort(SMTIdentifier(SMTSymbol("Array")), listOf(IntSort, RealSort))))

object ExampleFixedSizeList : Sort(SMTIdentifier(SMTSymbol("FixedSizeList"), listOf("4")), listOf(RealSort))

object ExampleSet : Sort(SMTIdentifier(SMTSymbol("Set")), listOf(BVSort32))

/**
 * Function sort
 */

/*
data class FunctionSort(val argTypes:List<Sort>, val returnType:Sort) : Sort {
    override fun toString() = "(${argTypes.joinToString(" ")}) $returnType"
}
*/

/**
open class ParameterizedSort(val name: String, val arity: Int) : Sort {
    override fun equals(other: Any?): Boolean = when {
        this === other -> true
        other !is ParameterizedSort -> false
        else -> name == other.name && arity == other.arity
    }
    override fun hashCode(): Int = name.hashCode() + 31 * arity
    override fun toString(): String = "(_ $name $arity)"
}
 */
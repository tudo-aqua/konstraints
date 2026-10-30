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

package tools.aqua.konstraints.smt

sealed interface SortFactory {
  fun build(parameters: List<Sort>, indices: List<NumeralIndex>): Sort

  fun isInstanceOf(sort: Sort): Boolean

  val isIndexed: Boolean
  val numIndicies: Int
}

object BoolFactory : SortFactory {
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): BoolSort {
    require(parameters.isEmpty())
    require(indices.isEmpty())

    return build()
  }

  fun build() = BoolSort

  override fun isInstanceOf(sort: Sort) = (sort is BoolSort)

  override val isIndexed = false
  override val numIndicies = 0
}

object IntFactory : SortFactory {
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): IntSort {
    require(parameters.isEmpty())
    require(indices.isEmpty())

    return build()
  }

  fun build() = IntSort

  override fun isInstanceOf(sort: Sort) = (sort is IntSort)

  override val isIndexed = false
  override val numIndicies = 0
}

object RealFactory : SortFactory {
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): RealSort {
    require(parameters.isEmpty())
    require(indices.isEmpty())

    return build()
  }

  fun build() = RealSort

  override fun isInstanceOf(sort: Sort) = (sort is RealSort)

  override val isIndexed = false
  override val numIndicies = 0
}

object StringFactory : SortFactory {
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): StringSort {
    require(parameters.isEmpty())
    require(indices.isEmpty())

    return build()
  }

  fun build() = StringSort

  override fun isInstanceOf(sort: Sort) = (sort is StringSort)

  override val isIndexed = false
  override val numIndicies = 0
}

object RegLanFactory : SortFactory {
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): RegLanSort {
    require(parameters.isEmpty())
    require(indices.isEmpty())

    return build()
  }

  fun build() = RegLanSort

  override fun isInstanceOf(sort: Sort) = (sort is RegLanSort)

  override val isIndexed = false
  override val numIndicies = 0
}

object RoundingModeFactory : SortFactory {
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): RoundingModeSort {
    require(parameters.isEmpty())
    require(indices.isEmpty())

    return build()
  }

  fun build() = RoundingModeSort

  override fun isInstanceOf(sort: Sort) = (sort is RoundingModeSort)

  override val isIndexed = false
  override val numIndicies = 0
}

object BitVecFactory : SortFactory {
  /**
   * Cache of common bitvector sorts containing Bitvectors sized 1-16, powers of two up to 2^16 and
   * sizes needed for IEEE 754 floating points such as 19, 24, 53, 113, 237
   */
  private val cache =
      arrayOf(
          BitVecSort(1.idx()),
          BitVecSort(2.idx()),
          BitVecSort(3.idx()),
          BitVecSort(4.idx()),
          BitVecSort(5.idx()),
          BitVecSort(6.idx()),
          BitVecSort(7.idx()),
          BitVecSort(8.idx()),
          BitVecSort(9.idx()),
          BitVecSort(10.idx()),
          BitVecSort(11.idx()),
          BitVecSort(12.idx()),
          BitVecSort(13.idx()),
          BitVecSort(14.idx()),
          BitVecSort(15.idx()),
          BitVecSort(16.idx()),
          BitVecSort(19.idx()),
          BitVecSort(24.idx()),
          BitVecSort(32.idx()),
          BitVecSort(53.idx()),
          BitVecSort(64.idx()),
          BitVecSort(113.idx()),
          BitVecSort(128.idx()),
          BitVecSort(237.idx()),
          BitVecSort(256.idx()),
          BitVecSort(512.idx()),
          BitVecSort(1024.idx()),
          BitVecSort(2048.idx()),
          BitVecSort(4096.idx()),
          BitVecSort(8192.idx()),
          BitVecSort(16384.idx()),
          BitVecSort(32786.idx()),
          BitVecSort(65536.idx()),
      )

  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): BitVecSort {
    require(parameters.isEmpty())
    require(indices.size == 1)

    return build(indices.single().numeral)
  }

  fun build(n: Int) =
      when (n) {
        1 -> cache[0]
        2 -> cache[1]
        3 -> cache[2]
        4 -> cache[3]
        5 -> cache[4]
        6 -> cache[5]
        7 -> cache[6]
        8 -> cache[7]
        9 -> cache[8]
        10 -> cache[9]
        11 -> cache[10]
        12 -> cache[11]
        13 -> cache[12]
        14 -> cache[13]
        15 -> cache[14]
        16 -> cache[15]
        19 -> cache[16]
        24 -> cache[17]
        32 -> cache[18]
        53 -> cache[19]
        64 -> cache[20]
        113 -> cache[21]
        128 -> cache[22]
        237 -> cache[23]
        256 -> cache[24]
        512 -> cache[25]
        1024 -> cache[26]
        2048 -> cache[27]
        4096 -> cache[28]
        8192 -> cache[29]
        16384 -> cache[30]
        32786 -> cache[31]
        65536 -> cache[32]
        else -> BitVecSort(n.idx())
      }

  override fun isInstanceOf(sort: Sort) = (sort is BitVecSort)

  override val isIndexed = true
  override val numIndicies = 1
}

class UserDefinedBitVectorFactory(symbol: Symbol, val bits: Int, val parameters: List<Symbol>) :
    UserDefinedSortFactory(symbol) {
  override fun build(
      parameters: List<Sort>,
      indices: List<NumeralIndex>,
  ): BitVecSort {
    require(parameters.size == this.parameters.size)
    require(indices.isEmpty())

    return bitvec
  }

  private val bitvec = BitVecFactory.build(bits)

  override fun isInstanceOf(sort: Sort) = sort is BitVecSort && bits == sort.bits
}

object FloatingPointFactory : SortFactory {

  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): FloatingPointSort {
    require(parameters.isEmpty())
    require(indices.size == 2)

    return build(indices[0].numeral, indices[1].numeral)
  }

  fun build(eb: Int, sb: Int) = FloatingPointSort(eb, sb)

  override fun isInstanceOf(sort: Sort) = (sort is FloatingPointSort)

  override val isIndexed = true
  override val numIndicies = 2
}

class UserDefinedFloatingPointFactory(
    symbol: Symbol,
    val eb: Int,
    val sb: Int,
    val parameters: List<Symbol>,
) : UserDefinedSortFactory(symbol) {
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): Sort {
    require(parameters.size == this.parameters.size)
    require(indices.isEmpty())

    return sort
  }

  private val sort = FloatingPointSort(eb, sb)

  override fun isInstanceOf(sort: Sort) =
      sort is FloatingPointSort && sort.exponentBits == eb && sort.significantBits == sb
}

object Float16Factory : SortFactory {

  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): FloatingPointSort {
    require(parameters.isEmpty())
    require(indices.isEmpty())

    return build()
  }

  fun build() = SMTFP16

  override fun isInstanceOf(sort: Sort) =
      (sort is FloatingPointSort) && (sort.exponentBits == 5) && (sort.significantBits == 11)

  override val isIndexed = false
  override val numIndicies = 0
}

object Float32Factory : SortFactory {

  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): FloatingPointSort {
    require(parameters.isEmpty())
    require(indices.isEmpty())

    return build()
  }

  fun build() = SMTFP32

  override fun isInstanceOf(sort: Sort) =
      (sort is FloatingPointSort) && (sort.exponentBits == 8) && (sort.significantBits == 24)

  override val isIndexed = false
  override val numIndicies = 0
}

object Float64Factory : SortFactory {

  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): FloatingPointSort {
    require(parameters.isEmpty())
    require(indices.isEmpty())

    return build()
  }

  fun build() = SMTFP64

  override fun isInstanceOf(sort: Sort) =
      (sort is FloatingPointSort) && (sort.exponentBits == 11) && (sort.significantBits == 53)

  override val isIndexed = false
  override val numIndicies = 0
}

object Float128Factory : SortFactory {

  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): FloatingPointSort {
    require(parameters.isEmpty())
    require(indices.isEmpty())

    return build()
  }

  fun build() = SMTFP128

  override fun isInstanceOf(sort: Sort) =
      (sort is FloatingPointSort) && (sort.exponentBits == 15) && (sort.significantBits == 113)

  override val isIndexed = false
  override val numIndicies = 0
}

object ArraySortFactory : SortFactory {
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): ArraySort<*, *> {
    require(parameters.size == 2)
    require(indices.isEmpty())

    return build(parameters[0], parameters[1])
  }

  fun <A : Sort, B : Sort> build(X: A, Y: B) = ArraySort(X, Y)

  override fun isInstanceOf(sort: Sort) = (sort is ArraySort<*, *>)

  override val isIndexed = false
  override val numIndicies = 0
}

class UserDefinedArrayFactory(
    symbol: Symbol,
    val parameters: List<Sort>,
    val sortParameters: List<Symbol>,
) : UserDefinedSortFactory(symbol) {
  init {
    require(parameters.size == 2)
  }

  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): ArraySort<*, *> {
    require(parameters.size == sortParameters.size)
    require(indices.isEmpty())

    val mapping = (sortParameters zip parameters).toMap()

    val actual =
        this.parameters.map { sort ->
          when (sort) {
            is SortParameter -> mapping[sort.symbol]!!
            else -> sort
          }
        }

    return ArraySort(actual[0], actual[1])
  }

  override fun isInstanceOf(sort: Sort): Boolean {
    TODO("Not yet implemented")
  }
}

/**
 * Base class for each SMT sort.
 *
 * @param symbol sort name
 */
sealed class Sort(open val symbol: Symbol) : SMTSerializable {
  constructor(name: String) : this(name.toSymbol())

  open val indices: List<Index> = emptyList()
  open val parameters: List<Sort> = emptyList()

  open val name: String = symbol.toString()
  open val definedSymbol: Symbol? = null

  abstract val theories: Set<Theories>

  fun isIndexed(): Boolean = indices.isNotEmpty()

  override fun equals(other: Any?): Boolean =
      when {
        this === other -> true
        other !is Sort -> false
        else -> sortEquality(other)
      }

  private fun sortEquality(other: Sort): Boolean {
    return if (symbol != other.symbol) false
    else if (!(indices zip other.indices).all { (lhs, rhs) -> lhs == rhs }) false
    else if (!(parameters zip other.parameters).all { (lhs, rhs) -> lhs == rhs }) false else true
  }

  override fun hashCode(): Int =
      symbol.hashCode() * 961 + indices.hashCode() * 31 + parameters.hashCode()

  override fun toString() =
      if (this.isIndexed()) {
        "(_ $symbol ${indices.joinToString(" ")})"
      } else if (parameters.isNotEmpty()) {
        "($symbol ${parameters.joinToString(" ")})"
      } else {
        symbol.toString()
      }

  fun toSMTString() = symbol.toSMTString(QuotingRule.SAME_AS_INPUT, false)

  override fun toSMTString(quotingRule: QuotingRule, useIterative: Boolean): String =
      if (this.isIndexed()) {
        "(_ ${symbol.toSMTString(quotingRule, useIterative)} ${indices.joinToString(" ")})"
      } else if (parameters.isNotEmpty()) {
        "($symbol ${parameters.joinToString(" ") { it.toSMTString(quotingRule, useIterative) }})"
      } else {
        symbol.toSMTString(quotingRule, useIterative)
      }

  override fun toSMTString(
      builder: Appendable,
      quotingRule: QuotingRule,
      useIterative: Boolean,
  ): Appendable =
      if (this.isIndexed()) {
        builder.append("(_ ")
        symbol.toSMTString(builder, quotingRule, useIterative)
        builder.append(" ${indices.joinToString(" ")})")
      } else if (parameters.isNotEmpty()) {
        builder.append("(")
        symbol.toSMTString(builder, quotingRule, useIterative)

        parameters.forEach {
          builder.append(" ")
          it.toSMTString(builder, quotingRule, useIterative)
        }
        builder.append(")")

        builder
      } else {
        symbol.toSMTString(builder, quotingRule, useIterative)
      }
}

class SortParameter(name: Symbol) : Sort(name) {
  constructor(name: String) : this(name.toSymbol())

  override val theories = emptySet<Theories>()
}

abstract class UserDefinedSortFactory(val symbol: Symbol) : SortFactory {
  override val isIndexed = false
  override val numIndicies = 0
}

class UserDefinedBoolFactory(symbol: Symbol, val parameters: List<Symbol>) :
    UserDefinedSortFactory(symbol) {
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): Sort {
    require(this.parameters.size == parameters.size)
    require(indices.isEmpty())

    return BoolSort
  }

  override fun isInstanceOf(sort: Sort) = sort is BoolSort && sort.definedSymbol == symbol

  override val isIndexed = false
  override val numIndicies = 0
}

class UserDefinedRealFactory(symbol: Symbol, val parameters: List<Symbol>) :
    UserDefinedSortFactory(symbol) {
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): Sort {
    require(this.parameters.size == parameters.size)
    require(indices.isEmpty())

    return RealSort
  }

  override fun isInstanceOf(sort: Sort) = sort is RealSort && sort.definedSymbol == symbol

  override val isIndexed = false
  override val numIndicies = 0
}

class UserDefinedIntFactory(symbol: Symbol, val parameters: List<Symbol>) :
    UserDefinedSortFactory(symbol) {
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): Sort {
    require(this.parameters.size == parameters.size)
    require(indices.isEmpty())

    return IntSort
  }

  override fun isInstanceOf(sort: Sort) = sort is IntSort && sort.definedSymbol == symbol

  override val isIndexed = false
  override val numIndicies = 0
}

class UserDefinedStringFactory(symbol: Symbol, val parameters: List<Symbol>) :
    UserDefinedSortFactory(symbol) {
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): Sort {
    require(this.parameters.size == parameters.size)
    require(indices.isEmpty())

    return StringSort
  }

  override fun isInstanceOf(sort: Sort) = sort is StringSort && sort.definedSymbol == symbol

  override val isIndexed = false
  override val numIndicies = 0
}

class UserDefinedRegLanFactory(symbol: Symbol, val parameters: List<Symbol>) :
    UserDefinedSortFactory(symbol) {
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): Sort {
    require(this.parameters.size == parameters.size)
    require(indices.isEmpty())

    return RegLanSort
  }

  override fun isInstanceOf(sort: Sort) = sort is RegLanSort && sort.definedSymbol == symbol

  override val isIndexed = false
  override val numIndicies = 0
}

class UserDefinedRoundingModeFactory(symbol: Symbol, val parameters: List<Symbol>) :
    UserDefinedSortFactory(symbol) {
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): Sort {
    require(this.parameters.size == parameters.size)
    require(indices.isEmpty())

    return RoundingModeSort
  }

  override fun isInstanceOf(sort: Sort) = sort is RoundingModeSort && sort.definedSymbol == symbol

  override val isIndexed = false
  override val numIndicies = 0
}

class UserDeclaredSortFactory(val symbol: Symbol, val arity: Int) : SortFactory {
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): Sort {
    require(parameters.size == arity)
    require(indices.isEmpty())

    return UserDeclaredSort(symbol, parameters)
  }

  override fun isInstanceOf(sort: Sort): Boolean {
    require(sort is UserDeclaredSort)

    return sort.symbol == symbol && sort.parameters.size == arity
  }

  override val isIndexed = false
  override val numIndicies = 0
}

class UserDeclaredSort(name: Symbol, override val parameters: List<Sort>) : Sort(name) {
  override val theories = emptySet<Theories>()
}

class SortParameterFactory(val symbol: Symbol) : SortFactory {
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>) = sort

  val sort = SortParameter(symbol)

  override fun isInstanceOf(sort: Sort) = sort is SortParameter && sort.symbol == symbol

  override val isIndexed = false
  override val numIndicies = 0
}

/** Default implementation of Array sort. */
class ArraySort<out X : Sort, out Y : Sort>(val x: X, val y: Y) : Sort("Array".toSymbol()) {
  override val parameters = listOf(x, y)

  override fun toString(): String = "(Array $x $y)"

  override val theories = ARRAYS_EX_MARKER_SET
}

// TODO the class is open for now to allow the SymbolicBitVec sub class might find a better solution
// in the future
/** Bitvector sort with [bits] length. */
open class BitVecSort(index: Index) : Sort("BitVec") {
  companion object {
    /**
     * Get BitVec sort with the given number of [bits].
     *
     * Currently, this generates a new BitVec every time it is invoked, this should only create a
     * single instance for each length
     */
    operator fun invoke(bits: Int): BitVecSort = BitVecFactory.build(bits)

    /**
     * Get a BitVec sort with an unknown number of bits, this is not a valid BitVec sort for SMT but
     * rather just a placeholder for function definitions that take arguments of any BitVec length.
     */
    internal fun fromSymbol(symbol: String): BitVecSort = SymbolicBitVec(symbol)
  }

  override val indices = listOf(index)

  val bits: Int
  override val theories = setOf(Theories.FIXED_SIZE_BIT_VECTORS, Theories.FLOATING_POINT)

  init {
    // indices must either be single numeral index or a symbolic index
    // if the index is symbolic we set the number of bits to 0 to indicate
    // that this is not a valid BitVec sort in the SMT sense, but rather used internally as
    // placeholder
    if (indices.single() is NumeralIndex) {
      bits = (indices.single() as NumeralIndex).numeral
      require(bits > 0)
    } else {
      bits = 0
    }
  }

  internal fun isSymbolic() = (indices.single() is SymbolIndex)
}

internal class SymbolicBitVec(bits: String) : BitVecSort(bits.idx())

/** Bool sort. */
object BoolSort : Sort("Bool") {
  override val theories = CORE_MARKER_SET
}

/** Int sort. */
object IntSort : Sort("Int") {
  override val theories = setOf(Theories.INTS, Theories.REALS_INTS, Theories.STRINGS)
}

/** Real sort. */
object RealSort : Sort("Real") {
  override val theories = REALS_REALS_INTS_MARKER_SET.plus(FLOATING_POINT_MARKER_SET)
}

/** String sort. */
object StringSort : Sort("String") {
  override val theories = STRINGS_MARKER_SET
}

/** Regular expression sort. */
object RegLanSort : Sort("RegLan") {
  override val theories = STRINGS_MARKER_SET
}

/** RoundingMode sort object. */
object RoundingModeSort : Sort("RoundingMode") {
  override val theories = FLOATING_POINT_MARKER_SET
}

/**
 * FloatingPoint sort with any positive number of bits.
 *
 * (_ FloatingPoint eb sb)
 *
 * @param eb exponent bits
 * @param sb significant bits
 */
open class FloatingPointSort(eb: Index, sb: Index) : Sort("FloatingPoint") {
  companion object {
    operator fun invoke(eb: Int, sb: Int): FloatingPointSort = FloatingPointSort(eb.idx(), sb.idx())

    operator fun invoke(eb: SymbolIndex, sb: SymbolIndex): FloatingPointSort =
        SymbolicFloatingPoint(eb, sb)
  }

  override val indices = listOf(eb, sb)

  val exponentBits: Int
  val significantBits: Int

  init {
    if (indices.all { index -> index is NumeralIndex }) {
      exponentBits = (eb as NumeralIndex).numeral
      significantBits = (sb as NumeralIndex).numeral

      require(exponentBits > 1)
      require(significantBits > 1)
    } else {
      exponentBits = 0
      significantBits = 0
    }
  }

  override val theories = FLOATING_POINT_MARKER_SET

  override fun equals(other: Any?): Boolean =
      when {
        this === other -> true
        other !is FloatingPointSort -> false
        else ->
            this.exponentBits == other.exponentBits && this.significantBits == other.significantBits
      }

  override fun hashCode(): Int {
    var result = super.hashCode()
    result = 31 * result + exponentBits
    result = 31 * result + significantBits
    return result
  }

  /*
  val zero = FPZero(exponentBits, significantBits)
  val minusZero = FPMinusZero(exponentBits, significantBits)
  val infinity = FPInfinity(exponentBits, significantBits)
  val minusInfinity = FPMinusInfinity(exponentBits, significantBits)
  val nan = FPNaN(exponentBits, significantBits)
  */
}

/** Standard 16-bit FloatingPoint sort. */
object SMTFP16 : FloatingPointSort(5.idx(), 11.idx()) {
  override val definedSymbol: Symbol = "Float16".toSymbol()

  override fun toString() = definedSymbol.toString()

  override fun toSMTString(quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(quotingRule, useIterative)

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(builder, quotingRule, useIterative)
}

/** Standard 32-bit FloatingPoint sort. */
object SMTFP32 : FloatingPointSort(8.idx(), 24.idx()) {
  override val definedSymbol: Symbol = "Float32".toSymbol()

  override fun toString() = definedSymbol.toString()

  override fun toSMTString(quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(quotingRule, useIterative)

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(builder, quotingRule, useIterative)
}

/** Standard 64-bit FloatingPoint sort. */
object SMTFP64 : FloatingPointSort(11.idx(), 53.idx()) {
  override val definedSymbol: Symbol = "Float64".toSymbol()

  override fun toString() = definedSymbol.toString()

  override fun toSMTString(quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(quotingRule, useIterative)

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(builder, quotingRule, useIterative)
}

/** Standard 128-bit FloatingPoint sort. */
object SMTFP128 : FloatingPointSort(15.idx(), 113.idx()) {
  override val definedSymbol: Symbol = "Float128".toSymbol()

  override fun toString() = definedSymbol.toString()

  override fun toSMTString(quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(quotingRule, useIterative)

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(builder, quotingRule, useIterative)
}

internal class SymbolicFloatingPoint(eb: SymbolIndex, sb: SymbolIndex) : FloatingPointSort(eb, sb)

/** Common base class for IntSort and RealSort used by common operations in Ints_Reals theory. */
sealed class NumeralSort(name: String) : Sort(name)

internal object NumeralSortInstance : NumeralSort("Numeral") {
  override val theories: Set<Theories> = INTS_REALS_INTS_MARKER_SET
}

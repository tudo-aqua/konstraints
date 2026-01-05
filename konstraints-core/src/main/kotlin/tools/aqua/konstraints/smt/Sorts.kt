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

  fun build() = Bool

  override fun isInstanceOf(sort: Sort) = (sort is BoolSort)

  override val isIndexed = false
  override val numIndicies = 0
}

class UserDefinedBoolFactory(symbol: Symbol, val parameters: List<Symbol>) :
    UserDefinedSortFactory(symbol) {
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): Sort {
    require(this.parameters.size == parameters.size)
    require(indices.isEmpty())

    return UserDefinedBoolSort(symbol, parameters)
  }

  override fun isInstanceOf(sort: Sort) =
      sort is UserDefinedBoolSort && sort.definedSymbol == symbol

  override val isIndexed = false
  override val numIndicies = 0
}

class UserDefinedBoolSort(override val definedSymbol: Symbol, override val parameters: List<Sort>) :
    BoolSort() {
  override fun toString() = definedSymbol.toString()

  override fun toSMTString(quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(quotingRule, useIterative)

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(builder, quotingRule, useIterative)
}

class UserDefinedRealFactory(symbol: Symbol, val parameters: List<Symbol>) :
    UserDefinedSortFactory(symbol) {
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): Sort {
    require(this.parameters.size == parameters.size)
    require(indices.isEmpty())

    return UserDefinedRealSort(symbol, parameters)
  }

  override fun isInstanceOf(sort: Sort) =
      sort is UserDefinedRealSort && sort.definedSymbol == symbol

  override val isIndexed = false
  override val numIndicies = 0
}

class UserDefinedRealSort(override val definedSymbol: Symbol, override val parameters: List<Sort>) :
    RealSort() {
  override fun toString() = definedSymbol.toString()

  override fun toSMTString(quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(quotingRule, useIterative)

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(builder, quotingRule, useIterative)
}

class UserDefinedIntFactory(symbol: Symbol, val parameters: List<Symbol>) :
    UserDefinedSortFactory(symbol) {
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): Sort {
    require(this.parameters.size == parameters.size)
    require(indices.isEmpty())

    return UserDefinedIntSort(symbol, parameters)
  }

  override fun isInstanceOf(sort: Sort) = sort is UserDefinedIntSort && sort.definedSymbol == symbol

  override val isIndexed = false
  override val numIndicies = 0
}

class UserDefinedIntSort(override val definedSymbol: Symbol, override val parameters: List<Sort>) :
    IntSort() {
  override fun toString() = definedSymbol.toString()

  override fun toSMTString(quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(quotingRule, useIterative)

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(builder, quotingRule, useIterative)
}

class UserDefinedStringFactory(symbol: Symbol, val parameters: List<Symbol>) :
    UserDefinedSortFactory(symbol) {
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): Sort {
    require(this.parameters.size == parameters.size)
    require(indices.isEmpty())

    return UserDefinedStringSort(symbol, parameters)
  }

  override fun isInstanceOf(sort: Sort) =
      sort is UserDefinedStringSort && sort.definedSymbol == symbol

  override val isIndexed = false
  override val numIndicies = 0
}

class UserDefinedStringSort(
    override val definedSymbol: Symbol,
    override val parameters: List<Sort>,
) : StringSort() {
  override fun toString() = definedSymbol.toString()

  override fun toSMTString(quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(quotingRule, useIterative)

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(builder, quotingRule, useIterative)
}

class UserDefinedRegLanFactory(symbol: Symbol, val parameters: List<Symbol>) :
    UserDefinedSortFactory(symbol) {
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): Sort {
    require(this.parameters.size == parameters.size)
    require(indices.isEmpty())

    return UserDefinedRegLanSort(symbol, parameters)
  }

  override fun isInstanceOf(sort: Sort) =
      sort is UserDefinedRegLanSort && sort.definedSymbol == symbol

  override val isIndexed = false
  override val numIndicies = 0
}

class UserDefinedRegLanSort(
    override val definedSymbol: Symbol,
    override val parameters: List<Sort>,
) : RegLanSort() {
  override fun toString() = definedSymbol.toString()

  override fun toSMTString(quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(quotingRule, useIterative)

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(builder, quotingRule, useIterative)
}

class UserDefinedRoundingModeFactory(symbol: Symbol, val parameters: List<Symbol>) :
    UserDefinedSortFactory(symbol) {
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): Sort {
    require(this.parameters.size == parameters.size)
    require(indices.isEmpty())

    return UserDefinedRoundingModeSort(symbol, parameters)
  }

  override fun isInstanceOf(sort: Sort) =
      sort is UserDefinedRoundingModeSort && sort.definedSymbol == symbol

  override val isIndexed = false
  override val numIndicies = 0
}

class UserDefinedRoundingModeSort(
    override val definedSymbol: Symbol,
    override val parameters: List<Sort>,
) : RoundingModeSort() {
  override fun toString() = definedSymbol.toString()

  override fun toSMTString(quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(quotingRule, useIterative)

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(builder, quotingRule, useIterative)
}

object IntFactory : SortFactory {
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): IntSort {
    require(parameters.isEmpty())
    require(indices.isEmpty())

    return build()
  }

  fun build() = SMTInt

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

  fun build() = Real

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

  fun build() = SMTString

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

  fun build() = RegLan

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

  fun build() = RoundingMode

  override fun isInstanceOf(sort: Sort) = (sort is RoundingMode)

  override val isIndexed = false
  override val numIndicies = 0
}

object BitVecFactory : SortFactory {
  private val cache =
      arrayOf(
          BitVec(1),
          BitVec(2),
          BitVec(3),
          BitVec(4),
          BitVec(5),
          BitVec(6),
          BitVec(7),
          BitVec(8),
          BitVec(9),
          BitVec(10),
          BitVec(11),
          BitVec(12),
          BitVec(13),
          BitVec(14),
          BitVec(15),
          BitVec(16),
          BitVec(19),
          BitVec(24),
          BitVec(32),
          BitVec(53),
          BitVec(64),
          BitVec(113),
          BitVec(128),
          BitVec(237),
          BitVec(256),
          BitVec(512),
          BitVec(1024),
          BitVec(2048),
          BitVec(4096),
          BitVec(8192),
          BitVec(16384),
          BitVec(32786),
          BitVec(65536),
      )

  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): BVSort {
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
        else -> BitVec(n)
      }

  override fun isInstanceOf(sort: Sort) = (sort is BVSort)

  override val isIndexed = true
  override val numIndicies = 1
}

object FloatingPointFactory : SortFactory {

  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): FPSort {
    require(parameters.isEmpty())
    require(indices.size == 2)

    return build(indices[0].numeral, indices[1].numeral)
  }

  fun build(eb: Int, sb: Int) = FPSort(eb, sb)

  override fun isInstanceOf(sort: Sort) = (sort is FPSort)

  override val isIndexed = true
  override val numIndicies = 2
}

object Float16Factory : SortFactory {

  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): FPSort {
    require(parameters.isEmpty())
    require(indices.isEmpty())

    return build()
  }

  fun build() = FP16

  override fun isInstanceOf(sort: Sort) =
      (sort is FPSort) && (sort.exponentBits == 5) && (sort.significantBits == 11)

  override val isIndexed = false
  override val numIndicies = 0
}

object Float32Factory : SortFactory {

  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): FPSort {
    require(parameters.isEmpty())
    require(indices.isEmpty())

    return build()
  }

  fun build() = FP32

  override fun isInstanceOf(sort: Sort) =
      (sort is FPSort) && (sort.exponentBits == 8) && (sort.significantBits == 24)

  override val isIndexed = false
  override val numIndicies = 0
}

object Float64Factory : SortFactory {

  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): FPSort {
    require(parameters.isEmpty())
    require(indices.isEmpty())

    return build()
  }

  fun build() = FP64

  override fun isInstanceOf(sort: Sort) =
      (sort is FPSort) && (sort.exponentBits == 11) && (sort.significantBits == 53)

  override val isIndexed = false
  override val numIndicies = 0
}

object Float128Factory : SortFactory {

  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): FPSort {
    require(parameters.isEmpty())
    require(indices.isEmpty())

    return build()
  }

  fun build() = FP128

  override fun isInstanceOf(sort: Sort) =
      (sort is FPSort) && (sort.exponentBits == 15) && (sort.significantBits == 113)

  override val isIndexed = false
  override val numIndicies = 0
}

object ArraySortFactory : SortFactory {
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): ArraySort<*, *> {
    require(parameters.size == 2)
    require(indices.isEmpty())

    return build(parameters[0], parameters[1])
  }

  fun <A : Sort, B : Sort> build(X: A, Y: B) = SMTArray(X, Y)

  override fun isInstanceOf(sort: Sort) = (sort is ArraySort<*, *>)

  override val isIndexed = false
  override val numIndicies = 0
}

/**
 * Base class for each SMT sort.
 *
 * @param symbol sort name
 */
sealed class Sort(open val symbol: Symbol) : SMTSerializable {
  constructor(name: String) : this(name.toSymbolWithQuotes())

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
  constructor(name: String) : this(name.toSymbolWithQuotes())

  override val theories = emptySet<Theories>()
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

open class UserDeclaredSort(name: Symbol, override val parameters: List<Sort>) : Sort(name) {
  override val theories = emptySet<Theories>()
}

class UserDefinedUserDeclaredFactory(
    symbol: Symbol,
    val parameters: List<Symbol>,
    val sort: UserDeclaredSortFactory,
) : UserDefinedSortFactory(symbol) {
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): Sort {
    require(this.parameters.size == parameters.size)
    require(indices.isEmpty())

    return UserDefinedUserDeclaredSort(symbol, sort.symbol, parameters)
  }

  override fun isInstanceOf(sort: Sort) =
      sort is UserDefinedRegLanSort && sort.definedSymbol == symbol

  override val isIndexed = false
  override val numIndicies = 0
}

class UserDefinedUserDeclaredSort(
    override val definedSymbol: Symbol,
    name: Symbol,
    parameters: List<Sort>,
) : UserDeclaredSort(name, parameters) {
  override fun toString() = definedSymbol.toString()

  override fun toSMTString(quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(quotingRule, useIterative)

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(builder, quotingRule, useIterative)
}

abstract class UserDefinedSortFactory(val symbol: Symbol) : SortFactory {
  override val isIndexed = false
  override val numIndicies = 0
}

class SortParameterFactory(val symbol: Symbol) : SortFactory {
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>) = sort

  val sort = SortParameter(symbol)

  override fun isInstanceOf(sort: Sort) = sort is SortParameter && sort.symbol == symbol

  override val isIndexed = false
  override val numIndicies = 0
}

class UserDefinedBitVectorFactory(symbol: Symbol, val bits: Int, val parameters: List<Symbol>) :
    UserDefinedSortFactory(symbol) {
  override fun build(
      parameters: List<Sort>,
      indices: List<NumeralIndex>,
  ): UserDefinedBitVectorSort {
    require(parameters.size == this.parameters.size)
    require(indices.isEmpty())

    return bitvec
  }

  private val bitvec = UserDefinedBitVectorSort(symbol, bits)

  override fun isInstanceOf(sort: Sort) = sort is BVSort && bits == sort.bits
}

class UserDefinedBitVectorSort(override val definedSymbol: Symbol, bits: Int) : BVSort(bits.idx()) {
  override fun toString() = definedSymbol.toString()

  override fun toSMTString(quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(quotingRule, useIterative)

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(builder, quotingRule, useIterative)
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

  private val sort = UserDefinedFloatingPointSort(symbol, eb, sb)

  override fun isInstanceOf(sort: Sort) =
      sort is UserDefinedFloatingPointSort && sort.exponentBits == eb && sort.significantBits == sb
}

class UserDefinedFloatingPointSort(override val definedSymbol: Symbol, eb: Int, sb: Int) :
    FPSort(eb.idx(), sb.idx()) {
  override fun toString() = definedSymbol.toString()

  override fun toSMTString(quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(quotingRule, useIterative)

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(builder, quotingRule, useIterative)
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

    return UserDefinedArraySort(symbol, actual[0], actual[1])
  }

  override fun isInstanceOf(sort: Sort): Boolean {
    TODO("Not yet implemented")
  }
}

class UserDefinedArraySort<X : Sort, Y : Sort>(override val definedSymbol: Symbol, x: X, y: Y) :
    ArraySort<X, Y>(x, y) {
  override fun toString() = definedSymbol.toString()
}

/** Default implementation of Array sort. */
sealed class ArraySort<X : Sort, Y : Sort>(val x: X, val y: Y) :
    Sort("Array".toSymbolWithQuotes()) {
  override val parameters = listOf(x, y)

  override fun toString(): String = "(Array $x $y)"

  override val theories = ARRAYS_EX_MARKER_SET
}

/** Base class for all ArraySorts. */
class SMTArray<X : Sort, Y : Sort>(x: X, y: Y) : ArraySort<X, Y>(x, y)

/** Bitvector sort with [bits] length. */
sealed class BVSort(index: Index) : Sort("BitVec") {
  companion object {
    /**
     * Get BitVec sort with the given number of [bits].
     *
     * Currently, this generates a new BitVec every time it is invoked, this should only create a
     * single instance for each length
     */
    operator fun invoke(bits: Int): BVSort = BitVecFactory.build(bits)

    /**
     * Get a BitVec sort with an unknown number of bits, this is not a valid BitVec sort for SMT but
     * rather just a placeholder for function definitions that take arguments of any BitVec length.
     */
    internal fun fromSymbol(symbol: String): BVSort = SymbolicBitVec(symbol)
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

/** Default implementation of bitvectors in smt. */
class BitVec(bits: Int) : BVSort(bits.idx())

internal class SymbolicBitVec(bits: String) : BVSort(bits.idx())

/** Bool sort. */
sealed class BoolSort : Sort("Bool") {
  override val theories = CORE_MARKER_SET
}

object Bool : BoolSort()

/** Int sort. */
sealed class IntSort : Sort("Int") {
  override val theories = setOf(Theories.INTS, Theories.REALS_INTS, Theories.STRINGS)
}

object SMTInt : IntSort()

/** Real sort. */
sealed class RealSort : Sort("Real") {
  override val theories = REALS_REALS_INTS_MARKER_SET.plus(FLOATING_POINT_MARKER_SET)
}

object Real : RealSort()

/** String sort. */
sealed class StringSort : Sort("String") {
  override val theories = STRINGS_MARKER_SET
}

object SMTString : StringSort()

/** Regular expression sort. */
sealed class RegLanSort : Sort("RegLan") {
  override val theories = STRINGS_MARKER_SET
}

object RegLan : RegLanSort()

/** RoundingMode sort object. */
sealed class RoundingModeSort : Sort("RoundingMode") {
  override val theories = FLOATING_POINT_MARKER_SET
}

/** Default implementation of rounding mode sort. */
object RoundingMode : RoundingModeSort()

/**
 * FloatingPoint sort with any positive number of bits.
 *
 * (_ FloatingPoint eb sb)
 *
 * @param eb exponent bits
 * @param sb significant bits
 */
sealed class FPSort(eb: Index, sb: Index) : Sort("FloatingPoint") {
  companion object {
    operator fun invoke(eb: Int, sb: Int): FPSort = FloatingPoint(eb, sb)

    operator fun invoke(eb: SymbolIndex, sb: SymbolIndex): FPSort = SymbolicFloatingPoint(eb, sb)
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
        other !is FPSort -> false
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
object FP16 : FPSort(5.idx(), 11.idx()) {
  override val definedSymbol: Symbol = "Float16".toSymbolWithQuotes()

  override fun toString() = definedSymbol.toString()

  override fun toSMTString(quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(quotingRule, useIterative)

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(builder, quotingRule, useIterative)
}

/** Standard 32-bit FloatingPoint sort. */
object FP32 : FPSort(8.idx(), 24.idx()) {
  override val definedSymbol: Symbol = "Float32".toSymbolWithQuotes()

  override fun toString() = definedSymbol.toString()

  override fun toSMTString(quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(quotingRule, useIterative)

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(builder, quotingRule, useIterative)
}

/** Standard 64-bit FloatingPoint sort. */
object FP64 : FPSort(11.idx(), 53.idx()) {
  override val definedSymbol: Symbol = "Float64".toSymbolWithQuotes()

  override fun toString() = definedSymbol.toString()

  override fun toSMTString(quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(quotingRule, useIterative)

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(builder, quotingRule, useIterative)
}

/** Standard 128-bit FloatingPoint sort. */
object FP128 : FPSort(15.idx(), 113.idx()) {
  override val definedSymbol: Symbol = "Float128".toSymbolWithQuotes()

  override fun toString() = definedSymbol.toString()

  override fun toSMTString(quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(quotingRule, useIterative)

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule, useIterative: Boolean) =
      definedSymbol.toSMTString(builder, quotingRule, useIterative)
}

/** Default floating point sort implementation. */
class FloatingPoint(eb: Int, sb: Int) : FPSort(eb.idx(), sb.idx())

internal class SymbolicFloatingPoint(eb: SymbolIndex, sb: SymbolIndex) : FPSort(eb, sb)

/** Common base class for IntSort and RealSort used by common operations in Ints_Reals theory. */
sealed class NumeralSort(name: String) : Sort(name)

internal object NumeralSortInstance : NumeralSort("Numeral") {
  override val theories: Set<Theories> = INTS_REALS_INTS_MARKER_SET
}

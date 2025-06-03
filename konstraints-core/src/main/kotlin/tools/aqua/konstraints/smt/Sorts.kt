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

package tools.aqua.konstraints.smt

import tools.aqua.konstraints.theories.*

sealed interface SortFactory {
  abstract fun build(parameters: List<Sort>, indices: List<NumeralIndex>): Sort

  abstract fun isInstanceOf(sort: Sort): Boolean

  abstract val isIndexed: Boolean
  abstract val numIndicies: Int
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
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): RegLan {
    require(parameters.isEmpty())
    require(indices.isEmpty())

    return build()
  }

  fun build() = RegLan

  override fun isInstanceOf(sort: Sort) = (sort is RegLan)

  override val isIndexed = false
  override val numIndicies = 0
}

object RoundingModeFactory : SortFactory {
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): RoundingMode {
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
          BVSort(1),
          BVSort(2),
          BVSort(3),
          BVSort(4),
          BVSort(5),
          BVSort(6),
          BVSort(7),
          BVSort(8),
          BVSort(9),
          BVSort(10),
          BVSort(11),
          BVSort(12),
          BVSort(13),
          BVSort(14),
          BVSort(15),
          BVSort(16),
          BVSort(19),
          BVSort(24),
          BVSort(32),
          BVSort(53),
          BVSort(64),
          BVSort(113),
          BVSort(128),
          BVSort(237),
          BVSort(256),
          BVSort(512),
          BVSort(1024),
          BVSort(2048),
          BVSort(4096),
          BVSort(8192),
          BVSort(16384),
          BVSort(32786),
          BVSort(65536),
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
        else -> BVSort(n)
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

  fun build() = FPSort(5, 11)

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

  fun build() = FPSort(8, 24)

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

  fun build() = FPSort(11, 53)

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

  fun build() = FPSort(15, 113)

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

  fun <A : Sort, B : Sort> build(X: A, Y: B) = ArraySort(X, Y)

  override fun isInstanceOf(sort: Sort) = (sort is ArraySort<*, *>)

  override val isIndexed = false
  override val numIndicies = 0
}

/**
 * Base class for each SMT sort
 *
 * @param symbol sort name
 * @param indices indices of indexed sorts (e.g. (_ BitVec m))
 * @param parameters parameters of parameterized sorts (e.g. (Array 2))
 */
abstract class Sort(
    val symbol: Symbol,
    val indices: List<Index> = emptyList(),
    val parameters: List<Sort> = emptyList()
) : ContextSort {
  constructor(
      name: String,
      indices: List<Index> = emptyList(),
      parameters: List<Sort> = emptyList()
  ) : this(name.toSymbolWithQuotes(), indices, parameters)

  override val name: String = symbol.toString()
  override val arity = parameters.size

  abstract val theories: Set<Theories>

  constructor(name: String, vararg indices: Index) : this(name, indices.toList())

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
      } else {
        symbol.toString()
      }

  fun toSMTString() = symbol.toSMTString(QuotingRule.SAME_AS_INPUT)
}

class SortParameter(name: String) : Sort(name, emptyList(), emptyList()) {
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

    return sort.symbol == symbol && sort.arity == arity
  }

  override val isIndexed = false
  override val numIndicies = 0
}

class UserDeclaredSort(name: Symbol, parameters: List<Sort>) : Sort(name, emptyList(), parameters) {
  override val theories = emptySet<Theories>()
}

class UserDefinedSortFactory(val symbol: Symbol, val sort: Sort) : SortFactory {
  override fun build(parameters: List<Sort>, indices: List<NumeralIndex>): Sort {
    require(parameters.isEmpty())
    require(indices.isEmpty())

    return sort
  }

  override fun isInstanceOf(sort: Sort): Boolean {
    require(sort is UserDefinedSort)

    return sort.symbol == symbol && sort.sort == sort
  }

  override val isIndexed = false
  override val numIndicies = 0
}

// TODO this only implements user defined sorts without sort parameters
class UserDefinedSort(name: Symbol, val sort: Sort) : Sort(name, emptyList(), emptyList()) {
  override val theories = emptySet<Theories>()
}

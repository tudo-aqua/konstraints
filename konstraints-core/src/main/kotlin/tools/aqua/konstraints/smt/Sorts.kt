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

import tools.aqua.konstraints.parser.Bindings
import tools.aqua.konstraints.parser.SortDecl

/**
 * Base class for each SMT sort
 *
 * @param name sort name
 * @param indices indices of indexed sorts (e.g. (_ BitVec m))
 * @param parameters parameters of parameterized sorts (e.g. (Array 2))
 */
open class Sort(
    val name: Symbol,
    val indices: List<Index> = emptyList(),
    val parameters: List<Sort> = emptyList()
) {
  constructor(
      name: String,
      indices: List<Index> = emptyList(),
      parameters: List<Sort> = emptyList()
  ) : this(Symbol(name), indices, parameters)

  constructor(name: String, vararg indices: Index) : this(name, indices.toList())

  fun isIndexed(): Boolean = indices.isNotEmpty()

  override fun equals(other: Any?): Boolean =
      when {
        this === other -> true
        other !is Sort -> false
        else -> sortEquality(other)
      }

  private fun sortEquality(other: Sort): Boolean {
    return if (name != other.name) false
    else if (!(indices zip other.indices).all { (lhs, rhs) -> lhs == rhs }) false
    else if (!(parameters zip other.parameters).all { (lhs, rhs) -> lhs == rhs }) false else true
  }

  override fun hashCode(): Int =
      name.hashCode() * 961 + indices.hashCode() * 31 + parameters.hashCode()

  override fun toString() =
      if (this.isIndexed()) {
        "(_ $name ${indices.joinToString(" ")})"
      } else {
        name.toString()
      }

  fun toSMTString() = name.toSMTString()
}

class SortParameter(name: String) : Sort(name, emptyList(), emptyList())

class UserDefinedSort(name: Symbol, arity: Int) :
    Sort(name, emptyList(), (0..arity).map { index -> SortParameter("sort$index") })

internal class UserDefinedSortDecl(name: Symbol, val arity: Int) :
    SortDecl<Sort>(
        name, (0..<arity).map { index -> SortParameter("sort$index") }.toSet(), emptySet()) {

  // FIXME parameter order is assume to be right in the bindings map
  override fun getSort(bindings: Bindings): Sort = UserDefinedSort(name, arity)
}

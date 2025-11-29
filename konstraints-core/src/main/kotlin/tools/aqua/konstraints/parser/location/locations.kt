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

package tools.aqua.konstraints.location

data class SourceLocation(
    val line: Int,
    val column: Int,
    val source: String? = null,
) {
  override fun toString(): String = buildString {
    append(line)
    append(":")
    append(column)
    append("@")
    append(source ?: "<anonymous>")
  }

  companion object {
    @JvmStatic fun startOf(source: String?): SourceLocation = SourceLocation(1, 1, source)
  }

  fun asSingletonSpan(): SourceSpan = SourceSpan(line, column, line, column, source)

  fun nextLine(): SourceLocation = copy(line = line + 1, column = 1)

  fun nextColumn(): SourceLocation = copy(column = column + 1)

  operator fun rangeTo(other: SourceLocation): SourceSpan {
    require(source == other.source) { "cannot span sources from multiple files" }
    return SourceSpan(
        lineFrom = line,
        columnFrom = column,
        lineTo = other.line,
        columnTo = other.column,
        source,
    )
  }
}

data class SourceSpan(
    val lineFrom: Int,
    val columnFrom: Int,
    val lineTo: Int,
    val columnTo: Int,
    val source: String? = null,
) {
  init {
    require(lineFrom <= lineTo) { "cannot range into previous lines" }
    require(lineFrom != lineTo || columnFrom <= columnTo) {
      "cannot range into previous columns in the same line"
    }
  }

  val from: SourceLocation
    get() = SourceLocation(lineFrom, columnFrom)

  val to: SourceLocation
    get() = SourceLocation(lineTo, columnTo)

  operator fun rangeTo(other: SourceSpan): SourceSpan {
    require(source == other.source) { "cannot span sources from multiple files" }
    return SourceSpan(
        lineFrom = lineFrom,
        columnFrom = columnFrom,
        lineTo = other.lineTo,
        columnTo = other.columnTo,
        source,
    )
  }

  override fun toString(): String = buildString {
    if (lineFrom == lineTo) append(lineFrom) else append("$lineFrom-$lineTo")
    append(":")
    if (lineFrom == lineTo && columnFrom == columnTo) append(columnFrom)
    else append("$columnFrom-$columnTo")
    append("@")
    append(source ?: "<anonymous>")
  }
}

interface Localizable {
  val source: SourceSpan
}

abstract class AbstractLocalizable(override val source: SourceSpan) : Localizable

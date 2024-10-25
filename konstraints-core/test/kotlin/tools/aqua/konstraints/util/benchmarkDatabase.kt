/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2024 The Konstraints Authors
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

package tools.aqua.konstraints.util

import kotlinx.serialization.DeserializationStrategy
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import kotlinx.serialization.json.JsonContentPolymorphicSerializer
import kotlinx.serialization.json.JsonElement
import kotlinx.serialization.json.JsonObject

/**
 * A benchmark database corresponding to a full SMT-Lib release. This contains categories indexed by
 * the category name (i.e., `incremental` and `non-incremental`).
 */
@Serializable
@JvmInline
value class BenchmarkDatabase(private val categories: Map<String, BenchmarkCategory>) :
    Map<String, BenchmarkCategory> by categories

/**
 * A benchmark category, containing benchmark sets (represented by the file tree root) indexed by
 * logic name (e.g., `QF_BV`).
 */
@Serializable
@JvmInline
value class BenchmarkCategory(private val sets: Map<String, BenchmarkDatabaseDirectory>) :
    Map<String, BenchmarkDatabaseDirectory> by sets

/** An element in a benchmark file tree. Either a file or a directory. */
@Serializable(with = BenchmarkDatabaseElementSerializer::class)
sealed interface BenchmarkDatabaseElement

/**
 * Convert a file tree element to a sequence of tuples of file objects with their path components
 * inside the archive. This lazily traverses the file tree.
 */
fun BenchmarkDatabaseElement.toFileSequence(
    path: List<String> = emptyList()
): Sequence<Pair<List<String>, BenchmarkDatabaseFile>> =
    when (this) {
      is BenchmarkDatabaseDirectory ->
          entries.asSequence().flatMap { (name, child) -> child.toFileSequence(path + name) }
      is BenchmarkDatabaseFile -> sequenceOf(path to this)
    }

private object BenchmarkDatabaseElementSerializer :
    JsonContentPolymorphicSerializer<BenchmarkDatabaseElement>(BenchmarkDatabaseElement::class) {
  override fun selectDeserializer(
      element: JsonElement
  ): DeserializationStrategy<BenchmarkDatabaseElement> {
    require(element is JsonObject) { "malformed input" }
    return when {
      EXECUTION_SPEEDS_SERIAL in element.keys -> BenchmarkDatabaseFile.serializer()
      else -> BenchmarkDatabaseDirectory.serializer()
    }
  }
}

/** A directory inside a benchmark archive. */
@Serializable
@JvmInline
value class BenchmarkDatabaseDirectory(private val members: Map<String, BenchmarkDatabaseElement>) :
    BenchmarkDatabaseElement, Map<String, BenchmarkDatabaseElement> by members {}

private const val EXECUTION_SPEEDS_SERIAL = "speeds"

/** A file inside a benchmark archive, containing metadata. */
@Serializable
data class BenchmarkDatabaseFile(
    /** Execution speeds on a reference machine indexed by solver. */
    @SerialName(EXECUTION_SPEEDS_SERIAL) val executionSpeeds: Map<String, Double>,
    /** Decompressed size in bytes. */
    @SerialName("size") val fileSizeInBytes: Long = Long.MIN_VALUE,
) : BenchmarkDatabaseElement

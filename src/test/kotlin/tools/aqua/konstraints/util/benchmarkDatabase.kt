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

@Serializable
@JvmInline
value class BenchmarkDatabaseCategory(private val categories: Map<String, BenchmarkDatabaseSet>) :
    Map<String, BenchmarkDatabaseSet> by categories

@Serializable
@JvmInline
value class BenchmarkDatabaseSet(private val sets: Map<String, BenchmarkDatabaseDirectory>) :
    Map<String, BenchmarkDatabaseDirectory> by sets

@Serializable(with = BenchmarkDatabaseElementSerializer::class)
sealed interface BenchmarkDatabaseElement

fun BenchmarkDatabaseElement.toFileSequence(
    path: List<String> = emptyList()
): Sequence<Pair<List<String>, BenchmarkDatabaseFile>> =
    when (this) {
      is BenchmarkDatabaseDirectory ->
          entries.asSequence().flatMap { (name, child) -> child.toFileSequence(path + name) }
      is BenchmarkDatabaseFile -> sequenceOf(path to this)
    }

object BenchmarkDatabaseElementSerializer :
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

@Serializable
@JvmInline
value class BenchmarkDatabaseDirectory(private val members: Map<String, BenchmarkDatabaseElement>) :
    BenchmarkDatabaseElement, Map<String, BenchmarkDatabaseElement> by members {}

private const val EXECUTION_SPEEDS_SERIAL = "speeds"

@Serializable
data class BenchmarkDatabaseFile(
    @SerialName(EXECUTION_SPEEDS_SERIAL) val executionSpeeds: Map<String, Double>
) : BenchmarkDatabaseElement

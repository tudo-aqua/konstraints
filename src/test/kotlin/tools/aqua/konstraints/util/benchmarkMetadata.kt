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

import kotlin.Double.Companion.POSITIVE_INFINITY
import kotlin.math.roundToInt

data class BenchmarkSet(val category: String, val set: String) {
  override fun toString(): String = "$category/$set"
}

data class BenchmarkFile(val name: List<String>, val executionSpeeds: Map<String, Double>) {
  fun speedOn(solver: String): Double = executionSpeeds[solver] ?: POSITIVE_INFINITY

  override fun toString(): String = name.joinToString("/")
}

@JvmInline
value class BenchmarkMetadata(private val benchmarks: Map<BenchmarkSet, Set<BenchmarkFile>>) :
    Map<BenchmarkSet, Set<BenchmarkFile>> by benchmarks

fun BenchmarkDatabaseCategory.toMetadata(): BenchmarkMetadata =
    BenchmarkMetadata(
        entries
            .asSequence()
            .flatMap { (category, sets) ->
              sets.asSequence().map { (set, tree) ->
                BenchmarkSet(category, set) to
                    tree
                        .toFileSequence()
                        .map { (name, file) -> BenchmarkFile(name, file.executionSpeeds) }
                        .toSet()
              }
            }
            .toMap())

inline fun BenchmarkMetadata.filterSets(
    crossinline predicate: (BenchmarkSet) -> Boolean
): BenchmarkMetadata = BenchmarkMetadata(filter { (set, _) -> predicate(set) })

inline fun BenchmarkMetadata.filterFiles(
    crossinline predicate: (BenchmarkFile) -> Boolean
): BenchmarkMetadata = filterSetFiles { _, file -> predicate(file) }

inline fun BenchmarkMetadata.filterSetFiles(
    crossinline predicate: (BenchmarkSet, BenchmarkFile) -> Boolean
): BenchmarkMetadata =
    BenchmarkMetadata(
        entries
            .asSequence()
            .mapNotNull { (set, files) ->
              val filtered = files.filterTo(mutableSetOf()) { predicate(set, it) }
              if (filtered.isNotEmpty()) set to filtered else null
            }
            .toMap())

fun BenchmarkMetadata.selectTests(
    vararg solversToConsider: String,
    maxSpeed: Double = POSITIVE_INFINITY,
    minPerGroup: Int = 1,
    sharePerGroup: Double = 1.0,
    maxPerGroup: Int = Int.MAX_VALUE
): BenchmarkMetadata =
    BenchmarkMetadata(
        entries
            .asSequence()
            .mapNotNull { (set, files) ->
              val filtered =
                  files.selectTests(
                      maxSpeed, minPerGroup, sharePerGroup, maxPerGroup, *solversToConsider)
              if (filtered.isNotEmpty()) set to filtered else null
            }
            .toMap())

private fun Collection<BenchmarkFile>.selectTests(
    maxSpeed: Double,
    minPerGroup: Int,
    sharePerGroup: Double,
    maxPerGroup: Int,
    vararg solversToConsider: String
): Set<BenchmarkFile> {
  return groupBy { it.name.first() }
      .mapValues { (_, filesInGroup) ->
        val candidates =
            filesInGroup
                .mapNotNull { file ->
                  file.getSpeedRatingOrNull(maxSpeed, *solversToConsider)?.let { file to it }
                }
                .sortedByDescending { (_, rating) -> rating }

        val targetSize =
            (candidates.size * sharePerGroup)
                .roundToInt()
                .coerceIn(minPerGroup, maxPerGroup)
                .coerceAtMost(candidates.size)

        candidates.take(targetSize).map { (file, _) -> file }
      }
      .flatMapTo(mutableSetOf()) { (_, unitTests) -> unitTests }
}

private fun BenchmarkFile.getSpeedRatingOrNull(
    maxSpeed: Double,
    vararg solversToConsider: String
): Double? {
  val speeds = solversToConsider.map { executionSpeeds[it] ?: return null }
  if (speeds.any { it > maxSpeed }) return null
  return speeds.average()
}

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

package tools.aqua.konstraints.util

import kotlin.Double.Companion.POSITIVE_INFINITY
import kotlin.math.roundToInt

/**
 * A single benchmark set, identified by the [category] (e.g., `non-incremental`) and the [set] (a
 * SMT-Lib logic, e.g. `QF_BV`).
 */
data class BenchmarkSet(val category: String, val set: String) {
  override fun toString(): String = "$category/$set"
}

/**
 * A single benchmark corresponding to an SMT-Lib file. The [name] describes the path inside the
 * benchmark set *without* the first two components (`category/set`). The [executionSpeeds] describe
 * solver speeds on a reference machine for correctly solved benchmarks (with an aggressive
 * timeout). The [fileSizeInBytes] is the decompressed size.
 */
data class BenchmarkFile(
    val name: List<String>,
    val executionSpeeds: Map<String, Double>,
    val fileSizeInBytes: Long
) {
  /** Get the solution speed on [solver] or [POSITIVE_INFINITY] if no speed is known. */
  fun speedOn(solver: String): Double = executionSpeeds[solver] ?: POSITIVE_INFINITY

  override fun toString(): String = name.joinToString("/")
}

/**
 * The collection of known benchmarks, represented as a mapping from benchmark set objects to sets
 * of files.
 */
@JvmInline
value class BenchmarkMetadata(private val benchmarks: Map<BenchmarkSet, Set<BenchmarkFile>>) :
    Map<BenchmarkSet, Set<BenchmarkFile>> by benchmarks

/**
 * Convert a given [BenchmarkDatabase] (i.e., the JSON structure representation) to a
 * [BenchmarkMetadata] object for simplified access.
 */
fun BenchmarkDatabase.toMetadata(): BenchmarkMetadata =
    BenchmarkMetadata(
        entries
            .asSequence()
            .flatMap { (category, sets) ->
              sets.asSequence().map { (set, tree) ->
                BenchmarkSet(category, set) to
                    tree
                        .toFileSequence()
                        .map { (name, file) ->
                          BenchmarkFile(name, file.executionSpeeds, file.fileSizeInBytes)
                        }
                        .toSet()
              }
            }
            .toMap())

/** Remove sets from a metadata collection that do not satisfy the [predicate]. */
inline fun BenchmarkMetadata.filterSets(
    crossinline predicate: (BenchmarkSet) -> Boolean
): BenchmarkMetadata = BenchmarkMetadata(filter { (set, _) -> predicate(set) })

/**
 * Remove files from a metadata collection that do not satisfy the [predicate]. If all files from a
 * set are discarded, so is the set.
 */
inline fun BenchmarkMetadata.filterFiles(
    crossinline predicate: (BenchmarkFile) -> Boolean
): BenchmarkMetadata = filterSetFiles { _, file -> predicate(file) }

/**
 * Remove files from a metadata collection that do not satisfy the [predicate]. If all files from a
 * set are discarded, so is the set.
 */
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

/**
 * Reduce a metadata collection to files conforming to certain standards. If all files from a set
 * are discarded, so is the set.
 *
 * Selection works as follows:
 * - Only files that have timing information for all [solversToConsider] are retained.
 * - Of those, only files that for *all* [solversToConsider] have timings below or equal to
 *   [maxSpeed] are retained.
 * - For each remaining file, the average speed for all [solversToConsider] is computed.
 * - For each directory in a benchmark set (i.e., one level *below* the logic), the files are
 *   aggregated.
 * - For each directory, retain [sharePerGroup] of the files, but at most [maxPerGroup] and at least
 *   [minPerGroup]. If insufficient files exist, take all.
 */
fun BenchmarkMetadata.selectTests(
    vararg solversToConsider: String,
    maxSpeed: Double = POSITIVE_INFINITY,
    maxSize: Long = Long.MAX_VALUE,
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
                      maxSpeed,
                      maxSize,
                      minPerGroup,
                      sharePerGroup,
                      maxPerGroup,
                      *solversToConsider)
              if (filtered.isNotEmpty()) set to filtered else null
            }
            .toMap())

private fun Collection<BenchmarkFile>.selectTests(
    maxSpeed: Double,
    maxSize: Long,
    minPerGroup: Int,
    sharePerGroup: Double,
    maxPerGroup: Int,
    vararg solversToConsider: String
): Set<BenchmarkFile> {
  return groupBy { it.name.first() }
      .mapValues { (_, filesInGroup) ->
        val candidates =
            filesInGroup
                .filter { file -> file.fileSizeInBytes <= maxSize }
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

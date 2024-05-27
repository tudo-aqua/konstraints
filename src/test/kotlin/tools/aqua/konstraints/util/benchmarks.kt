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

import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.json.Json
import kotlinx.serialization.json.decodeFromStream

data class Benchmark(val set: BenchmarkSet, val file: BenchmarkFile, val program: String) {
  override fun toString(): String = "$set/$file"
}

@OptIn(ExperimentalSerializationApi::class)
fun Any.loadBenchmarkDatabase(): BenchmarkDatabaseCategory =
    javaClass.getResourceAsStream("/benchmarks-metadata.json")!!.use {
      Json.decodeFromStream<BenchmarkDatabaseCategory>(it)
    }

fun Any.loadBenchmarks(metadata: BenchmarkMetadata): Sequence<Benchmark> = sequence {
  metadata.forEach { (set, files) ->
    val lookup = files.associateBy { "${set.category}/${set.set}/${it.name.joinToString("/")}" }
    var matches = 0

    this@loadBenchmarks.javaClass.getResourceAsStream("/${set.category}/${set.set}.tar.zst")!!.use {
      val tar = it.buffered().unzstd().buffered().untar()

      for ((entry, stream) in tar.asEntrySequence()) {
        // abort early if we have discovered all described files
        if (matches == files.size) break

        if (entry.isFile.not()) continue
        val file = lookup[entry.name] ?: continue

        yield(Benchmark(set, file, entry.readText(stream)))

        matches++
      }
    }
  }
}

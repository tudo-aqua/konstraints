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

/**
 * Reentrant version of [MutableMap.computeIfAbsent]. If this map contains [key], the corresponding
 * entry is returned. Else, [mapping] is applied to the [key]. If a side effect of [mapping] caused
 * [key] to be present in the map, [merge] is called with the key, the side effect-computed value,
 * and the function-computed value and the resulting value used.
 */
inline fun <K, V> MutableMap<K, V>.computeIfAbsentAndMerge(
    key: K,
    mapping: (K) -> V,
    merge: (K, V, V) -> V
): V {
  // key already present, return value
  this[key]?.let {
    return it
  }

  val computed = mapping(key)
  val present = this[key]
  if (present != null) {
    // concurrent computation of same key, merge and return
    val merged = merge(key, present, computed)
    this[key] = merged
    return merged
  } else {
    // key not computed, assign and return
    this[key] = computed
    return computed
  }
}

/**
 * Reentrant version of [MutableMap.computeIfAbsent]. If this map contains [key], the corresponding
 * entry is returned. Else, [mapping] is applied to the [key]. If a side effect of [mapping] caused
 * [key] to be present in the map, the side-effect-computed value and function-computed value are
 * required to be equal.
 */
inline fun <K, V> MutableMap<K, V>.computeIfAbsentAndMerge(key: K, mapping: (K) -> V): V =
    computeIfAbsentAndMerge(key, mapping) { _, computed, present ->
      require(computed == present) {
        "the mapping function set $key: $present, but computed $key: $computed"
      }
      computed
    }

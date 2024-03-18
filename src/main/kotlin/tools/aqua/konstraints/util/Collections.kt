/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2023 The Konstraints Authors
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

/* parametricBindings.putIfAbsent(symbolic, actual)?.let {
    require(it == actual) //TODO nice exception
} */

/**
 * Returns a list of pairs built from the elements of this collection and other collection with the
 * same index. Enforces that both lists have the same length.
 */
infix fun <T, R> Iterable<T>.zipWithSameLength(other: Iterable<R>): List<Pair<T, R>> {
  require(this.count() == other.count()) {
    "zipWithSameLength called with Iterable of different length"
  }
  return zip(other)
}

/** Reduce collection or return default value if collection is empty */
inline fun <S, T : S> Iterable<T>.reduceOrDefault(default: S, operation: (acc: S, T) -> S): S {
  return reduceOrNull(operation) ?: default
}

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

package tools.aqua.konstraints.parser.util

class ResettableIterator<T>(private val delegate: Iterator<T>) : Iterator<T> {
  private val cache = mutableListOf<T>()
  private var cacheIndex = 1

  override fun hasNext(): Boolean = (cacheIndex < cache.size) || delegate.hasNext()

  override fun next(): T =
      if (cacheIndex < cache.size) {
            cache[cacheIndex]
          } else {
            delegate.next().also { cache += it }
          }
          .also { cacheIndex++ }

  fun reset(): Iterator<T> {
    cacheIndex = 0
    return this
  }

  fun unwrap(): Iterator<T> {
    check(cacheIndex >= cache.size) { "attempt tu unwrap iterator still caching values" }
    return delegate
  }
}

fun <T> Iterator<T>.checkpoint(): ResettableIterator<T> = ResettableIterator(this)

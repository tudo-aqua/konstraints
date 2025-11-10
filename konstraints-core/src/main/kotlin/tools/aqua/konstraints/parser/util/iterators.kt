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

inline fun <T> PeekableIterator<T>.peekIs(depth: Int = 0, predicate: (T) -> Boolean): Boolean =
    hasNext(depth) && predicate(peek(depth))

inline fun <reified T> PeekableIterator<*>.peekIsInstance(depth: Int = 0): Boolean =
    peekIs(depth) { it is T }

inline fun <T> PeekableIterator<T>.peekIsNot(depth: Int = 0, predicate: (T) -> Boolean): Boolean =
    peekIs(depth, predicate).not()

inline fun <reified T> PeekableIterator<*>.peekIsNotInstance(depth: Int = 0): Boolean =
    peekIsInstance<T>(depth).not()

inline fun <T> PeekableIterator<T>.nextIs(predicate: (T) -> Boolean): Boolean =
    hasNext() && predicate(next())

inline fun <reified T> PeekableIterator<*>.nextIsInstance(): Boolean = nextIs() { it is T }

inline fun <T> PeekableIterator<T>.nextIsNot(predicate: (T) -> Boolean): Boolean =
    nextIs(predicate).not()

inline fun <reified T> PeekableIterator<*>.nextIsNotInstance(): Boolean = nextIsInstance<T>().not()

inline fun <T> PeekableIterator<T>.nextWhile(predicate: (T) -> Boolean): List<T> = buildList {
  while (peekIs(0, predicate)) {
    add(next())
  }
}

fun <T> Iterator<T>.filter(predicate: (T) -> Boolean): Iterator<T> =
    asSequence().filter(predicate).iterator()

inline fun <reified T> Iterator<*>.filterIsInstance(): Iterator<T> =
    asSequence().filterIsInstance<T>().iterator()

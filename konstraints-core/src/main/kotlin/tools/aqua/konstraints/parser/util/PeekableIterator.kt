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

import java.util.LinkedList

open class PeekableIterator<T>(private val delegate: Iterator<T>) : Iterator<T> {

  private var peekBuffer = LinkedList<T>()

  open fun peek(depth: Int = 0): T {
    require(depth >= 0) { "peek depth must be >= 0, was $depth" }
    if (peekBuffer.size <= depth) {
      repeat(depth - peekBuffer.size + 1) { peekBuffer += delegate.next() }
    }
    return peekBuffer[depth]
  }

  override fun hasNext(): Boolean = hasNext(0)

  fun hasNext(depth: Int): Boolean {
    require(depth >= 0) { "peek depth must be >= 0, was $depth" }
    if (peekBuffer.size < depth) {
      repeat(depth - peekBuffer.size) {
        if (!delegate.hasNext()) return false
        peekBuffer += delegate.next()
      }
    }
    return delegate.hasNext()
  }

  override fun next(): T =
      if (peekBuffer.isNotEmpty()) peekBuffer.removeFirst() else delegate.next()
}

fun <T> Iterator<T>.peekable() = this as? PeekableIterator<T> ?: PeekableIterator(this)

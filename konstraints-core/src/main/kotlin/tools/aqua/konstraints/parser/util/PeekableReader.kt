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

import java.io.FilterReader
import java.io.IOException
import java.io.Reader

open class PeekableReader(`in`: Reader) : FilterReader(`in`) {

  private var peekBuffer: Int? = null

  private inline fun <T> actOnBuffer(action: (Int?) -> T): T =
      synchronized(this) { action(peekBuffer) }

  private inline fun <T> actOnBuffer(empty: () -> T, filled: (Int) -> T): T = actOnBuffer {
    it?.let(filled) ?: empty()
  }

  open fun peek(): Int =
      actOnBuffer(empty = { super.read().also { if (it >= 0) peekBuffer = it } }, filled = { it })

  override fun close() = actOnBuffer {
    peekBuffer = null
    super.close()
  }

  override fun read(): Int =
      actOnBuffer(
          empty = { super.read() },
          filled = {
            peekBuffer = null
            it
          },
      )

  override fun read(cbuf: CharArray, off: Int, len: Int): Int =
      actOnBuffer(
          empty = { super.read(cbuf, off, len) },
          filled = {
            peekBuffer = null
            cbuf[off] = it.toChar()
            super.read(cbuf, off + 1, len - 1) + 1
          },
      )

  override fun skip(n: Long): Long =
      actOnBuffer(
          empty = { super.skip(n) },
          filled = {
            peekBuffer = null
            super.skip(n - 1) + 1
          },
      )

  override fun mark(readAheadLimit: Int): Unit = throw IOException("mark/reset not supported")

  override fun reset(): Unit = throw IOException("mark/reset not supported")

  override fun markSupported(): Boolean = false
}

fun Reader.peekable() = this as? PeekableReader ?: PeekableReader(this)

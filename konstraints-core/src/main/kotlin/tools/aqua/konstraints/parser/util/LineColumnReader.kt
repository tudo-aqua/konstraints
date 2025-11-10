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

import java.io.IOException
import java.io.Reader

private const val SKIP_BLOCK_SIZE = 0xFFFF

public open class LineColumnReader(`in`: PeekableReader) : PeekableReader(`in`) {
  private var _lastLine: Int = 1
  val lastLine: Int
    get() = _lastLine

  private var _nextLine: Int = 1
  val nextLine: Int
    get() = _nextLine

  private var _lastColumn: Int = 0
  val lastColumn: Int
    get() = _lastColumn

  private var _nextColumn: Int = 1
  val nextColumn: Int
    get() = _nextColumn

  private fun update(char: Char) {
    _lastLine = _nextLine
    _lastColumn = _nextColumn

    if (char == '\n' || (char == '\r' && peekIsNot { it == '\n' })) {
      _nextLine++
      _nextColumn = 1
    } else {
      _nextColumn++
    }
  }

  private fun update(char: Char, peek: Char) {
    _lastLine = _nextLine
    _lastColumn = _nextColumn

    if (char == '\n' || (char == '\r' && peek != '\n')) {
      _nextLine++
      _nextColumn = 1
    } else {
      _nextColumn++
    }
  }

  override fun read(): Int = super.read().also { if (it >= 0) update(it.toChar()) }

  override fun read(cbuf: CharArray, off: Int, len: Int): Int =
      super.read(cbuf, off, len).also {
        if (it > 0) {
          val lastReadIndex = off + it - 1
          (off..<lastReadIndex).forEach { idx ->
            // these peek in the read buffer
            update(cbuf[idx], cbuf[idx + 1])
          }
          // this needs to peek in the stream, if necessary
          update(cbuf[lastReadIndex])
        }
      }

  override fun skip(n: Long): Long {
    require(n >= 0)
    val size = if (n > SKIP_BLOCK_SIZE) SKIP_BLOCK_SIZE else n.toInt()
    val buffer = CharArray(size)
    // the read operation tracks line/column info
    return read(buffer).toLong()
  }

  override fun mark(readAheadLimit: Int): Unit = throw IOException("mark/reset not supported")

  override fun reset(): Unit = throw IOException("mark/reset not supported")

  override fun markSupported(): Boolean = false
}

fun Reader.lineColumnTracking(): LineColumnReader =
    this as? LineColumnReader ?: LineColumnReader(peekable())

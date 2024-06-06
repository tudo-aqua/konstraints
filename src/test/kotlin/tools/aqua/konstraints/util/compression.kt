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

import java.io.InputStream
import java.nio.charset.Charset
import kotlin.text.Charsets.UTF_8
import org.apache.commons.compress.archivers.tar.TarArchiveEntry
import org.apache.commons.compress.archivers.tar.TarArchiveInputStream
import org.apache.commons.compress.compressors.xz.XZCompressorInputStream
import org.apache.commons.compress.compressors.zstandard.ZstdCompressorInputStream
import org.apache.commons.io.input.BoundedInputStream

/**
 * Wrap this input stream into a bounded input stream that reads at most [size] bytes. Iff
 * [propagateClose] is set, closing the bounded stream closes the complete underlying stream.
 */
fun InputStream.bounded(size: Long, propagateClose: Boolean = true): BoundedInputStream =
    BoundedInputStream.builder()
        .setInputStream(this)
        .setMaxCount(size)
        .setPropagateClose(propagateClose)
        .get()

/** Wraps this input stream into a TAR input stream. */
fun InputStream.untar(): TarArchiveInputStream = TarArchiveInputStream(this)

/** Wraps this input stream into a XZ decompressor stream. */
fun InputStream.unxz(): XZCompressorInputStream = XZCompressorInputStream(this)

/** Wraps this input stream into a Zstandard decompressor stream. */
fun InputStream.unzstd(): ZstdCompressorInputStream = ZstdCompressorInputStream(this)

/**
 * Transforms this TAR archive stream into a sequence of entries consisting of the entry metadata
 * and the archive stream state. Note that this does *not* fork the stream -- if the file is
 * supposed to be read, this must be done *before* consuming the next element!
 */
fun TarArchiveInputStream.asEntrySequence():
    Sequence<Pair<TarArchiveEntry, TarArchiveInputStream>> = sequence {
  var entry = nextEntry
  while (entry != null) {
    yield(entry to this@asEntrySequence)
    entry = nextEntry
  }
}

/** Reads a TAR entry as a byte array from the corresponding stream. */
fun TarArchiveEntry.readBytes(
    from: TarArchiveInputStream,
): ByteArray = from.bounded(size, propagateClose = false).use { it.readBytes() }

/** Reads a TAR entry as a string from the corresponding stream using the given [charset]. */
fun TarArchiveEntry.readText(from: TarArchiveInputStream, charset: Charset = UTF_8): String =
    from.bounded(size, propagateClose = false).bufferedReader(charset).use { it.readText() }

/** Reads a TAR entry as a list of lines from the corresponding stream using the given [charset]. */
fun TarArchiveEntry.readLines(from: TarArchiveInputStream, charset: Charset = UTF_8): List<String> =
    from.bounded(size, propagateClose = false).bufferedReader(charset).use { it.readLines() }

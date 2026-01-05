/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2026 The Konstraints Authors
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

import java.io.Reader

inline fun PeekableReader.peekIs(predicate: (Char) -> Boolean): Boolean =
    peek().let { it >= 0 && predicate(it.toChar()) }

inline fun PeekableReader.peekIsNot(predicate: (Char) -> Boolean): Boolean = peekIs(predicate).not()

inline fun Reader.readIs(predicate: (Char) -> Boolean): Boolean =
    read().let { it >= 0 && predicate(it.toChar()) }

inline fun Reader.readIsNot(predicate: (Char) -> Boolean): Boolean = readIs(predicate).not()

inline fun PeekableReader.readWhile(predicate: (Char) -> Boolean): String = buildString {
  while (peekIs(predicate)) {
    append(read().toChar())
  }
}

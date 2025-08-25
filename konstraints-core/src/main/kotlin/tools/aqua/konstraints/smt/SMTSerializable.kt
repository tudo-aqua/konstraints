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

package tools.aqua.konstraints.smt

import tools.aqua.konstraints.parser.Parser

interface SMTSerializable

/** String representation of a smt keyword. */
class Keyword(val value: String) : SMTSerializable {
  init {
    Parser.reserved.parse(value)
  }

  override fun equals(other: Any?): Boolean =
      if (this === other) true else if (other !is Keyword) false else value == other.value

  override fun hashCode() = value.hashCode()
}

/** String representation of a smt literal. */
class LiteralString(val value: String) : SMTSerializable {
  override fun toString() = value
}

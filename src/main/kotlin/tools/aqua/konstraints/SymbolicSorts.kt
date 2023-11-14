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

package tools.aqua.konstraints

/**
 * BVSort with a symbolic number of bits, only used for binding actual instances of BVSort name must
 * be BitVec so the class can act like a BVSort in the context of binding
 */
// TODO prevent accidental usage of this class in normal sort context
internal class SymbolicBVSort(symbol: SymbolIndex) : BVSort(symbol) {
  constructor(symbol: String) : this(SymbolIndex(symbol))
}

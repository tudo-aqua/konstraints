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

enum class Theories {
  ARRAYS_EX,
  FIXED_SIZE_BIT_VECTORS,
  CORE,
  FLOATING_POINT,
  INTS,
  REALS,
  REALS_INTS,
  STRINGS
}

val ARRAYS_EX_MARKER_SET = setOf(Theories.ARRAYS_EX)
val FIXED_SIZE_BIT_VECTORS_MARKER_SET = setOf(Theories.FIXED_SIZE_BIT_VECTORS)
val CORE_MARKER_SET = setOf(Theories.CORE)
val FLOATING_POINT_MARKER_SET = setOf(Theories.FLOATING_POINT)
val INTS_REALS_INTS_MARKER_SET = setOf(Theories.INTS, Theories.REALS_INTS)
val REALS_REALS_INTS_MARKER_SET = setOf(Theories.REALS, Theories.REALS_INTS)
val REALS_INTS_MARKER_SET = setOf(Theories.REALS_INTS)
val STRINGS_MARKER_SET = setOf(Theories.STRINGS)

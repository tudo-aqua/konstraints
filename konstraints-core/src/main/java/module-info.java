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

/** A library for working with SMT expressions on the JVM. */
module tools.aqua.konstraints {
  // Konstraints' public API is written in Kotlin and exposes Kotlin standard library types
  // (sequences, function types, Pair, ...) throughout, so consumers always need to read them.
  requires transitive kotlin.stdlib;

  exports tools.aqua.konstraints.dsl;
  exports tools.aqua.konstraints.parser;
  exports tools.aqua.konstraints.parser.lexer;
  exports tools.aqua.konstraints.parser.location;
  exports tools.aqua.konstraints.parser.util;
  exports tools.aqua.konstraints.smt;
  exports tools.aqua.konstraints.solvers;
  exports tools.aqua.konstraints.util;
  exports tools.aqua.konstraints.visitors;
}

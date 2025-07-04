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

package tools.aqua.konstraints.parser

import org.petitparser.context.Token
import tools.aqua.konstraints.smt.*

class ParseSymbol(val token: Token) :
    Symbol(
        token.getValue(),
        token.getValue<String>().startsWith('|') && token.getValue<String>().endsWith('|')) {
  val symbol: String = token.getValue()
}

// Terms

data class Pattern(val symbols: List<ParseSymbol>)

data class MatchCase(val pattern: Pattern, val term: Expression<*>)

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

sealed interface ProtoCommand

data class ProtoAssert(val term: ProtoTerm) : ProtoCommand

// TODO what is symbol necessary for here
data class ProtoDeclareConst(val symbol: ParseSymbol, val sort: ProtoSort) : ProtoCommand {
  val name = symbol.token.getValue<String>()
}

data class ProtoDeclareFun(
    val symbol: ParseSymbol,
    val parameters: List<ProtoSort>,
    val sort: ProtoSort
) : ProtoCommand {
  val name = symbol.symbol
}

data class ProtoSetLogic(val logic: Logic) : ProtoCommand

data class ProtoDeclareSort(val symbol: ParseSymbol, val arity: Int) : ProtoCommand {
  val name = symbol.symbol
}

data class ProtoDefineFun(val definition: ProtoFunctionDef) : ProtoCommand

data class ProtoFunctionDef(
    val symbol: ParseSymbol,
    val sortedVars: List<ProtoSortedVar>,
    val sort: ProtoSort,
    val term: ProtoTerm
)

data class ProtoPush(val n: Int) : ProtoCommand

data class ProtoPop(val n: Int) : ProtoCommand

class ParseSymbol(val token: Token) : Symbol(token.getValue(), token.getValue<String>().startsWith('|') && token.getValue<String>().endsWith('|')) {
  val symbol: String = token.getValue()
}

// Sorts

data class ProtoSort(val identifier: Identifier, val sorts: List<ProtoSort>) {
  val name = identifier.symbol.toString()
}

// Terms

// QualIdentifier is also a ProtoTerm because BracketedProtoTerm.terms can be more QualIdentifiers
sealed interface QualIdentifier : ProtoTerm {
  val identifier: Identifier
}

data class SimpleQualIdentifier(override val identifier: Identifier) : QualIdentifier

data class AsQualIdentifier(override val identifier: Identifier, val sort: ProtoSort) :
    QualIdentifier

data class ProtoVarBinding(val symbol: ParseSymbol, val term: ProtoTerm)

data class ProtoSortedVar(val symbol: ParseSymbol, val sort: ProtoSort)

data class Pattern(val symbols: List<ParseSymbol>)

data class MatchCase(val pattern: Pattern, val term: ProtoTerm)

sealed interface ProtoTerm

data class SpecConstantTerm(val specConstant: SpecConstant) : ProtoTerm

data class BracketedProtoTerm(val qualIdentifier: QualIdentifier, val terms: List<ProtoTerm>) :
    ProtoTerm

data class ProtoLet(val bindings: List<ProtoVarBinding>, val term: ProtoTerm) : ProtoTerm

data class ProtoForAll(val sortedVars: List<ProtoSortedVar>, val term: ProtoTerm) : ProtoTerm

data class ProtoExists(val sortedVars: List<ProtoSortedVar>, val term: ProtoTerm) : ProtoTerm

data class ProtoMatch(val term: ProtoTerm, val matchCases: List<MatchCase>) : ProtoTerm

data class ProtoAnnotation(val term: ProtoTerm, val attributes: List<Attribute>) : ProtoTerm

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

package tools.aqua.konstraints.parser

import java.math.BigDecimal
import org.petitparser.context.Token

sealed interface ProtoCommand

data class ProtoAssert(val term: ProtoTerm) : ProtoCommand

data class ProtoDeclareConst(val name: Symbol, val sort: ProtoSort) : ProtoCommand

data class ProtoDeclareFun(val name: Symbol, val parameters: List<ProtoSort>, val sort: ProtoSort) :
    ProtoCommand

data class Symbol(val token: Token)

sealed interface SpecConstant // Token?

data class StringConstant(val string: String) : SpecConstant

data class NumeralConstant(val numeral: Int) : SpecConstant

data class BinaryConstant(val binary: String) : SpecConstant

data class HexConstant(val hexadecimal: String) : SpecConstant

data class DecimalConstant(val decimal: BigDecimal) : SpecConstant

// Identifiers

sealed interface Identifier {
  val symbol: Symbol
}

data class SymbolIdentifier(override val symbol: Symbol) : Identifier

data class IndexedIdentifier(override val symbol: Symbol, val indices: List<Index>) : Identifier

sealed interface Index

data class SymbolIndex(val symbol: Symbol) : Index

data class NumeralIndex(val numeral: Int) : Index

// Sorts

data class ProtoSort(val identifier: Identifier, val sorts: List<ProtoSort>)

// S-Expression

sealed interface SExpression

data class SubSExpression(val subExpressions: List<SExpression>) : SExpression

data class SExpressionConstant(val constant: SpecConstant) : SExpression

data class SExpressionSymbol(val symbol: Symbol) : SExpression

data class SExpressionReserved(val reserved: Token) : SExpression

data class SExpressionKeyword(val keyword: Token) : SExpression

// Attributes

data class Attribute(val keyword: Token, val value: AttributeValue?)

sealed interface AttributeValue

data class ConstantAttributeValue(val constant: SpecConstant) : AttributeValue

data class SymbolAttributeValue(val symbol: Symbol) : AttributeValue

data class SExpressionAttributeValue(val sExpressions: List<SExpression>) : AttributeValue

// Terms

// QualIdentifier is also a ProtoTerm because BracketedProtoTerm.terms can be more QualIdentifiers
sealed interface QualIdentifier : ProtoTerm {
  val identifier: Identifier
}

data class SimpleQualIdentifier(override val identifier: Identifier) : QualIdentifier

data class AsQualIdentifier(override val identifier: Identifier, val sort: ProtoSort) :
    QualIdentifier

data class VarBinding(val symbol: Symbol, val term: ProtoTerm)

data class SortedVar(val symbol: Symbol, val sort: ProtoSort)

data class Pattern(val symbols: List<Symbol>)

data class MatchCase(val pattern: Pattern, val term: ProtoTerm)

sealed interface ProtoTerm

data class SpecConstantTerm(val specConstant: SpecConstant) : ProtoTerm

data class BracketedProtoTerm(val qualIdentifier: QualIdentifier, val terms: List<ProtoTerm>) :
    ProtoTerm

data class ProtoLet(val bindings: List<VarBinding>, val term: ProtoTerm) : ProtoTerm

data class ProtoForAll(val sortedVars: List<SortedVar>, val term: ProtoTerm) : ProtoTerm

data class ProtoExists(val sortedVars: List<SortedVar>, val term: ProtoTerm) : ProtoTerm

data class ProtoMatch(val term: ProtoTerm, val matchCases: List<MatchCase>) : ProtoTerm

data class ProtoExclamation(val term: ProtoTerm, val attributes: List<Attribute>) : ProtoTerm

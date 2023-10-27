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

// TODO(make parser classes internal)

internal sealed interface ProtoCommand

internal data class ProtoAssert(val term: ProtoTerm) : ProtoCommand

internal data class ProtoDeclareConst(val name: Symbol, val sort: ProtoSort) : ProtoCommand

internal data class ProtoDeclareFun(
    val name: Symbol,
    val parameters: List<ProtoSort>,
    val sort: ProtoSort
) : ProtoCommand

internal data class Symbol(val token: Token)

internal sealed interface SpecConstant

internal data class StringConstant(val string: String) : SpecConstant

internal data class NumeralConstant(val numeral: Int) : SpecConstant

internal data class BinaryConstant(val binary: String) : SpecConstant

internal data class HexConstant(val hexadecimal: String) : SpecConstant

internal data class DecimalConstant(val decimal: BigDecimal) : SpecConstant

// Identifiers

internal sealed interface Identifier {
  val symbol: Symbol
}

internal data class SymbolIdentifier(override val symbol: Symbol) : Identifier

internal data class IndexedIdentifier(override val symbol: Symbol, val indices: List<Index>) :
    Identifier

internal sealed interface Index

internal data class SymbolIndex(val symbol: Symbol) : Index

internal data class NumeralIndex(val numeral: Int) : Index

// Sorts

internal data class ProtoSort(val identifier: Identifier, val sorts: List<ProtoSort>)

// S-Expression

internal sealed interface SExpression

internal data class SubSExpression(val subExpressions: List<SExpression>) : SExpression

internal data class SExpressionConstant(val constant: SpecConstant) : SExpression

internal data class SExpressionSymbol(val symbol: Symbol) : SExpression

internal data class SExpressionReserved(val reserved: Token) : SExpression

internal data class SExpressionKeyword(val keyword: Token) : SExpression

// Attributes

internal data class Attribute(val keyword: Token, val value: AttributeValue?)

sealed interface AttributeValue

internal data class ConstantAttributeValue(val constant: SpecConstant) : AttributeValue

internal data class SymbolAttributeValue(val symbol: Symbol) : AttributeValue

internal data class SExpressionAttributeValue(val sExpressions: List<SExpression>) : AttributeValue

// Terms

// QualIdentifier is also a ProtoTerm because BracketedProtoTerm.terms can be more QualIdentifiers
internal sealed interface QualIdentifier : ProtoTerm {
  val identifier: Identifier
}

internal data class SimpleQualIdentifier(override val identifier: Identifier) : QualIdentifier

internal data class AsQualIdentifier(override val identifier: Identifier, val sort: ProtoSort) :
    QualIdentifier

internal data class VarBinding(val symbol: Symbol, val term: ProtoTerm)

internal data class SortedVar(val symbol: Symbol, val sort: ProtoSort)

internal data class Pattern(val symbols: List<Symbol>)

internal data class MatchCase(val pattern: Pattern, val term: ProtoTerm)

internal sealed interface ProtoTerm

internal data class SpecConstantTerm(val specConstant: SpecConstant) : ProtoTerm

internal data class BracketedProtoTerm(
    val qualIdentifier: QualIdentifier,
    val terms: List<ProtoTerm>
) : ProtoTerm

internal data class ProtoLet(val bindings: List<VarBinding>, val term: ProtoTerm) : ProtoTerm

internal data class ProtoForAll(val sortedVars: List<SortedVar>, val term: ProtoTerm) : ProtoTerm

internal data class ProtoExists(val sortedVars: List<SortedVar>, val term: ProtoTerm) : ProtoTerm

internal data class ProtoMatch(val term: ProtoTerm, val matchCases: List<MatchCase>) : ProtoTerm

internal data class ProtoAnnotation(val term: ProtoTerm, val attributes: List<Attribute>) :
    ProtoTerm

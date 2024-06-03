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
import tools.aqua.konstraints.smt.Index
import tools.aqua.konstraints.smt.Logic
import tools.aqua.konstraints.smt.QuotingRule
import tools.aqua.konstraints.smt.Symbol

internal sealed interface ProtoCommand

internal data class ProtoAssert(val term: ProtoTerm) : ProtoCommand

// TODO what is symbol necessary for here
internal data class ProtoDeclareConst(val symbol: ParseSymbol, val sort: ProtoSort) : ProtoCommand {
  val name = symbol.token.getValue<String>()
}

internal data class ProtoDeclareFun(
    val symbol: ParseSymbol,
    val parameters: List<ProtoSort>,
    val sort: ProtoSort
) : ProtoCommand {
  val name = symbol.symbol
}

internal data class ProtoSetLogic(val logic: Logic) : ProtoCommand

internal data class ProtoDeclareSort(val symbol: ParseSymbol, val arity: Int) : ProtoCommand {
  val name = symbol.symbol
}

internal data class ProtoDefineFun(val definition: ProtoFunctionDef) : ProtoCommand

internal data class ProtoFunctionDef(
    val symbol: ParseSymbol,
    val sortedVars: List<ProtoSortedVar>,
    val sort: ProtoSort,
    val term: ProtoTerm
)

internal data class ProtoPush(val n: Int) : ProtoCommand

internal data class ProtoPop(val n: Int) : ProtoCommand

internal class ParseSymbol(val token: Token) : Symbol(token.getValue(), QuotingRule.NONE) {
  val symbol: String = token.getValue()
}

sealed interface SpecConstant

data class StringConstant(val string: String) : SpecConstant

data class NumeralConstant(val numeral: Int) : SpecConstant

/* BinaryConstant of the form #b followed by a non-empty sequence of 0 and 1 characters */
data class BinaryConstant(val binary: String) : SpecConstant {
  /* Number of bits for this binary */
  val bits = binary.length - 2
}

/* Hexadecimal constant of the form
 * #x followed by a non-empty sequence of digits and letters from A to F , capitalized or not
 */
data class HexConstant(val hexadecimal: String) : SpecConstant {
  /* Number of bits for this hexadecimal */
  val bits = (hexadecimal.length - 2) * 4
}

data class DecimalConstant(val decimal: BigDecimal) : SpecConstant

// Identifiers

sealed interface Identifier {
  val symbol: Symbol
}

internal data class SymbolIdentifier(override val symbol: ParseSymbol) : Identifier

internal data class IndexedIdentifier(override val symbol: ParseSymbol, val indices: List<Index>) :
    Identifier

// Sorts

internal data class ProtoSort(val identifier: Identifier, val sorts: List<ProtoSort>) {
  val name = identifier.symbol.toString()
}

// S-Expression

sealed interface SExpression

data class SubSExpression(val subExpressions: List<SExpression>) : SExpression

data class SExpressionConstant(val constant: SpecConstant) : SExpression

data class SExpressionSymbol(val symbol: Symbol) : SExpression

data class SExpressionReserved(val reserved: Token) : SExpression

data class SExpressionKeyword(val keyword: Token) : SExpression

// Attributes

// keyword is a token, so when we pass an Attribute to a solver via set-info, we can generate a
// better failure message
data class Attribute(val keyword: String, val value: AttributeValue?)

sealed interface AttributeValue

data class ConstantAttributeValue(val constant: SpecConstant) : AttributeValue

data class SymbolAttributeValue(val symbol: Symbol) : AttributeValue

data class SExpressionAttributeValue(val sExpressions: List<SExpression>) : AttributeValue

sealed interface OptionValue

data class BooleanOptionValue(val bool: Boolean) : OptionValue

data class StringOptionValue(val sting: String) : OptionValue

data class NumeralOptionValue(val numeral: Int) : OptionValue

data class AttributeOptionValue(val attribute: Attribute) : OptionValue

// Terms

// QualIdentifier is also a ProtoTerm because BracketedProtoTerm.terms can be more QualIdentifiers
internal sealed interface QualIdentifier : ProtoTerm {
  val identifier: Identifier
}

internal data class SimpleQualIdentifier(override val identifier: Identifier) : QualIdentifier

internal data class AsQualIdentifier(override val identifier: Identifier, val sort: ProtoSort) :
    QualIdentifier

internal data class ProtoVarBinding(val symbol: ParseSymbol, val term: ProtoTerm)

internal data class ProtoSortedVar(val symbol: ParseSymbol, val sort: ProtoSort)

internal data class Pattern(val symbols: List<ParseSymbol>)

internal data class MatchCase(val pattern: Pattern, val term: ProtoTerm)

internal sealed interface ProtoTerm

internal data class SpecConstantTerm(val specConstant: SpecConstant) : ProtoTerm

internal data class BracketedProtoTerm(
    val qualIdentifier: QualIdentifier,
    val terms: List<ProtoTerm>
) : ProtoTerm

internal data class ProtoLet(val bindings: List<ProtoVarBinding>, val term: ProtoTerm) : ProtoTerm

internal data class ProtoForAll(val sortedVars: List<ProtoSortedVar>, val term: ProtoTerm) :
    ProtoTerm

internal data class ProtoExists(val sortedVars: List<ProtoSortedVar>, val term: ProtoTerm) :
    ProtoTerm

internal data class ProtoMatch(val term: ProtoTerm, val matchCases: List<MatchCase>) : ProtoTerm

internal data class ProtoAnnotation(val term: ProtoTerm, val attributes: List<Attribute>) :
    ProtoTerm

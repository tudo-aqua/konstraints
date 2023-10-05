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

import org.petitparser.context.Token

sealed interface ProtoCommand {}

data class ProtoAssert(val term: ProtoTerm) : ProtoCommand {}

data class ProtoDeclareConst(val name: Symbol, val sort: ProtoSort) : ProtoCommand {}

data class ProtoDeclareFun(val name: Symbol, val parameters: List<ProtoSort>, val sort: ProtoSort) :
    ProtoCommand {}

data class Symbol(val token: Token)

data class ProtoSort(val identifier: Identifier, val sorts: List<Any>) {}

// QualIdentifier is also a ProtoTerm because BracketedProtoTerm.terms can be more QualIdentifiers
sealed interface QualIdentifier : ProtoTerm {
  val identifier: Identifier
}

data class SimpleQualIdentifier(override val identifier: Identifier) : QualIdentifier

data class AsQualIdentifier(override val identifier: Identifier, val sort: ProtoSort) :
    QualIdentifier

sealed interface ProtoTerm

data class BracketedProtoTerm(val qualIdentifier: QualIdentifier, val terms: List<ProtoTerm>) :
    ProtoTerm

data class ProtoLet(val binding: VarBinding, val term: ProtoTerm, val terms: List<ProtoTerm>) :
    ProtoTerm {}

data class VarBinding(val symbol: Symbol, val term: ProtoTerm) {}

sealed interface Identifier {
  val symbol: Symbol
}

data class SymbolIdentifier(override val symbol: Symbol) : Identifier

data class IndexedIdentifier(override val symbol: Symbol, val indices: List<Index>) : Identifier

sealed interface Index

data class SymbolIndex(val symbol: Symbol) : Index

data class NumeralIndex(val numeral: Int) : Index

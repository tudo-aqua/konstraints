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

object PrintVisitor : Visitor {

  override fun visit(protoAssert: ProtoAssert) {
    println("assert")
    protoAssert.term.accept(this)
  }

  override fun visit(protoDeclareConst: ProtoDeclareConst) {
    println("declare-const")
    println(protoDeclareConst.name)
    protoDeclareConst.sort.accept(this)
  }

  override fun visit(protoDeclareFun: ProtoDeclareFun) {
    println("declare-fun")
    println(protoDeclareFun.name)
    protoDeclareFun.parameters.forEach { it.accept(this) }
    protoDeclareFun.sort.accept(this)
  }

  // Visit functions for all SpecConstant implementations

  override fun visit(stringConstant: StringConstant) {
    println(stringConstant.string)
  }

  override fun visit(numeralConstant: NumeralConstant) {
    println(numeralConstant.numeral)
  }

  override fun visit(binaryConstant: BinaryConstant) {
    println(binaryConstant.binary)
  }

  override fun visit(hexConstant: HexConstant) {
    println(hexConstant.hexadecimal)
  }

  override fun visit(decimalConstant: DecimalConstant) {
    println(decimalConstant.decimal)
  }

  // Visit function for ProtoSort
  override fun visit(protoSort: ProtoSort) {
    println(protoSort.identifier)
    protoSort.sorts.forEach { it.accept(this) }
  }

  // Visit functions for SExpression

  override fun visit(subExpression: SubSExpression) {
    subExpression.subExpressions.forEach { it.accept(this) }
  }

  override fun visit(sExpressionConstant: SExpressionConstant) {
    sExpressionConstant.constant.accept(this)
  }

  override fun visit(sExpressionSymbol: SExpressionSymbol) {
    println(sExpressionSymbol.symbol.token)
  }

  override fun visit(sExpressionReserved: SExpressionReserved) {
    println(sExpressionReserved.reserved)
  }

  override fun visit(sExpressionKeyword: SExpressionKeyword) {
    println(sExpressionKeyword.keyword)
  }

  // Visit functions for ProtoTerms

  override fun visit(simpleQualIdentifier: SimpleQualIdentifier) {
    println(simpleQualIdentifier.identifier)
  }

  override fun visit(asQualIdentifier: AsQualIdentifier) {
    println(asQualIdentifier.identifier)
    asQualIdentifier.sort.accept(this)
  }

  override fun visit(specConstantTerm: SpecConstantTerm) {
    specConstantTerm.specConstant.accept(this)
  }

  override fun visit(bracketedProtoTerm: BracketedProtoTerm) {
    bracketedProtoTerm.qualIdentifier.accept(this)
    bracketedProtoTerm.terms.forEach { it.accept(this) }
  }

  override fun visit(protoLet: ProtoLet) {
    println(protoLet.bindings)
    protoLet.term.accept(this)
  }

  override fun visit(protoForAll: ProtoForAll) {
    println(protoForAll.sortedVars)
    protoForAll.term.accept(this)
  }

  override fun visit(protoExists: ProtoExists) {
    println(protoExists.sortedVars)
    protoExists.term.accept(this)
  }

  override fun visit(protoMatch: ProtoMatch) {
    protoMatch.term.accept(this)
    println(protoMatch.matchCases)
  }

  override fun visit(protoExclamation: ProtoExclamation) {
    protoExclamation.term.accept(this)
    println(protoExclamation.attributes)
  }
}

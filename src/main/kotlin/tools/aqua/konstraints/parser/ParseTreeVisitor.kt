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

import tools.aqua.konstraints.*

object ParseTreeVisitor : CommandVisitor, TermVisitor, SortVisitor {
  override fun visit(protoAssert: ProtoAssert): Assert {
    val term = visit(protoAssert.term)

    require(term.sort is BoolSort)

    return Assert(term as Expression<BoolSort>)
  }

  override fun visit(protoDeclareConst: ProtoDeclareConst): DeclareConst {
    val sort = visit(protoDeclareConst.sort)

    return DeclareConst(SMTSymbol(protoDeclareConst.name.token.getValue()), sort)
  }

  override fun visit(protoDeclareFun: ProtoDeclareFun): DeclareFun {
    val sort = visit(protoDeclareFun.sort)
    val parameters = protoDeclareFun.parameters.map { visit(it) }

    return DeclareFun(SMTSymbol(protoDeclareFun.name.token.getValue()), parameters, sort)
  }

  override fun visit(simpleQualIdentifier: SimpleQualIdentifier): Expression<*> {
    return when (simpleQualIdentifier.identifier.symbol.token.getValue<String>()) {
      "A" -> BasicExpression("A", BoolSort)
      "B" -> BasicExpression("B", BoolSort)
      "C" -> BasicExpression("C", BoolSort)
      "s" -> BasicExpression("s", BVSort(32))
      "t" -> BasicExpression("t", BVSort(32))
      else -> throw IllegalStateException() // TODO UnknownFunctionException
    }
  }

  override fun visit(asQualIdentifier: AsQualIdentifier): Expression<*> {
    TODO("Implement visit AsQualIdentifier")
  }

  override fun visit(specConstantTerm: SpecConstantTerm): Expression<*> {
    TODO("Implement visit SpecConstantTerm")
  }

  override fun visit(bracketedProtoTerm: BracketedProtoTerm): Expression<*> {
    val terms = bracketedProtoTerm.terms.map { visit(it) }

    return when (bracketedProtoTerm.qualIdentifier.identifier.symbol.token.getValue<String>()) {
      "and" -> And(terms as List<Expression<BoolSort>>)
      "or" -> Or(terms as List<Expression<BoolSort>>)
      "xor" -> XOr(terms as List<Expression<BoolSort>>)
      "not" -> Not(terms[0] as Expression<BoolSort>)
      "bvult" -> BVUlt(terms[0] as Expression<BVSort>, terms[1] as Expression<BVSort>)
      else -> throw IllegalStateException() // TODO UnknownFunctionException
    }
  }

  override fun visit(protoLet: ProtoLet): Expression<*> {
    TODO("Implement visit ProtoLet")
  }

  override fun visit(protoForAll: ProtoForAll): Expression<*> {
    TODO("Implement visit ProtoForAll")
  }

  override fun visit(protoExists: ProtoExists): Expression<*> {
    TODO("Implement visit ProtoExists")
  }

  override fun visit(protoMatch: ProtoMatch): Expression<*> {
    TODO("Implement visit ProtoMatch")
  }

  override fun visit(protoExclamation: ProtoExclamation): Expression<*> {
    TODO("Implement visit ProtoExclamation")
  }

  override fun visit(protoSort: ProtoSort): Sort {
    return when (protoSort.identifier.symbol.token.getValue<String>()) {
      "Bool" -> return BoolSort
      "BitVec" ->
          return BVSort(
              ((protoSort.identifier as IndexedIdentifier).indices[0] as NumeralIndex).numeral)
      else ->
          throw IllegalStateException(protoSort.identifier.toString()) // TODO UnknownSortException
    }
  }
}

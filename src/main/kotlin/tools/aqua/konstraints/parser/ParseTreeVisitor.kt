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
import java.math.BigInteger
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.theories.*

internal class ParseTreeVisitor :
    ProtoCommandVisitor, ProtoTermVisitor, ProtoSortVisitor, SpecConstantVisitor {

  var context: Context? = null

  override fun visit(protoAssert: ProtoAssert): Assert {
    val term = visit(protoAssert.term)

    require(term.sort is BoolSort)

    return Assert(term as Expression<BoolSort>)
  }

  override fun visit(protoDeclareConst: ProtoDeclareConst): DeclareConst {
    val sort = visit(protoDeclareConst.sort)

    context?.registerFunction(protoDeclareConst, sort)

    return DeclareConst(Symbol(protoDeclareConst.name), sort)
  }

  override fun visit(protoDeclareFun: ProtoDeclareFun): DeclareFun {
    val sort = visit(protoDeclareFun.sort)
    val parameters = protoDeclareFun.parameters.map { visit(it) }

    context?.registerFunction(protoDeclareFun, parameters, sort)

    return DeclareFun(protoDeclareFun.name.symbol(), parameters, sort)
  }

  override fun visit(protoSetLogic: ProtoSetLogic): SetLogic {
    context = Context(protoSetLogic.logic)

    return SetLogic(protoSetLogic.logic)
  }

  override fun visit(protoDeclareSort: ProtoDeclareSort): DeclareSort {
    context?.registerSort(protoDeclareSort.symbol, protoDeclareSort.arity)

    return DeclareSort(protoDeclareSort.symbol, protoDeclareSort.arity)
  }

  override fun visit(protoDefineFun: ProtoDefineFun): DefineFun {
    val def = visit(protoDefineFun.definition)

    context?.registerFunction(def)

    return DefineFun(def)
  }

  override fun visit(protoFunctionDef: ProtoFunctionDef): FunctionDef<*> {
    val namedParameters = protoFunctionDef.sortedVars.map { visit(it) }

    // add a temporary assertion level where all the named parameters are valid
    // to construct the term
    context?.push(1)
    namedParameters.forEach { context?.registerFunction(it) }

    val funDef =
        FunctionDef(
            protoFunctionDef.symbol,
            namedParameters,
            visit(protoFunctionDef.sort),
            visit(protoFunctionDef.term) as Expression<Sort>)

    // remove the named parameters from the assertion stack
    context?.pop(1)

    return funDef
  }

  override fun visit(protoSortedVar: ProtoSortedVar): SortedVar<*> =
      SortedVar(protoSortedVar.symbol, visit(protoSortedVar.sort))

  override fun visit(protoPush: ProtoPush): Push {
    context?.push(protoPush.n)

    return Push(protoPush.n)
  }

  override fun visit(protoPop: ProtoPop): Pop {
    context?.pop(protoPop.n)

    return Pop(protoPop.n)
  }

  override fun visit(simpleQualIdentifier: SimpleQualIdentifier): Expression<*> {
    val op = context?.getFunction(simpleQualIdentifier.identifier, listOf())

    val functionIndices =
        if (simpleQualIdentifier.identifier is IndexedIdentifier) {
          simpleQualIdentifier.identifier.indices.map { it as NumeralIndex }.toSet()
        } else {
          emptySet()
        }

    if (op != null) {
      return op.buildExpression(listOf(), functionIndices)
    } else if (simpleQualIdentifier.identifier.symbol.toString().startsWith("bv") &&
        simpleQualIdentifier.identifier.symbol.toString().substring(2).toBigIntegerOrNull() !=
            null) {
      // temporary code for (_ bvX n) as context can not handle it right now
      // convert X into binary
      return BVLiteral(
          "#b${simpleQualIdentifier.identifier.symbol.toString().substring(2).toBigInteger().toString(2)}",
          functionIndices.single().numeral)
    } else {
      throw IllegalStateException("Unknown fun ${simpleQualIdentifier.identifier.symbol}")
      // TODO UnknownFunctionException
    }
  }

  override fun visit(asQualIdentifier: AsQualIdentifier): Expression<*> {
    TODO("Implement visit AsQualIdentifier")
  }

  override fun visit(specConstantTerm: SpecConstantTerm): Expression<*> {
    return visit(specConstantTerm.specConstant)
  }

  override fun visit(bracketedProtoTerm: BracketedProtoTerm): Expression<*> {
    val terms = bracketedProtoTerm.terms.map { visit(it) }

    val op =
        context?.getFunction(bracketedProtoTerm.qualIdentifier.identifier.symbol.toString(), terms)

    val functionIndices =
        if (bracketedProtoTerm.qualIdentifier.identifier is IndexedIdentifier) {
          (bracketedProtoTerm.qualIdentifier.identifier as IndexedIdentifier)
              .indices
              .map { it as NumeralIndex }
              .toSet()
        } else {
          emptySet()
        }

    if (op != null) {
      return op.buildExpression(terms, functionIndices)
    } else {
      throw IllegalStateException(
          "Unknown fun ${bracketedProtoTerm.qualIdentifier.identifier.symbol}") // TODO
      // UnknownFunctionException
    }
  }

  override fun visit(protoLet: ProtoLet): Expression<*> {
    val bindings = protoLet.bindings.map { VarBinding(it.symbol, visit(it.term)) }

    val inner = context?.let(bindings) { visit(protoLet.term) }!!

    return LetExpression(inner.sort, bindings, inner as Expression<Sort>)
  }

  override fun visit(protoForAll: ProtoForAll): Expression<*> {
    val sortedVars = protoForAll.sortedVars.map { visit(it) }
    val term = context?.bindVars(sortedVars) { visit(protoForAll.term) }!!

    return ForallExpression(sortedVars, term castTo BoolSort)
  }

  override fun visit(protoExists: ProtoExists): Expression<*> {
    val sortedVars = protoExists.sortedVars.map { visit(it) }
    val term = context?.bindVars(sortedVars) { visit(protoExists.term) }!!

    return ExistsExpression(sortedVars, term castTo BoolSort)
  }

  override fun visit(protoMatch: ProtoMatch): Expression<*> {
    TODO("Implement visit ProtoMatch")
  }

  override fun visit(protoAnnotation: ProtoAnnotation): Expression<*> {
    val term = visit(protoAnnotation.term)

    return AnnotatedExpression(term, protoAnnotation.attributes)
  }

  override fun visit(protoSort: ProtoSort): Sort {
    return context!!.getSort(protoSort)
  }

  override fun visit(stringConstant: StringConstant): Expression<*> {
    TODO("Not yet implemented")
  }

  override fun visit(numeralConstant: NumeralConstant): Expression<*> {
    return if (context?.numeralSort == IntSort) IntLiteral(BigInteger(numeralConstant.numeral))
    else if (context?.numeralSort == RealSort) RealLiteral(BigDecimal(numeralConstant.numeral))
    else throw RuntimeException("Unsupported numeral literal sort ${context?.numeralSort}")
  }

  override fun visit(binaryConstant: BinaryConstant): Expression<*> {
    return BVLiteral(binaryConstant.binary)
  }

  override fun visit(hexConstant: HexConstant): Expression<*> {
    return BVLiteral(hexConstant.hexadecimal)
  }

  override fun visit(decimalConstant: DecimalConstant): Expression<*> {
    return RealLiteral(decimalConstant.decimal)
  }
}

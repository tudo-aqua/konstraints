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
import jdk.jshell.spi.ExecutionControl.NotImplementedException
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.theories.*
import tools.aqua.konstraints.theories.BitVectorExpressionContext
import tools.aqua.konstraints.theories.IntsContext

internal class ParseTreeVisitor :
    ProtoCommandVisitor, ProtoTermVisitor, ProtoSortVisitor, SpecConstantVisitor {

  val context = Context()

  override fun visit(protoAssert: ProtoAssert): Assert {
    val term = visit(protoAssert.term)

    require(term.sort is BoolSort)

    return Assert(term as Expression<BoolSort>)
  }

  override fun visit(protoDeclareConst: ProtoDeclareConst): DeclareConst {
    val sort = visit(protoDeclareConst.sort)

    context.registerFunction(protoDeclareConst, sort)

    return DeclareConst(Symbol(protoDeclareConst.name), sort)
  }

  override fun visit(protoDeclareFun: ProtoDeclareFun): DeclareFun {
    val sort = visit(protoDeclareFun.sort)
    val parameters = protoDeclareFun.parameters.map { visit(it) }

    context.registerFunction(protoDeclareFun, parameters, sort)

    return DeclareFun(protoDeclareFun.name.symbol(), parameters, sort)
  }

  override fun visit(protoSetLogic: ProtoSetLogic): SetLogic {
    when (protoSetLogic.logic) {
      QF_BV -> context.registerTheory(BitVectorExpressionContext)
      QF_IDL -> {
        context.registerTheory(IntsContext)
        context.numeralSort = IntSort
      }
      QF_RDL -> {
        context.registerTheory(RealsContext)
        context.numeralSort = RealSort
      }
      QF_FP -> context.registerTheory(FloatingPointContext)
      // QF_AX uses only ArrayEx with free function and sort symbols, as free sorts are not yet
      // supported
      // load int theory as well for testing purposes
      QF_AX -> {
        context.registerTheory(ArrayExContext)
      }
      else -> throw NotImplementedException("${protoSetLogic.logic} not yet supported")
    }

    return SetLogic(protoSetLogic.logic)
  }

  override fun visit(protoDeclareSort: ProtoDeclareSort): DeclareSort {
    context.registerSort(protoDeclareSort.symbol, protoDeclareSort.arity)

    return DeclareSort(protoDeclareSort.symbol, protoDeclareSort.arity)
  }

  override fun visit(protoDefineFun: ProtoDefineFun): DefineFun {
    val def = visit(protoDefineFun.definition)

    // TODO check if fun exists in current context
    // Expected behaviour like declare fun

    return DefineFun(def)
  }

  override fun visit(protoFunctionDef: ProtoFunctionDef): FunctionDef =
      FunctionDef(
          protoFunctionDef.symbol,
          protoFunctionDef.sortedVars.map { visit(it) },
          visit(protoFunctionDef.sort),
          visit(protoFunctionDef.term))

  override fun visit(protoSortedVar: ProtoSortedVar): SortedVar =
      SortedVar(protoSortedVar.symbol, visit(protoSortedVar.sort))

  override fun visit(simpleQualIdentifier: SimpleQualIdentifier): Expression<*> {
    val op = context.getFunction(simpleQualIdentifier.identifier, listOf())

    if (op != null) {
      return op.buildExpression(listOf(), emptySet())
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
        context.getFunction(bracketedProtoTerm.qualIdentifier.identifier.symbol.toString(), terms)

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

  override fun visit(protoAnnotation: ProtoAnnotation): Expression<*> {
    TODO("Implement visit ProtoExclamation")
  }

  override fun visit(protoSort: ProtoSort): Sort {
    return context.getSort(protoSort)
  }

  override fun visit(stringConstant: StringConstant): Expression<*> {
    TODO("Not yet implemented")
  }

  override fun visit(numeralConstant: NumeralConstant): Expression<*> {
    if (context.numeralSort == IntSort) return IntLiteral(numeralConstant.numeral)
    else if (context.numeralSort == RealSort)
        return RealLiteral(BigDecimal(numeralConstant.numeral))
    else throw RuntimeException("Unsupported numeral literal sort ${context.numeralSort}")
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

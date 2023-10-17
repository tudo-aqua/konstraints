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

interface CommandVisitor {
  // Visit functions for all ProtoCommands
  fun visit(command: ProtoCommand): Command =
      when (command) {
        is ProtoAssert -> visit(command)
        is ProtoDeclareConst -> visit(command)
        is ProtoDeclareFun -> visit(command)
      }

  fun visit(protoAssert: ProtoAssert): Assert

  fun visit(protoDeclareConst: ProtoDeclareConst): DeclareConst

  fun visit(protoDeclareFun: ProtoDeclareFun): DeclareFun
}

interface SpecConstantVisitor {
  // Visit functions for all SpecConstant implementations
  fun visit(specConstant: SpecConstant) {
    when (specConstant) {
      is StringConstant -> visit(specConstant)
      is NumeralConstant -> visit(specConstant)
      is BinaryConstant -> visit(specConstant)
      is HexConstant -> visit(specConstant)
      is DecimalConstant -> visit(specConstant)
    }
  }

  fun visit(stringConstant: StringConstant)

  fun visit(numeralConstant: NumeralConstant)

  fun visit(binaryConstant: BinaryConstant)

  fun visit(hexConstant: HexConstant)

  fun visit(decimalConstant: DecimalConstant)
}

interface SortVisitor {
  fun visit(protoSort: ProtoSort): Sort
}

interface SExpressionVisitor {
  fun visit(sExpression: SExpression) {
    when (sExpression) {
      is SubSExpression -> visit(sExpression)
      is SExpressionConstant -> visit(sExpression)
      is SExpressionSymbol -> visit(sExpression)
      is SExpressionReserved -> visit(sExpression)
      is SExpressionKeyword -> visit(sExpression)
    }
  }

  fun visit(subExpression: SubSExpression)

  fun visit(sExpressionConstant: SExpressionConstant)

  fun visit(sExpressionSymbol: SExpressionSymbol)

  fun visit(sExpressionReserved: SExpressionReserved)

  fun visit(sExpressionKeyword: SExpressionKeyword)
}

interface TermVisitor {
  fun visit(protoTerm: ProtoTerm): Expression<*> =
      when (protoTerm) {
        is SimpleQualIdentifier -> visit(protoTerm)
        is AsQualIdentifier -> visit(protoTerm)
        is SpecConstantTerm -> visit(protoTerm)
        is BracketedProtoTerm -> visit(protoTerm)
        is ProtoLet -> visit(protoTerm)
        is ProtoForAll -> visit(protoTerm)
        is ProtoExists -> visit(protoTerm)
        is ProtoMatch -> visit(protoTerm)
        is ProtoAnnotation -> visit(protoTerm)
      }

  fun visit(simpleQualIdentifier: SimpleQualIdentifier): Expression<*>

  fun visit(asQualIdentifier: AsQualIdentifier): Expression<*>

  fun visit(specConstantTerm: SpecConstantTerm): Expression<*>

  fun visit(bracketedProtoTerm: BracketedProtoTerm): Expression<*>

  fun visit(protoLet: ProtoLet): Expression<*>

  fun visit(protoForAll: ProtoForAll): Expression<*>

  fun visit(protoExists: ProtoExists): Expression<*>

  fun visit(protoMatch: ProtoMatch): Expression<*>

  fun visit(protoAnnotation: ProtoAnnotation): Expression<*>
}

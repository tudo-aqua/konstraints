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

import java.math.BigDecimal
import java.math.BigInteger
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.theories.*

internal class ParseTreeVisitor :
    ProtoCommandVisitor, ProtoTermVisitor, ProtoSortVisitor, SpecConstantVisitor {

  var context: ParseContext? = null

  override fun visit(simpleQualIdentifier: SimpleQualIdentifier): Expression<*> {
    val op = context?.getFunction(simpleQualIdentifier.identifier, listOf())

    val functionIndices =
        if (simpleQualIdentifier.identifier is IndexedIdentifier) {
          simpleQualIdentifier.identifier.indices.map { it as NumeralIndex }
        } else {
          emptyList()
        }

    if (op != null) {
      return op.buildExpression(listOf(), functionIndices)
    } else if (simpleQualIdentifier.identifier.symbol.toString().startsWith("bv") &&
        simpleQualIdentifier.identifier.symbol.toString().substring(2).toBigIntegerOrNull() !=
            null) {
      // temporary code for (_ bvX n) as context can not handle it right now
      // convert X into binary
      return BVLiteral(
          simpleQualIdentifier.identifier.symbol.toString(), functionIndices.single().numeral)
    } else {
      throw IllegalStateException("Unknown fun ${simpleQualIdentifier.identifier.symbol}")
      // TODO UnknownFunctionException
    }
  }

  override fun visit(numeralConstant: NumeralConstant): Expression<*> {
    return if (context?.numeralSort == IntSort) IntLiteral(BigInteger(numeralConstant.numeral))
    else if (context?.numeralSort == RealSort) RealLiteral(BigDecimal(numeralConstant.numeral))
    else throw RuntimeException("Unsupported numeral literal sort ${context?.numeralSort}")
  }
}

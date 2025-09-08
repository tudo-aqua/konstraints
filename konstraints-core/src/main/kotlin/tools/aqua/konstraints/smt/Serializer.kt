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

package tools.aqua.konstraints.smt

/**
 * move to string from commands/expressions to smt string implement to string as name or name
 * indices
 */
object Serializer {
  fun visit(builder: StringBuilder, command: Command) {
    when (command) {
      is Assert -> visit(builder, command)
      CheckSat -> visit(builder, command)
      is DeclareConst<*> -> visit(builder, command)
      is DeclareFun<*> -> visit(builder, command)
      is DeclareSort -> visit(builder, command)
      is DefineConst -> visit(builder, command)
      is DefineFun -> visit(builder, command)
      is DefineSort -> visit(builder, command)
      Exit -> visit(builder, command)
      GetModel -> visit(builder, command)
      is Pop -> visit(builder, command)
      is Push -> visit(builder, command)
      is SetInfo -> visit(builder, command)
      is SetLogic -> visit(builder, command)
      is SetOption -> visit(builder, command)
    }
  }

  fun visit(builder: StringBuilder, expression: Expression<*>) {
    if (expression.children.isEmpty()) {
      builder.append(expression.name.toSMTString(QuotingRule.SAME_AS_INPUT))
    } else {
      builder.append("(${expression.name.toSMTString(QuotingRule.SAME_AS_INPUT)}")
      expression.children.forEach { visit(builder, it) }
      builder.append(")")
    }
  }

  fun visit(builder: StringBuilder, assert: Assert) {
    builder.append("(assert ")
    visit(builder, assert.expr)
    builder.append(")")
  }

  fun visit(builder: StringBuilder, declareConst: DeclareConst<*>) {
    builder.append(
        "(declare-const ${declareConst.name.toSMTString(QuotingRule.SAME_AS_INPUT)} ${declareConst.sort})")
  }

  fun visit(builder: StringBuilder, declareFun: DeclareFun<*>) {
    builder.append(
        "(declare-const ${declareFun.name.toSMTString(QuotingRule.SAME_AS_INPUT)} (${declareFun.parameters.joinToString(" ")}) ${declareFun.sort})")
  }

  fun visit(builder: StringBuilder, checkSat: CheckSat) {
    builder.append("(check-sat)")
  }

  fun visit(builder: StringBuilder, exit: Exit) {
    builder.append("(exit)")
  }

  fun visit(builder: StringBuilder, setInfo: SetInfo) {
    builder.append("(set-info ${setInfo.attribute})")
  }

  fun visit(builder: StringBuilder, setOption: SetOption) {
    builder.append(setOption.toString())
  }

  fun visit(builder: StringBuilder, setLogic: SetLogic) {
    TODO("Not yet implemented")
  }

  fun visit(builder: StringBuilder, declareSort: DeclareSort) {
    TODO("Not yet implemented")
  }

  fun visit(builder: StringBuilder, getModel: GetModel) {
    TODO("Not yet implemented")
  }

  fun visit(builder: StringBuilder, defineConst: DefineConst) {
    TODO("Not yet implemented")
  }

  fun visit(builder: StringBuilder, defineFun: DefineFun) {
    TODO("Not yet implemented")
  }

  fun visit(builder: StringBuilder, push: Push) {
    TODO("Not yet implemented")
  }

  fun visit(builder: StringBuilder, pop: Pop) {
    TODO("Not yet implemented")
  }

  fun visit(builder: StringBuilder, defineSort: DefineSort) {
    TODO("Not yet implemented")
  }
}

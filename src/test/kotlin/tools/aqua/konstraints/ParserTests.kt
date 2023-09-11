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

package tools.aqua.konstraints

import java.lang.Exception
import org.junit.jupiter.api.assertDoesNotThrow
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.ValueSource
import tools.aqua.konstraints.parser.Parser

class ParserTests {
  @ParameterizedTest
  @ValueSource(
      strings =
          [
              "(declare-fun A () Bool)",
              "(declare-fun |A| () Bool)",
              "(declare-fun B () Bool)",
              "(declare-fun C () Bool)",
              "(assert (and (or (not A) (not B)) (xor A B (not C)) (and B (or A C))))",
              "(check-sat)",
              "(declare-fun A (Bool (_ BitVec 32)) (_ BitVec 16))",
              "(declare-fun A (Bool (_ BitVec 32)) Bool)"])
  fun testParse(statement: String) {
    assertDoesNotThrow {
      val root = Parser.createParseTreeV2(statement)

      printTree(root, "")
      println(parseCommand(root.childs.first()))
    }
  }

  fun parseCommand(node: Parser.ParseNode): SimpleCommand {
    when (node.token) {
      "assert" -> {
        require(node.childs.size == 1)
        return Assert(parseBoolExpression(node.childs.first()))
      }
      "declare-fun" -> {
        require(node.childs.size >= 3)
        return DeclareFun(
            SMTSymbol(node.childs[0].token),
            node.childs.subList(1, node.childs.size - 2).map { parseSort(it) },
            parseSort(node.childs.last()))
      }
      "check-sat" -> {
        require(node.childs.isEmpty())
        return CheckSat
      }
      else -> throw Exception()
    }
  }

  fun parseSort(node: Parser.ParseNode): Sort {
    when (node.token) {
      "Bool" -> return BoolSort
      "_" -> {
        require(node.childs.size == 2)
        return parseParametricSort(node)
      }
      else -> throw Exception()
    }
  }

  fun parseParametricSort(node: Parser.ParseNode): Sort {
    when (node.childs[0].token) {
      "BitVec" -> return BVSort(node.childs[1].token.toInt())
      else -> throw Exception()
    }
  }

  fun parseBoolExpression(node: Parser.ParseNode): Expression<BoolSort> {
    when (node.token) {
      "and" -> return And(node.childs.map { parseBoolExpression(it) })
      "or" -> return Or(node.childs.map { parseBoolExpression(it) })
      "xor" -> return XOr(node.childs.map { parseBoolExpression(it) })
      "not" -> {
        require(node.childs.size == 1)
        return Not(parseBoolExpression(node.childs.first()))
      }
      else -> {
        return BasicExpression(node.token, BoolSort)
      }
    }
  }

  fun printTree(node: Parser.ParseNode, prefix: String) {
    println(prefix + node.token)

    node.childs.forEach { printTree(it, "$prefix\t") }
  }
}

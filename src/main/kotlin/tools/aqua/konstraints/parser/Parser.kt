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

import java.lang.Exception

object Parser {
  class ParseNode(var token: String, val parent: ParseNode?) {
    val childs: MutableList<ParseNode> = mutableListOf()
  }

  fun tokenize(string: String, delimiters: List<Char>): List<String> {
    val tokens = mutableListOf<String>()
    var token = ""

    string.forEach {
      if (delimiters.contains(it)) {
        if (token.isNotEmpty()) tokens.add(token)

        token = ""

        tokens.add(it.toString())
      } else {
        token += it
      }
    }

    if (token.isNotEmpty()) tokens.add(token)

    return tokens
  }

  fun createParseTreeV2(statement: String): ParseNode {
    val tokens = tokenize(statement, listOf('(', ')', ' ')).filter { it != " " }

    val root = ParseNode("", null)
    var current = root

    tokens.forEach {
      if (it == "(") {
        val temp = ParseNode("", current)
        current.childs.add(temp)
        current = temp
      } else if (it == ")") {
        if (current.parent != null) {
          current = current.parent!!
        } else {
          throw Exception("Illegal Statement")
        }
      } else if (it != " ") {
        if (current.token.isEmpty()) {
          current.token = it
        } else {
          current.childs.add(ParseNode(it, current))
        }
      }
    }

    return root
  }
}

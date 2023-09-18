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

class ASTVisitor : Visitor {
  override fun visit(node: Node) {
    if (node.token != null) {
      if (PetitParser.reservedCommands.accept(node.token.getValue())) {
        println("Found KW ${node.token}")
      } else if (PetitParser.reservedGeneral.accept(node.token.getValue())) {
        println("Found reserved ${node.token}")
      } else if (PetitParser.specConstant.accept(node.token.getValue())) {
        println("Found specConstant ${node.token}")
      } else if (PetitParser.symbol.accept(node.token.getValue())) {
        println("Found symbol ${node.token}")
      } else if (PetitParser.symbol.accept(node.token.getValue())) {
        println("Found command ${node.token}")
      } else {
        println("Found unknown ${node.token}")
      }
    }

    node.childs.forEach { visit(it) }
  }
}

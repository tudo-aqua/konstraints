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

// TODO ambiguous lookup with params and return type
internal abstract class SortDecl<T : Sort>(val name: String) {
  abstract fun getSort(sort: ProtoSort): T
}

internal class Context {
  fun registerTheory(other: TheoryContext) {
    functions.addAll(other.functions)
    other.sorts.forEach { registerSort(it.value) }
  }

  /* Function is private to not allow illegal FunctionDecl to be registered */
  fun isFunctionLegal(function: FunctionDecl<*>) {
    /*val unambiguous = unambiguousFunctions[function.name]

    if (unambiguous != null) {
      // there already is a function with the same name
      if (unambiguous.accepts(function.params)) {
        // there already is a function with the same name that accepts the same arguments
        if(unambiguous.signature.bindReturnOrNull(function.sort) != null) {
          //there already is a function with this signature
          throw FunctionAlreadyDeclaredException(function)
        } else {
          println("New ambiguous function $function")
          return
        }
      } else {
        println("New overloaded function $function")
        return
      }
    }

    val overloaded = overloadedFunctions[function.name]

    if(overloaded != null) {
      // there already is a family of overloaded functions with the same name

      val conflicts = overloaded.filter { it.accepts(function.params) }

      if(conflicts.isEmpty()) {
        println("New overloaded function $function")
        return
      } else {
        if(conflicts.any { it.signature.bindReturnOrNull(function.sort) != null }) {
          throw FunctionAlreadyDeclaredException(function)
        } else {
          println("New ambiguous function $function")
          return
        }
      }
    }

    val ambiguous = ambiguousFunctions[function.name]

    if (ambiguous != null) {
      // there already is a family of ambiguous functions with the same name

      val conflicts = ambiguous.filter { it.accepts(function.params) }

      if(conflicts.isEmpty()) {
        println("New overloaded ambiguous function $function")
        return
      } else {
        if(conflicts.any { it.signature.bindReturnOrNull(function.sort) != null }) {
          throw FunctionAlreadyDeclaredException(function)
        } else {
          println("New ambiguous function $function")
          return
        }
      }
    }

    println("New unambiguous function $function")*/

    val conflicts = functionLookup[function.name]

    if (conflicts != null) {
      println("Conflicts found $conflicts")

      val conflictParams = conflicts.filter { it.accepts(function.params) }

      if (conflictParams.isNotEmpty()) {
        println("Param conflicts with $conflictParams")

        val conflictReturns =
            conflictParams.filter { it.signature.bindReturnOrNull(function.sort) != null }

        if (conflictReturns.isNotEmpty()) {
          throw FunctionAlreadyDeclaredException(function)
        } else {
          println("New ambiguous $function")
        }
      } else {
        println("New overloaded $function")
      }
    } else {
      println("Register new function $function")
    }
  }

  fun registerFunction(function: FunctionDecl<*>) {
    functions.add(function)
  }

  fun registerFunction(const: ProtoDeclareConst, sort: Sort) {
    functions.add(
        FunctionDecl(const.name.token.getValue(), listOf(), emptySet(), sort, Associativity.NONE))
  }

  fun registerFunction(function: ProtoDeclareFun, parameters: List<Sort>, sort: Sort) {
    if (parameters.isEmpty()) {
      registerFunction(function.name.token.getValue<String>(), listOf(), sort)
    } else {
      registerFunction(function.name.token.getValue<String>(), parameters, sort)
    }
  }

  fun registerFunction(name: String, params: List<Sort>, sort: Sort) {
    registerFunction(FunctionDecl(name, params, emptySet(), sort, Associativity.NONE))
  }

  fun registerSort(sort: SortDecl<*>) {
    if (sorts.containsKey(sort.name))
        throw Exception("Sort ${sort.name} is already defined in context")

    sorts[sort.name] = sort
  }

  /**
   * Returns a function matching the identifier, which accepts the provided arguments Function must
   * not be ambiguous
   */
  fun getFunction(name: Identifier, args: List<Expression<*>>): FunctionDecl<*>? {
    return getFunction(name.symbol.token.getValue<String>(), args)
  }

  /**
   * Returns a function matching the name, which accepts the provided arguments Function must not be
   * ambiguous
   */
  fun getFunction(name: String, args: List<Expression<*>>): FunctionDecl<*>? {
    return functions.find { (it.name == name) && (it.acceptsExpressions(args)) && !it.isAmbiguous }
  }

  /**
   * Returns a function matching the name and sort, which accepts the provided arguments Function
   * can be ambiguous
   */
  fun getFunction(name: String, args: List<Expression<*>>, sort: Sort): FunctionDecl<*>? {
    return functions.find { (it.name == name) && (it.acceptsExpressions(args)) && it.sort == sort }
  }

  fun getSort(protoSort: ProtoSort): Sort {
    return sorts[protoSort.identifier.symbol.token.getValue()]?.getSort(protoSort)
        ?: throw Exception("Unknown sort ${protoSort.identifier.symbol.token.getValue<String>()}")
  }

  private val functions: HashSet<FunctionDecl<*>> = hashSetOf()
  private val sorts: MutableMap<String, SortDecl<*>> = mutableMapOf()

  /*
   * Lookup for all simple functions
   * excludes indexed functions of the form e.g. ((_ extract i j) (_ BitVec m) (_ BitVec n))
   */
  val functionLookup: MutableMap<String, List<FunctionDecl<*>>> = mutableMapOf()

  /*val unambiguousFunctions = UnambiguousLookup()
  val overloadedFunctions: MutableMap<String, List<FunctionDecl<*>>> = mutableMapOf()
  val ambiguousFunctions: MutableMap<String, List<FunctionDecl<*>>> = mutableMapOf()*/
}

internal interface TheoryContext {
  val functions: HashSet<FunctionDecl<*>>
  val sorts: Map<String, SortDecl<*>>
}

internal class UnambiguousLookup {
  val functions: MutableMap<String, FunctionDecl<*>> = mutableMapOf()

  operator fun get(name: String): FunctionDecl<*>? {
    return functions[name]
  }
}

internal class OverloadedLookup {
  val functions: MutableMap<String, List<FunctionDecl<*>>> = mutableMapOf()

  operator fun get(name: String): List<FunctionDecl<*>>? {
    return functions[name]
  }
}

class FunctionAlreadyDeclaredException(func: FunctionDecl<*>) :
    RuntimeException("Function $func has already been declared")

/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2026 The Konstraints Authors
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

/** Model class holding the data of solver return get-model. */
data class Model(val definitions: Map<Symbol, FunctionDef<*>>) {
  constructor(definitions: List<FunctionDef<*>>) : this(definitions.associateBy { def -> def.name })

  /** All definitions that do not have any parameters. */
  val constants: Map<Symbol, FunctionDef<*>> =
      definitions.filter { (symbol, def) -> def.parameters.isEmpty() }

  /** All definitions that have at least one parameter. */
  val functions: Map<Symbol, FunctionDef<*>> =
      definitions.filter { (symbol, def) -> def.parameters.isNotEmpty() }

  /**
   * Get [FunctionDef] by name [symbol].
   *
   * @throws [IllegalArgumentException] if no function with name [symbol] exists
   */
  fun getDefinition(symbol: Symbol) =
      definitions[symbol]
          ?: throw IllegalArgumentException("FunctionDef for $symbol not found in model!")

  /**
   * Get [FunctionDef] by name [symbol].
   *
   * @throws [IllegalArgumentException] if no function with name [symbol] exists
   */
  fun getDefinition(symbol: String) = getDefinition(symbol.toSymbol())

  /**
   * Get [FunctionDef] by name [symbol], automatically casts to [T].
   *
   * @throws [IllegalArgumentException] if no function with name [symbol] exists
   * @throws [DefinitionCastException] if [FunctionDef] is not of sort [T]
   */
  inline fun <reified T : Sort> getDefinition(symbol: Symbol, sort: T) =
      getDefinition(symbol).cast<T>()

  /**
   * Get [FunctionDef] by name [symbol], automatically casts to [T].
   *
   * @throws [IllegalArgumentException] if no function with name [symbol] exists
   * @throws [DefinitionCastException] if [FunctionDef] is not of sort [T]
   */
  inline fun <reified T : Sort> getDefinition(symbol: String, sort: T) =
      getDefinition(symbol.toSymbol(), sort)

  /**
   * Get [FunctionDef] for [func], automatically casts to [SMTFunction.sort].
   *
   * @throws [IllegalArgumentException] if no function that matches [func] exists
   * @throws [DefinitionCastException] if [FunctionDef] is not of sort [SMTFunction.sort]
   */
  inline fun <reified T : Sort> getDefinition(func: SMTFunction<T>) =
      getDefinition(func.symbol, func.sort)

  /** Get [FunctionDef] by name [symbol] or null if no such function exists. */
  fun getDefinitionOrNull(symbol: Symbol) = definitions[symbol]

  /** Get [FunctionDef] by name [symbol] or null if no such function exists. */
  fun getDefinitionOrNull(symbol: String) = getDefinitionOrNull(symbol.toSymbol())

  /**
   * Get [FunctionDef] by name [symbol] or null if no such function exists, automatically casts to
   * [T].
   *
   * @throws [DefinitionCastException] if [FunctionDef] is not of sort [T]
   */
  inline fun <reified T : Sort> getDefinitionOrNull(symbol: Symbol, sort: T) =
      getDefinitionOrNull(symbol)?.cast<T>()

  /**
   * Get [FunctionDef] by name [symbol] or null if no such function exists, automatically casts to
   * [T].
   *
   * @throws [DefinitionCastException] if [FunctionDef] is not of sort [T]
   */
  inline fun <reified T : Sort> getDefinitionOrNull(symbol: String, sort: T) =
      getDefinitionOrNull(symbol.toSymbol(), sort)

  /**
   * Get [FunctionDef] for [func] or null if no such function exists, automatically casts to
   * [SMTFunction.sort].
   *
   * @throws [DefinitionCastException] if [FunctionDef] is not of sort [SMTFunction.sort]
   */
  inline fun <reified T : Sort> getDefinitionOrNull(func: SMTFunction<T>) =
      getDefinitionOrNull(func.symbol, func.sort)

  /**
   * Get [Expression] by name [symbol].
   *
   * @throws [IllegalArgumentException] if no function with name [symbol] exists
   */
  fun getTerm(symbol: Symbol) = getDefinition(symbol).term

  /**
   * Get [Expression] by name [symbol].
   *
   * @throws [IllegalArgumentException] if no function with name [symbol] exists
   */
  fun getTerm(symbol: String) = getDefinition(symbol).term

  /**
   * Get [Expression] by name [symbol], automatically casts to [T].
   *
   * @throws [IllegalArgumentException] if no function with name [symbol] exists
   * @throws [ExpressionCastException] if [FunctionDef] is not of sort [T]
   */
  inline fun <reified T : Sort> getTerm(symbol: Symbol, sort: T) = getTerm(symbol).cast<T>()

  /**
   * Get [Expression] by name [symbol], automatically casts to [T].
   *
   * @throws [IllegalArgumentException] if no function with name [symbol] exists
   * @throws [ExpressionCastException] if [FunctionDef] is not of sort [T]
   */
  inline fun <reified T : Sort> getTerm(symbol: String, sort: T) = getTerm(symbol).cast<T>()

  /**
   * Get [Expression] for [func], automatically casts to [SMTFunction.sort].
   *
   * @throws [IllegalArgumentException] if no function that matches [func] exists
   * @throws [ExpressionCastException] if [FunctionDef] is not of sort [T]
   */
  inline fun <reified T : Sort> getTerm(func: SMTFunction<T>) = getTerm(func.symbol, func.sort)

  /** Get [Expression] by name [symbol] or null if no such function exists. */
  fun getTermOrNull(symbol: Symbol) = getDefinitionOrNull(symbol)?.term

  /** Get [Expression] by name [symbol] or null if no such function exists. */
  fun getTermOrNull(symbol: String) = getDefinitionOrNull(symbol)?.term

  /**
   * Get [Expression] by name [symbol] or null if no such function exists, automatically casts to
   * [T].
   *
   * @throws [ExpressionCastException] if [FunctionDef] is not of sort [T]
   */
  inline fun <reified T : Sort> getTermOrNull(symbol: Symbol, sort: T) =
      getTermOrNull(symbol)?.cast<T>()

  /**
   * Get [Expression] by name [symbol] or null if no such function exists, automatically casts to
   * [T].
   *
   * @throws [ExpressionCastException] if [FunctionDef] is not of sort [T]
   */
  inline fun <reified T : Sort> getTermOrNull(symbol: String, sort: T) =
      getTermOrNull(symbol)?.cast<T>()

  /**
   * Get [Expression] for [func] or null if no such function exists, automatically casts to
   * [SMTFunction.sort].
   *
   * @throws [ExpressionCastException] if [FunctionDef] is not of sort [SMTFunction.sort]
   */
  inline fun <reified T : Sort> getTermOrNull(func: SMTFunction<T>) =
      getTermOrNull(func.symbol, func.sort)

  fun getConstant(symbol: Symbol): Literal<*> {
    require(constants.getValue(symbol).term is Literal<*>) {
      "Unexpected constant term ${constants.getValue(symbol).term}! Please report this as a testcase to the developers of konstraints!"
    }

    return constants.getValue(symbol).term as Literal<*>
  }

  fun getConstant(symbol: String) = getConstant(symbol.toSymbol())

  fun getConstant(func: SMTFunction<BitVecSort>): BitVecLiteral {
    return getConstant(getDefinition(func).term)
  }

  // TODO this only extract the value from a given term implement a version for getting the value
  // associated with an expression
  fun getConstant(term: Expression<BitVecSort>): BitVecLiteral {
    require(term is BitVecLiteral)

    return term
  }

  fun getConstant(func: SMTFunction<IntSort>): IntLiteral {
    return getConstant(getDefinition(func).term)
  }

  fun getConstant(term: Expression<IntSort>): IntLiteral {
    require(term is IntLiteral)

    return term
  }

  fun getConstant(func: SMTFunction<RealSort>): RealLiteral {
    return getConstant(getDefinition(func).term)
  }

  fun getConstant(term: Expression<RealSort>): RealLiteral {
    require(term is RealLiteral)

    return term
  }

  fun getConstant(func: SMTFunction<FPSort>): FloatingPointLiteral {
    return getConstant(getDefinition(func).term)
  }

  fun getConstant(term: Expression<FPSort>): FloatingPointLiteral {
    require(term is FloatingPointLiteral)

    return term
  }

  fun getConstant(func: SMTFunction<StringSort>): StringLiteral {
    return getConstant(getDefinition(func).term)
  }

  fun getConstant(term: Expression<StringSort>): StringLiteral {
    require(term is StringLiteral)

    return term
  }

  @JvmName("getConstantValueBitVecSort")
  fun getConstantValue(func: SMTFunction<BitVecSort>) = getConstant(func).value

  @JvmName("getConstantValueBitVecSort")
  fun getConstantValue(term: Expression<BitVecSort>) = getConstant(term).value

  @JvmName("getConstantValueIntSort")
  fun getConstantValue(func: SMTFunction<IntSort>) = getConstant(func).value

  @JvmName("getConstantValueIntSort")
  fun getConstantValue(term: Expression<IntSort>) = getConstant(term).value

  @JvmName("getConstantValueRealSort")
  fun getConstantValue(func: SMTFunction<RealSort>) = getConstant(func).value

  @JvmName("getConstantValueRealSort")
  fun getConstantValue(term: Expression<RealSort>) = getConstant(term).value

  @JvmName("getConstantValueFloat")
  fun getConstantFloatValue(func: SMTFunction<FPSort>) = getConstant(func).asFloat()

  @JvmName("getConstantValueFloat")
  fun getConstantFloatValue(term: Expression<FPSort>) = getConstant(term).asFloat()

  @JvmName("getConstantValueDouble")
  fun getConstantDoubleValue(func: SMTFunction<FPSort>) = getConstant(func).asDouble()

  @JvmName("getConstantValueDouble")
  fun getConstantDoubleValue(term: Expression<FPSort>) = getConstant(term).asDouble()

  @JvmName("getConstantValueStringSort")
  fun getConstantValue(func: SMTFunction<StringSort>) = getConstant(func).value

  @JvmName("getConstantValueStringSort")
  fun getConstantValue(term: Expression<StringSort>) = getConstant(term).value

  /**
   * This will later hold the functions to convert from solver models to a generic konstraints
   * model.
   */
  companion object
}

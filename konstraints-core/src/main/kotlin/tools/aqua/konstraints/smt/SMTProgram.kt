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

import java.math.BigDecimal
import java.math.BigInteger
import tools.aqua.konstraints.dsl.UserDeclaredSMTFunction0
import tools.aqua.konstraints.dsl.UserDeclaredSMTFunctionN
import tools.aqua.konstraints.dsl.UserDefinedSMTFunction0
import tools.aqua.konstraints.dsl.UserDefinedSMTFunctionN

/** Sat status of an smt program. */
enum class SatStatus {
  SAT, // program is satisfiable
  UNSAT, // program is unsatisfiable
  UNKNOWN, // solver timed out
  PENDING; // solve has not been called yet on program

  override fun toString() =
      when (this) {
        SAT -> "sat"
        UNSAT -> "unsat"
        UNKNOWN -> "unknown"
        PENDING -> "pending"
      }
}

/** Base class for all types of smt program. */
abstract class SMTProgram(commands: List<Command>) : SMTSerializable {
  var model: Model? = null
  var status = SatStatus.PENDING
  var logic: Logic? = null
    protected set

  val context = Context()

  protected val _commands: MutableList<Command> = commands.toMutableList()
  val commands: List<Command>
    get() = _commands.toList()

  protected val _info = mutableMapOf<String, AttributeValue?>()

  /**
   * Get info value associated with [keyword].
   * - [keyword] may or may not contain prefix ':' (e.g. `status` and `:status` both refer to the
   *   same info)
   *
   * @throws [NoSuchInfoException] if no value is associated with [keyword]
   */
  fun info(keyword: String) = infoOrNull(keyword) ?: throw NoSuchInfoException(keyword)

  /**
   * Get info value associated with [keyword] or `null` if no such info exists.
   * - [keyword] may or may not contain prefix ':' (e.g. `status` and `:status` both refer to the
   *   same info)
   */
  fun infoOrNull(keyword: String) = _info[keyword.removePrefix(":")]

  protected val _options = mutableMapOf<String, OptionValue>()

  /**
   * Get option value associated with [keyword].
   * - [keyword] may or may not contain prefix ':' (e.g. `print-success` and `:print-success` both
   *   refer to the same option)
   *
   * @throws [NoSuchInfoException] if no value is associated with [keyword]
   */
  fun option(keyword: String) = optionOrNull(keyword) ?: throw NoSuchOptionException(keyword)

  /**
   * Get option value associated with [keyword] or `null` if no such info exists.
   * - [keyword] may or may not contain prefix ':' (e.g. `print-success` and `:print-success` both
   *   refer to the same option)
   */
  fun optionOrNull(keyword: String) = _options[keyword.removePrefix(":")]

  final override fun toString() = _commands.joinToString(separator = "\n")

  override fun toSMTString(quotingRule: QuotingRule) =
      _commands.joinToString(separator = "\n") { it.toSMTString(quotingRule) }

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule): Appendable {
    var counter = 0
    _commands.forEach {
      if (++counter > 1) builder.append("\n")
      it.toSMTString(builder, quotingRule)
    }

    return builder
  }
}

/** SMT Program with a mutable command list. */
class MutableSMTProgram(commands: List<Command>) : SMTProgram(commands) {

  constructor() : this(emptyList())

  /**
   * Inserts [command] at the end of the program.
   *
   * Checks if [command] is legal w.r.t. the [context]
   */
  @Deprecated(
      "Prefer usage of specialized functions (e.g. assert)",
      level = DeprecationLevel.WARNING,
  )
  fun add(command: Command) {
    add(command, _commands.size)
  }

  /**
   * Inserts [command] at [index] into the program.
   *
   * Checks if [command] is legal w.r.t. the [context]
   */
  @Deprecated(
      "Prefer usage of specialized functions (e.g. assert)",
      level = DeprecationLevel.WARNING,
  )
  fun add(command: Command, index: Int) {
    if (command is Assert) {
      require(command.expr.all { context.contains(it) })
    }

    _commands.add(index, command)
  }

  fun assert(assertion: Assert) {
    check(logic != null) { "Logic must be set before adding assertions!" }

    // check expr is in logic
    assertion.expr.all {
      if (!(it.theories.isEmpty() || it.theories.any { it in logic!!.theories })) {
        throw AssertionOutOfLogicBounds(
            "$it was not in logic bounds: expected any of ${logic!!.theories} but was ${it.theories}"
        )
      } else if (!(it.sort.theories.isEmpty() || it.sort.theories.any { it in logic!!.theories })) {
        throw AssertionOutOfLogicBounds(
            "${it.sort} was not in logic bounds: expected any of ${logic!!.theories} but was ${it.sort.theories}"
        )
      }
      true
    }

    // check all symbols are known
    require(checkContext(assertion.expr))

    _commands.add(assertion)
  }

  private fun checkContext(expr: Expression<*>): Boolean {
    return if (expr is ExistsExpression) {
      context.exists(expr.vars) { checkContext(expr.term) }
    } else if (expr is ForallExpression) {
      context.forall(expr.vars) { checkContext(expr.term) }
    } else if (expr is LetExpression) {
      context.let(expr.bindings) { checkContext(expr.inner) }
    } else if (expr is AnnotatedExpression) {
      checkContext(expr.term)
    } else {
      val result =
          (expr.theories.isNotEmpty() || expr in context) && expr.children.all { checkContext(it) }

      if (!result)
          println(
              "Not in theories ${logic?.theories}: ($expr ${expr.children.joinToString(" ")}) is in ${expr.theories}"
          )

      result
    }
  }

  fun <T : Sort> declareConst(name: Symbol, sort: T): UserDeclaredSMTFunction0<T> {
    val func = UserDeclaredSMTFunction0(name, sort)

    context.addFun(func)
    _commands.add(DeclareConst(func()))

    return func
  }

  fun <T : Sort> declareFun(func: UserDeclaredSMTFunction<T>): UserDeclaredSMTFunction<T> {
    context.addFun(func)
    _commands.add(DeclareFun(func))

    return func
  }

  fun <T : Sort> defineConst(
      name: Symbol,
      sort: T,
      term: Expression<T>,
  ): UserDefinedSMTFunction0<T> {
    val func = UserDefinedSMTFunction0(name, sort, term)
    context.addFun(func)

    _commands.add(DefineConst(name, sort, term))

    return func
  }

  fun <T : Sort> defineFun(func: DefinedSMTFunction<T>): DefinedSMTFunction<T> {
    context.addFun(func)
    _commands.add(DefineFun(func.symbol, func.sortedVars, func.sort, func.term))

    return func
  }

  fun push(n: Int) = context.push(n)

  fun push() = context.push()

  fun push(block: (Context) -> Unit) = context.push(block)

  fun pop(n: Int) = context.pop(n)

  fun setOption(option: SetOption) {
    _options[option.name.removePrefix(":")] = option.value

    _commands.add(option)
  }

  fun setInfo(info: SetInfo) {
    _info[info.attribute.keyword.removePrefix(":")] = info.attribute.value

    _commands.add(info)
  }

  fun declareSort(decl: DeclareSort) {
    context.declareSort(decl)
    _commands.add(decl)
  }

  fun declareSort(name: Symbol, arity: Int) {
    context.declareSort(name, arity)
    _commands.add(DeclareSort(name, arity))
  }

  fun defineSort(name: Symbol, parameters: List<Symbol>, sort: Sort) {
    context.defineSort(name, parameters, sort)
    _commands.add(DefineSort(name, parameters, sort))
  }

  /**
   * Inserts all [commands] at the end of the program
   *
   * For each command checks if it is legal w.r.t. the [context]
   */
  @Deprecated(
      "Prefer usage of specialized functions (e.g. assert)",
      level = DeprecationLevel.WARNING,
  )
  fun addAll(commands: List<Command>) = commands.forEach { add(it) }

  // conflicting jvm signature with setter of property logic
  /**
   * Set logic used by the SMT-Program this should only be done once
   *
   * @throws [RuntimeException] if logic was already set
   */
  @JvmName("setlogic")
  fun setLogic(logic: Logic) {
    if (this.logic != null) {
      throw RuntimeException("Logic already set")
    }

    this.logic = logic
    context.setLogic(logic)

    _commands.add(SetLogic(logic))
  }
}

class DefaultSMTProgram(commands: List<Command>) : SMTProgram(commands)

fun MutableSMTProgram.assert(expr: Expression<BoolSort>) = assert(Assert(expr))

fun MutableSMTProgram.declareFun(name: Symbol, parameters: List<Sort>, sort: Sort) =
    if (parameters.isEmpty()) {
      declareFun(UserDeclaredSMTFunction0(name, sort))
    } else {
      declareFun(UserDeclaredSMTFunctionN(name, sort, parameters))
    }

/*fun <T : Sort> MutableSMTProgram.defineFun(
    name: Symbol,
    parameters: List<Sort>,
    sort: T,
    term: Expression<T>
) = defineFun(UserDefinedSMTFunctionN(name, sort, parameters, term))*/

fun <T : Sort> MutableSMTProgram.defineFun(def: FunctionDef<T>) =
    defineFun(UserDefinedSMTFunctionN(def.name, def.sort, def.parameters, def.term))

fun MutableSMTProgram.setOption(name: String, value: Boolean) =
    setOption(SetOption(name, BooleanOptionValue(value)))

fun MutableSMTProgram.setOption(name: String, value: String) =
    setOption(SetOption(name, StringOptionValue(value)))

fun MutableSMTProgram.setOption(name: String, value: Int) =
    setOption(SetOption(name, NumeralOptionValue(value.toBigInteger())))

fun MutableSMTProgram.setOption(name: String, value: Long) =
    setOption(SetOption(name, NumeralOptionValue(value.toBigInteger())))

fun MutableSMTProgram.setOption(name: String, value: BigInteger) =
    setOption(SetOption(name, NumeralOptionValue(value)))

fun MutableSMTProgram.setOption(name: String, value: OptionValue) =
    setOption(SetOption(name, value))

fun MutableSMTProgram.setInfo(name: String, value: String) =
    setInfo(SetInfo(Attribute(name, ConstantAttributeValue(StringConstant(value)))))

fun MutableSMTProgram.setInfo(name: String, value: Int) =
    setInfo(SetInfo(Attribute(name, ConstantAttributeValue(NumeralConstant(value.toBigInteger())))))

fun MutableSMTProgram.setInfo(name: String, value: Long) =
    setInfo(SetInfo(Attribute(name, ConstantAttributeValue(NumeralConstant(value.toBigInteger())))))

fun MutableSMTProgram.setInfo(name: String, value: BigInteger) =
    setInfo(SetInfo(Attribute(name, ConstantAttributeValue(NumeralConstant(value)))))

fun MutableSMTProgram.setInfo(name: String, value: Float) =
    setInfo(SetInfo(Attribute(name, ConstantAttributeValue(DecimalConstant(value.toBigDecimal())))))

fun MutableSMTProgram.setInfo(name: String, value: Double) =
    setInfo(SetInfo(Attribute(name, ConstantAttributeValue(DecimalConstant(value.toBigDecimal())))))

fun MutableSMTProgram.setInfo(name: String, value: BigDecimal) =
    setInfo(SetInfo(Attribute(name, ConstantAttributeValue(DecimalConstant(value)))))

fun MutableSMTProgram.setInfo(name: String, value: Symbol) =
    setInfo(SetInfo(Attribute(name, SymbolAttributeValue(value))))

class AssertionOutOfLogicBounds(msg: String) : RuntimeException(msg)

class NoSuchInfoException(keyword: String) : RuntimeException("Info $keyword not found!")

class NoSuchOptionException(keyword: String) : RuntimeException("Option $keyword not found!")

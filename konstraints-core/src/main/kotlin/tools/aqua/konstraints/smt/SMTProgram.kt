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

import java.math.BigDecimal
import java.math.BigInteger
import kotlin.let
import tools.aqua.konstraints.dsl.UserDeclaredSMTFunction0
import tools.aqua.konstraints.dsl.UserDeclaredSMTFunctionN
import tools.aqua.konstraints.dsl.UserDefinedSMTFunction0
import tools.aqua.konstraints.dsl.UserDefinedSMTFunctionN
import tools.aqua.konstraints.solvers.Solver
import tools.aqua.konstraints.util.StackOperation
import tools.aqua.konstraints.util.StackOperationType

/** Sat status of an smt program. */
enum class SatStatus {
  SAT, // program is satisfiable
  UNSAT, // program is unsatisfiable
  ERROR, // there was an error during the solving process
  UNKNOWN, // solver timed out
  PENDING; // solve has not been called yet on program

  override fun toString() =
      when (this) {
        SAT -> "sat"
        UNSAT -> "unsat"
        ERROR -> "error"
        UNKNOWN -> "unknown"
        PENDING -> "pending"
      }
}

/**
 * Provides access to all functions that modify the assertion stack inside a push block by
 * forwarding the parameters to the underlying context. All functions that modify the assertion
 * stack are: ``assert``, ``declare-sort``, ``declare-fun``, ``declare-const``, ``define-sort``,
 * ``define-fun``, ``define-fun-rec``, ``define-funs-rec``, ``pop``, ``push``, ``reset`` and
 * ``reset-assertions``
 */
interface PushContext {
  fun assert(assertion: Assert)

  fun assert(expr: Expression<BoolSort>)

  fun <T : Sort> defineFun(
      name: Symbol,
      parameters: List<SortedVar<*>>,
      sort: T,
      term: Expression<T>,
  ): DefinedSMTFunction<T>

    fun <T : Sort> defineFun(
        name: Symbol,
        parameters: List<SortedVar<*>>,
        sort: T,
        term: (List<SortedVar<*>>) -> Expression<T>,
    ): DefinedSMTFunction<T> = defineFun(name, parameters, sort, term(parameters))

  fun <T : Sort> defineFun(def: FunctionDef<T>): DefinedSMTFunction<T>

  fun <T : Sort> declareConst(name: Symbol, sort: T): UserDeclaredSMTFunction0<T>

  fun <T : Sort> declareFun(func: UserDeclaredSMTFunction<T>): UserDeclaredSMTFunction<T>

  // TODO add sort parameter here, this requires some more work on the sort factory in the parser
  fun declareFun(name: Symbol, parameters: List<Sort>, sort: Sort): UserDeclaredSMTFunction<Sort>

  fun <T : Sort> defineConst(
      name: Symbol,
      sort: T,
      term: Expression<T>,
  ): UserDefinedSMTFunction0<T>

  fun <T : Sort> defineFun(func: DefinedSMTFunction<T>): DefinedSMTFunction<T>

  fun push(n: Int)

  fun push() = push(1)

  fun pop() = pop(1)

  fun pop(n: Int)

  fun declareSort(decl: DeclareSort)

  fun declareSort(name: Symbol, arity: Int)

  fun defineSort(name: Symbol, parameters: List<Symbol>, sort: Sort)
}

/** Base class for all types of smt program. */
abstract class SMTProgram(commands: List<Command>) : SMTSerializable {
  var logic: Logic? = null
    protected set

  val context = Context()

  protected val _commands: MutableList<Command> = commands.toMutableList()

  // TODO change to function that concatenates the commands in the correct order and inserts
  // push/pop in the correct places when necessary
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

  override fun toSMTString(quotingRule: QuotingRule, useIterative: Boolean) =
      _commands.joinToString(separator = "\n") { it.toSMTString(quotingRule, useIterative) }

  override fun toSMTString(
      builder: Appendable,
      quotingRule: QuotingRule,
      useIterative: Boolean,
  ): Appendable {
    var counter = 0
    _commands.forEach {
      if (++counter > 1) builder.append("\n")
      it.toSMTString(builder, quotingRule, useIterative)
    }

    return builder
  }
}

/** SMT Program with a mutable command list. */
class MutableSMTProgram(commands: List<Command>) : SMTProgram(commands), PushContext {
  // TODO implement assertion stack more explicitly in the future
  // should also split commands into different lists to give the program more structure
  // this will require changing the visitors and is planned for a future release
  /*
  class AssertionLevel {
    // TODO add sorts
    val definitions = mutableListOf<Declaration<*>>()
    val assertions = mutableListOf<Assert>()
  }

  val assertionLevels = ArrayDeque<AssertionLevel>()
  */

  constructor() : this(emptyList())

  /**
   * Inserts [command] at the end of the program.
   *
   * Checks if [command] is legal w.r.t. the [context]
   */
  internal fun add(command: Command) {
    add(command, _commands.size)
  }

  /**
   * Inserts [command] at [index] into the program.
   *
   * Checks if [command] is legal w.r.t. the [context]
   */
  internal fun add(command: Command, index: Int) {
    if (command is Assert) {
      require(command.expr.all { context.contains(it) })
    }

    _commands.add(index, command)
  }

  override fun assert(assertion: Assert) {
    check(logic != null) { "Logic must be set before adding assertions!" }

    // check expr is in logic
    /*
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
    */

    // check all symbols are known
    checkContext(assertion.expr)

    _commands.add(assertion)
  }

  private fun checkContext(root: Expression<*>) {
    val stack = ArrayDeque<StackOperation<Expression<*>>>()

    if (root is ExistsExpression || root is ForallExpression || root is LetExpression) {
      stack.add(StackOperation(StackOperationType.BIND, root))
    } else {
      stack.add(StackOperation(StackOperationType.NONE, root))
    }

    while (stack.isNotEmpty()) {
      val op = stack.removeLast()

      // let here makes code later more readable and allows for auto-casting of expr
      op.let { (operation, expr) ->
        when (operation) {
          // bind vars when taking binder from the stack
          // also add operation to unbind later
          StackOperationType.BIND -> {
            if (expr is ExistsExpression) {
              context.bindVariables(expr.vars)
              stack.addLast(op.unbind())
            } else if (expr is ForallExpression) {
              context.bindVariables(expr.vars)
              stack.addLast(op.unbind())
            } else if (expr is LetExpression) {
              context.bindVariables(expr.bindings)
              stack.addLast(op.unbind())
            }

            stack.addAll(
                expr.children.map { expression ->
                  if (
                      expression is ExistsExpression ||
                          expression is ForallExpression ||
                          expression is LetExpression
                  ) {
                    StackOperation(StackOperationType.BIND, expression)
                  } else {
                    StackOperation(StackOperationType.NONE, expression)
                  }
                }
            )
          }
          StackOperationType.UNBIND -> {
            context.unbindVariables()
          }
          StackOperationType.NONE -> {
            stack.addAll(
                expr.children.map { expression ->
                  if (
                      expression is ExistsExpression ||
                          expression is ForallExpression ||
                          expression is LetExpression
                  ) {
                    StackOperation(StackOperationType.BIND, expression)
                  } else {
                    StackOperation(StackOperationType.NONE, expression)
                  }
                }
            )

            // actual context check
            // TODO maybe add smt function to expr.func
            if (
                expr.theories.all { it !in logic!!.theories } &&
                    (expr !in context) &&
                    expr !is AnnotatedExpression
            ) {
              throw IllegalArgumentException("Illegal expression $expr!")
            }
          }
          else -> throw IllegalArgumentException()
        }
      }
    }
  }

  override fun <T : Sort> declareConst(name: Symbol, sort: T): UserDeclaredSMTFunction0<T> {
    val func = UserDeclaredSMTFunction0(name, sort)

    context.addFun(func)
    _commands.add(DeclareConst(func()))

    return func
  }

  override fun <T : Sort> declareFun(func: UserDeclaredSMTFunction<T>): UserDeclaredSMTFunction<T> {
    context.addFun(func)
    _commands.add(DeclareFun(func))

    return func
  }

  override fun <T : Sort> defineConst(
      name: Symbol,
      sort: T,
      term: Expression<T>,
  ): UserDefinedSMTFunction0<T> {
    val func = UserDefinedSMTFunction0(name, sort, term)
    context.addFun(func)

    _commands.add(DefineConst(name, sort, term))

    return func
  }

  override fun <T : Sort> defineFun(func: DefinedSMTFunction<T>): DefinedSMTFunction<T> {
    context.addFun(func)
    _commands.add(DefineFun(func.symbol, func.sortedVars, func.sort, func.term))

    return func
  }

  fun <T> push(
      solver: Solver,
      produceModel: Boolean,
      timeout: Long = 5000,
      block: PushContext.() -> T,
  ): Pair<SatStatus, Model?> {
    push()
    this.block()

    val result = solver.solve(this, produceModel, timeout)
    pop()

    return result
  }

  override fun assert(expr: Expression<BoolSort>) = assert(Assert(expr))

  fun MutableSMTProgram.declareFun(name: Symbol, parameters: List<Sort>, sort: Sort) =
      if (parameters.isEmpty()) {
        declareFun(UserDeclaredSMTFunction0(name, sort))
      } else {
        declareFun(UserDeclaredSMTFunctionN(name, sort, parameters))
      }

  override fun <T : Sort> defineFun(
      name: Symbol,
      parameters: List<SortedVar<*>>,
      sort: T,
      term: Expression<T>,
  ) = defineFun(UserDefinedSMTFunctionN(name, sort, parameters, term))

  override fun <T : Sort> defineFun(def: FunctionDef<T>) =
      defineFun(UserDefinedSMTFunctionN(def.name, def.sort, def.parameters, def.term))

  override fun declareFun(name: Symbol, parameters: List<Sort>, sort: Sort) =
      if (parameters.isEmpty()) {
        declareFun(UserDeclaredSMTFunction0(name, sort))
      } else {
        declareFun(UserDeclaredSMTFunctionN(name, sort, parameters))
      }

  override fun push(n: Int) {
    _commands.add(Push(n))
    context.push(n)
    // repeat(n) { assertionLevels.add(AssertionLevel()) }
  }

  override fun pop(n: Int) {
    context.pop(n)

    // remove all commands since last push
    // this is technically unsafe since this can remove commands that do not modify the assertion
    // stack
    // however this is only a temporary solution and inside a push block only functions that modify
    // the assertion stack
    // should be used
    while (_commands.last() !is Push) {
      _commands.removeLast()
    }

    _commands.removeLast()

    // repeat(n) { assertionLevels.removeLast() }
  }

  fun setOption(option: SetOption) {
    _options[option.name.removePrefix(":")] = option.value

    _commands.add(option)
  }

  fun setInfo(info: SetInfo) {
    _info[info.attribute.keyword.removePrefix(":")] = info.attribute.value

    _commands.add(info)
  }

  override fun declareSort(decl: DeclareSort) {
    context.declareSort(decl)
    _commands.add(decl)
  }

  override fun declareSort(name: Symbol, arity: Int) {
    context.declareSort(name, arity)
    _commands.add(DeclareSort(name, arity))
  }

  override fun defineSort(name: Symbol, parameters: List<Symbol>, sort: Sort) {
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

  /**
   * Declare a datatype without any constructors or selectors. This only notifies the program that
   * this datatype exists, constructors still need to be added.
   */
  internal fun declareEmptyDatatype(arity: Int, symbol: Symbol): Datatype {
    val datatype = Datatype(arity, symbol)

    _commands.add(DeclareDatatype(datatype))
    context.addSort(DatatypeFactory(datatype), datatype.symbol)

    return datatype
  }

  internal fun finishDatatype(datatype: Datatype) {
    datatype.constructors.forEach {
      context.addFun(it)
      Testers.constructors.add(it.symbol)
    }

    datatype.selectors.forEach { context.addFun(it) }
  }

  fun declareDatatype(datatype: Datatype) {
    context.addSort(DatatypeFactory(datatype), datatype.symbol)

    datatype.constructors.forEach {
      context.addFun(it)
      Testers.constructors.add(it.symbol)
    }

    datatype.selectors.forEach { context.addFun(it) }

    _commands.add(DeclareDatatype(datatype))
  }
}

class DefaultSMTProgram(commands: List<Command>) : SMTProgram(commands)

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

fun MutableSMTProgram.setInfo(attribute: Attribute) = setInfo(SetInfo(attribute))

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

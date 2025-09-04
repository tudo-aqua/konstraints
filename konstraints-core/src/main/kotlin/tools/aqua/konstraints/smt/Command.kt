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

import java.math.BigInteger

/** Base class for each SMT command. */
sealed class Command(val command: String) {
  final override fun toString(): String = "($command)"
}

/** SMT (check-sat) command. */
object CheckSat : Command("check-sat")

/** SMT (exit) command. */
object Exit : Command("exit")

/** SMT (get-model) command. */
object GetModel : Command("get-model")

/** SMT (assert) command. */
data class Assert(val expr: Expression<BoolSort>) : Command("assert $expr")

/**
 * SMT (declare-const [name] [sort]) command.
 *
 * Declares a new a constant function of [sort] with the given [name]
 */
data class DeclareConst<T : Sort>(val instance: UserDeclaredExpression<T>) :
    Command("declare-const ${instance.name} ${instance.sort}") {
  val func = instance.func
  val name = instance.name
  val sort = instance.sort
}

/**
 * SMT (declare-fun [name] ([parameters]) [sort]) command.
 *
 * Declares a new a function of [sort] with the given [name] and [parameters]
 */
data class DeclareFun<T : Sort>(val func: SMTFunction<T>) :
    Command("declare-fun ${func.symbol.toSMTString()} (${func.parameters.joinToString(" ")}) ${func.sort}") {
  val name = func.symbol
  val parameters = func.parameters
  val sort = func.sort
}

/** SMT (set-info [Attribute.keyword] [Attribute.value]) command. */
data class SetInfo(val attribute: Attribute) :
    Command("set-info $attribute") {
  /** SMT (set-info [keyword] [value]) command */
  constructor(keyword: String, value: AttributeValue?) : this(Attribute(keyword, value))
}

/** SMT Attribute use by [SetInfo]. */
data class Attribute(val keyword: String, val value: AttributeValue?) {
    override fun toString() = "$keyword $value"
}

/** Attribute value base class. */
sealed interface AttributeValue

/** Attribute value of type [SpecConstant]. */
data class ConstantAttributeValue(val constant: SpecConstant) : AttributeValue {
    override fun toString(): String = "$constant"
}

/** Symbolic attribute value. */
data class SymbolAttributeValue(val symbol: Symbol) : AttributeValue {
    override fun toString(): String = symbol.toSMTString()
}

/** SExpression attribute value. */
data class SExpressionAttributeValue(val sExpressions: List<SExpression>) : AttributeValue

/** SMT (declare-sort [name] [arity]) command. */
data class DeclareSort(val name: Symbol, val arity: Int) : Command("declare-sort $name $arity")

/** SMT (define-sort [name] ([sortParameters]) [sort]) command. */
data class DefineSort(val name: Symbol, var sortParameters: List<Symbol>, val sort: Sort) :
    Command("define-sort $name (${sortParameters.joinToString(" ")}) $sort")

// TODO string serialization of OptionValue
/** SMT (set-option [name] [OptionValue]) command. */
data class SetOption(val name: String, val value: OptionValue) : Command("set-option $name $value")

/** SMT Option value used by [SetOption]. */
sealed interface OptionValue

/** Boolean option value. */
data class BooleanOptionValue(val bool: Boolean) : OptionValue

/** String option value. */
data class StringOptionValue(val sting: String) : OptionValue

/** Numeral option value. */
data class NumeralOptionValue(val numeral: BigInteger) : OptionValue

/** Attribute option value. */
data class AttributeOptionValue(val attribute: Attribute) : OptionValue

/** SMT (set-logic [logic]) command. */
data class SetLogic(val logic: Logic) : Command("set-logic $logic")

/** SMT (define-const [name] [sort] [term]) command. */
data class DefineConst(val name: Symbol, val sort: Sort, val term: Expression<Sort>) :
    Command("define-const $name $sort $term")

/** SMT (define-fun [functionDef]) command. */
data class DefineFun(val functionDef: FunctionDef<*>) : Command("define-fun $functionDef") {
  /**
   * SMT (define-fun [functionDef]) command.
   *
   * Automatically construct [functionDef] from individual parameters
   */
  constructor(
      name: Symbol,
      parameters: List<SortedVar<*>>,
      sort: Sort,
      term: Expression<Sort>
  ) : this(FunctionDef(name, parameters, sort, term))
}

/**
 * Function definition object holding, [name], [parameters], [sort] and [term] of a function defined
 * via [DefineFun].
 */
data class FunctionDef<out S : Sort>(
    val name: Symbol,
    val parameters: List<SortedVar<*>>,
    val sort: S,
    val term: Expression<S>
) {
  override fun toString(): String = "$name (${parameters.joinToString(" ")}) $sort $term)"

  fun expand(args: List<Expression<*>>): Expression<*> {
    // term is a placeholder expression using the parameters as expressions
    // we need to build the same term but replace every occurrence of a parameter with
    // the corresponding argument expression
    val bindings = (parameters zip args)

    return term.transform { expr: Expression<*> ->
      // TODO do not check name equality here,
      // its probably better to implement some form of Decl.isInstanceOf(Expression) or
      // Expression.isInstanceOf(Decl)
      if (expr.children.isEmpty()) {
        bindings.find { (param, _) -> param.symbol == expr.name }?.second ?: expr
      } else {
        expr
      }
    }
  }
}

/** SMT (push [n]) command. */
data class Push(val n: Int) : Command("push $n")

/** SMT (pop [n]) command. */
data class Pop(val n: Int) : Command("pop $n")

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
sealed class Command(val command: String) : SMTSerializable {
  override fun toString(): String = "($command)"
}

/** SMT (check-sat) command. */
object CheckSat : Command("check-sat") {
  override fun toSMTString(quotingRule: QuotingRule) = "($command)"

  override fun toSMTString(builder: StringBuilder, quotingRule: QuotingRule) =
      builder.append("($command)")
}

/** SMT (exit) command. */
object Exit : Command("exit") {
  override fun toSMTString(quotingRule: QuotingRule) = "($command)"

  override fun toSMTString(builder: StringBuilder, quotingRule: QuotingRule) =
      builder.append("($command)")
}

/** SMT (get-model) command. */
object GetModel : Command("get-model") {
  override fun toSMTString(quotingRule: QuotingRule) = "($command)"

  override fun toSMTString(builder: StringBuilder, quotingRule: QuotingRule) =
      builder.append("($command)")
}

/** SMT (assert) command. */
data class Assert(val expr: Expression<BoolSort>) : Command("assert") {
  override fun toString() = "(assert $expr)"

  override fun toSMTString(quotingRule: QuotingRule) = "(assert ${expr.toSMTString(quotingRule)})"

  override fun toSMTString(builder: StringBuilder, quotingRule: QuotingRule): StringBuilder {
    builder.append("(assert ")
    expr.toSMTString(builder, quotingRule)
    return builder.append(")")
  }
}

/**
 * SMT (declare-const [name] [sort]) command.
 *
 * Declares a new a constant function of [sort] with the given [name]
 */
data class DeclareConst<T : Sort>(val instance: UserDeclaredExpression<T>) :
    Command("declare-const") {
  val func = instance.func
  val name = instance.name
  val sort = instance.sort

  override fun toString() = "(declare-const ${instance.name} ${instance.sort})"

  override fun toSMTString(quotingRule: QuotingRule) =
      "(declare-const ${instance.name.toSMTString(quotingRule)} ${instance.sort.toSMTString(quotingRule)})"

  override fun toSMTString(builder: StringBuilder, quotingRule: QuotingRule): StringBuilder {
    builder.append("(declare-const ")
    name.toSMTString(builder, quotingRule)
    builder.append(" ")
    sort.toSMTString(builder, quotingRule)
    return builder.append(")")
  }
}

/**
 * SMT (declare-fun [name] ([parameters]) [sort]) command.
 *
 * Declares a new a function of [sort] with the given [name] and [parameters]
 */
data class DeclareFun<T : Sort>(val func: SMTFunction<T>) : Command("declare-fun") {
  val name = func.symbol
  val parameters = func.parameters
  val sort = func.sort

  override fun toString() =
      "(declare-fun ${func.symbol} (${func.parameters.joinToString(" ")}) ${func.sort})"

  override fun toSMTString(quotingRule: QuotingRule) =
      "(declare-fun ${func.symbol.toSMTString(quotingRule)} (${func.parameters.joinToString(" ") {it.toSMTString(quotingRule)}}) ${func.sort.toSMTString(quotingRule)})"

  override fun toSMTString(builder: StringBuilder, quotingRule: QuotingRule): StringBuilder {
    builder.append("(declare-fun ")
    func.symbol.toSMTString(builder, quotingRule)
    builder.append(" ")

    func.parameters.onEach {
      it.toSMTString(builder, quotingRule)
      builder.append(" ")
    }

    sort.toSMTString(builder, quotingRule)
    return builder.append(")")
  }
}

/** SMT (set-info [Attribute.keyword] [Attribute.value]) command. */
data class SetInfo(val attribute: Attribute) : Command("set-info") {
  /** SMT (set-info [keyword] [value]) command */
  constructor(keyword: String, value: AttributeValue?) : this(Attribute(keyword, value))

  override fun toString() = "(set-info $attribute)"

  override fun toSMTString(quotingRule: QuotingRule) = toString()

  override fun toSMTString(builder: StringBuilder, quotingRule: QuotingRule) =
      builder.append(toString())
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
  override fun toString(): String = symbol.toSMTString(QuotingRule.SAME_AS_INPUT)
}

/** SExpression attribute value. */
data class SExpressionAttributeValue(val sExpressions: List<SExpression>) : AttributeValue {
  override fun toString() = sExpressions.joinToString(separator = " ", prefix = "(", postfix = ")")
}

/** SMT (declare-sort [name] [arity]) command. */
data class DeclareSort(val name: Symbol, val arity: Int) : Command("declare-sort") {
  override fun toString() = "(declare-sort $name $arity)"

  override fun toSMTString(quotingRule: QuotingRule) = toString()

  override fun toSMTString(builder: StringBuilder, quotingRule: QuotingRule) =
      builder.append(toString())
}

/** SMT (define-sort [name] ([sortParameters]) [sort]) command. */
data class DefineSort(val name: Symbol, var sortParameters: List<Symbol>, val sort: Sort) :
    Command("define-sort") {
  override fun toString() = "define-sort $name (${sortParameters.joinToString(" ")}) $sort"

  override fun toSMTString(quotingRule: QuotingRule) = toString()

  override fun toSMTString(builder: StringBuilder, quotingRule: QuotingRule) =
      builder.append(toString())
}

// TODO string serialization of OptionValue
/** SMT (set-option [name] [OptionValue]) command. */
data class SetOption(val name: String, val value: OptionValue) : Command("set-option") {
  override fun toString() = "(set-option $name $value)"

  override fun toSMTString(quotingRule: QuotingRule) = toString()

  override fun toSMTString(builder: StringBuilder, quotingRule: QuotingRule) =
      builder.append(toString())
}

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
data class SetLogic(val logic: Logic) : Command("set-logic") {
  override fun toString() = "(set-logic $logic)"

  override fun toSMTString(quotingRule: QuotingRule) = toString()

  override fun toSMTString(builder: StringBuilder, quotingRule: QuotingRule) =
      builder.append(toString())
}

/** SMT (define-const [name] [sort] [term]) command. */
data class DefineConst(val name: Symbol, val sort: Sort, val term: Expression<Sort>) :
    Command("define-const") {
  override fun toString() = "(define-const $name $sort $term)"

  override fun toSMTString(quotingRule: QuotingRule) = toString()

  override fun toSMTString(builder: StringBuilder, quotingRule: QuotingRule) =
      builder.append(toString())
}

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

  override fun toString() = ""

  override fun toSMTString(quotingRule: QuotingRule) = toString()

  override fun toSMTString(builder: StringBuilder, quotingRule: QuotingRule) =
      builder.append(toString())
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
  override fun toString(): String = "$name (${parameters.joinToString(" ")}) $sort $term"

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
data class Push(val n: Int) : Command("push") {
  override fun toString() = "(push $n)"

  override fun toSMTString(quotingRule: QuotingRule) = toString()

  override fun toSMTString(builder: StringBuilder, quotingRule: QuotingRule) =
      builder.append(toString())
}

/** SMT (pop [n]) command. */
data class Pop(val n: Int) : Command("pop") {
  override fun toString() = "(pop $n)"

  override fun toSMTString(quotingRule: QuotingRule) = toString()

  override fun toSMTString(builder: StringBuilder, quotingRule: QuotingRule) =
      builder.append(toString())
}

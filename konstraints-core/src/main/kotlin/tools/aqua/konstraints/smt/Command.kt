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

import java.math.BigInteger

/** Base class for each SMT command. */
sealed class Command(val command: String) : SMTSerializable {
  override fun toString(): String = "($command)"
}

/** SMT (check-sat) command. */
object CheckSat : Command("check-sat") {
  override fun toSMTString(quotingRule: QuotingRule) = "($command)"

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule): Appendable =
      builder.append("($command)")
}

/** SMT (exit) command. */
object Exit : Command("exit") {
  override fun toSMTString(quotingRule: QuotingRule) = "($command)"

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule): Appendable =
      builder.append("($command)")
}

/** SMT (get-model) command. */
object GetModel : Command("get-model") {
  override fun toSMTString(quotingRule: QuotingRule) = "($command)"

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule): Appendable =
      builder.append("($command)")
}

/** SMT (assert) command. */
data class Assert(val expr: Expression<BoolSort>) : Command("assert") {
  override fun toString() = "(assert $expr)"

  override fun toSMTString(quotingRule: QuotingRule) = "(assert ${expr.toSMTString(quotingRule)})"

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule): Appendable {
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

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule): Appendable {
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
      "declare-fun ${func.symbol} (${func.parameters.joinToString(" ")}) ${func.sort}"

  override fun toSMTString(quotingRule: QuotingRule) =
      "(declare-fun ${func.symbol.toSMTString(quotingRule)} (${func.parameters.joinToString(" ") {it.toSMTString(quotingRule)}}) ${func.sort.toSMTString(quotingRule)})"

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule): Appendable {
    builder.append("(declare-fun ")
    func.symbol.toSMTString(builder, quotingRule)
    builder.append(" (")

    var counter = 0
    func.parameters.forEach {
      if (++counter > 1) builder.append(" ")
      it.toSMTString(builder, quotingRule)
    }
    builder.append(") ")

    sort.toSMTString(builder, quotingRule)
    return builder.append(")")
  }
}

/** SMT (set-info [Attribute.keyword] [Attribute.value]) command. */
data class SetInfo(val attribute: Attribute) : Command("set-info") {
  /** SMT (set-info [keyword] [value]) command */
  constructor(keyword: String, value: AttributeValue?) : this(Attribute(keyword, value))

  override fun toString() = "set-info $attribute"

  override fun toSMTString(quotingRule: QuotingRule) =
      "(set-info ${attribute.toSMTString(quotingRule)})"

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule): Appendable {
    builder.append("(set-info ")
    attribute.toSMTString(builder, quotingRule)
    return builder.append(")")
  }
}

/** SMT Attribute use by [SetInfo]. */
data class Attribute(val keyword: String, val value: AttributeValue?) : SMTSerializable {
  override fun toString() = "$keyword $value"

  override fun toSMTString(quotingRule: QuotingRule) =
      "$keyword ${value?.toSMTString(quotingRule) ?: ""}"

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule): Appendable {
    builder.append(keyword)
    value?.let {
      builder.append(" ")
      it.toSMTString(builder, quotingRule)
    }
    return builder
  }
}

/** Attribute value base class. */
sealed interface AttributeValue : SMTSerializable

/** Attribute value of type [SpecConstant]. */
data class ConstantAttributeValue(val constant: SpecConstant) : AttributeValue {
  override fun toString(): String = "$constant"

  override fun toSMTString(quotingRule: QuotingRule) = constant.toString()

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule): Appendable =
      builder.append(constant.toString())
}

/** Symbolic attribute value. */
data class SymbolAttributeValue(val symbol: Symbol) : AttributeValue {
  override fun toString(): String = symbol.toSMTString(QuotingRule.SAME_AS_INPUT)

  override fun toSMTString(quotingRule: QuotingRule) = symbol.toSMTString(quotingRule)

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule): Appendable =
      symbol.toSMTString(builder, quotingRule)
}

/** SExpression attribute value. */
data class SExpressionAttributeValue(val sExpressions: List<SExpression>) : AttributeValue {
  override fun toString() = sExpressions.joinToString(separator = " ", prefix = "(", postfix = ")")

  override fun toSMTString(quotingRule: QuotingRule): String {
    TODO("Not yet implemented")
  }

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule): Appendable {
    TODO("Not yet implemented")
  }
}

/** SMT (declare-sort [name] [arity]) command. */
data class DeclareSort(val name: Symbol, val arity: Int) : Command("declare-sort") {
  override fun toString() = "declare-sort $name $arity"

  override fun toSMTString(quotingRule: QuotingRule) =
      "(declare-sort ${name.toSMTString(quotingRule)} $arity)"

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule): Appendable {
    builder.append("(declare-sort ")
    name.toSMTString(builder, quotingRule)
    return builder.append(" $arity)")
  }
}

/** SMT (define-sort [name] ([sortParameters]) [sort]) command. */
data class DefineSort(val name: Symbol, var sortParameters: List<Symbol>, val sort: Sort) :
    Command("define-sort") {
  override fun toString() = "define-sort $name (${sortParameters.joinToString(" ")}) $sort"

  override fun toSMTString(quotingRule: QuotingRule) =
      "(define-sort ${name.toSMTString(quotingRule)} (${sortParameters.joinToString(" "){ it.toSMTString(quotingRule) }}) ${sort.toSMTString(quotingRule)})"

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule): Appendable {
    builder.append(" (define-sort ")
    name.toSMTString(builder, quotingRule)
    builder.append(" (")

    var counter = 0
    sortParameters.forEach {
      if (++counter > 1) builder.append(" ")
      it.toSMTString(builder, quotingRule)
    }
    builder.append(") ")

    sort.toSMTString(builder, quotingRule)
    return builder.append(")")
  }
}

// TODO string serialization of OptionValue
/** SMT (set-option [name] [OptionValue]) command. */
data class SetOption(val name: String, val value: OptionValue) : Command("set-option") {
  override fun toString() = "(set-option $name $value)"

  override fun toSMTString(quotingRule: QuotingRule) =
      "(set-option $name ${value.toSMTString(quotingRule)})"

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule): Appendable {
    builder.append("(set-option $name ")
    value.toSMTString(builder, quotingRule)
    return builder.append(")")
  }
}

/** SMT Option value used by [SetOption]. */
sealed interface OptionValue : SMTSerializable

/** Boolean option value. */
data class BooleanOptionValue(val bool: Boolean) : OptionValue {
  override fun toSMTString(quotingRule: QuotingRule) = bool.toString()

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule) =
      builder.append(bool.toString())
}

/** String option value. */
data class StringOptionValue(val string: String) : OptionValue {
  override fun toSMTString(quotingRule: QuotingRule) = string

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule): Appendable =
      builder.append(string)
}

/** Numeral option value. */
data class NumeralOptionValue(val numeral: BigInteger) : OptionValue {
  override fun toSMTString(quotingRule: QuotingRule) = numeral.toString()

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule): Appendable =
      builder.append(numeral.toString())
}

/** Attribute option value. */
data class AttributeOptionValue(val attribute: Attribute) : OptionValue {
  override fun toSMTString(quotingRule: QuotingRule) = attribute.toSMTString(quotingRule)

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule): Appendable =
      attribute.toSMTString(builder, quotingRule)
}

/** SMT (set-logic [logic]) command. */
data class SetLogic(val logic: Logic) : Command("set-logic") {
  override fun toString() = "(set-logic $logic)"

  override fun toSMTString(quotingRule: QuotingRule) = toString()

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule): Appendable =
      builder.append(toString())
}

/** SMT (define-const [name] [sort] [term]) command. */
data class DefineConst(val name: Symbol, val sort: Sort, val term: Expression<Sort>) :
    Command("define-const") {
  override fun toString() = "(define-const $name $sort $term)"

  override fun toSMTString(quotingRule: QuotingRule) =
      "(define-const ${name.toSMTString(quotingRule)} ${sort.toSMTString(quotingRule)} ${term.toSMTString(quotingRule)})"

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule): Appendable {
    builder.append("(define-const ")

    name.toSMTString(builder, quotingRule)
    builder.append(" ")
    sort.toSMTString(builder, quotingRule)
    builder.append(" ")
    term.toSMTString(builder, quotingRule)

    return builder.append(")")
  }
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
      term: Expression<Sort>,
  ) : this(FunctionDef(name, parameters, sort, term))

  override fun toString() = "(define-fun $functionDef)"

  override fun toSMTString(quotingRule: QuotingRule) =
      "(define-fun ${functionDef.name.toSMTString(quotingRule)} (${functionDef.parameters.joinToString(" "){it.toSMTString(quotingRule)}}) ${functionDef.sort.toSMTString(quotingRule)} ${functionDef.term.toSMTString(quotingRule)})"

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule): Appendable {
    builder.append("(define-fun ")
    functionDef.name.toSMTString(builder, quotingRule)
    builder.append(" (")

    var counter = 0
    functionDef.parameters.forEach {
      if (++counter > 1) builder.append(" ")
      it.toSMTString(builder, quotingRule)
    }
    builder.append(") ")

    functionDef.sort.toSMTString(builder, quotingRule)
    builder.append(" ")
    functionDef.term.toSMTString(builder, quotingRule)
    return builder.append(")")
  }
}

/**
 * Function definition object holding, [name], [parameters], [sort] and [term] of a function defined
 * via [DefineFun].
 */
data class FunctionDef<out S : Sort>(
    val name: Symbol,
    val parameters: List<SortedVar<*>>,
    val sort: S,
    val term: Expression<S>,
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

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule): Appendable =
      builder.append(toString())
}

/** SMT (pop [n]) command. */
data class Pop(val n: Int) : Command("pop") {
  override fun toString() = "(pop $n)"

  override fun toSMTString(quotingRule: QuotingRule) = toString()

  override fun toSMTString(builder: Appendable, quotingRule: QuotingRule): Appendable =
      builder.append(toString())
}

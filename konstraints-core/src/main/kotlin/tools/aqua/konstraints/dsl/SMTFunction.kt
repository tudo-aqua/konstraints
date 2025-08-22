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

package tools.aqua.konstraints.dsl

import java.util.*
import kotlin.reflect.KProperty
import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.util.SimpleDelegate

/**
 * Declares an SMT constant: (declare-const |const!sort!UUID| [sort]).
 *
 * The name of the constant is automatically generated as '|const!sort!UUID|'
 *
 * @return [SMTFunction0]
 */
fun <T : Sort> SMTProgramBuilder.declaringConst(sort: T) =
    Const(sort, this, "|const!$sort!${UUID.randomUUID()}|")

/**
 * Declares an SMT constant: (declare-const [name] [sort]).
 *
 * If the name is empty, the function automatically generates a name as '|const!sort!UUID|'
 *
 * @return [SMTFunction0]
 */
fun <T : Sort> SMTProgramBuilder.declaringConst(sort: T, name: String) = Const(sort, this, name)

/**
 * Declares an SMT function without any parameters: (declare-fun symbol () [sort]).
 *
 * [SMTFunction.invoke] has to called to generate an Expression with the given parameters applied.
 * For functions of arity 0, prefer [declaringConst]. The functions name will be the same as the
 * variables name.
 *
 * @return an [SMTFunction] object with arity 0.
 */
fun <T : Sort> SMTProgramBuilder.declaring(sort: T) = Declare0(sort, this)

/**
 * Declares an SMT function with one parameter: (declare-fun symbol ([par]) [sort]).
 *
 * [SMTFunction.invoke] has to called to generate an Expression with the given parameters applied.
 * The functions name will be the same as the variables name.
 *
 * @return an [SMTFunction] object with arity 1.
 */
fun <T : Sort, S : Sort> SMTProgramBuilder.declaring(sort: T, par: S) = Declare1(sort, par, this)

/**
 * Declares an SMT function with two parameters: (declare-fun symbol ([par1] [par2]) [sort]).
 *
 * [SMTFunction.invoke] has to called to generate an Expression with the given parameters applied.
 * The functions name will be the same as the variables name.
 *
 * @return an [SMTFunction] object with arity 2.
 */
fun <T : Sort, S1 : Sort, S2 : Sort> SMTProgramBuilder.declaring(sort: T, par1: S1, par2: S2) =
    Declare2(sort, par1, par2, this)

/**
 * Declares an SMT function with three parameters: (declare-fun symbol ([par1] [par2] [par3]).
 * [sort])
 *
 * [SMTFunction.invoke] has to called to generate an Expression with the given parameters applied.
 * The functions name will be the same as the variables name.
 *
 * @return an [SMTFunction] object with arity 3.
 */
fun <T : Sort, S1 : Sort, S2 : Sort, S3 : Sort> SMTProgramBuilder.declaring(
    sort: T,
    par1: S1,
    par2: S2,
    par3: S3
) = Declare3(sort, par1, par2, par3, this)

/**
 * Declares an SMT function with four parameters: (declare-fun symbol ([par1] [par2] [par3] [par4]).
 * [sort])
 *
 * [SMTFunction.invoke] has to called to generate an Expression with the given parameters applied.
 * The functions name will be the same as the variables name.
 *
 * @return an [SMTFunction] object with arity 4.
 */
fun <T : Sort, S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort> SMTProgramBuilder.declaring(
    sort: T,
    par1: S1,
    par2: S2,
    par3: S3,
    par4: S4
) = Declare4(sort, par1, par2, par3, par4, this)

/**
 * Declares an SMT function with five parameters: (declare-fun symbol ([par1] [par2] [par3] [par4]
 * [par5]) [sort]).
 *
 * [SMTFunction.invoke] has to called to generate an Expression with the given parameters applied.
 * The functions name will be the same as the variables name.
 *
 * @return an [SMTFunction] object with arity 5.
 */
fun <T : Sort, S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort, S5 : Sort> SMTProgramBuilder.declaring(
    sort: T,
    par1: S1,
    par2: S2,
    par3: S3,
    par4: S4,
    par5: S5
) = Declare5(sort, par1, par2, par3, par4, par5, this)

/**
 * Define an SMT function: (define-fun symbol () [sort] [block]).
 *
 * [SMTFunction.invoke] has to called to generate an Expression with the given parameters applied.
 * The functions name will be the same as the variables name.
 *
 * @return an [SMTFunction] object with arity 0.
 */
fun <T : Sort> SMTProgramBuilder.defining(sort: T, block: (List<Expression<*>>) -> Expression<T>) =
    Define(sort, block, this)

/**
 * Define an SMT function: (define-fun symbol ([par]) [sort] [block]).
 *
 * [SMTFunction.invoke] has to called to generate an Expression with the given parameters applied.
 * The functions name will be the same as the variables name.
 *
 * @return an [SMTFunction] object with arity 1.
 */
fun <T : Sort, S : Sort> SMTProgramBuilder.defining(
    sort: T,
    par: S,
    block: (Expression<S>) -> Expression<T>
) = Define1(sort, block, par, this)

/**
 * Define an SMT function: (define-fun symbol ([par1] [par2]) [sort] [block]).
 *
 * [SMTFunction.invoke] has to called to generate an Expression with the given parameters applied.
 * The functions name will be the same as the variables name.
 *
 * @return an [SMTFunction] object with arity 2.
 */
fun <T : Sort, S1 : Sort, S2 : Sort> SMTProgramBuilder.defining(
    sort: T,
    par1: S1,
    par2: S2,
    block: (Expression<S1>, Expression<S2>) -> Expression<T>
) = Define2(sort, block, par1, par2, this)

/**
 * Define an SMT function: (define-fun symbol ([par1] [par2] [par3]) [sort] [block]).
 *
 * [SMTFunction.invoke] has to called to generate an Expression with the given parameters applied.
 * The functions name will be the same as the variables name.
 *
 * @return an [SMTFunction] object with arity 3.
 */
fun <T : Sort, S1 : Sort, S2 : Sort, S3 : Sort> SMTProgramBuilder.defining(
    sort: T,
    par1: S1,
    par2: S2,
    par3: S3,
    block: (Expression<S1>, Expression<S2>, Expression<S3>) -> Expression<T>
) = Define3(sort, block, par1, par2, par3, this)

/**
 * Define an SMT function: (define-fun symbol ([par1] [par2] [par3] [par4]) [sort] [block]).
 *
 * [SMTFunction.invoke] has to called to generate an Expression with the given parameters applied.
 * The functions name will be the same as the variables name.
 *
 * @return an [SMTFunction] object with arity 4.
 */
fun <T : Sort, S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort> SMTProgramBuilder.defining(
    sort: T,
    par1: S1,
    par2: S2,
    par3: S3,
    par4: S4,
    block: (Expression<S1>, Expression<S2>, Expression<S3>, Expression<S4>) -> Expression<T>
) = Define4(sort, block, par1, par2, par3, par4, this)

/**
 * Define an SMT function: (define-fun symbol ([par1] [par2] [par3] [par4] [par5]) [sort] [block]).
 *
 * [SMTFunction.invoke] has to called to generate an Expression with the given parameters applied.
 * The functions name will be the same as the variables name.
 *
 * @return an [SMTFunction] object with arity 5.
 */
fun <T : Sort, S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort, S5 : Sort> SMTProgramBuilder.defining(
    sort: T,
    par1: S1,
    par2: S2,
    par3: S3,
    par4: S4,
    par5: S5,
    block:
        (
            Expression<S1>,
            Expression<S2>,
            Expression<S3>,
            Expression<S4>,
            Expression<S5>) -> Expression<T>
) = Define5(sort, block, par1, par2, par3, par4, par5, this)

/**
 * Delegate provider class for declaring SMT functions of any arity: (declare-fun [name]
 * ([parameters]) [sort]).
 *
 * Registers the function in the given [program]. If [name] is null, the name register will be
 * `|property.name|`.
 *
 * @return [SMTFunctionN]
 */
class Declare<T : Sort>(
    val sort: T,
    val program: SMTProgramBuilder,
    val parameters: List<Sort> = emptyList(),
    val name: String? = null
) {
  operator fun provideDelegate(
      thisRef: Any?,
      property: KProperty<*>
  ): SimpleDelegate<SMTFunction<T>> =
      SimpleDelegate(
          program.declareFun(
              UserDeclaredSMTFunctionN(
                  (name ?: "|${property.name}|").toSymbolWithQuotes(), sort, parameters)))
}

/**
 * Delegate provider class for declaring SMT functions: (declare-fun [name] () [sort]).
 *
 * Registers the function in the given [program]. If [name] is null, the name register will be
 * `|property.name|`.
 *
 * @return [SMTFunction0]
 */
class Const<T : Sort>(val sort: T, val program: SMTProgramBuilder, val name: String? = null) {
  operator fun provideDelegate(
      thisRef: Any?,
      property: KProperty<*>
  ): SimpleDelegate<Expression<T>> =
      SimpleDelegate(
          program
              .declareFun(
                  UserDeclaredSMTFunction0(
                      (name ?: "|${property.name}|").toSymbolWithQuotes(), sort))
              .invoke())
}

/**
 * Delegate provider class for declaring SMT functions: (declare-fun [name] () [sort]).
 *
 * Registers the function in the given [program]. If [name] is null, the name register will be
 * `|property.name|`.
 *
 * @return [SMTFunction0]
 */
class Declare0<T : Sort>(val sort: T, val program: SMTProgramBuilder, val name: String? = null) {
  operator fun provideDelegate(
      thisRef: Any?,
      property: KProperty<*>
  ): SimpleDelegate<UserDeclaredSMTFunction0<T>> =
      SimpleDelegate(
          program.declareFun(
              UserDeclaredSMTFunction0((name ?: "|${property.name}|").toSymbolWithQuotes(), sort)))
}

/**
 * Delegate provider class for declaring SMT functions: (declare-fun [name] ([par]) [sort]).
 *
 * Registers the function in the given [program]. If [name] is null, the name register will be
 * `|property.name|`.
 *
 * @return [SMTFunction1]
 */
class Declare1<T : Sort, S : Sort>(
    val sort: T,
    val par: S,
    val program: SMTProgramBuilder,
    val name: String? = null
) {
  operator fun provideDelegate(
      thisRef: Any?,
      property: KProperty<*>
  ): SimpleDelegate<UserDeclaredSMTFunction1<T, S>> =
      SimpleDelegate(
          program.declareFun(
              UserDeclaredSMTFunction1(
                  (name ?: "|${property.name}|").toSymbolWithQuotes(), sort, par)))
}

/**
 * Delegate provider class for declaring SMT functions: (declare-fun [name] ([par1] [par2]) [sort]).
 *
 * Registers the function in the given [program]. If [name] is null, the name register will be
 * `|property.name|`.
 *
 * @return [SMTFunction2]
 */
class Declare2<T : Sort, S1 : Sort, S2 : Sort>(
    val sort: T,
    val par1: S1,
    val par2: S2,
    val program: SMTProgramBuilder,
    val name: String? = null
) {
  operator fun provideDelegate(
      thisRef: Any?,
      property: KProperty<*>
  ): SimpleDelegate<UserDeclaredSMTFunction2<T, S1, S2>> =
      SimpleDelegate(
          program.declareFun(
              UserDeclaredSMTFunction2(
                  (name ?: "|${property.name}|").toSymbolWithQuotes(), sort, par1, par2)))
}

/**
 * Delegate provider class for declaring SMT functions: (declare-fun [name] ([par1] [par2] [par3])
 * [sort]).
 *
 * Registers the function in the given [program]. If [name] is null, the name register will be
 * `|property.name|`.
 *
 * @return [SMTFunction3]
 */
class Declare3<T : Sort, S1 : Sort, S2 : Sort, S3 : Sort>(
    val sort: T,
    val par1: S1,
    val par2: S2,
    val par3: S3,
    val program: SMTProgramBuilder,
    val name: String? = null
) {
  operator fun provideDelegate(
      thisRef: Any?,
      property: KProperty<*>
  ): SimpleDelegate<UserDeclaredSMTFunction3<T, S1, S2, S3>> =
      SimpleDelegate(
          program.declareFun(
              UserDeclaredSMTFunction3(
                  (name ?: "|${property.name}|").toSymbolWithQuotes(), sort, par1, par2, par3)))
}

/**
 * Delegate provider class for declaring SMT functions: (declare-fun [name] ([par1] [par2] [par3]
 * [par4]) [sort]).
 *
 * Registers the function in the given [program]. If [name] is null, the name register will be
 * `|property.name|`.
 *
 * @return [SMTFunction4]
 */
class Declare4<T : Sort, S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort>(
    val sort: T,
    val par1: S1,
    val par2: S2,
    val par3: S3,
    val par4: S4,
    val program: SMTProgramBuilder,
    val name: String? = null
) {
  operator fun provideDelegate(
      thisRef: Any?,
      property: KProperty<*>
  ): SimpleDelegate<UserDeclaredSMTFunction4<T, S1, S2, S3, S4>> =
      SimpleDelegate(
          program.declareFun(
              UserDeclaredSMTFunction4(
                  (name ?: "|${property.name}|").toSymbolWithQuotes(),
                  sort,
                  par1,
                  par2,
                  par3,
                  par4)))
}

/**
 * Delegate provider class for declaring SMT functions: (declare-fun [name] ([par1] [par2] [par3]
 * [par4] [par5]) [sort]).
 *
 * Registers the function in the given [program]. If [name] is null, the name register will be
 * `|property.name|`.
 *
 * @return [SMTFunction5]
 */
class Declare5<T : Sort, S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort, S5 : Sort>(
    val sort: T,
    val par1: S1,
    val par2: S2,
    val par3: S3,
    val par4: S4,
    val par5: S5,
    val program: SMTProgramBuilder,
    val name: String? = null
) {
  operator fun provideDelegate(
      thisRef: Any?,
      property: KProperty<*>
  ): SimpleDelegate<UserDeclaredSMTFunction5<T, S1, S2, S3, S4, S5>> =
      SimpleDelegate(
          program.declareFun(
              UserDeclaredSMTFunction5(
                  (name ?: "|${property.name}|").toSymbolWithQuotes(),
                  sort,
                  par1,
                  par2,
                  par3,
                  par4,
                  par5)))
}

/**
 * Delegate provider class for defining SMT functions of any arity: (define-fun [name]
 * ([parameters]) [sort] [block]).
 *
 * Registers the function in the given [program]. If [name] is null, the name register will be
 * `|property.name|`.
 *
 * @return [SMTFunctionN]
 */
class Define<T : Sort>(
    val sort: T,
    val block: (List<Expression<Sort>>) -> Expression<T>,
    val program: SMTProgramBuilder,
    val parameters: List<Sort> = emptyList(),
    val name: String? = null
) {
  operator fun provideDelegate(
      thisRef: Any?,
      property: KProperty<*>
  ): SimpleDelegate<UserDefinedSMTFunctionN<T>> {
    val n = name ?: "|${property.name}|"
    val sortedVars =
        parameters.mapIndexed { id, sort ->
          SortedVar("|${property.name}!local!$sort!$id|".toSymbolWithQuotes(), sort)
        }
    val term = block(sortedVars.map { it.instance })

    return SimpleDelegate(
        program.defineFun(UserDefinedSMTFunctionN(n.toSymbolWithQuotes(), sort, sortedVars, term)))
  }
}

/**
 * Delegate provider class for defining SMT functions: (define-fun [name] ([par]) [sort] [block]).
 *
 * Registers the function in the given [program]. If [name] is null, the name register will be
 * `|property.name|`.
 *
 * @return [SMTFunction1]
 */
class Define1<T : Sort, S : Sort>(
    val sort: T,
    val block: (Expression<S>) -> Expression<T>,
    val par: S,
    val program: SMTProgramBuilder,
    val name: String? = null
) {
  operator fun provideDelegate(
      thisRef: Any?,
      property: KProperty<*>
  ): SimpleDelegate<UserDefinedSMTFunction1<T, S>> {
    val n = name ?: "|${property.name}|"
    val sortedVar = SortedVar("|${property.name}!local!$par!1|".toSymbolWithQuotes(), par)
    val term = block(sortedVar.instance)

    return SimpleDelegate(
        program.defineFun(UserDefinedSMTFunction1(n.toSymbolWithQuotes(), sort, sortedVar, term)))
  }
}

/**
 * Delegate provider class for defining SMT functions: (define-fun [name] ([par1] [par2]) [sort]
 * [block]).
 *
 * Registers the function in the given [program]. If [name] is null, the name register will be
 * `|property.name|`.
 *
 * @return [SMTFunction2]
 */
class Define2<T : Sort, S1 : Sort, S2 : Sort>(
    val sort: T,
    val block: (Expression<S1>, Expression<S2>) -> Expression<T>,
    val par1: S1,
    val par2: S2,
    val program: SMTProgramBuilder,
    val name: String? = null
) {
  operator fun provideDelegate(
      thisRef: Any?,
      property: KProperty<*>
  ): SimpleDelegate<UserDefinedSMTFunction2<T, S1, S2>> {
    val n = name ?: "|${property.name}|"
    val sortedVar1 = SortedVar("|${property.name}!local!$par1!1|".toSymbolWithQuotes(), par1)
    val sortedVar2 = SortedVar("|${property.name}!local!$par2!2|".toSymbolWithQuotes(), par2)
    val term = block(sortedVar1.instance, sortedVar2.instance)

    return SimpleDelegate(
        program.defineFun(
            UserDefinedSMTFunction2(n.toSymbolWithQuotes(), sort, sortedVar1, sortedVar2, term)))
  }
}

/**
 * Delegate provider class for defining SMT functions: (define-fun [name] ([par1] [par2] [par3])
 * [sort] [block]).
 *
 * Registers the function in the given [program]. If [name] is null, the name register will be
 * `|property.name|`.
 *
 * @return [SMTFunction3]
 */
class Define3<T : Sort, S1 : Sort, S2 : Sort, S3 : Sort>(
    val sort: T,
    val block: (Expression<S1>, Expression<S2>, Expression<S3>) -> Expression<T>,
    val par1: S1,
    val par2: S2,
    val par3: S3,
    val program: SMTProgramBuilder,
    val name: String? = null
) {
  operator fun provideDelegate(
      thisRef: Any?,
      property: KProperty<*>
  ): SimpleDelegate<UserDefinedSMTFunction3<T, S1, S2, S3>> {
    val n = name ?: "|${property.name}|"
    val sortedVar1 = SortedVar("|${property.name}!local!$par1!1|".toSymbolWithQuotes(), par1)
    val sortedVar2 = SortedVar("|${property.name}!local!$par2!2|".toSymbolWithQuotes(), par2)
    val sortedVar3 = SortedVar("|${property.name}!local!$par3!3|".toSymbolWithQuotes(), par3)
    val term = block(sortedVar1.instance, sortedVar2.instance, sortedVar3.instance)

    return SimpleDelegate(
        program.defineFun(
            UserDefinedSMTFunction3(
                n.toSymbolWithQuotes(), sort, sortedVar1, sortedVar2, sortedVar3, term)))
  }
}

/**
 * Delegate provider class for defining SMT functions: (define-fun [name] ([par1] [par2] [par3]
 * [par4]) [sort] [block]).
 *
 * Registers the function in the given [program]. If [name] is null, the name register will be
 * `|property.name|`.
 *
 * @return [UserDefinedSMTFunction4]
 */
class Define4<T : Sort, S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort>(
    val sort: T,
    val block: (Expression<S1>, Expression<S2>, Expression<S3>, Expression<S4>) -> Expression<T>,
    val par1: S1,
    val par2: S2,
    val par3: S3,
    val par4: S4,
    val program: SMTProgramBuilder,
    val name: String? = null
) {
  operator fun provideDelegate(
      thisRef: Any?,
      property: KProperty<*>
  ): SimpleDelegate<UserDefinedSMTFunction4<T, S1, S2, S3, S4>> {
    val n = name ?: "|${property.name}|"
    val sortedVar1 = SortedVar("|${property.name}!local!$par1!1|".toSymbolWithQuotes(), par1)
    val sortedVar2 = SortedVar("|${property.name}!local!$par2!2|".toSymbolWithQuotes(), par2)
    val sortedVar3 = SortedVar("|${property.name}!local!$par3!3|".toSymbolWithQuotes(), par3)
    val sortedVar4 = SortedVar("|${property.name}!local!$par4!4|".toSymbolWithQuotes(), par4)
    val term =
        block(sortedVar1.instance, sortedVar2.instance, sortedVar3.instance, sortedVar4.instance)

    return SimpleDelegate(
        program.defineFun(
            UserDefinedSMTFunction4(
                n.toSymbolWithQuotes(),
                sort,
                sortedVar1,
                sortedVar2,
                sortedVar3,
                sortedVar4,
                term)))
  }
}

/**
 * Delegate provider class for defining SMT functions: (define-fun [name] ([par1] [par2] [par3]
 * [par4] [par5]) [sort] [block]).
 *
 * Registers the function in the given [program]. If [name] is null, the name register will be
 * `|property.name|`.
 *
 * @return [SMTFunction5]
 */
class Define5<T : Sort, S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort, S5 : Sort>(
    val sort: T,
    val block:
        (
            Expression<S1>,
            Expression<S2>,
            Expression<S3>,
            Expression<S4>,
            Expression<S5>) -> Expression<T>,
    val par1: S1,
    val par2: S2,
    val par3: S3,
    val par4: S4,
    val par5: S5,
    val program: SMTProgramBuilder,
    val name: String? = null
) {
  operator fun provideDelegate(
      thisRef: Any?,
      property: KProperty<*>
  ): SimpleDelegate<UserDefinedSMTFunction5<T, S1, S2, S3, S4, S5>> {
    val n = name ?: "|${property.name}|"
    val sortedVar1 = SortedVar("|${property.name}!local!$par1!1|".toSymbolWithQuotes(), par1)
    val sortedVar2 = SortedVar("|${property.name}!local!$par2!2|".toSymbolWithQuotes(), par2)
    val sortedVar3 = SortedVar("|${property.name}!local!$par3!3|".toSymbolWithQuotes(), par3)
    val sortedVar4 = SortedVar("|${property.name}!local!$par4!4|".toSymbolWithQuotes(), par4)
    val sortedVar5 = SortedVar("|${property.name}!local!$par5!5|".toSymbolWithQuotes(), par5)
    val term =
        block(
            sortedVar1.instance,
            sortedVar2.instance,
            sortedVar3.instance,
            sortedVar4.instance,
            sortedVar5.instance)

    return SimpleDelegate(
        program.defineFun(
            UserDefinedSMTFunction5(
                n.toSymbolWithQuotes(),
                sort,
                sortedVar1,
                sortedVar2,
                sortedVar3,
                sortedVar4,
                sortedVar5,
                term)))
  }
}

/** User declared smt function with any number of arguments. */
data class UserDeclaredSMTFunctionN<T : Sort>(
    override val symbol: Symbol,
    override val sort: T,
    override val parameters: List<Sort>,
) : UserDeclaredSMTFunction<T>()

/**
 * SMTFunction of arity 0.
 *
 * Use [invoke] to generate an expression with the given parameters applied.
 */
data class UserDeclaredSMTFunction0<T : Sort>(
    override val symbol: Symbol,
    override val sort: T,
) : UserDeclaredSMTFunction<T>() {
  override val parameters = emptyList<Sort>()

  val instance = UserDeclaredExpression(symbol, sort, this)

    /** Get instance. */
  operator fun invoke() = instance
}

/**
 * SMTFunction of arity 1.
 *
 * Use [invoke] to generate an expression with the given parameters applied.
 */
data class UserDeclaredSMTFunction1<T : Sort, S : Sort>(
    override val symbol: Symbol,
    override val sort: T,
    val parameter: S,
) : UserDeclaredSMTFunction<T>() {
  override val parameters = listOf(parameter)

  /** Create instance by applying [arg] to [this]. */
  operator fun invoke(arg: Expression<S>) = UserDeclaredExpression(symbol, sort, listOf(arg), this)
}

/**
 * SMTFunction of arity 2.
 *
 * Use [invoke] to generate an expression with the given parameters applied.
 */
data class UserDeclaredSMTFunction2<T : Sort, S1 : Sort, S2 : Sort>(
    override val symbol: Symbol,
    override val sort: T,
    val parameter1: S1,
    val parameter2: S2,
) : UserDeclaredSMTFunction<T>() {
  override val parameters = listOf(parameter1, parameter2)

  /** Create instance by applying [arg1], [arg2] to [this]. */
  operator fun invoke(arg1: Expression<S1>, arg2: Expression<S2>) =
      UserDeclaredExpression(symbol, sort, listOf(arg1, arg2), this)
}

/**
 * SMTFunction of arity 3.
 *
 * Use [invoke] to generate an expression with the given parameters applied.
 */
data class UserDeclaredSMTFunction3<T : Sort, S1 : Sort, S2 : Sort, S3 : Sort>(
    override val symbol: Symbol,
    override val sort: T,
    val parameter1: S1,
    val parameter2: S2,
    val parameter3: S3,
) : UserDeclaredSMTFunction<T>() {
  override val parameters = listOf(parameter1, parameter2, parameter3)

  /** Create instance by applying [arg1], [arg2], [arg3] to [this]. */
  operator fun invoke(arg1: Expression<S1>, arg2: Expression<S2>, arg3: Expression<S3>) =
      UserDeclaredExpression(symbol, sort, listOf(arg1, arg2, arg3), this)
}

/**
 * SMTFunction of arity 4.
 *
 * Use [invoke] to generate an expression with the given parameters applied.
 */
data class UserDeclaredSMTFunction4<T : Sort, S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort>(
    override val symbol: Symbol,
    override val sort: T,
    val parameter1: S1,
    val parameter2: S2,
    val parameter3: S3,
    val parameter4: S4,
) : UserDeclaredSMTFunction<T>() {
  override val parameters = listOf(parameter1, parameter2, parameter3, parameter4)

  /** Create instance by applying [arg1], [arg2], [arg3], [arg4] to [this]. */
  operator fun invoke(
      arg1: Expression<S1>,
      arg2: Expression<S2>,
      arg3: Expression<S3>,
      arg4: Expression<S4>
  ) = UserDeclaredExpression(symbol, sort, listOf(arg1, arg2, arg3, arg4), this)
}

/**
 * SMTFunction of arity 5.
 *
 * Use [invoke] to generate an expression with the given parameters applied.
 */
data class UserDeclaredSMTFunction5<
    T : Sort, S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort, S5 : Sort>(
    override val symbol: Symbol,
    override val sort: T,
    val parameter1: S1,
    val parameter2: S2,
    val parameter3: S3,
    val parameter4: S4,
    val parameter5: S5,
) : UserDeclaredSMTFunction<T>() {
  override val parameters = listOf(parameter1, parameter2, parameter3, parameter4, parameter5)

  /** Create instance by applying [arg1], [arg2], [arg3], [arg4], [arg5] to [this]. */
  operator fun invoke(
      arg1: Expression<S1>,
      arg2: Expression<S2>,
      arg3: Expression<S3>,
      arg4: Expression<S4>,
      arg5: Expression<S5>
  ) = UserDeclaredExpression(symbol, sort, listOf(arg1, arg2, arg3, arg4, arg5), this)
}

/** User defined smt function with any number of arguments. */
data class UserDefinedSMTFunctionN<T : Sort>(
    override val symbol: Symbol,
    override val sort: T,
    override val sortedVars: List<SortedVar<*>>,
    override val term: Expression<T>
) : DefinedSMTFunction<T>() {
  /** Companion object for pseudo constructor. */
  companion object {
    /** Pseudo constructor. */
    operator fun <T : Sort> invoke(
        symbol: Symbol,
        sort: T,
        parameters: List<Sort>,
        term: Expression<T>
    ) =
        UserDefinedSMTFunctionN(
            symbol,
            sort,
            parameters.mapIndexed { index, sort ->
              SortedVar("|local!$sort!$index|".toSymbolWithQuotes(), sort)
            },
            term)
  }

  override val parameters = sortedVars.map { it.sort }
}

/**
 * SMTFunction of arity 0.
 *
 * Use [invoke] to generate an expression with the given parameters applied.
 */
data class UserDefinedSMTFunction0<T : Sort>(
    override val symbol: Symbol,
    override val sort: T,
    override val term: Expression<T>
) : DefinedSMTFunction<T>() {
  override val parameters = emptyList<Sort>()
  override val sortedVars = emptyList<SortedVar<*>>()

  /** Create instance. */
  operator fun invoke() =
      UserDefinedExpression(
          symbol, sort, emptyList(), FunctionDef(symbol, sortedVars, sort, term), this)
}

/**
 * SMTFunction of arity 1.
 *
 * Use [invoke] to generate an expression with the given parameters applied.
 */
data class UserDefinedSMTFunction1<T : Sort, S : Sort>(
    override val symbol: Symbol,
    override val sort: T,
    val parameter: SortedVar<S>,
    override val term: Expression<T>
) : DefinedSMTFunction<T>() {
  constructor(
      symbol: Symbol,
      sort: T,
      parameter: S,
      term: Expression<T>
  ) : this(symbol, sort, SortedVar("|local!$parameter!2|".toSymbolWithQuotes(), parameter), term)

  override val parameters = listOf(parameter.sort)
  override val sortedVars = listOf(parameter)

  /** Create instance by applying [arg] to [this]. */
  operator fun invoke(arg: Expression<S>) =
      UserDefinedExpression(
          symbol, sort, listOf(arg), FunctionDef(symbol, sortedVars, sort, term), this)
}

/**
 * SMTFunction of arity 2.
 *
 * Use [invoke] to generate an expression with the given parameters applied.
 */
data class UserDefinedSMTFunction2<T : Sort, S1 : Sort, S2 : Sort>(
    override val symbol: Symbol,
    override val sort: T,
    val parameter1: SortedVar<S1>,
    val parameter2: SortedVar<S2>,
    override val term: Expression<T>
) : DefinedSMTFunction<T>() {
  constructor(
      symbol: Symbol,
      sort: T,
      parameter1: S1,
      parameter2: S2,
      term: Expression<T>
  ) : this(
      symbol,
      sort,
      SortedVar("|$parameter1!1|".toSymbolWithQuotes(), parameter1),
      SortedVar("|$parameter2!2|".toSymbolWithQuotes(), parameter2),
      term)

  override val parameters = listOf(parameter1.sort, parameter2.sort)
  override val sortedVars = listOf(parameter1, parameter2)

  /** Create instance by applying [arg1], [arg2] to [this]. */
  operator fun invoke(arg1: Expression<S1>, arg2: Expression<S2>) =
      UserDefinedExpression(
          symbol, sort, listOf(arg1, arg2), FunctionDef(symbol, sortedVars, sort, term), this)
}

/**
 * SMTFunction of arity 3.
 *
 * Use [invoke] to generate an expression with the given parameters applied.
 */
data class UserDefinedSMTFunction3<T : Sort, S1 : Sort, S2 : Sort, S3 : Sort>(
    override val symbol: Symbol,
    override val sort: T,
    val parameter1: SortedVar<S1>,
    val parameter2: SortedVar<S2>,
    val parameter3: SortedVar<S3>,
    override val term: Expression<T>
) : DefinedSMTFunction<T>() {
  override val parameters = listOf(parameter1.sort, parameter2.sort, parameter3.sort)
  override val sortedVars = listOf(parameter1, parameter2, parameter3)

  constructor(
      symbol: Symbol,
      sort: T,
      parameter1: S1,
      parameter2: S2,
      parameter3: S3,
      term: Expression<T>
  ) : this(
      symbol,
      sort,
      SortedVar("|local!$sort!1|".toSymbolWithQuotes(), parameter1),
      SortedVar("|local!$sort!2|".toSymbolWithQuotes(), parameter2),
      SortedVar("|local!$sort!3|".toSymbolWithQuotes(), parameter3),
      term)

  /** Create instance by applying [arg1], [arg2], [arg3] to [this]. */
  operator fun invoke(arg1: Expression<S1>, arg2: Expression<S2>, arg3: Expression<S3>) =
      UserDefinedExpression(
          symbol, sort, listOf(arg1, arg2, arg3), FunctionDef(symbol, sortedVars, sort, term), this)
}

/**
 * SMTFunction of arity 4.
 *
 * Use [invoke] to generate an expression with the given parameters applied.
 */
data class UserDefinedSMTFunction4<T : Sort, S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort>(
    override val symbol: Symbol,
    override val sort: T,
    val parameter1: SortedVar<S1>,
    val parameter2: SortedVar<S2>,
    val parameter3: SortedVar<S3>,
    val parameter4: SortedVar<S4>,
    override val term: Expression<T>
) : DefinedSMTFunction<T>() {
  override val parameters =
      listOf(parameter1.sort, parameter2.sort, parameter3.sort, parameter4.sort)
  override val sortedVars = listOf(parameter1, parameter2, parameter3, parameter4)

  constructor(
      symbol: Symbol,
      sort: T,
      parameter1: S1,
      parameter2: S2,
      parameter3: S3,
      parameter4: S4,
      term: Expression<T>
  ) : this(
      symbol,
      sort,
      SortedVar("|local!$sort!1|".toSymbolWithQuotes(), parameter1),
      SortedVar("|local!$sort!2|".toSymbolWithQuotes(), parameter2),
      SortedVar("|local!$sort!3|".toSymbolWithQuotes(), parameter3),
      SortedVar("|local!$sort!4|".toSymbolWithQuotes(), parameter4),
      term)

  /** Create instance by applying [arg1], [arg2], [arg3], [arg4] to [this]. */
  operator fun invoke(
      arg1: Expression<S1>,
      arg2: Expression<S2>,
      arg3: Expression<S3>,
      arg4: Expression<S4>
  ) =
      UserDefinedExpression(
          symbol,
          sort,
          listOf(arg1, arg2, arg3, arg4),
          FunctionDef(symbol, sortedVars, sort, term),
          this)
}

/**
 * SMTFunction of arity 5.
 *
 * Use [invoke] to generate an expression with the given parameters applied.
 */
data class UserDefinedSMTFunction5<T : Sort, S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort, S5 : Sort>(
    override val symbol: Symbol,
    override val sort: T,
    val parameter1: SortedVar<S1>,
    val parameter2: SortedVar<S2>,
    val parameter3: SortedVar<S3>,
    val parameter4: SortedVar<S4>,
    val parameter5: SortedVar<S5>,
    override val term: Expression<T>
) : DefinedSMTFunction<T>() {
  override val parameters =
      listOf(parameter1.sort, parameter2.sort, parameter3.sort, parameter4.sort, parameter5.sort)
  override val sortedVars = listOf(parameter1, parameter2, parameter3, parameter4, parameter5)

  constructor(
      symbol: Symbol,
      sort: T,
      parameter1: S1,
      parameter2: S2,
      parameter3: S3,
      parameter4: S4,
      parameter5: S5,
      term: Expression<T>
  ) : this(
      symbol,
      sort,
      SortedVar("|local!$sort!1|".toSymbolWithQuotes(), parameter1),
      SortedVar("|local!$sort!2|".toSymbolWithQuotes(), parameter2),
      SortedVar("|local!$sort!3|".toSymbolWithQuotes(), parameter3),
      SortedVar("|local!$sort!4|".toSymbolWithQuotes(), parameter4),
      SortedVar("|local!$sort!5|".toSymbolWithQuotes(), parameter5),
      term)

  /** Create instance by applying [arg1], [arg2], [arg3], [arg4], [arg5] to [this]. */
  operator fun invoke(
      arg1: Expression<S1>,
      arg2: Expression<S2>,
      arg3: Expression<S3>,
      arg4: Expression<S4>,
      arg5: Expression<S5>
  ) =
      UserDefinedExpression(
          symbol,
          sort,
          listOf(arg1, arg2, arg3, arg4, arg5),
          FunctionDef(symbol, sortedVars, sort, term),
          this)
}

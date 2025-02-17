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
 * Declares an SMT constant: (declare-const |const!sort!UUID| [sort])
 *
 * The name of the constant is automatically generated as '|const!sort!UUID|'
 *
 * @return [Declare0]
 */
fun <T : Sort> SMTProgramBuilder.declaringConst(sort: T) =
    Const(sort, this, "|const!$sort!${UUID.randomUUID()}|")

/**
 * Declares an SMT constant: (declare-const [name] [sort])
 *
 * If the name is empty, the function automatically generates a name as '|const!sort!UUID|'
 *
 * @return [Declare0]
 */
fun <T : Sort> SMTProgramBuilder.declaringConst(sort: T, name: String) = Const(sort, this, name)

/**
 * Declares an SMT function without any parameters: (declare-fun symbol () [sort])
 *
 * [SMTFunction.invoke] has to called to generate an Expression with the given parameters applied.
 * For functions of arity 0, prefer [declaringConst]. The functions name will be the same as the
 * variables name.
 *
 * @return an [SMTFunction] object with arity 0.
 */
fun <T : Sort> SMTProgramBuilder.declaring(sort: T) = Declare0(sort, this)

/**
 * Declares an SMT function with one parameter: (declare-fun symbol ([par]) [sort])
 *
 * [SMTFunction.invoke] has to called to generate an Expression with the given parameters applied.
 * The functions name will be the same as the variables name.
 *
 * @return an [SMTFunction] object with arity 1.
 */
fun <T : Sort, S : Sort> SMTProgramBuilder.declaring(sort: T, par: S) = Declare1(sort, par, this)

/**
 * Declares an SMT function with two parameters: (declare-fun symbol ([par1] [par2]) [sort])
 *
 * [SMTFunction.invoke] has to called to generate an Expression with the given parameters applied.
 * The functions name will be the same as the variables name.
 *
 * @return an [SMTFunction] object with arity 2.
 */
fun <T : Sort, S1 : Sort, S2 : Sort> SMTProgramBuilder.declaring(sort: T, par1: S1, par2: S2) =
    Declare2(sort, par1, par2, this)

/**
 * Declares an SMT function with three parameters: (declare-fun symbol ([par1] [par2] [par3])
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
 * Declares an SMT function with four parameters: (declare-fun symbol ([par1] [par2] [par3] [par4])
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
 * [par5]) [sort])
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
 * Define an SMT function: (define-fun symbol () [sort] [block])
 *
 * [SMTFunction.invoke] has to called to generate an Expression with the given parameters applied.
 * The functions name will be the same as the variables name.
 *
 * @return an [SMTFunction] object with arity 0.
 */
fun <T : Sort> SMTProgramBuilder.defining(sort: T, block: (List<Expression<*>>) -> Expression<T>) =
    Define(sort, block, this)

/**
 * Define an SMT function: (define-fun symbol ([par]) [sort] [block])
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
 * Define an SMT function: (define-fun symbol ([par1] [par2]) [sort] [block])
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
 * Define an SMT function: (define-fun symbol ([par1] [par2] [par3]) [sort] [block])
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
 * Define an SMT function: (define-fun symbol ([par1] [par2] [par3] [par4]) [sort] [block])
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
 * Define an SMT function: (define-fun symbol ([par1] [par2] [par3] [par4] [par5]) [sort] [block])
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
 * Registers the function in the given [program]. If [name] is empty, the name register will be the
 * same as the variable.
 *
 * @return [SMTFunction]
 */
class Declare<T : Sort>(
    val sort: T,
    val program: SMTProgramBuilder,
    val parameters: List<Sort> = emptyList(),
    val name: String = ""
) {
  operator fun provideDelegate(
      thisRef: Any?,
      property: KProperty<*>
  ): SimpleDelegate<SMTFunction<T>> {
    val n = name.ifEmpty { "|$thisRef|" }

    return SimpleDelegate(program.registerFun(SMTFunctionN(n.symbol(), sort, parameters, null)))
  }
}

/**
 * Delegate provider class for declaring SMT functions: (declare-fun [name] () [sort]).
 *
 * Registers the function in the given [program]. If [name] is empty, the name register will be the
 * same as the variable.
 *
 * @return [SMTFunction]
 */
class Const<T : Sort>(val sort: T, val program: SMTProgramBuilder, val name: String = "") {
  operator fun provideDelegate(
      thisRef: Any?,
      property: KProperty<*>
  ): SimpleDelegate<Expression<T>> {
    val n = name.ifEmpty { "|$thisRef|" }

    return SimpleDelegate(program.registerFun(SMTFunction0(n.symbol(), sort, null)).invoke())
  }
}

/**
 * Delegate provider class for declaring SMT functions: (declare-fun [name] () [sort]).
 *
 * Registers the function in the given [program]. If [name] is empty, the name register will be the
 * same as the variable.
 *
 * @return [SMTFunction]
 */
class Declare0<T : Sort>(val sort: T, val program: SMTProgramBuilder, val name: String = "") {
  operator fun provideDelegate(
      thisRef: Any?,
      property: KProperty<*>
  ): SimpleDelegate<SMTFunction0<T>> {
    val n = name.ifEmpty { "|$thisRef|" }

    return SimpleDelegate(program.registerFun(SMTFunction0(n.symbol(), sort, null)))
  }
}

/**
 * Delegate provider class for declaring SMT functions: (declare-fun [name] ([par]) [sort]).
 *
 * Registers the function in the given [program]. If [name] is empty, the name register will be the
 * same as the variable.
 *
 * @return [SMTFunction]
 */
class Declare1<T : Sort, S : Sort>(
    val sort: T,
    val par: S,
    val program: SMTProgramBuilder,
    val name: String = ""
) {
  operator fun provideDelegate(
      thisRef: Any?,
      property: KProperty<*>
  ): SimpleDelegate<SMTFunction1<T, S>> {
    val n = name.ifEmpty { "|$thisRef|" }

    return SimpleDelegate(program.registerFun(SMTFunction1(n.symbol(), sort, par, null)))
  }
}

/**
 * Delegate provider class for declaring SMT functions: (declare-fun [name] ([par1] [par2]) [sort]).
 *
 * Registers the function in the given [program]. If [name] is empty, the name register will be the
 * same as the variable.
 *
 * @return [SMTFunction]
 */
class Declare2<T : Sort, S1 : Sort, S2 : Sort>(
    val sort: T,
    val par1: S1,
    val par2: S2,
    val program: SMTProgramBuilder,
    val name: String = ""
) {
  operator fun provideDelegate(
      thisRef: Any?,
      property: KProperty<*>
  ): SimpleDelegate<SMTFunction2<T, S1, S2>> {
    val n = name.ifEmpty { "|$thisRef|" }

    return SimpleDelegate(program.registerFun(SMTFunction2(n.symbol(), sort, par1, par2, null)))
  }
}

/**
 * Delegate provider class for declaring SMT functions: (declare-fun [name] ([par1] [par2] [par3])
 * [sort]).
 *
 * Registers the function in the given [program]. If [name] is empty, the name register will be the
 * same as the variable.
 *
 * @return [SMTFunction]
 */
class Declare3<T : Sort, S1 : Sort, S2 : Sort, S3 : Sort>(
    val sort: T,
    val par1: S1,
    val par2: S2,
    val par3: S3,
    val program: SMTProgramBuilder,
    val name: String = ""
) {
  operator fun provideDelegate(
      thisRef: Any?,
      property: KProperty<*>
  ): SimpleDelegate<SMTFunction3<T, S1, S2, S3>> {
    val n = name.ifEmpty { "|$thisRef|" }

    return SimpleDelegate(
        program.registerFun(SMTFunction3(n.symbol(), sort, par1, par2, par3, null)))
  }
}

/**
 * Delegate provider class for declaring SMT functions: (declare-fun [name] ([par1] [par2] [par3]
 * [par4]) [sort]).
 *
 * Registers the function in the given [program]. If [name] is empty, the name register will be the
 * same as the variable.
 *
 * @return [SMTFunction]
 */
class Declare4<T : Sort, S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort>(
    val sort: T,
    val par1: S1,
    val par2: S2,
    val par3: S3,
    val par4: S4,
    val program: SMTProgramBuilder,
    val name: String = ""
) {
  operator fun provideDelegate(
      thisRef: Any?,
      property: KProperty<*>
  ): SimpleDelegate<SMTFunction4<T, S1, S2, S3, S4>> {
    val n = name.ifEmpty { "|$thisRef|" }
    return SimpleDelegate(
        program.registerFun(SMTFunction4(n.symbol(), sort, par1, par2, par3, par4, null)))
  }
}

/**
 * Delegate provider class for declaring SMT functions: (declare-fun [name] ([par1] [par2] [par3]
 * [par4] [par5]) [sort]).
 *
 * Registers the function in the given [program]. If [name] is empty, the name register will be the
 * same as the variable.
 *
 * @return [SMTFunction]
 */
class Declare5<T : Sort, S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort, S5 : Sort>(
    val sort: T,
    val par1: S1,
    val par2: S2,
    val par3: S3,
    val par4: S4,
    val par5: S5,
    val program: SMTProgramBuilder,
    val name: String = ""
) {
  operator fun provideDelegate(
      thisRef: Any?,
      property: KProperty<*>
  ): SimpleDelegate<SMTFunction5<T, S1, S2, S3, S4, S5>> {
    val n = name.ifEmpty { "|$thisRef|" }

    return SimpleDelegate(
        program.registerFun(SMTFunction5(n.symbol(), sort, par1, par2, par3, par4, par5, null)))
  }
}

/**
 * Delegate provider class for defining SMT functions of any arity: (define-fun [name]
 * ([parameters]) [sort] [block]).
 *
 * Registers the function in the given [program]. If [name] is empty, the name register will be the
 * same as the variable.
 *
 * @return [SMTFunction]
 */
class Define<T : Sort>(
    val sort: T,
    val block: (List<Expression<Sort>>) -> Expression<T>,
    val program: SMTProgramBuilder,
    val parameters: List<Sort> = emptyList(),
    val name: String = ""
) {
  operator fun provideDelegate(
      thisRef: Any?,
      property: KProperty<*>
  ): SimpleDelegate<SMTFunction<T>> {
    val n = name.ifEmpty { "|$thisRef|" }
    val sortedVars =
        parameters.mapIndexed { id, sort -> SortedVar("|$thisRef!local!$sort!$id|".symbol(), sort) }
    val term = block(sortedVars.map { it.instance })

    return SimpleDelegate(
        program.registerFun(
            SMTFunctionN(
                n.symbol(), sort, parameters, FunctionDef(n.symbol(), emptyList(), sort, term))))
  }
}

/**
 * Delegate provider class for defining SMT functions: (define-fun [name] ([par]) [sort] [block]).
 *
 * Registers the function in the given [program]. If [name] is empty, the name register will be the
 * same as the variable.
 *
 * @return [SMTFunction]
 */
class Define1<T : Sort, S : Sort>(
    val sort: T,
    val block: (Expression<S>) -> Expression<T>,
    val par: S,
    val program: SMTProgramBuilder,
    val name: String = ""
) {
  operator fun provideDelegate(
      thisRef: Any?,
      property: KProperty<*>
  ): SimpleDelegate<SMTFunction1<T, S>> {
    val n = name.ifEmpty { "|$thisRef|" }
    val sortedVar = SortedVar("|$thisRef!local!$par!1|".symbol(), par)
    val term = block(sortedVar.instance)

    return SimpleDelegate(
        program.registerFun(
            SMTFunction1(
                n.symbol(), sort, par, FunctionDef(n.symbol(), listOf(sortedVar), sort, term))))
  }
}

/**
 * Delegate provider class for defining SMT functions: (define-fun [name] ([par1] [par2]) [sort]
 * [block]).
 *
 * Registers the function in the given [program]. If [name] is empty, the name register will be the
 * same as the variable.
 *
 * @return [SMTFunction]
 */
class Define2<T : Sort, S1 : Sort, S2 : Sort>(
    val sort: T,
    val block: (Expression<S1>, Expression<S2>) -> Expression<T>,
    val par1: S1,
    val par2: S2,
    val program: SMTProgramBuilder,
    val name: String = ""
) {
  operator fun provideDelegate(
      thisRef: Any?,
      property: KProperty<*>
  ): SimpleDelegate<SMTFunction2<T, S1, S2>> {
    val n = name.ifEmpty { "|$thisRef|" }
    val sortedVar1 = SortedVar("|$thisRef!local!$par1!1|".symbol(), par1)
    val sortedVar2 = SortedVar("|$thisRef!local!$par2!2|".symbol(), par2)
    val term = block(sortedVar1.instance, sortedVar2.instance)

    return SimpleDelegate(
        program.registerFun(
            SMTFunction2(
                n.symbol(),
                sort,
                par1,
                par2,
                FunctionDef(n.symbol(), listOf(sortedVar1, sortedVar2), sort, term))))
  }
}

/**
 * Delegate provider class for defining SMT functions: (define-fun [name] ([par1] [par2] [par3])
 * [sort] [block]).
 *
 * Registers the function in the given [program]. If [name] is empty, the name register will be the
 * same as the variable.
 *
 * @return [SMTFunction]
 */
class Define3<T : Sort, S1 : Sort, S2 : Sort, S3 : Sort>(
    val sort: T,
    val block: (Expression<S1>, Expression<S2>, Expression<S3>) -> Expression<T>,
    val par1: S1,
    val par2: S2,
    val par3: S3,
    val program: SMTProgramBuilder,
    val name: String = ""
) {
  operator fun provideDelegate(
      thisRef: Any?,
      property: KProperty<*>
  ): SimpleDelegate<SMTFunction3<T, S1, S2, S3>> {
    val n = name.ifEmpty { "|$thisRef|" }
    val sortedVar1 = SortedVar("|$thisRef!local!$par1!1|".symbol(), par1)
    val sortedVar2 = SortedVar("|$thisRef!local!$par2!2|".symbol(), par2)
    val sortedVar3 = SortedVar("|$thisRef!local!$par3!3|".symbol(), par3)
    val term = block(sortedVar1.instance, sortedVar2.instance, sortedVar3.instance)

    return SimpleDelegate(
        program.registerFun(
            SMTFunction3(
                n.symbol(),
                sort,
                par1,
                par2,
                par3,
                FunctionDef(n.symbol(), listOf(sortedVar1, sortedVar2, sortedVar3), sort, term))))
  }
}

/**
 * Delegate provider class for defining SMT functions: (define-fun [name] ([par1] [par2] [par3]
 * [par4]) [sort] [block]).
 *
 * Registers the function in the given [program]. If [name] is empty, the name register will be the
 * same as the variable.
 *
 * @return [SMTFunction]
 */
class Define4<T : Sort, S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort>(
    val sort: T,
    val block: (Expression<S1>, Expression<S2>, Expression<S3>, Expression<S4>) -> Expression<T>,
    val par1: S1,
    val par2: S2,
    val par3: S3,
    val par4: S4,
    val program: SMTProgramBuilder,
    val name: String = ""
) {
  operator fun provideDelegate(
      thisRef: Any?,
      property: KProperty<*>
  ): SimpleDelegate<SMTFunction4<T, S1, S2, S3, S4>> {
    val n = name.ifEmpty { "|$thisRef|" }
    val sortedVar1 = SortedVar("|$thisRef!local!$par1!1|".symbol(), par1)
    val sortedVar2 = SortedVar("|$thisRef!local!$par2!2|".symbol(), par2)
    val sortedVar3 = SortedVar("|$thisRef!local!$par3!3|".symbol(), par3)
    val sortedVar4 = SortedVar("|$thisRef!local!$par4!4|".symbol(), par4)
    val term =
        block(sortedVar1.instance, sortedVar2.instance, sortedVar3.instance, sortedVar4.instance)

    return SimpleDelegate(
        program.registerFun(
            SMTFunction4(
                n.symbol(),
                sort,
                par1,
                par2,
                par3,
                par4,
                FunctionDef(
                    n.symbol(),
                    listOf(sortedVar1, sortedVar2, sortedVar3, sortedVar4),
                    sort,
                    term))))
  }
}

/**
 * Delegate provider class for defining SMT functions: (define-fun [name] ([par1] [par2] [par3]
 * [par4] [par5]) [sort] [block]).
 *
 * Registers the function in the given [program]. If [name] is empty, the name register will be the
 * same as the variable.
 *
 * @return [SMTFunction]
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
    val name: String = ""
) {
  operator fun provideDelegate(
      thisRef: Any?,
      property: KProperty<*>
  ): SimpleDelegate<SMTFunction5<T, S1, S2, S3, S4, S5>> {
    val n = name.ifEmpty { "|$thisRef|" }
    val sortedVar1 = SortedVar("|$thisRef!local!$par1!1|".symbol(), par1)
    val sortedVar2 = SortedVar("|$thisRef!local!$par2!2|".symbol(), par2)
    val sortedVar3 = SortedVar("|$thisRef!local!$par3!3|".symbol(), par3)
    val sortedVar4 = SortedVar("|$thisRef!local!$par4!4|".symbol(), par4)
    val sortedVar5 = SortedVar("|$thisRef!local!$par5!5|".symbol(), par5)
    val term =
        block(
            sortedVar1.instance,
            sortedVar2.instance,
            sortedVar3.instance,
            sortedVar4.instance,
            sortedVar5.instance)

    return SimpleDelegate(
        program.registerFun(
            SMTFunction5(
                n.symbol(),
                sort,
                par1,
                par2,
                par3,
                par4,
                par5,
                FunctionDef(
                    n.symbol(),
                    listOf(sortedVar1, sortedVar2, sortedVar3, sortedVar4, sortedVar5),
                    sort,
                    term))))
  }
}

data class SMTFunctionN<T : Sort>(
    override val symbol: Symbol,
    override val sort: T,
    override val parameters: List<Sort>,
    override val definition: FunctionDef<T>?
) : SMTFunction<T>()

/**
 * SMTFunction of arity 0.
 *
 * Use [invoke] to generate an expression with the given parameters applied.
 */
data class SMTFunction0<T : Sort>(
    override val symbol: Symbol,
    override val sort: T,
    override val definition: FunctionDef<T>?
) : SMTFunction<T>() {
  override val parameters = emptyList<Sort>()

  operator fun invoke(): Expression<T> {
    return if (definition == null) {
      UserDeclaredExpression(symbol, sort, this)
    } else {
      UserDefinedExpression(symbol, sort, emptyList(), definition, this)
    }
  }
}

/**
 * SMTFunction of arity 1.
 *
 * Use [invoke] to generate an expression with the given parameters applied.
 */
data class SMTFunction1<T : Sort, S : Sort>(
    override val symbol: Symbol,
    override val sort: T,
    val parameter: S,
    override val definition: FunctionDef<T>?
) : SMTFunction<T>() {
  override val parameters = listOf(parameter)

  operator fun invoke(arg: Expression<S>): Expression<T> {
    return if (definition == null) {
      UserDeclaredExpression(symbol, sort, listOf(arg), this)
    } else {
      UserDefinedExpression(symbol, sort, listOf(arg), definition, this)
    }
  }
}

/**
 * SMTFunction of arity 2.
 *
 * Use [invoke] to generate an expression with the given parameters applied.
 */
data class SMTFunction2<T : Sort, S1 : Sort, S2 : Sort>(
    override val symbol: Symbol,
    override val sort: T,
    val parameter1: S1,
    val parameter2: S2,
    override val definition: FunctionDef<T>?
) : SMTFunction<T>() {
  override val parameters = listOf(parameter1, parameter2)

  operator fun invoke(arg1: Expression<S1>, arg2: Expression<S2>): Expression<T> {
    return if (definition == null) {
      UserDeclaredExpression(symbol, sort, listOf(arg1, arg2), this)
    } else {
      UserDefinedExpression(symbol, sort, listOf(arg1, arg2), definition, this)
    }
  }
}

/**
 * SMTFunction of arity 3.
 *
 * Use [invoke] to generate an expression with the given parameters applied.
 */
data class SMTFunction3<T : Sort, S1 : Sort, S2 : Sort, S3 : Sort>(
    override val symbol: Symbol,
    override val sort: T,
    val parameter1: S1,
    val parameter2: S2,
    val parameter3: S3,
    override val definition: FunctionDef<T>?
) : SMTFunction<T>() {
  override val parameters = listOf(parameter1, parameter2, parameter3)

  operator fun invoke(
      arg1: Expression<S1>,
      arg2: Expression<S2>,
      arg3: Expression<S3>
  ): Expression<T> {
    return if (definition == null) {
      UserDeclaredExpression(symbol, sort, listOf(arg1, arg2, arg3), this)
    } else {
      UserDefinedExpression(symbol, sort, listOf(arg1, arg2, arg3), definition, this)
    }
  }
}

/**
 * SMTFunction of arity 4.
 *
 * Use [invoke] to generate an expression with the given parameters applied.
 */
data class SMTFunction4<T : Sort, S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort>(
    override val symbol: Symbol,
    override val sort: T,
    val parameter1: S1,
    val parameter2: S2,
    val parameter3: S3,
    val parameter4: S4,
    override val definition: FunctionDef<T>?
) : SMTFunction<T>() {
  override val parameters = listOf(parameter1, parameter2, parameter3, parameter4)

  operator fun invoke(
      arg1: Expression<S1>,
      arg2: Expression<S2>,
      arg3: Expression<S3>,
      arg4: Expression<S4>
  ): Expression<T> {
    return if (definition == null) {
      UserDeclaredExpression(symbol, sort, listOf(arg1, arg2, arg3, arg4), this)
    } else {
      UserDefinedExpression(symbol, sort, listOf(arg1, arg2, arg3, arg4), definition, this)
    }
  }
}

/**
 * SMTFunction of arity 5.
 *
 * Use [invoke] to generate an expression with the given parameters applied.
 */
data class SMTFunction5<T : Sort, S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort, S5 : Sort>(
    override val symbol: Symbol,
    override val sort: T,
    val parameter1: S1,
    val parameter2: S2,
    val parameter3: S3,
    val parameter4: S4,
    val parameter5: S5,
    override val definition: FunctionDef<T>?
) : SMTFunction<T>() {
  override val parameters = listOf(parameter1, parameter2, parameter3, parameter4, parameter5)

  operator fun invoke(
      arg1: Expression<S1>,
      arg2: Expression<S2>,
      arg3: Expression<S3>,
      arg4: Expression<S4>,
      arg5: Expression<S5>
  ): Expression<T> {
    return if (definition == null) {
      UserDeclaredExpression(symbol, sort, listOf(arg1, arg2, arg3, arg4, arg5), this)
    } else {
      UserDefinedExpression(symbol, sort, listOf(arg1, arg2, arg3, arg4, arg5), definition, this)
    }
  }
}

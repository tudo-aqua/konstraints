/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2024 The Konstraints Authors
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
import tools.aqua.konstraints.parser.FunctionDefinition
import tools.aqua.konstraints.parser.SortedVar
import tools.aqua.konstraints.smt.*

fun <T : Sort> SMTProgramBuilder.declaringConst(sort: T) =
    Const(sort, this, "|const!$sort!${UUID.randomUUID()}|")

fun <T : Sort> SMTProgramBuilder.declaringConst(sort: Sort, name: String) = Const(sort, this, name)

fun <T : Sort> SMTProgramBuilder.declaring(sort: T) = Declare(sort, this)

fun <T : Sort, S : Sort> SMTProgramBuilder.declaring(sort: T, par: S) = Declare1(sort, par, this)

fun <T : Sort, S1 : Sort, S2 : Sort> SMTProgramBuilder.declaring(sort: T, par1: S1, par2: S2) =
    Declare2(sort, par1, par2, this)

fun <T : Sort, S1 : Sort, S2 : Sort, S3 : Sort> SMTProgramBuilder.declaring(
    sort: T,
    par1: S1,
    par2: S2,
    par3: S3
) = Declare3(sort, par1, par2, par3, this)

fun <T : Sort, S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort> SMTProgramBuilder.declaring(
    sort: T,
    par1: S1,
    par2: S2,
    par3: S3,
    par4: S4
) = Declare4(sort, par1, par2, par3, par4, this)

fun <T : Sort, S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort, S5 : Sort> SMTProgramBuilder.declaring(
    sort: T,
    par1: S1,
    par2: S2,
    par3: S3,
    par4: S4,
    par5: S5
) = Declare5(sort, par1, par2, par3, par4, par5, this)

fun <T : Sort> SMTProgramBuilder.defining(
    sort: T,
    block: Builder<T>.(List<Expression<*>>) -> Expression<T>
) = Define(sort, block, this)

fun <T : Sort, S : Sort> SMTProgramBuilder.defining(
    sort: T,
    par: S,
    block: Builder<T>.(Expression<S>) -> Expression<T>
) = Define1(sort, block, par, this)

fun <T : Sort, S1 : Sort, S2 : Sort> SMTProgramBuilder.defining(
    sort: T,
    par1: S1,
    par2: S2,
    block: Builder<T>.(Expression<S1>, Expression<S2>) -> Expression<T>
) = Define2(sort, block, par1, par2, this)

fun <T : Sort, S1 : Sort, S2 : Sort, S3 : Sort> SMTProgramBuilder.defining(
    sort: T,
    par1: S1,
    par2: S2,
    par3: S3,
    block: Builder<T>.(Expression<S1>, Expression<S2>, Expression<S3>) -> Expression<T>
) = Define3(sort, block, par1, par2, par3, this)

fun <T : Sort, S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort> SMTProgramBuilder.defining(
    sort: T,
    par1: S1,
    par2: S2,
    par3: S3,
    par4: S4,
    block:
        Builder<T>.(Expression<S1>, Expression<S2>, Expression<S3>, Expression<S4>) -> Expression<T>
) = Define4(sort, block, par1, par2, par3, par4, this)

fun <T : Sort, S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort, S5 : Sort> SMTProgramBuilder.defining(
    sort: T,
    par1: S1,
    par2: S2,
    par3: S3,
    par4: S4,
    par5: S5,
    block:
        Builder<T>.(
            Expression<S1>,
            Expression<S2>,
            Expression<S3>,
            Expression<S4>,
            Expression<S5>) -> Expression<T>
) = Define5(sort, block, par1, par2, par3, par4, par5, this)

class Const<T : Sort>(val sort: T, val program: SMTProgramBuilder, val name: String) {
  operator fun getValue(thisRef: Any?, property: KProperty<*>): Expression<T> {
    program.registerFun(name, sort, emptyList())
    return UserDeclaredExpression(name.symbol(), sort)
  }
}

class Declare<T : Sort>(
    val sort: T,
    val program: SMTProgramBuilder,
    val parameters: List<Sort> = emptyList(),
    val name: String = ""
) {
  operator fun getValue(thisRef: Any?, property: KProperty<*>): SMTFunction<T> {
    val n = name.ifEmpty { "|${thisRef.toString()}|" }

    program.registerFun(n, sort, parameters)
    return SMTFunction(n.symbol(), sort, parameters, null)
  }
}

class Declare1<T : Sort, S : Sort>(
    val sort: T,
    val par: S,
    val program: SMTProgramBuilder,
    val name: String = ""
) {
  operator fun getValue(thisRef: Any?, property: KProperty<*>): SMTFunction1<T, S> {
    val n = name.ifEmpty { "|${thisRef.toString()}|" }

    program.registerFun(n, sort, listOf(par))
    return SMTFunction1(n.symbol(), sort, par, null)
  }
}

class Declare2<T : Sort, S1 : Sort, S2 : Sort>(
    val sort: T,
    val par1: S1,
    val par2: S2,
    val program: SMTProgramBuilder,
    val name: String = ""
) {
  operator fun getValue(thisRef: Any?, property: KProperty<*>): SMTFunction2<T, S1, S2> {
    val n = name.ifEmpty { "|${thisRef.toString()}|" }

    program.registerFun(n, sort, listOf(par1, par2))
    return SMTFunction2(n.symbol(), sort, par1, par2, null)
  }
}

class Declare3<T : Sort, S1 : Sort, S2 : Sort, S3 : Sort>(
    val sort: T,
    val par1: S1,
    val par2: S2,
    val par3: S3,
    val program: SMTProgramBuilder,
    val name: String = ""
) {
  operator fun getValue(thisRef: Any?, property: KProperty<*>): SMTFunction3<T, S1, S2, S3> {
    val n = name.ifEmpty { "|${thisRef.toString()}|" }

    program.registerFun(n, sort, listOf(par1, par2, par3))
    return SMTFunction3(n.symbol(), sort, par1, par2, par3, null)
  }
}

class Declare4<T : Sort, S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort>(
    val sort: T,
    val par1: S1,
    val par2: S2,
    val par3: S3,
    val par4: S4,
    val program: SMTProgramBuilder,
    val name: String = ""
) {
  operator fun getValue(thisRef: Any?, property: KProperty<*>): SMTFunction4<T, S1, S2, S3, S4> {
    val n = name.ifEmpty { "|${thisRef.toString()}|" }

    program.registerFun(n, sort, listOf(par1, par2, par3, par4))
    return SMTFunction4(n.symbol(), sort, par1, par2, par3, par4, null)
  }
}

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
  operator fun getValue(
      thisRef: Any?,
      property: KProperty<*>
  ): SMTFunction5<T, S1, S2, S3, S4, S5> {
    val n = name.ifEmpty { "|${thisRef.toString()}|" }

    program.registerFun(n, sort, listOf(par1, par2, par3, par4, par5))
    return SMTFunction5(n.symbol(), sort, par1, par2, par3, par4, par5, null)
  }
}

class Define<T : Sort>(
    val sort: T,
    val block: Builder<T>.(List<Expression<Sort>>) -> Expression<T>,
    val program: SMTProgramBuilder,
    val parameters: List<Sort> = emptyList(),
    val name: String = ""
) {
  operator fun getValue(thisRef: Any?, property: KProperty<*>): SMTFunction<T> {
    val n = name.ifEmpty { "|${thisRef.toString()}|" }
    val sortedVars =
        parameters.mapIndexed { id, sort ->
          SortedVar("|${thisRef.toString()}!local!$sort!$id|".symbol(), sort)
        }
    val term = Builder<T>().block(sortedVars.map { it.instance })

    program.registerFun(n, sort, sortedVars, term)
    return SMTFunction(
        n.symbol(), sort, parameters, FunctionDefinition(n.symbol(), emptyList(), sort, term))
  }
}

class Define1<T : Sort, S : Sort>(
    val sort: T,
    val block: Builder<T>.(Expression<S>) -> Expression<T>,
    val par: S,
    val program: SMTProgramBuilder,
    val name: String = ""
) {
  operator fun getValue(thisRef: Any?, property: KProperty<*>): SMTFunction1<T, S> {
    val n = name.ifEmpty { "|${thisRef.toString()}|" }
    val sortedVar = SortedVar("|${thisRef.toString()}!local!$par!1|".symbol(), par)
    val term = Builder<T>().block(sortedVar.instance)

    program.registerFun(n, sort, listOf(sortedVar), term)
    return SMTFunction1(
        n.symbol(), sort, par, FunctionDefinition(n.symbol(), listOf(sortedVar), sort, term))
  }
}

class Define2<T : Sort, S1 : Sort, S2 : Sort>(
    val sort: T,
    val block: Builder<T>.(Expression<S1>, Expression<S2>) -> Expression<T>,
    val par1: S1,
    val par2: S2,
    val program: SMTProgramBuilder,
    val name: String = ""
) {
  operator fun getValue(thisRef: Any?, property: KProperty<*>): SMTFunction2<T, S1, S2> {
    val n = name.ifEmpty { "|${thisRef.toString()}|" }
    val sortedVar1 = SortedVar("|${thisRef.toString()}!local!$par1!1|".symbol(), par1)
    val sortedVar2 = SortedVar("|${thisRef.toString()}!local!$par2!2|".symbol(), par2)
    val term = Builder<T>().block(sortedVar1.instance, sortedVar2.instance)

    program.registerFun(n, sort, listOf(sortedVar1, sortedVar2), term)

    return SMTFunction2(
        n.symbol(),
        sort,
        par1,
        par2,
        FunctionDefinition(n.symbol(), listOf(sortedVar1, sortedVar2), sort, term))
  }
}

class Define3<T : Sort, S1 : Sort, S2 : Sort, S3 : Sort>(
    val sort: T,
    val block: Builder<T>.(Expression<S1>, Expression<S2>, Expression<S3>) -> Expression<T>,
    val par1: S1,
    val par2: S2,
    val par3: S3,
    val program: SMTProgramBuilder,
    val name: String = ""
) {
  operator fun getValue(thisRef: Any?, property: KProperty<*>): SMTFunction3<T, S1, S2, S3> {
    val n = name.ifEmpty { "|${thisRef.toString()}|" }
    val sortedVar1 = SortedVar("|${thisRef.toString()}!local!$par1!1|".symbol(), par1)
    val sortedVar2 = SortedVar("|${thisRef.toString()}!local!$par2!2|".symbol(), par2)
    val sortedVar3 = SortedVar("|${thisRef.toString()}!local!$par3!3|".symbol(), par3)
    val term = Builder<T>().block(sortedVar1.instance, sortedVar2.instance, sortedVar3.instance)

    program.registerFun(n, sort, listOf(sortedVar1, sortedVar2, sortedVar3), term)

    return SMTFunction3(
        n.symbol(),
        sort,
        par1,
        par2,
        par3,
        FunctionDefinition(n.symbol(), listOf(sortedVar1, sortedVar2, sortedVar3), sort, term))
  }
}

class Define4<T : Sort, S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort>(
    val sort: T,
    val block:
        Builder<T>.(Expression<S1>, Expression<S2>, Expression<S3>, Expression<S4>) -> Expression<
                T>,
    val par1: S1,
    val par2: S2,
    val par3: S3,
    val par4: S4,
    val program: SMTProgramBuilder,
    val name: String = ""
) {
  operator fun getValue(thisRef: Any?, property: KProperty<*>): SMTFunction4<T, S1, S2, S3, S4> {
    val n = name.ifEmpty { "|${thisRef.toString()}|" }
    val sortedVar1 = SortedVar("|${thisRef.toString()}!local!$par1!1|".symbol(), par1)
    val sortedVar2 = SortedVar("|${thisRef.toString()}!local!$par2!2|".symbol(), par2)
    val sortedVar3 = SortedVar("|${thisRef.toString()}!local!$par3!3|".symbol(), par3)
    val sortedVar4 = SortedVar("|${thisRef.toString()}!local!$par4!4|".symbol(), par4)
    val term =
        Builder<T>()
            .block(
                sortedVar1.instance, sortedVar2.instance, sortedVar3.instance, sortedVar4.instance)

    program.registerFun(n, sort, listOf(sortedVar1, sortedVar2, sortedVar3, sortedVar4), term)

    return SMTFunction4(
        n.symbol(),
        sort,
        par1,
        par2,
        par3,
        par4,
        FunctionDefinition(
            n.symbol(), listOf(sortedVar1, sortedVar2, sortedVar3, sortedVar4), sort, term))
  }
}

class Define5<T : Sort, S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort, S5 : Sort>(
    val sort: T,
    val block:
        Builder<T>.(
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
  operator fun getValue(
      thisRef: Any?,
      property: KProperty<*>
  ): SMTFunction5<T, S1, S2, S3, S4, S5> {
    val n = name.ifEmpty { "|${thisRef.toString()}|" }
    val sortedVar1 = SortedVar("|${thisRef.toString()}!local!$par1!1|".symbol(), par1)
    val sortedVar2 = SortedVar("|${thisRef.toString()}!local!$par2!2|".symbol(), par2)
    val sortedVar3 = SortedVar("|${thisRef.toString()}!local!$par3!3|".symbol(), par3)
    val sortedVar4 = SortedVar("|${thisRef.toString()}!local!$par4!4|".symbol(), par4)
    val sortedVar5 = SortedVar("|${thisRef.toString()}!local!$par5!5|".symbol(), par5)
    val term =
        Builder<T>()
            .block(
                sortedVar1.instance,
                sortedVar2.instance,
                sortedVar3.instance,
                sortedVar4.instance,
                sortedVar5.instance)

    program.registerFun(
        n, sort, listOf(sortedVar1, sortedVar2, sortedVar3, sortedVar4, sortedVar5), term)

    return SMTFunction5(
        n.symbol(),
        sort,
        par1,
        par2,
        par3,
        par4,
        par5,
        FunctionDefinition(
            n.symbol(),
            listOf(sortedVar1, sortedVar2, sortedVar3, sortedVar4, sortedVar5),
            sort,
            term))
  }
}

data class SMTFunction<T : Sort>(
    val name: Symbol,
    val sort: T,
    val parameters: List<Sort>,
    val definition: FunctionDefinition<T>?
) {
  operator fun invoke(args: List<Expression<*>>): Expression<T> {
    require(args.size == parameters.size)

    return if (definition == null) {
      UserDeclaredExpression(name, sort, args)
    } else {
      UserDefinedExpression(name, sort, emptyList(), definition)
    }
  }
}

data class SMTFunction1<T : Sort, S : Sort>(
    val name: Symbol,
    val sort: T,
    val parameter: S,
    val definition: FunctionDefinition<T>?
) {
  operator fun invoke(arg: Expression<S>): Expression<T> {
    return if (definition == null) {
      UserDeclaredExpression(name, sort, listOf(arg))
    } else {
      UserDefinedExpression(name, sort, listOf(arg), definition)
    }
  }
}

data class SMTFunction2<T : Sort, S1 : Sort, S2 : Sort>(
    val name: Symbol,
    val sort: T,
    val parameter1: S1,
    val parameter2: S2,
    val definition: FunctionDefinition<T>?
) {
  operator fun invoke(arg1: Expression<S1>, arg2: Expression<S2>): Expression<T> {
    return if (definition == null) {
      UserDeclaredExpression(name, sort, listOf(arg1, arg2))
    } else {
      UserDefinedExpression(name, sort, listOf(arg1, arg2), definition)
    }
  }
}

data class SMTFunction3<T : Sort, S1 : Sort, S2 : Sort, S3 : Sort>(
    val name: Symbol,
    val sort: T,
    val parameter1: S1,
    val parameter2: S2,
    val parameter3: S3,
    val definition: FunctionDefinition<T>?
) {
  operator fun invoke(
      arg1: Expression<S1>,
      arg2: Expression<S2>,
      arg3: Expression<S3>
  ): Expression<T> {
    return if (definition == null) {
      UserDeclaredExpression(name, sort, listOf(arg1, arg2, arg3))
    } else {
      UserDefinedExpression(name, sort, listOf(arg1, arg2, arg3), definition)
    }
  }
}

data class SMTFunction4<T : Sort, S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort>(
    val name: Symbol,
    val sort: T,
    val parameter1: S1,
    val parameter2: S2,
    val parameter3: S3,
    val parameter4: S4,
    val definition: FunctionDefinition<T>?
) {
  operator fun invoke(
      arg1: Expression<S1>,
      arg2: Expression<S2>,
      arg3: Expression<S3>,
      arg4: Expression<S4>
  ): Expression<T> {
    return if (definition == null) {
      UserDeclaredExpression(name, sort, listOf(arg1, arg2, arg3, arg4))
    } else {
      UserDefinedExpression(name, sort, listOf(arg1, arg2, arg3, arg4), definition)
    }
  }
}

data class SMTFunction5<T : Sort, S1 : Sort, S2 : Sort, S3 : Sort, S4 : Sort, S5 : Sort>(
    val name: Symbol,
    val sort: T,
    val parameter1: S1,
    val parameter2: S2,
    val parameter3: S3,
    val parameter4: S4,
    val parameter5: S5,
    val definition: FunctionDefinition<T>?
) {
  operator fun invoke(
      arg1: Expression<S1>,
      arg2: Expression<S2>,
      arg3: Expression<S3>,
      arg4: Expression<S4>,
      arg5: Expression<S5>
  ): Expression<T> {
    return if (definition == null) {
      UserDeclaredExpression(name, sort, listOf(arg1, arg2, arg3, arg4, arg5))
    } else {
      UserDefinedExpression(name, sort, listOf(arg1, arg2, arg3, arg4, arg5), definition)
    }
  }
}

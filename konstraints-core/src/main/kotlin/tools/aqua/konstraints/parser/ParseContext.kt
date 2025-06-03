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

package tools.aqua.konstraints.parser

import tools.aqua.konstraints.smt.*
import tools.aqua.konstraints.theories.*

val logicLookup =
    mapOf(
        Theories.CORE to CoreTheory,
        Theories.FIXED_SIZE_BIT_VECTORS to BitVectorExpressionTheory,
        Theories.INTS to IntsTheory,
        Theories.REALS to RealsTheory,
        Theories.REALS_INTS to RealsIntsTheory,
        Theories.FLOATING_POINT to FloatingPointTheory,
        Theories.ARRAYS_EX to ArrayExTheory,
        Theories.STRINGS to StringsTheory)

class IllegalFunctionOverloadException(func: String, msg: String) :
    RuntimeException("Illegal overload of $func: $msg.")

internal class FunctionAlreadyDeclaredException(func: SMTFunction<*>) :
    RuntimeException("Function $func has already been declared")

class SortAlreadyDeclaredException(sort: Symbol, arity: Int) :
    RuntimeException("Sort ($sort $arity) has already been declared")

class TheoryAlreadySetException :
    RuntimeException(
        "Theory has already been set, use the smt-command (reset) before using a new logic or theory")

class IllegalOperationException(operation: String, reason: String) :
    RuntimeException("Illegal Operation $operation: $reason.")

/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2023 The Konstraints Authors
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

import org.petitparser.context.Token
import tools.aqua.konstraints.*

sealed interface ProtoCommand {}

data object ProtoAssert : ProtoCommand {}

data class ProtoDeclareConst(val name: Symbol, val sort: ProtoSort) : ProtoCommand {}

data class ProtoDeclareFun(val name: Symbol, val parameters: List<ProtoSort>, val sort: ProtoSort) :
    ProtoCommand {}

data class Symbol(val token: Token) {}

data class ProtoSort(val token: Token, val sorts: List<Any>) {}

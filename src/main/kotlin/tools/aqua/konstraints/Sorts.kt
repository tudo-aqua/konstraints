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

package tools.aqua.konstraints

open class Sort(val name: Symbol, val indices : List<Index>, val parameters : List<Sort>) {
    constructor(name: String, indices : List<Index>, parameters : List<Sort>) : this(Symbol(name), indices, parameters)
}

object BoolSort : Sort("Bool", listOf(), listOf())
class BVSort(val bits : Int) : Sort("BitVec", listOf(NumeralIndex(bits)), listOf())
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

import java.math.BigInteger

class OptionsBuilder {
  val stringOptions = mutableMapOf<String, String>()
  val boolOptions = mutableMapOf<String, Boolean>()
  val numeralOptions = mutableMapOf<String, BigInteger>()

  fun diagnosticOutputChannel(value: String): OptionsBuilder {
    stringOptions[":diagnostic-output-channel"] = value
    return this
  }

  fun globalDeclarations(value: Boolean): OptionsBuilder {
    boolOptions[":global-declarations"] = value
    return this
  }

  fun interactiveModel(value: Boolean): OptionsBuilder {
    boolOptions[":interactive-model"] = value
    return this
  }

  fun printSuccess(value: Boolean): OptionsBuilder {
    boolOptions[":print-success"] = value
    return this
  }

  fun produceAssertions(value: Boolean): OptionsBuilder {
    boolOptions[":produce-assertions"] = value
    return this
  }

  fun produceAssignments(value: Boolean): OptionsBuilder {
    boolOptions[":produce-assignments"] = value
    return this
  }

  fun produceModels(value: Boolean): OptionsBuilder {
    boolOptions[":produce-models"] = value
    return this
  }

  fun produceProofs(value: Boolean): OptionsBuilder {
    boolOptions[":produce-proofs"] = value
    return this
  }

  fun produceUnsatAssumptions(value: Boolean): OptionsBuilder {
    boolOptions[":produce-unsat-assumptions"] = value
    return this
  }

  fun produceUnsatCores(value: Boolean): OptionsBuilder {
    boolOptions[":produce-unsat-cores"] = value
    return this
  }

  fun randomSeed(value: BigInteger): OptionsBuilder {
    numeralOptions[":random-seed"] = value
    return this
  }

  fun randomSeed(value: Int): OptionsBuilder {
    numeralOptions[":random-seed"] = value.toBigInteger()
    return this
  }

  fun regularOutputChannel(value: String): OptionsBuilder {
    stringOptions[":regular-output-channel"] = value
    return this
  }

  fun reproducibleResourceLimit(value: BigInteger): OptionsBuilder {
    numeralOptions[":reproducible-resource-limit"] = value
    return this
  }

  fun reproducibleResourceLimit(value: Int): OptionsBuilder {
    numeralOptions[":reproducible-resource-limit"] = value.toBigInteger()
    return this
  }

  fun verbosity(value: BigInteger): OptionsBuilder {
    numeralOptions[":verbosity"] = value
    return this
  }

  fun verbosity(value: Int): OptionsBuilder {
    numeralOptions[":verbosity"] = value.toBigInteger()
    return this
  }

  infix fun String.setTo(value: String): OptionsBuilder {
    // add ":" prefix to option name if not already present
    val option =
        this.apply {
          if (!this.startsWith(':')) {
            this.padStart(this.length + 1, ':')
          }
        }
    stringOptions[option] = value

    return this@OptionsBuilder
  }

  infix fun String.setTo(value: Boolean): OptionsBuilder {
    // add ":" prefix to option name if not already present
    val option =
        this.apply {
          if (!this.startsWith(':')) {
            this.padStart(this.length + 1, ':')
          }
        }
    boolOptions[option] = value

    return this@OptionsBuilder
  }

  infix fun String.setTo(value: BigInteger): OptionsBuilder {
    // add ":" prefix to option name if not already present
    val option =
        this.apply {
          if (!this.startsWith(':')) {
            this.padStart(this.length + 1, ':')
          }
        }
    numeralOptions[option] = value

    return this@OptionsBuilder
  }

  infix fun String.setTo(value: Int): OptionsBuilder {
    // add ":" prefix to option name if not already present
    val option =
        this.apply {
          if (!this.startsWith(':')) {
            this.padStart(this.length + 1, ':')
          }
        }
    numeralOptions[option] = value.toBigInteger()

    return this@OptionsBuilder
  }
}

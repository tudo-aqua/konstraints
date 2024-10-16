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

  /**
   * Set diagnostic-output-channel to [value].
   *
   * The argument is a string consisting of the name of a file to be used subsequently as the
   * diagnostic output channel. The input value "stderr" is interpreted specially to mean
   * the solver’s standard error channel. With other filenames, subsequent solver output is to
   * be appended to the named file (and the file should be first created if it does not already
   * exist).
   *
   * default: "stderr".
   * support: required.
   */
  fun diagnosticOutputChannel(value: String): OptionsBuilder {
    stringOptions[":diagnostic-output-channel"] = value
    return this
  }

  /**
   * Set global-declarations to [value].
   *
   * If the solver supports this option, setting it to true causes all declarations and definitions
   * to be global (permanent) as opposed to being added to the current assertion level.
   *
   * default: false.
   * support: optional.
   * mode: start.
   */
  fun globalDeclarations(value: Boolean): OptionsBuilder {
    boolOptions[":global-declarations"] = value
    return this
  }

  /**
   * Set interactive-mode to [value].
   *
   * The old name for produce-assertions. Deprecated.
   *
   * default: false.
   * support: optional.
   * mode: start.
   */
  @Deprecated("The old name for produce-assertions. Prefer using produce-assertions.", level = DeprecationLevel.WARNING)
  fun interactiveMode(value: Boolean): OptionsBuilder {
    boolOptions[":interactive-model"] = value
    return this
  }

  /**
   * Set print-success to [value].
   *
   * Setting this option to true causes the solver to print success as a response to commands.
   * Other output remains unchanged.
   *
   * default: false.
   * support: required.
   */
  fun printSuccess(value: Boolean): OptionsBuilder {
    boolOptions[":print-success"] = value
    return this
  }

  /**
   * Set produce-assertions to [value].
   *
   * If the solver supports this option, setting it to true enables the get-assertions command.
   * This option was called interactive-mode in previous versions.
   *
   * default: false.
   * support: optional.
   * mode: start.
   */
  fun produceAssertions(value: Boolean): OptionsBuilder {
    boolOptions[":produce-assertions"] = value
    return this
  }

  /**
   * Set produce-assignments to [value].
   *
   * If supported, this enables the command get-assignment.
   *
   * default: false.
   * support: optional.
   * mode: start.
   */
  fun produceAssignments(value: Boolean): OptionsBuilder {
    boolOptions[":produce-assignments"] = value
    return this
  }

  /**
   * Set produce-models to [value].
   *
   * If supported, this enables the commands get-value and get-model.
   *
   * default: false.
   * support: optional.
   * mode: start.
   */
  fun produceModels(value: Boolean): OptionsBuilder {
    boolOptions[":produce-models"] = value
    return this
  }

  /**
   * Set produce-proofs to [value].
   *
   * If supported, this enables the command get-proof.
   *
   * default: false.
   * support: optional.
   * mode: start.
   */
  fun produceProofs(value: Boolean): OptionsBuilder {
    boolOptions[":produce-proofs"] = value
    return this
  }

  /**
   * Set produce-unsat-assumptions to [value].
   *
   * If supported, this enables the command get-unsat-assumptions.
   *
   * default: false.
   * support: optional.
   * mode: start.
   */
  fun produceUnsatAssumptions(value: Boolean): OptionsBuilder {
    boolOptions[":produce-unsat-assumptions"] = value
    return this
  }

  /**
   * Set produce-unsat-cores to [value].
   *
   * If supported, this enables the command get-unsat-core.
   *
   * default: false.
   * support: optional.
   * mode: start.
   */
  fun produceUnsatCores(value: Boolean): OptionsBuilder {
    boolOptions[":produce-unsat-cores"] = value
    return this
  }

  /**
   * Set random-seed to [value].
   *
   * The argument is a numeral for the solver to use as a random seed, in case the solver
   * uses (pseudo-)randomization. The default value of 0 means that the solver can use
   * any random seed—possibly even a different one for each run of the same script. The
   * intended use of the option is to force the solver to produce identical results whenever
   * given identical input (including identical non-zero seeds) on repeated runs of the solver.
   *
   * default: 0.
   * support: optional.
   * mode: start.
   */
  fun randomSeed(value: BigInteger): OptionsBuilder {
    numeralOptions[":random-seed"] = value
    return this
  }

  /**
   * Set random-seed to [value].
   *
   * The argument is a numeral for the solver to use as a random seed, in case the solver
   * uses (pseudo-)randomization. The default value of 0 means that the solver can use
   * any random seed—possibly even a different one for each run of the same script. The
   * intended use of the option is to force the solver to produce identical results whenever
   * given identical input (including identical non-zero seeds) on repeated runs of the solver.
   *
   * default: 0.
   * support: optional.
   * mode: start.
   */
  fun randomSeed(value: Int): OptionsBuilder {
    numeralOptions[":random-seed"] = value.toBigInteger()
    return this
  }

  /**
   * Set regular-output-channel to [value].
   *
   * The argument should be a filename to use subsequently for the regular output channel.
   * The input value "stdout" is interpreted specially to mean the solver’s standard output
   * channel. With other filenames, subsequent solver output is to be appended to the named
   * file (and the file should be first created if it does not already exist).
   *
   * default: "stdout".
   * support: required.
   */
  fun regularOutputChannel(value: String): OptionsBuilder {
    stringOptions[":regular-output-channel"] = value
    return this
  }

  /**
   * Set reproducible-resource-limit to [value].
   *
   * If the solver supports this option, setting it to 0 disables it. Setting it a non-zero numeral
   * n will cause each subsequent check command to terminate within a bounded amount
   * of time dependent on n. The internal implementation of this option and its relation
   * to run time or other concrete resources can be solver-specific. However, it is required
   * that the invocation of a check command return unknown whenever the solver is unable
   * to determine the satisfiability of the formulas in the current context within the current
   * resource limit. Setting a higher value of n should allow more resources to be used,
   * which may cause the command to return sat or unsat instead of unknown. Furthermore,
   * the returned result should depend deterministically on n; specifically, it should be the
   * same every time the solver is run with the same sequence of previous commands on the
   * same machine (and with an arbitrarily long external time out). If the solver makes use
   * of randomization, it may require the :random-seed option to be set to a value other than
   * 0 before :reproducible-resource-limit can be set to a positive value.
   *
   * default: 0.
   * support: optional.
   */
  fun reproducibleResourceLimit(value: BigInteger): OptionsBuilder {
    numeralOptions[":reproducible-resource-limit"] = value
    return this
  }

  /**
   * Set reproducible-resource-limit to [value].
   *
   * If the solver supports this option, setting it to 0 disables it. Setting it a non-zero numeral
   * n will cause each subsequent check command to terminate within a bounded amount
   * of time dependent on n. The internal implementation of this option and its relation
   * to run time or other concrete resources can be solver-specific. However, it is required
   * that the invocation of a check command return unknown whenever the solver is unable
   * to determine the satisfiability of the formulas in the current context within the current
   * resource limit. Setting a higher value of n should allow more resources to be used,
   * which may cause the command to return sat or unsat instead of unknown. Furthermore,
   * the returned result should depend deterministically on n; specifically, it should be the
   * same every time the solver is run with the same sequence of previous commands on the
   * same machine (and with an arbitrarily long external time out). If the solver makes use
   * of randomization, it may require the :random-seed option to be set to a value other than
   * 0 before :reproducible-resource-limit can be set to a positive value.
   *
   * default: 0.
   * support: optional.
   */
  fun reproducibleResourceLimit(value: Int): OptionsBuilder {
    numeralOptions[":reproducible-resource-limit"] = value.toBigInteger()
    return this
  }

  /**
   * Set verbosity to [value].
   *
   * The argument is a numeral controlling the level of diagnostic output produced by the
   * solver. All such output should be written to the diagnostic output channel(31) which can
   * be set and later changed via the diagnostic-output-channel option. An argument of 0
   * requests that no such output be produced. Higher values correspond to more verbose
   * output.
   *
   * default: no standard default value.
   * support: optional.
   */
  fun verbosity(value: BigInteger): OptionsBuilder {
    numeralOptions[":verbosity"] = value
    return this
  }

  /**
   * Set verbosity to [value].
   *
   * The argument is a numeral controlling the level of diagnostic output produced by the
   * solver. All such output should be written to the diagnostic output channel(31) which can
   * be set and later changed via the diagnostic-output-channel option. An argument of 0
   * requests that no such output be produced. Higher values correspond to more verbose
   * output.
   *
   * default: no standard default value.
   * support: optional.
   */
  fun verbosity(value: Int): OptionsBuilder {
    numeralOptions[":verbosity"] = value.toBigInteger()
    return this
  }

  /**
   * Set any named option [this] to [value].
   *
   * If [this] does not have the prefix ':'. its automatically added.
   */
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

  /**
   * Set any named option [this] to [value].
   *
   * If [this] does not have the prefix ':'. its automatically added.
   */
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

  /**
   * Set any named option [this] to [value].
   *
   * If [this] does not have the prefix ':'. its automatically added.
   */
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

  /**
   * Set any named option [this] to [value].
   *
   * If [this] does not have the prefix ':'. its automatically added.
   */
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

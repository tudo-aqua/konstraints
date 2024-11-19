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

package tools.aqua

private val stableKeywords = setOf("RELEASE", "FINAL", "GA")
private val versionRegex = "^[0-9,.v-]+(-r)?$".toRegex()

/** Checks is this string appears to encode a stable version. */
val String.isStableVersion: Boolean
  get() {
    val hasStableKeyword = stableKeywords.any { this.uppercase().contains(it) }
    return hasStableKeyword || versionRegex.matches(this)
  }

/** Checks is this string appears to encode a prerelease version. */
val String.isPrereleaseVersion: Boolean
  get() = !isStableVersion
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

plugins {
  id("konstraints.developer-utilities")
  id("konstraints.kotlin-library")
  id("konstraints.kotlin-static-analysis")
  id("konstraints.maven-library")
}

metadata {
  name = "Konstraints Core"
  description = "A library for working with SMT expressions on the JVM"
}

dependencies {
  implementation(libs.commons.compress)
  implementation(libs.commons.io)
  implementation(libs.kotlin.coroutines)
  implementation(libs.petitparser.core)
}

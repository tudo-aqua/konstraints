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

plugins {
  id("kotlin")
  id("org.jetbrains.kotlinx.benchmark") version "0.4.14"
  id("konstraints.developer-utilities")
  id("konstraints.kotlin-library")
  id("konstraints.kotlin-static-analysis")
  id("konstraints.maven-library")
  kotlin("plugin.allopen") version "2.0.20"
}

dependencies {
  implementation(project(":konstraints-core"))
  implementation("org.jetbrains.kotlinx:kotlinx-benchmark-runtime:0.4.13")
}

sourceSets { create("benchmark") }

kotlin {
  target { compilations.getByName("benchmark").associateWith(compilations.getByName("main")) }
}

benchmark { targets { register("benchmark") } }

repositories { mavenCentral() }

allOpen { annotation("org.openjdk.jmh.annotations.State") }

benchmark { targets { register("main") } }

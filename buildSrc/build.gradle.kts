/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2026 The Konstraints Authors
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

plugins { `kotlin-dsl` }

repositories {
  gradlePluginPortal()
  mavenCentral()
}

dependencies {
  // dependency catalog sharing
  implementation(files(libs.javaClass.superclass.protectionDomain.codeSource.location))

  implementation(libs.gradle.detekt)
  implementation(libs.gradle.gitVersioning)
  implementation(libs.gradle.kotlin.dokka)
  implementation(libs.gradle.kotlin.jvm)
  implementation(libs.gradle.kotlin.serialization)
  implementation(libs.gradle.nexus.publish)
  implementation(libs.gradle.node)
  implementation(libs.gradle.spotless)
  implementation(libs.gradle.taskTree)
  implementation(libs.gradle.versions)
}

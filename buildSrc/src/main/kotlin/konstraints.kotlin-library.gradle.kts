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

import org.gradle.accessors.dm.LibrariesForLibs
import org.gradle.api.plugins.JavaBasePlugin.DOCUMENTATION_GROUP
import org.gradle.api.tasks.testing.logging.TestLogEvent.*

plugins {
  `java-library`
  kotlin("jvm")

  id("org.jetbrains.dokka")
  id("org.jetbrains.dokka-javadoc")
}

val libs = the<LibrariesForLibs>()

repositories { mavenCentral() }

dependencies {
  testImplementation(platform(libs.junit.bom))
  testImplementation(libs.junit.jupiter)
  testRuntimeOnly(libs.junit.launcher)
}

val kdocJar: TaskProvider<Jar> by
    tasks.registering(Jar::class) {
      group = DOCUMENTATION_GROUP
      archiveClassifier = "kdoc"
      from(tasks.dokkaGeneratePublicationHtml.flatMap { it.outputDirectory })
    }

val kdoc: Configuration by
    configurations.creating {
      isCanBeConsumed = true
      isCanBeResolved = false
    }

artifacts { add(kdoc.name, kdocJar) }

tasks.register("javadocJar", Jar::class) {
  group = DOCUMENTATION_GROUP
  archiveClassifier = "javadoc"
  from(tasks.dokkaGeneratePublicationJavadoc.flatMap { it.outputDirectory })
}

java {
  withJavadocJar()
  withSourcesJar()
}

kotlin { jvmToolchain(libs.versions.java.jdk.get().toInt()) }

tasks.test {
  useJUnitPlatform()
  testLogging { events(FAILED, SKIPPED, PASSED) }
}

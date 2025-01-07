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

import org.gradle.accessors.dm.LibrariesForLibs
import org.gradle.kotlin.dsl.*
import tools.aqua.MetadataExtension
import tools.aqua.commonSetup

plugins {
  `java-library`
  `maven-publish`
  signing
}

val libs = the<LibrariesForLibs>()

repositories { mavenCentral() }

java { toolchain { languageVersion = JavaLanguageVersion.of(libs.versions.java.jdk.get()) } }

val metadata = project.extensions.create<MetadataExtension>("metadata")

val maven by
    publishing.publications.creating(MavenPublication::class) {
      from(components["java"])

      pom { commonSetup(metadata) }
    }

signing {
  setRequired { gradle.taskGraph.allTasks.any { it is PublishToMavenRepository } }
  useGpgCmd()
  sign(maven)
}

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

import com.vanniktech.maven.publish.JavaLibrary
import com.vanniktech.maven.publish.JavadocJar
import com.vanniktech.maven.publish.SourcesJar
import tools.aqua.MetadataExtension
import tools.aqua.commonSetup

plugins { id("com.vanniktech.maven.publish") }

repositories { mavenCentral() }

val metadata = project.extensions.create<MetadataExtension>("metadata")

mavenPublishing {
  publishToMavenCentral()
  signAllPublications()

  // unfortunately, we have to add an empty JAR in this step due to Gradle / Vanniktech limitations
  configure(JavaLibrary(JavadocJar.None(), SourcesJar.None()))

  pom {
    packaging = "pom"
    commonSetup(metadata)
  }
}

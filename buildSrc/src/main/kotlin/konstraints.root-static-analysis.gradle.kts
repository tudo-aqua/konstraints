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

import com.diffplug.gradle.spotless.KotlinExtension
import com.diffplug.gradle.spotless.KotlinGradleExtension
import com.github.gradle.node.variant.computeNodeDir
import com.github.gradle.node.variant.computeNodeExec
import org.gradle.accessors.dm.LibrariesForLibs
import org.gradle.kotlin.dsl.the

plugins {
  id("com.github.node-gradle.node")
  id("com.diffplug.spotless")
}

val libs = the<LibrariesForLibs>()

repositories { mavenCentral() }

node {
  download = true
  workDir = layout.buildDirectory.dir("nodejs")
}

spotless {
  kotlinGradle {
    licenseHeaderFile(project.file("config/license/Apache-2.0-cstyle"), "(import|plugins)")
        .updateYearWithLatest(true)
    ktfmt()
  }
  format("kotlinBuildSrc", KotlinExtension::class.java) {
    target("buildSrc/src/*/kotlin/**/*.kt")
    licenseHeaderFile(rootProject.file("config/license/Apache-2.0-cstyle"))
        .updateYearWithLatest(true)
    ktfmt()
  }
  format("kotlinGradleBuildSrc", KotlinGradleExtension::class.java) {
    target("buildSrc/src/*/kotlin/**/*.gradle.kts", "buildSrc/*.gradle.kts")
    licenseHeaderFile(
            rootProject.file("config/license/Apache-2.0-cstyle"),
            "(dependencyResolutionManagement|import|plugins)")
        .updateYearWithLatest(true)
    ktfmt()
  }
  format("contribPython") {
    target("contrib/*.py")
    licenseHeaderFile(rootProject.file("config/license/Apache-2.0-hashmark"), "import")
        .skipLinesMatching("#!")
        .updateYearWithLatest(true)
  }
  format("contribShell") {
    target("contrib/*.sh")
    licenseHeaderFile(rootProject.file("config/license/Apache-2.0-hashmark"), "set")
        .skipLinesMatching("#!")
        .updateYearWithLatest(true)
  }
  format("contribSingularity") {
    target("contrib/*.def")
    licenseHeaderFile(rootProject.file("config/license/Apache-2.0-hashmark"), "Bootstrap:")
        .updateYearWithLatest(true)
  }
  format("properties") {
    target("*.properties")
    licenseHeaderFile(rootProject.file("config/license/Apache-2.0-hashmark"), "[a-zA-Z]")
        .updateYearWithLatest(true)
  }
  format("markdown") {
    target(".github/**/*.md", "*.md")
    licenseHeaderFile(rootProject.file("config/license/CC-BY-4.0-xmlstyle"), "#+")
        .updateYearWithLatest(true)
    prettier()
        .npmInstallCache()
        .nodeExecutable(computeNodeExec(node, computeNodeDir(node)).get())
        .config(mapOf("parser" to "markdown", "printWidth" to 100, "proseWrap" to "always"))
  }
  yaml {
    target("config/**/*.yml", ".github/**/*.yml", "CITATION.cff")
    licenseHeaderFile(rootProject.file("config/license/Apache-2.0-hashmark"), "[A-Za-z-]+:")
        .updateYearWithLatest(true)
    prettier()
        .npmInstallCache()
        .nodeExecutable(computeNodeExec(node, computeNodeDir(node)).get())
        .config(mapOf("parser" to "yaml", "printWidth" to 100))
  }
  format("toml") {
    target("gradle/libs.versions.toml")
    licenseHeaderFile(rootProject.file("config/license/Apache-2.0-hashmark"), """\[[A-Za-z-]+]""")
        .updateYearWithLatest(true)
    prettier(mapOf("prettier-plugin-toml" to libs.versions.prettier.toml.get()))
        .npmInstallCache()
        .nodeExecutable(computeNodeExec(node, computeNodeDir(node)).get())
        .config(
            mapOf(
                "plugins" to listOf("prettier-plugin-toml"),
                "parser" to "toml",
                "alignComments" to false,
                "printWidth" to 100,
            ))
  }
}

tasks.named("spotlessMarkdown") { dependsOn(tasks.npmSetup) }

tasks.named("spotlessToml") { dependsOn(tasks.npmSetup) }

tasks.named("spotlessYaml") { dependsOn(tasks.npmSetup) }

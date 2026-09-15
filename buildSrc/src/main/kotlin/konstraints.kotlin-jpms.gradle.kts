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

import org.gradle.api.plugins.JavaBasePlugin.VERIFICATION_GROUP
import org.jetbrains.kotlin.gradle.tasks.KotlinCompile
import tools.aqua.CheckModuleExportsTask
import tools.aqua.JavaModuleExtension

plugins {
  `java-library`
  kotlin("jvm")
}

val javaModule = extensions.create<JavaModuleExtension>("javaModule")

// Resolve the compile and runtime classpaths as a module path wherever a module declaration is
// present, so that the `requires` directives can actually be satisfied.
java { modularity.inferModulePath = true }

// The Kotlin compiler does not understand module declarations, so `module-info.java` is left to
// javac. It lives in src/main/java and would otherwise be picked up for Java-interop analysis.
tasks.named<KotlinCompile>("compileKotlin") { exclude("module-info.java") }

val kotlinMainClasses: Provider<Directory> =
    tasks.named<KotlinCompile>("compileKotlin").flatMap { it.destinationDirectory }

tasks.named<JavaCompile>("compileJava") {
  // javac verifies that every exported package exists and that every used package is required.
  // As all of the module's classes are produced by the Kotlin compiler, they have to be patched
  // into the module under compilation.
  options.compilerArgumentProviders.add(
      CommandLineArgumentProvider {
        listOf("--patch-module", "${javaModule.name.get()}=${kotlinMainClasses.get().asFile}")
      }
  )
}

val checkModuleExports: TaskProvider<CheckModuleExportsTask> by
    tasks.registering(CheckModuleExportsTask::class) {
      group = VERIFICATION_GROUP
      description = "Checks that the module declaration exports every non-internal package."

      moduleInfo = layout.projectDirectory.file("src/main/java/module-info.java")
      classes = kotlinMainClasses
      internalPackages = javaModule.internalPackages
      report = layout.buildDirectory.file("reports/jpms/exported-packages.txt")
    }

tasks.check { dependsOn(checkModuleExports) }

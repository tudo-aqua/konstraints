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

package tools.aqua

import java.io.File
import org.gradle.api.DefaultTask
import org.gradle.api.GradleException
import org.gradle.api.file.DirectoryProperty
import org.gradle.api.file.RegularFileProperty
import org.gradle.api.provider.Property
import org.gradle.api.provider.SetProperty
import org.gradle.api.tasks.CacheableTask
import org.gradle.api.tasks.Input
import org.gradle.api.tasks.InputDirectory
import org.gradle.api.tasks.InputFile
import org.gradle.api.tasks.OutputFile
import org.gradle.api.tasks.PathSensitive
import org.gradle.api.tasks.PathSensitivity.RELATIVE
import org.gradle.api.tasks.TaskAction

/** Describes the Java Platform Module System module produced by a project. */
interface JavaModuleExtension {
  /**
   * The module's name, as declared in its `module-info.java`. This is required to hand the Kotlin
   * compiler output to `javac` via `--patch-module` while compiling the module declaration.
   */
  val name: Property<String>

  /**
   * Packages that are deliberately kept out of the module's `exports` directives. Every other
   * package is expected to be exported, since everything usable from Kotlin should also be usable
   * from a modular consumer.
   */
  val internalPackages: SetProperty<String>
}

private val exportsRegex = """^\s*exports\s+([\w.]+)""".toRegex(RegexOption.MULTILINE)

/**
 * Verifies that the module declaration exports every package that actually holds classes. `javac`
 * rejects exports of nonexistent packages, but happily compiles a module that hides a package by
 * omission, which would silently drop a package from the public API.
 */
@CacheableTask
abstract class CheckModuleExportsTask : DefaultTask() {
  /** The `module-info.java` declaring the module. */
  @get:InputFile @get:PathSensitive(RELATIVE) abstract val moduleInfo: RegularFileProperty

  /** The directory holding the module's compiled classes. */
  @get:InputDirectory @get:PathSensitive(RELATIVE) abstract val classes: DirectoryProperty

  /** Packages that are allowed to remain unexported. */
  @get:Input abstract val internalPackages: SetProperty<String>

  /** Marker file written on success, so that the task can be up-to-date and cacheable. */
  @get:OutputFile abstract val report: RegularFileProperty

  /** Compares the declared exports against the packages found in [classes]. */
  @TaskAction
  fun check() {
    val declaration = moduleInfo.get().asFile.readText()
    val exported = exportsRegex.findAll(declaration).map { it.groupValues[1] }.toSet()

    val classesDir = classes.get().asFile
    val present =
        classesDir
            .walkTopDown()
            .filter { it.isFile && it.extension == "class" }
            .mapNotNull { it.parentFile.relativeTo(classesDir).path.takeIf(String::isNotEmpty) }
            .map { it.replace(File.separatorChar, '.') }
            .toSet()

    val missing = (present - exported - internalPackages.get()).sorted()
    if (missing.isNotEmpty()) {
      throw GradleException(
          missing.joinToString(
              prefix =
                  "${moduleInfo.get().asFile} does not export these packages, " +
                      "add an `exports` directive or list them in `javaModule.internalPackages`:\n  - ",
              separator = "\n  - ",
          )
      )
    }

    report.get().asFile.writeText(present.sorted().joinToString("\n", postfix = "\n"))
  }
}

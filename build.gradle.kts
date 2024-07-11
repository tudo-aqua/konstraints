/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * Copyright 2023-2023 The Konstraints Authors
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

import com.github.benmanes.gradle.versions.updates.DependencyUpdatesTask
import com.github.gradle.node.variant.computeNodeDir
import com.github.gradle.node.variant.computeNodeExec
import org.gradle.api.plugins.JavaBasePlugin.DOCUMENTATION_GROUP
import org.gradle.api.publish.plugins.PublishingPlugin.PUBLISH_TASK_GROUP
import org.gradle.api.tasks.testing.logging.TestLogEvent.FAILED
import org.gradle.api.tasks.testing.logging.TestLogEvent.PASSED
import org.gradle.api.tasks.testing.logging.TestLogEvent.SKIPPED

plugins {
  `java-library`
  `maven-publish`
  signing

  alias(libs.plugins.detekt)
  alias(libs.plugins.download)
  alias(libs.plugins.gitVersioning)
  alias(libs.plugins.kotlin.dokka)
  alias(libs.plugins.kotlin.jvm)
  alias(libs.plugins.kotlin.kover)
  alias(libs.plugins.kotlin.serialization)
  alias(libs.plugins.nexus.publish)
  alias(libs.plugins.node)
  alias(libs.plugins.spotless)
  alias(libs.plugins.taskTree)
  alias(libs.plugins.versions)
}

group = "tools.aqua"

version = "0.0.0-SNAPSHOT"

gitVersioning.apply {
  describeTagFirstParent = false
  refs {
    considerTagsOnBranches = true
    tag("(?<version>.*)") {
      // on a tag: use the tag name as is
      version = "\${ref.version}"
    }
    branch("main") {
      // on the main branch: use <last.tag.version>-<distance>-<commit>-SNAPSHOT
      version = "\${describe.tag.version}-\${describe.distance}-\${commit.short}-SNAPSHOT"
    }
    branch(".+") {
      // on other branches: use <last.tag.version>-<branch.name>-<distance>-<commit>-SNAPSHOT
      version =
          "\${describe.tag.version}-\${ref.slug}-\${describe.distance}-\${commit.short}-SNAPSHOT"
    }
  }

  // optional fallback configuration in case of no matching ref configuration
  rev {
    // in case of missing git data: use 0.0.0-unknown-0-<commit>-SNAPSHOT
    version = "0.0.0-unknown-0-\${commit.short}-SNAPSHOT"
  }
}

repositories { mavenCentral() }

dependencies {
  implementation(libs.commons.compress)
  implementation(libs.commons.io)
  implementation(libs.kotlin.coroutines)
  implementation(libs.petitparser.core)
  implementation(libs.z3.turnkey)

  testImplementation(platform(libs.junit.bom))
  testImplementation(libs.junit.jupiter)
  testImplementation(libs.kotlin.serialization.json)
  testRuntimeOnly(libs.junit.launcher)
  testRuntimeOnly(libs.xz)
  testRuntimeOnly(libs.zstd)
}

node {
  download = true
  workDir = layout.buildDirectory.dir("nodejs")
}

fun isNonStable(version: String): Boolean {
  val stableKeyword = listOf("RELEASE", "FINAL", "GA").any { version.uppercase().contains(it) }
  val regex = "^[0-9,.v-]+(-r)?$".toRegex()
  val isStable = stableKeyword || regex.matches(version)
  return isStable.not()
}

tasks.withType<DependencyUpdatesTask> {
  gradleReleaseChannel = "current"
  rejectVersionIf { isNonStable(candidate.version) && !isNonStable(currentVersion) }
}

spotless {
  kotlin {
    licenseHeaderFile(project.file("config/license/Apache-2.0-cstyle"))
    ktfmt("0.46")
  }
  kotlinGradle {
    licenseHeaderFile(project.file("config/license/Apache-2.0-cstyle"), "(plugins|import )")
    ktfmt("0.46")
  }
  format("contribPython") {
    target("contrib/*.py")
    licenseHeaderFile(project.file("config/license/Apache-2.0-hashmark"), "import")
        .skipLinesMatching("#!")
  }
  format("contribShell") {
    target("contrib/*.sh")
    licenseHeaderFile(project.file("config/license/Apache-2.0-hashmark"), "set")
        .skipLinesMatching("#!")
  }
  format("contribSingularity") {
    target("contrib/*.def")
    licenseHeaderFile(project.file("config/license/Apache-2.0-hashmark"), "Bootstrap:")
  }
  format("markdown") {
    target(".github/**/*.md", "*.md")
    licenseHeaderFile(project.file("config/license/CC-BY-4.0-xmlstyle"), "#+")
    prettier()
        .npmInstallCache()
        .nodeExecutable(computeNodeExec(node, computeNodeDir(node)).get())
        .config(mapOf("parser" to "markdown", "printWidth" to 100, "proseWrap" to "always"))
  }
  yaml {
    target("config/**/*.yml", ".github/**/*.yml", "CITATION.cff")
    licenseHeaderFile(project.file("config/license/Apache-2.0-hashmark"), "[A-Za-z-]+:")
    prettier()
        .npmInstallCache()
        .nodeExecutable(computeNodeExec(node, computeNodeDir(node)).get())
        .config(mapOf("parser" to "yaml", "printWidth" to 100))
  }
  format("toml") {
    target("gradle/libs.versions.toml")
    licenseHeaderFile(project.file("config/license/Apache-2.0-hashmark"), """\[[A-Za-z-]+]""")
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

detekt { ignoreFailures = true }

val kdocJar: TaskProvider<Jar> by
    tasks.registering(Jar::class) {
      group = DOCUMENTATION_GROUP
      archiveClassifier = "kdoc"
      from(tasks.dokkaHtml.flatMap { it.outputDirectory })
    }

val kdoc: Configuration by
    configurations.creating {
      isCanBeConsumed = true
      isCanBeResolved = false
    }

artifacts { add(kdoc.name, kdocJar) }

val javadocJar: TaskProvider<Jar> by
    tasks.registering(Jar::class) {
      group = DOCUMENTATION_GROUP
      archiveClassifier = "javadoc"
      from(tasks.dokkaJavadoc.flatMap { it.outputDirectory })
    }

java {
  withJavadocJar()
  withSourcesJar()
}

kotlin { jvmToolchain(libs.versions.java.jdk.get().toInt()) }

/*
val smtLibDir = layout.buildDirectory.dir("smtlib")

tasks {
  val incremental = layout.projectDirectory.file("contrib/smtlib-incremental-2024.05.13.urls")
  incremental.asFile.readLines().forEach { benchmark ->
    val url = uri(benchmark)
    val name =
        url.path.split('/').let { components ->
          components[components.size - 2].removeSuffix(".tar.zst")
        }
    val task =
        register<Download>("downloadIncremental$name") {
          inputs.file(incremental)
          group = "download"
          src(url)
          dest(smtLibDir.map { it.file("incremental/$name.tar.zst") })
          overwrite(false)
        }
    processTestResources { dependsOn(task) }
  }
}

tasks {
  val nonIncremental =
      layout.projectDirectory.file("contrib/smtlib-non-incremental-2024.04.23.urls")
  nonIncremental.asFile.readLines().forEach { benchmark ->
    val url = uri(benchmark)
    val name =
        url.path.split('/').let { components ->
          components[components.size - 2].removeSuffix(".tar.zst")
        }
    val task =
        register<Download>("downloadNonIncremental$name") {
          inputs.file(nonIncremental)
          group = "download"
          src(url)
          dest(smtLibDir.map { it.file("non-incremental/$name.tar.zst") })
          overwrite(false)
        }
    processTestResources { dependsOn(task) }
  }
}

sourceSets { test { resources { srcDir(smtLibDir) } } }
 */

tasks.test {
  useJUnitPlatform()
  testLogging { events(FAILED, SKIPPED, PASSED) }
}

publishing {
  publications {
    create<MavenPublication>("maven") {
      from(components["java"])

      pom {
        name = "Konstraints"
        description = "A library for working with SMT Expressions in the JVM"
        url = "https://github.com/tudo-aqua/konstraints"

        licenses {
          license {
            name = "Apache-2.0"
            url = "https://www.apache.org/licenses/LICENSE-2.0"
          }
          license {
            name = "CC-BY-4.0"
            url = "https://creativecommons.org/licenses/by/4.0/"
          }
        }

        developers {
          developer {
            name = "Simon Dierl"
            email = "simon.dierl@tu-dortmund.de"
            organization = "TU Dortmund University"
          }
          developer {
            name = "Falk Howar"
            email = "falk.howar@tu-dortmund.de"
            organization = "TU Dortmund University"
          }
          developer {
            name = "Laurenz Levi Spielmann"
            email = "laurenz-levi.spielmann@tu-dortmund.de"
            organization = "TU Dortmund University"
          }
        }

        scm {
          url = "https://github.com/tudo-aqua/konstraints/tree/main"
          connection = "scm:git:git://github.com:tudo-aqua/konstraints.git"
          developerConnection = "scm:git:ssh://git@github.com:tudo-aqua/konstraints.git"
        }
      }
    }
  }
}

signing {
  setRequired { gradle.taskGraph.allTasks.any { it.group == PUBLISH_TASK_GROUP } }
  useGpgCmd()
  sign(publishing.publications["maven"])
}

nexusPublishing { this.repositories { sonatype() } }

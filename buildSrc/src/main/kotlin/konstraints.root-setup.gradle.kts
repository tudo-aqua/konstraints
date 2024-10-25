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

import org.gradle.kotlin.dsl.repositories

plugins {
  id("io.github.gradle-nexus.publish-plugin")
  id("me.qoomon.git-versioning")
}

allprojects { group = "tools.aqua" }

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

nexusPublishing { this.repositories { sonatype() } }

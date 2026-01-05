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

import org.gradle.api.publish.maven.MavenPom

/**
 * Common setup code for all POMs. This populates the POM with Konstraints project information and
 * the [metadata].
 */
fun MavenPom.commonSetup(metadata: MetadataExtension) {
  name.set(metadata.name)
  description.set(metadata.description)
  url.set("https://github.com/tudo-aqua/konstraints")

  licenses {
    license {
      name.set("Apache-2.0")
      url.set("https://www.apache.org/licenses/LICENSE-2.0")
    }
    license {
      name.set("CC-BY-4.0")
      url.set("https://creativecommons.org/licenses/by/4.0/")
    }
  }

  developers {
    developer {
      name.set("Simon Dierl")
      email.set("simon.dierl@tu-dortmund.de")
      organization.set("TU Dortmund University")
    }
    developer {
      name.set("Falk Howar")
      email.set("falk.howar@tu-dortmund.de")
      organization.set("TU Dortmund University")
    }
    developer {
      name.set("Laurenz Levi Spielmann")
      email.set("laurenz-levi.spielmann@tu-dortmund.de")
      organization.set("TU Dortmund University")
    }
  }

  scm {
    url.set("https://github.com/tudo-aqua/konstraints/tree/main")
    connection.set("scm:git:git://github.com:tudo-aqua/konstraints.git")
    developerConnection.set("scm:git:ssh://git@github.com:tudo-aqua/konstraints.git")
  }
}

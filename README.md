<!--
   SPDX-License-Identifier: CC-BY-4.0

   Copyright 2023-2024 The Konstraints Authors

   This work is licensed under the Creative Commons Attribution 4.0
   International License.

   You should have received a copy of the license along with this
   work. If not, see <https://creativecommons.org/licenses/by/4.0/>.
-->

# Konstraints

Konstraints is a Kotlin library for working with SMT expressions that is designed to be used from
any JVM language. It allows the definition and inspection of SMT expressions, serialization and
deserialization via the SMT-Lib 2.6 format[^1] and provides bindings to multiple solvers. As opposed
to Java-SMT[^2], it SMT-Lib programs are represented as generic objects, allowing easy programmatic
introspection. It is designed to succeed JConstraints[^3] and build upon its concepts.

At the moment, Konstraints is pre-alpha software. While we are happy te receive feedback from early
adopters, the library is still incomplete and APIs may change without warning.

### Development

Building is completely done using Gradle. Most IDEs should be able to import the project without any
manual configuration.

To build Konstraints and deploy it to a local Maven repository for subsequent use, run

```shell
./gradlew publishToMavenLocal
```

Style enforcement is performed by Spotless. Run

```shell
./gradlew spotlessApply
```

to apply formatting to all files before committing.

### License

Konstraints source code is licensed unser the Apache License, Version 2.0. Its documentation is
licensed under the Creative Commons Attribution 4.0 International License. Dependencies, especially
solvers, may use other licenses.

[^1]:
    Barrett, C., Fontaine, P., & Tinelli, C. (2021, May). The SMT-LIB standard: Version 2.6 (tech.
    rep.) (Release: 2021-05-12). Department of Computer Science, The University of Iowa.
    https://smtlib.cs.uiowa.edu

[^2]:
    Baier, D., Beyer, D., & Friedberger, K. (2021). JavaSMT 3: Interacting with SMT solvers in Java.
    In A. Silva & K. R. M. Leino (Eds.), _Computer aided verification_ (pp. 195–208, Vol. 12760).
    Springer International Publishing. https://doi.org/10.1007/978-3-030-81688-9_9

[^3]:
    Howar, F., Jabbour, F., & Mues, M. (2019). JConstraints: A library for working with logic
    expressions in Java. In T. Margaria, S. Graf, & K. G. Larsen (Eds.), _Models, mindsets, meta:
    The what, the how, and the why not?_ (pp. 310–325, Vol. 11200). Springer International
    Publishing. https://doi.org/10.1007/978-3-030-22348-9_19

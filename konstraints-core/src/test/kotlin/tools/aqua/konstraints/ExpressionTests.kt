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

package tools.aqua.konstraints

/*
@Disabled
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class ExpressionTests {
  private fun loadResource(path: String) =
      File(javaClass.getResource(path)!!.file)
          .walk()
          .filter { file: File -> file.isFile }
          .map { file: File -> Arguments.arguments(file) }

  private fun loadResourceZipped(path: String) =
      File(javaClass.getResource(path)!!.file)
          .walk()
          .filter { file: File -> file.isFile }
          .zipWithNext()
          .map { Arguments.of(it.first, it.second) }

  /** Test that two expressions with same reference are considered equal */
  @ParameterizedTest
  @MethodSource("getFiles")
  fun testExpressionIsEqualToItselfSameReference(file: File) {
    val program =
        Parser().parse(file.bufferedReader().use(BufferedReader::readLines).joinToString("\n"))

    assertTrue(
        program.commands.filterIsInstance<Assert>().first().expr ==
            program.commands.filterIsInstance<Assert>().first().expr
    )
  }

  /** Test that two identical expressions with different references are considered equal */
  @ParameterizedTest
  @MethodSource("getFiles")
  fun testExpressionIsEqualToItselfDifferentReference(file: File) {
    val expr1 =
        Parser()
            .parse(file.bufferedReader().use(BufferedReader::readLines).joinToString("\n"))
            .commands
            .filterIsInstance<Assert>()
            .first()
            .expr
    val expr2 =
        Parser()
            .parse(file.bufferedReader().use(BufferedReader::readLines).joinToString("\n"))
            .commands
            .filterIsInstance<Assert>()
            .first()
            .expr

    assertTrue(expr1 == expr2)
  }

  fun getFiles(): Stream<Arguments> =
      (loadResource("/QF_BV/20190311-bv-term-small-rw-Noetzli/") +
              loadResource("/QF_IDL/Averest/binary_search/") +
              loadResource("/QF_RDL/") +
              loadResource("/QF_FP/wintersteiger/"))
          .asStream()

  @ParameterizedTest
  @MethodSource("getFilesZipped")
  fun testExpressionIsNotEqualToDifferentExpression(file1: File, file2: File) {
    val expr1 =
        Parser()
            .parse(file1.bufferedReader().use(BufferedReader::readLines).joinToString("\n"))
            .commands
            .filterIsInstance<Assert>()
            .first()
            .expr
    val expr2 =
        Parser()
            .parse(file2.bufferedReader().use(BufferedReader::readLines).joinToString("\n"))
            .commands
            .filterIsInstance<Assert>()
            .first()
            .expr

    // it rarely happens that two benchmarks start with the same expression
    // we try to skip these using this string comparison
    assumeTrue(expr1.toString() != expr2.toString())

    assertTrue(expr1 != expr2)
  }

  fun getFilesZipped(): Stream<Arguments> =
      (loadResourceZipped("/QF_BV/20190311-bv-term-small-rw-Noetzli/") +
              loadResourceZipped("/QF_IDL/Averest/binary_search/") +
              loadResourceZipped("/QF_RDL/") +
              loadResourceZipped("/QF_FP/wintersteiger/"))
          .asStream()
}
*/

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

package tools.aqua.konstraints

import java.io.File
import java.util.stream.Stream
import kotlin.streams.asStream
import org.junit.jupiter.api.Assertions.assertDoesNotThrow
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assumptions.assumeTrue
import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import tools.aqua.konstraints.parser.Parser
import tools.aqua.konstraints.smt.Expression
import tools.aqua.konstraints.smt.QuotingRule
import tools.aqua.konstraints.smt.SMTRegLan
import tools.aqua.konstraints.smt.Theories

@Disabled
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class ParserBenchmark {

  private fun loadResource(path: String) =
      File(javaClass.getResource(path)!!.file)
          .walk()
          .filter { file: File -> file.isFile }
          .map { file: File -> Arguments.arguments(file) }
          .asStream()

  private fun removeComments(program: String): String {
    var inQuotedSymbol = false
    var inStringLiteral = false
    var inComment = false
    var finished = false
    var low = 0
    val builder = StringBuilder(program.length)

    program.forEachIndexed { i, c ->
      if (c == '|' && !inStringLiteral && !inComment) { // beginning or end of quoted symbol
        inQuotedSymbol = !inQuotedSymbol
      } else if (c == '"' && !inQuotedSymbol && !inComment) { // beginning or end of string literal
        inStringLiteral = !inStringLiteral
      } else if (
          c == ';' && !inQuotedSymbol && !inStringLiteral && !inComment
      ) { // beginning of comment we need to check we are not already in a comment or
        // any appearance of ';' will duplicate the last substring
        inComment = true
        // add all previous chars to builder unless string starts with comment
        builder.append(program.substring(low, i))
        finished = true
      } else if (c == '\n' && inComment) { // end of comment
        inComment = false
        // set index of new first character to be included in the program later
        low = i
        finished = false
      }
    }

    if (!finished) {
      builder.append(program.substring(low))
    }

    // if we have no comment nothing is ever added to the builder so we just return the input
    return if (builder.isNotEmpty()) builder.toString() else program
  }

  private fun parse(file: File) {
    assumeTrue(file.length() < 5000000, "Skipped due to file size exceeding limit of 5000000")

    /*assertDoesNotThrow {
      // its crucial that the separator is '\n' as comments dont have an ending symbol but rather
      // end that the end of a line
      Parser().parse(file.bufferedReader().use(BufferedReader::readLines).joinToString("\n"))
    }*/

    try {
      val input = file.bufferedReader().readLines().joinToString("\n")
      val program = Parser(input)

      assertEquals(
          removeComments(input)
              .replace(" ", "")
              .replace("\n", "")
              .replace("\r", "")
              .replace("\t", "")
              .replace("|", ""),
          program
              .toSMTString(StringBuilder(), QuotingRule.SAME_AS_INPUT, true)
              .toString()
              .replace(" ", "")
              .replace("\n", "")
              .replace("\r", "")
              .replace("\t", "")
              .replace("|", ""),
      )
    } catch (e: NotImplementedError) {
      println("Skipped due to not implemented error ${e.message}")
      assumeTrue(false)
    } catch (e: Exception) {
      assertDoesNotThrow { throw e }
    }
  }

  @ParameterizedTest @MethodSource("getABVFiles") fun parseABV(file: File) = parse(file)

  fun getABVFiles(): Stream<Arguments> = loadResource("/smt-benchmark/ABV/")

  @ParameterizedTest @MethodSource("getABVFPFiles") fun parseABVFP(file: File) = parse(file)

  fun getABVFPFiles(): Stream<Arguments> = loadResource("/smt-benchmark/ABVFP/")

  @ParameterizedTest @MethodSource("getABVFPLRAFiles") fun parseABVFPLRA(file: File) = parse(file)

  fun getABVFPLRAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/ABVFPLRA/")

  @ParameterizedTest @MethodSource("getALIAFiles") fun parseALIA(file: File) = parse(file)

  fun getALIAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/ALIA/")

  @ParameterizedTest @MethodSource("getANIAFiles") fun parseANIA(file: File) = parse(file)

  fun getANIAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/ANIA/")

  @ParameterizedTest @MethodSource("getAUFBVFiles") fun parseAUFBV(file: File) = parse(file)

  fun getAUFBVFiles(): Stream<Arguments> = loadResource("/smt-benchmark/AUFBV/")

  /* @Disabled */
  @ParameterizedTest
  @MethodSource("getAUFBVDTLIAFiles")
  fun parseAUFBVDTLIA(file: File) = parse(file)

  fun getAUFBVDTLIAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/AUFBVDTLIA/")

  /* @Disabled */
  @ParameterizedTest
  @MethodSource("getAUFBVDTNIAFiles")
  fun parseAUFBVDTNIA(file: File) = parse(file)

  fun getAUFBVDTNIAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/AUFBVDTNIA/")

  /* @Disabled */
  @ParameterizedTest
  @MethodSource("getAUFBVDTNIRAFiles")
  fun parseAUFBVDTNIRA(file: File) = parse(file)

  fun getAUFBVDTNIRAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/AUFBVDTNIRA/")

  @ParameterizedTest @MethodSource("getAUFBVFPFiles") fun parseAUFBVFP(file: File) = parse(file)

  fun getAUFBVFPFiles(): Stream<Arguments> = loadResource("/smt-benchmark/AUFBVFP/")

  /* @Disabled */
  @ParameterizedTest @MethodSource("getAUFDTLIAFiles") fun parseAUFDTLIA(file: File) = parse(file)

  fun getAUFDTLIAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/AUFDTLIA/")

  /* @Disabled */
  @ParameterizedTest @MethodSource("getAUFDTLIRAFiles") fun parseAUFDTLIRA(file: File) = parse(file)

  fun getAUFDTLIRAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/AUFDTLIRA/")

  /* @Disabled */
  @ParameterizedTest @MethodSource("getAUFDTNIRAFiles") fun parseAUFDTNIRA(file: File) = parse(file)

  fun getAUFDTNIRAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/AUFDTNIRA/")

  /* @Disabled */
  @ParameterizedTest
  @MethodSource("getAUFFPDTNIRAFiles")
  fun parseAUFFPDTNIRA(file: File) = parse(file)

  fun getAUFFPDTNIRAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/AUFFPDTNIRA/")

  @ParameterizedTest @MethodSource("getAUFLIAFiles") fun parseAUFLIA(file: File) = parse(file)

  fun getAUFLIAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/AUFLIA/")

  @ParameterizedTest @MethodSource("getAUFLIRAFiles") fun parseAUFLIRA(file: File) = parse(file)

  fun getAUFLIRAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/AUFLIRA/")

  @ParameterizedTest @MethodSource("getAUFNIAFiles") fun parseAUFNIA(file: File) = parse(file)

  fun getAUFNIAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/AUFNIA/")

  @ParameterizedTest @MethodSource("getAUFNIRAFiles") fun parseAUFNIRA(file: File) = parse(file)

  fun getAUFNIRAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/AUFNIRA/")

  @ParameterizedTest @MethodSource("getBVFiles") fun parseBV(file: File) = parse(file)

  fun getBVFiles(): Stream<Arguments> = loadResource("/smt-benchmark/BV/")

  @ParameterizedTest @MethodSource("getBVFPFiles") fun parseBVFP(file: File) = parse(file)

  fun getBVFPFiles(): Stream<Arguments> = loadResource("/smt-benchmark/BVFP/")

  @ParameterizedTest @MethodSource("getBVFPLRAFiles") fun parseBVFPLRA(file: File) = parse(file)

  fun getBVFPLRAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/BVFPLRA/")

  @ParameterizedTest @MethodSource("getFPFiles") fun parseFP(file: File) = parse(file)

  fun getFPFiles(): Stream<Arguments> = loadResource("/smt-benchmark/FP/")

  @ParameterizedTest @MethodSource("getFPLRAFiles") fun parseFPLRA(file: File) = parse(file)

  fun getFPLRAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/FPLRA/")

  @ParameterizedTest @MethodSource("getLIAFiles") fun parseLIA(file: File) = parse(file)

  fun getLIAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/LIA/")

  @ParameterizedTest @MethodSource("getLRAFiles") fun parseLRA(file: File) = parse(file)

  fun getLRAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/LRA/")

  @ParameterizedTest @MethodSource("getNIAFiles") fun parseNIA(file: File) = parse(file)

  fun getNIAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/NIA/")

  @ParameterizedTest @MethodSource("getNRAFiles") fun parseNRA(file: File) = parse(file)

  fun getNRAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/NRA/")

  @ParameterizedTest @MethodSource("getQF_ABVFiles") fun parseQF_ABV(file: File) = parse(file)

  fun getQF_ABVFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_ABV/")

  @ParameterizedTest @MethodSource("getQF_ABVFPFiles") fun parseQF_ABVFP(file: File) = parse(file)

  fun getQF_ABVFPFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_ABVFP/")

  @ParameterizedTest
  @MethodSource("getQF_ABVFPLRAFiles")
  fun parseQF_ABVFPLRA(file: File) = parse(file)

  fun getQF_ABVFPLRAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_ABVFPLRA/")

  @ParameterizedTest @MethodSource("getQF_ALIAFiles") fun parseQF_ALIA(file: File) = parse(file)

  fun getQF_ALIAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_ALIA/")

  @ParameterizedTest @MethodSource("getQF_ANIAFiles") fun parseQF_ANIA(file: File) = parse(file)

  fun getQF_ANIAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_ANIA/")

  @ParameterizedTest @MethodSource("getQF_AUFBVFiles") fun parseQF_AUFBV(file: File) = parse(file)

  fun getQF_AUFBVFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_AUFBV/")

  @ParameterizedTest
  @MethodSource("getQF_AUFBVFPFiles")
  fun parseQF_AUFBVFP(file: File) = parse(file)

  fun getQF_AUFBVFPFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_AUFBVFP/")

  @ParameterizedTest @MethodSource("getQF_AUFLIAFiles") fun parseQF_AUFLIA(file: File) = parse(file)

  fun getQF_AUFLIAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_AUFLIA/")

  @ParameterizedTest @MethodSource("getQF_AUFNIAFiles") fun parseQF_AUFNIA(file: File) = parse(file)

  fun getQF_AUFNIAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_AUFNIA/")

  @ParameterizedTest @MethodSource("getQF_AXFiles") fun parseQF_AX(file: File) = parse(file)

  fun getQF_AXFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_AX/")

  @ParameterizedTest @MethodSource("getQF_BVFiles") fun parseQF_BV(file: File) = parse(file)

  fun getQF_BVFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_BV/")

  @ParameterizedTest @MethodSource("getQF_BVFPFiles") fun parseQF_BVFP(file: File) = parse(file)

  fun getQF_BVFPFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_BVFP/")

  @ParameterizedTest
  @MethodSource("getQF_BVFPLRAFiles")
  fun parseQF_BVFPLRA(file: File) = parse(file)

  fun getQF_BVFPLRAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_BVFPLRA/")

  /* @Disabled */
  @ParameterizedTest @MethodSource("getQF_DTFiles") fun parseQF_DT(file: File) = parse(file)

  fun getQF_DTFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_DT/")

  @ParameterizedTest @MethodSource("getQF_FPFiles") fun parseQF_FP(file: File) = parse(file)

  fun getQF_FPFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_FP/")

  @ParameterizedTest @MethodSource("getQF_FPLRAFiles") fun parseQF_FPLRA(file: File) = parse(file)

  fun getQF_FPLRAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_FPLRA/")

  @ParameterizedTest @MethodSource("getQF_IDLFiles") fun parseQF_IDL(file: File) = parse(file)

  fun getQF_IDLFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_IDL/")

  @ParameterizedTest @MethodSource("getQF_LIAFiles") fun parseQF_LIA(file: File) = parse(file)

  fun getQF_LIAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_LIA/")

  @ParameterizedTest @MethodSource("getQF_LIRAFiles") fun parseQF_LIRA(file: File) = parse(file)

  fun getQF_LIRAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_LIRA/")

  @ParameterizedTest @MethodSource("getQF_LRAFiles") fun parseQF_LRA(file: File) = parse(file)

  fun getQF_LRAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_LRA/")

  @ParameterizedTest @MethodSource("getQF_NIAFiles") fun parseQF_NIA(file: File) = parse(file)

  fun getQF_NIAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_NIA/")

  @ParameterizedTest @MethodSource("getQF_NIRAFiles") fun parseQF_NIRA(file: File) = parse(file)

  fun getQF_NIRAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_NIRA/")

  @ParameterizedTest @MethodSource("getQF_NRAFiles") fun parseQF_NRA(file: File) = parse(file)

  fun getQF_NRAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_NRA/")

  @ParameterizedTest @MethodSource("getQF_RDLFiles") fun parseQF_RDL(file: File) = parse(file)

  fun getQF_RDLFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_RDL/")

  @ParameterizedTest @MethodSource("getQF_SFiles") fun parseQF_S(file: File) = parse(file)

  fun getQF_SFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_S/")

  @ParameterizedTest @MethodSource("getQF_SLIAFiles") fun parseQF_SLIA(file: File) = parse(file)

  fun getQF_SLIAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_SLIA/")

  @ParameterizedTest @MethodSource("getQF_SNIAFiles") fun parseQF_SNIA(file: File) = parse(file)

  fun getQF_SNIAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_SNIA/")

  @ParameterizedTest @MethodSource("getQF_UFFiles") fun parseQF_UF(file: File) = parse(file)

  fun getQF_UFFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_UF/")

  @ParameterizedTest @MethodSource("getQF_UFBVFiles") fun parseQF_UFBV(file: File) = parse(file)

  fun getQF_UFBVFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_UFBV/")

  /* @Disabled */
  @ParameterizedTest @MethodSource("getQF_UFBVDTFiles") fun parseQF_UFBVDT(file: File) = parse(file)

  fun getQF_UFBVDTFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_UFBVDT/")

  /* @Disabled */
  @ParameterizedTest @MethodSource("getQF_UFDTFiles") fun parseQF_UFDT(file: File) = parse(file)

  fun getQF_UFDTFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_UFDT/")

  /* @Disabled */
  @ParameterizedTest
  @MethodSource("getQF_UFDTLIAFiles")
  fun parseQF_UFDTLIA(file: File) = parse(file)

  fun getQF_UFDTLIAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_UFDTLIA/")

  /* @Disabled */
  @ParameterizedTest
  @MethodSource("getQF_UFDTLIRAFiles")
  fun parseQF_UFDTLIRA(file: File) = parse(file)

  fun getQF_UFDTLIRAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_UFDTLIRA/")

  /* @Disabled */
  @ParameterizedTest
  @MethodSource("getQF_UFDTNIAFiles")
  fun parseQF_UFDTNIA(file: File) = parse(file)

  fun getQF_UFDTNIAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_UFDTNIA/")

  @ParameterizedTest @MethodSource("getQF_UFFPFiles") fun parseQF_UFFP(file: File) = parse(file)

  fun getQF_UFFPFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_UFFP/")

  /* @Disabled */
  @ParameterizedTest
  @MethodSource("getQF_UFFPDTNIRAFiles")
  fun parseQF_UFFPDTNIRA(file: File) = parse(file)

  fun getQF_UFFPDTNIRAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_UFFPDTNIRA/")

  @ParameterizedTest @MethodSource("getQF_UFIDLFiles") fun parseQF_UFIDL(file: File) = parse(file)

  fun getQF_UFIDLFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_UFIDL/")

  @ParameterizedTest @MethodSource("getQF_UFLIAFiles") fun parseQF_UFLIA(file: File) = parse(file)

  fun getQF_UFLIAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_UFLIA/")

  @ParameterizedTest @MethodSource("getQF_UFLRAFiles") fun parseQF_UFLRA(file: File) = parse(file)

  fun getQF_UFLRAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_UFLRA/")

  @ParameterizedTest @MethodSource("getQF_UFNIAFiles") fun parseQF_UFNIA(file: File) = parse(file)

  fun getQF_UFNIAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_UFNIA/")

  @ParameterizedTest @MethodSource("getQF_UFNRAFiles") fun parseQF_UFNRA(file: File) = parse(file)

  fun getQF_UFNRAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/QF_UFNRA/")

  @ParameterizedTest @MethodSource("getUFFiles") fun parseUF(file: File) = parse(file)

  fun getUFFiles(): Stream<Arguments> = loadResource("/smt-benchmark/UF/")

  @ParameterizedTest @MethodSource("getUFBVFiles") fun parseUFBV(file: File) = parse(file)

  fun getUFBVFiles(): Stream<Arguments> = loadResource("/smt-benchmark/UFBV/")

  /* @Disabled */
  @ParameterizedTest @MethodSource("getUFBVDTFiles") fun parseUFBVDT(file: File) = parse(file)

  fun getUFBVDTFiles(): Stream<Arguments> = loadResource("/smt-benchmark/UFBVDT/")

  @ParameterizedTest @MethodSource("getUFBVFPFiles") fun parseUFBVFP(file: File) = parse(file)

  fun getUFBVFPFiles(): Stream<Arguments> = loadResource("/smt-benchmark/UFBVFP/")

  @ParameterizedTest @MethodSource("getUFBVLIAFiles") fun parseUFBVLIA(file: File) = parse(file)

  fun getUFBVLIAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/UFBVLIA/")

  /* @Disabled */
  @ParameterizedTest @MethodSource("getUFDTFiles") fun parseUFDT(file: File) = parse(file)

  fun getUFDTFiles(): Stream<Arguments> = loadResource("/smt-benchmark/UFDT/")

  /* @Disabled */
  @ParameterizedTest @MethodSource("getUFDTLIAFiles") fun parseUFDTLIA(file: File) = parse(file)

  fun getUFDTLIAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/UFDTLIA/")

  /* @Disabled */
  @ParameterizedTest @MethodSource("getUFDTLIRAFiles") fun parseUFDTLIRA(file: File) = parse(file)

  fun getUFDTLIRAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/UFDTLIRA/")

  /* @Disabled */
  @ParameterizedTest @MethodSource("getUFDTNIAFiles") fun parseUFDTNIA(file: File) = parse(file)

  fun getUFDTNIAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/UFDTNIA/")

  /* @Disabled */
  @ParameterizedTest @MethodSource("getUFDTNIRAFiles") fun parseUFDTNIRA(file: File) = parse(file)

  fun getUFDTNIRAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/UFDTNIRA/")

  /* @Disabled */
  @ParameterizedTest
  @MethodSource("getUFFPDTNIRAFiles")
  fun parseUFFPDTNIRA(file: File) = parse(file)

  fun getUFFPDTNIRAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/UFFPDTNIRA/")

  @ParameterizedTest @MethodSource("getUFIDLFiles") fun parseUFIDL(file: File) = parse(file)

  fun getUFIDLFiles(): Stream<Arguments> = loadResource("/smt-benchmark/UFIDL/")

  @ParameterizedTest @MethodSource("getUFLIAFiles") fun parseUFLIA(file: File) = parse(file)

  fun getUFLIAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/UFLIA/")

  @ParameterizedTest @MethodSource("getUFLRAFiles") fun parseUFLRA(file: File) = parse(file)

  fun getUFLRAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/UFLRA/")

  @ParameterizedTest @MethodSource("getUFNIAFiles") fun parseUFNIA(file: File) = parse(file)

  fun getUFNIAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/UFNIA/")

  @ParameterizedTest @MethodSource("getUFNIRAFiles") fun parseUFNIRA(file: File) = parse(file)

  fun getUFNIRAFiles(): Stream<Arguments> = loadResource("/smt-benchmark/UFNIRA/")
}

val Expression<*>.traverse: DeepRecursiveFunction<(Expression<*>) -> Unit, Unit>
  get() =
      DeepRecursiveFunction<(Expression<*>) -> Unit, Unit> { action ->
        action(this@traverse)
        this@traverse.children.onEach { it.traverse.callRecursive(action) }
      }

fun getKey(expr: Expression<*>): String {
  if (expr.theories.contains(Theories.CORE)) {
    return "Core"
  } else if (expr.theories.contains(Theories.INTS)) {
    return "Int"
  } else if (expr.sort is SMTRegLan) {
    return "RegLan"
  } else {
    return "String"
  }
}

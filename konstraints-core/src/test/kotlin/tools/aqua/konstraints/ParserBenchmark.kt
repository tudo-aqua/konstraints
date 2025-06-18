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

import java.io.BufferedReader
import java.io.File
import java.util.concurrent.TimeUnit
import java.util.stream.Stream
import kotlin.streams.asStream
import kotlin.use
import org.junit.jupiter.api.Assertions.assertDoesNotThrow
import org.junit.jupiter.api.Assumptions.assumeTrue
import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.Timeout
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import tools.aqua.konstraints.parser.Parser

@Disabled
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class ParserBenchmark {
  private fun loadResource(path: String) =
      File(javaClass.getResource(path)!!.file)
          .walk()
          .filter { file: File -> file.isFile }
          .map { file: File -> Arguments.arguments(file) }
          .asStream()

  private fun parse(file: File) {
    assumeTrue(file.length() < 5000000, "Skipped due to file size exceeding limit of 5000000")

    assertDoesNotThrow {
      // its crucial that the separator is '\n' as comments dont have an ending symbol but rather
      // end that the end of a line
      Parser().parse(file.bufferedReader().use(BufferedReader::readLines).joinToString("\n"))
    }
  }

  @Disabled @ParameterizedTest @MethodSource("getABVFiles") fun parseABV(file: File) = parse(file)

  fun getABVFiles(): Stream<Arguments> = loadResource("/full/ABV/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getABVFPFiles")
  fun parseABVFP(file: File) = parse(file)

  fun getABVFPFiles(): Stream<Arguments> = loadResource("/full/ABVFP/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getABVFPLRAFiles")
  fun parseABVFPLRA(file: File) = parse(file)

  fun getABVFPLRAFiles(): Stream<Arguments> = loadResource("/full/ABVFPLRA/")

  @Disabled @ParameterizedTest @MethodSource("getALIAFiles") fun parseALIA(file: File) = parse(file)

  fun getALIAFiles(): Stream<Arguments> = loadResource("/full/ALIA/")

  @Disabled @ParameterizedTest @MethodSource("getANIAFiles") fun parseANIA(file: File) = parse(file)

  fun getANIAFiles(): Stream<Arguments> = loadResource("/full/ANIA/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getAUFBVFiles")
  fun parseAUFBV(file: File) = parse(file)

  fun getAUFBVFiles(): Stream<Arguments> = loadResource("/full/AUFBV/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getAUFBVDTLIAFiles")
  fun parseAUFBVDTLIA(file: File) = parse(file)

  fun getAUFBVDTLIAFiles(): Stream<Arguments> = loadResource("/full/AUFBVDTLIA/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getAUFBVDTNIAFiles")
  fun parseAUFBVDTNIA(file: File) = parse(file)

  fun getAUFBVDTNIAFiles(): Stream<Arguments> = loadResource("/full/AUFBVDTNIA/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getAUFBVDTNIRAFiles")
  fun parseAUFBVDTNIRA(file: File) = parse(file)

  fun getAUFBVDTNIRAFiles(): Stream<Arguments> = loadResource("/full/AUFBVDTNIRA/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getAUFBVFPFiles")
  fun parseAUFBVFP(file: File) = parse(file)

  fun getAUFBVFPFiles(): Stream<Arguments> = loadResource("/full/AUFBVFP/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getAUFDTLIAFiles")
  fun parseAUFDTLIA(file: File) = parse(file)

  fun getAUFDTLIAFiles(): Stream<Arguments> = loadResource("/full/AUFDTLIA/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getAUFDTLIRAFiles")
  fun parseAUFDTLIRA(file: File) = parse(file)

  fun getAUFDTLIRAFiles(): Stream<Arguments> = loadResource("/full/AUFDTLIRA/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getAUFDTNIRAFiles")
  fun parseAUFDTNIRA(file: File) = parse(file)

  fun getAUFDTNIRAFiles(): Stream<Arguments> = loadResource("/full/AUFDTNIRA/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getAUFFPDTNIRAFiles")
  fun parseAUFFPDTNIRA(file: File) = parse(file)

  fun getAUFFPDTNIRAFiles(): Stream<Arguments> = loadResource("/full/AUFFPDTNIRA/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getAUFLIAFiles")
  fun parseAUFLIA(file: File) = parse(file)

  fun getAUFLIAFiles(): Stream<Arguments> = loadResource("/full/AUFLIA/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getAUFLIRAFiles")
  fun parseAUFLIRA(file: File) = parse(file)

  fun getAUFLIRAFiles(): Stream<Arguments> = loadResource("/full/AUFLIRA/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getAUFNIAFiles")
  fun parseAUFNIA(file: File) = parse(file)

  fun getAUFNIAFiles(): Stream<Arguments> = loadResource("/full/AUFNIA/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getAUFNIRAFiles")
  fun parseAUFNIRA(file: File) = parse(file)

  fun getAUFNIRAFiles(): Stream<Arguments> = loadResource("/full/AUFNIRA/")

  @ParameterizedTest @MethodSource("getBVFiles") fun parseBV(file: File) = parse(file)

  fun getBVFiles(): Stream<Arguments> = loadResource("/BV/")

  @Disabled @ParameterizedTest @MethodSource("getBVFPFiles") fun parseBVFP(file: File) = parse(file)

  fun getBVFPFiles(): Stream<Arguments> = loadResource("/full/BVFP/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getBVFPLRAFiles")
  fun parseBVFPLRA(file: File) = parse(file)

  fun getBVFPLRAFiles(): Stream<Arguments> = loadResource("/full/BVFPLRA/")

  @ParameterizedTest @MethodSource("getFPFiles") fun parseFP(file: File) = parse(file)

  fun getFPFiles(): Stream<Arguments> = loadResource("/full/FP/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getFPLRAFiles")
  fun parseFPLRA(file: File) = parse(file)

  fun getFPLRAFiles(): Stream<Arguments> = loadResource("/full/FPLRA/")

  @Disabled @ParameterizedTest @MethodSource("getLIAFiles") fun parseLIA(file: File) = parse(file)

  fun getLIAFiles(): Stream<Arguments> = loadResource("/full/LIA/")

  @Disabled @ParameterizedTest @MethodSource("getLRAFiles") fun parseLRA(file: File) = parse(file)

  fun getLRAFiles(): Stream<Arguments> = loadResource("/full/LRA/")

  @Disabled @ParameterizedTest @MethodSource("getNIAFiles") fun parseNIA(file: File) = parse(file)

  fun getNIAFiles(): Stream<Arguments> = loadResource("/full/NIA/")

  @Disabled @ParameterizedTest @MethodSource("getNRAFiles") fun parseNRA(file: File) = parse(file)

  fun getNRAFiles(): Stream<Arguments> = loadResource("/full/NRA/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getQF_ABVFiles")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun parseQF_ABV(file: File) = parse(file)

  fun getQF_ABVFiles(): Stream<Arguments> = loadResource("/full/QF_ABV/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getQF_ABVFPFiles")
  fun parseQF_ABVFP(file: File) = parse(file)

  fun getQF_ABVFPFiles(): Stream<Arguments> = loadResource("/full/QF_ABVFP/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getQF_ABVFPLRAFiles")
  fun parseQF_ABVFPLRA(file: File) = parse(file)

  fun getQF_ABVFPLRAFiles(): Stream<Arguments> = loadResource("/full/QF_ABVFPLRA/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getQF_ALIAFiles")
  fun parseQF_ALIA(file: File) = parse(file)

  fun getQF_ALIAFiles(): Stream<Arguments> = loadResource("/full/QF_ALIA/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getQF_ANIAFiles")
  fun parseQF_ANIA(file: File) = parse(file)

  fun getQF_ANIAFiles(): Stream<Arguments> = loadResource("/full/QF_ANIA/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getQF_AUFBVFiles")
  fun parseQF_AUFBV(file: File) = parse(file)

  fun getQF_AUFBVFiles(): Stream<Arguments> = loadResource("/full/QF_AUFBV/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getQF_AUFBVFPFiles")
  fun parseQF_AUFBVFP(file: File) = parse(file)

  fun getQF_AUFBVFPFiles(): Stream<Arguments> = loadResource("/full/QF_AUFBVFP/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getQF_AUFLIAFiles")
  fun parseQF_AUFLIA(file: File) = parse(file)

  fun getQF_AUFLIAFiles(): Stream<Arguments> = loadResource("/full/QF_AUFLIA/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getQF_AUFNIAFiles")
  fun parseQF_AUFNIA(file: File) = parse(file)

  fun getQF_AUFNIAFiles(): Stream<Arguments> = loadResource("/full/QF_AUFNIA/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getQF_AXFiles")
  fun parseQF_AX(file: File) = parse(file)

  fun getQF_AXFiles(): Stream<Arguments> = loadResource("/full/QF_AX/")

  @ParameterizedTest
  @MethodSource("getQF_BVFiles")
  @Timeout(value = 10, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun parseQF_BV(file: File) = parse(file)

  fun getQF_BVFiles(): Stream<Arguments> = loadResource("/full/QF_BV/sage/")

  @ParameterizedTest @MethodSource("getQF_BVFPFiles") fun parseQF_BVFP(file: File) = parse(file)

  fun getQF_BVFPFiles(): Stream<Arguments> = loadResource("/full/QF_BVFP/")

  @ParameterizedTest
  @MethodSource("getQF_BVFPLRAFiles")
  fun parseQF_BVFPLRA(file: File) = parse(file)

  fun getQF_BVFPLRAFiles(): Stream<Arguments> = loadResource("/full/QF_BVFPLRA/")

  @ParameterizedTest @MethodSource("getQF_DTFiles") fun parseQF_DT(file: File) = parse(file)

  fun getQF_DTFiles(): Stream<Arguments> = loadResource("/full/QF_DT/")

  @ParameterizedTest @MethodSource("getQF_FPFiles") fun parseQF_FP(file: File) = parse(file)

  fun getQF_FPFiles(): Stream<Arguments> = loadResource("/full/QF_FP/")

  @ParameterizedTest @MethodSource("getQF_FPLRAFiles") fun parseQF_FPLRA(file: File) = parse(file)

  fun getQF_FPLRAFiles(): Stream<Arguments> = loadResource("/full/QF_FPLRA/")

  @ParameterizedTest @MethodSource("getQF_IDLFiles") fun parseQF_IDL(file: File) = parse(file)

  fun getQF_IDLFiles(): Stream<Arguments> = loadResource("/full/QF_IDL/")

  @ParameterizedTest @MethodSource("getQF_LIAFiles") fun parseQF_LIA(file: File) = parse(file)

  fun getQF_LIAFiles(): Stream<Arguments> = loadResource("/full/QF_LIA/")

  @ParameterizedTest @MethodSource("getQF_LIRAFiles") fun parseQF_LIRA(file: File) = parse(file)

  fun getQF_LIRAFiles(): Stream<Arguments> = loadResource("/full/QF_LIRA/")

  @ParameterizedTest @MethodSource("getQF_LRAFiles") fun parseQF_LRA(file: File) = parse(file)

  fun getQF_LRAFiles(): Stream<Arguments> = loadResource("/full/QF_LRA/")

  @ParameterizedTest @MethodSource("getQF_NIAFiles") fun parseQF_NIA(file: File) = parse(file)

  fun getQF_NIAFiles(): Stream<Arguments> = loadResource("/full/QF_NIA/")

  @ParameterizedTest @MethodSource("getQF_NIRAFiles") fun parseQF_NIRA(file: File) = parse(file)

  fun getQF_NIRAFiles(): Stream<Arguments> = loadResource("/full/QF_NIRA/")

  @ParameterizedTest @MethodSource("getQF_NRAFiles") fun parseQF_NRA(file: File) = parse(file)

  fun getQF_NRAFiles(): Stream<Arguments> = loadResource("/full/QF_NRA/")

  @ParameterizedTest @MethodSource("getQF_RDLFiles") fun parseQF_RDL(file: File) = parse(file)

  fun getQF_RDLFiles(): Stream<Arguments> = loadResource("/full/QF_RDL/")

  @ParameterizedTest @MethodSource("getQF_SFiles") fun parseQF_S(file: File) = parse(file)

  fun getQF_SFiles(): Stream<Arguments> = loadResource("/full/QF_S/")

  @ParameterizedTest @MethodSource("getQF_SLIAFiles") fun parseQF_SLIA(file: File) = parse(file)

  fun getQF_SLIAFiles(): Stream<Arguments> = loadResource("/full/QF_SLIA/")

  @ParameterizedTest @MethodSource("getQF_SNIAFiles") fun parseQF_SNIA(file: File) = parse(file)

  fun getQF_SNIAFiles(): Stream<Arguments> = loadResource("/full/QF_SNIA/")

  @ParameterizedTest @MethodSource("getQF_UFFiles") fun parseQF_UF(file: File) = parse(file)

  fun getQF_UFFiles(): Stream<Arguments> = loadResource("/full/QF_UF/")

  @ParameterizedTest @MethodSource("getQF_UFBVFiles") fun parseQF_UFBV(file: File) = parse(file)

  fun getQF_UFBVFiles(): Stream<Arguments> = loadResource("/full/QF_UFBV/")

  @ParameterizedTest @MethodSource("getQF_UFBVDTFiles") fun parseQF_UFBVDT(file: File) = parse(file)

  fun getQF_UFBVDTFiles(): Stream<Arguments> = loadResource("/full/QF_UFBVDT/")

  @ParameterizedTest @MethodSource("getQF_UFDTFiles") fun parseQF_UFDT(file: File) = parse(file)

  fun getQF_UFDTFiles(): Stream<Arguments> = loadResource("/full/QF_UFDT/")

  @ParameterizedTest
  @MethodSource("getQF_UFDTLIAFiles")
  fun parseQF_UFDTLIA(file: File) = parse(file)

  fun getQF_UFDTLIAFiles(): Stream<Arguments> = loadResource("/full/QF_UFDTLIA/")

  @ParameterizedTest
  @MethodSource("getQF_UFDTLIRAFiles")
  fun parseQF_UFDTLIRA(file: File) = parse(file)

  fun getQF_UFDTLIRAFiles(): Stream<Arguments> = loadResource("/full/QF_UFDTLIRA/")

  @ParameterizedTest
  @MethodSource("getQF_UFDTNIAFiles")
  fun parseQF_UFDTNIA(file: File) = parse(file)

  fun getQF_UFDTNIAFiles(): Stream<Arguments> = loadResource("/full/QF_UFDTNIA/")

  @ParameterizedTest @MethodSource("getQF_UFFPFiles") fun parseQF_UFFP(file: File) = parse(file)

  fun getQF_UFFPFiles(): Stream<Arguments> = loadResource("/full/QF_UFFP/")

  @ParameterizedTest
  @MethodSource("getQF_UFFPDTNIRAFiles")
  fun parseQF_UFFPDTNIRA(file: File) = parse(file)

  fun getQF_UFFPDTNIRAFiles(): Stream<Arguments> = loadResource("/full/QF_UFFPDTNIRA/")

  @ParameterizedTest @MethodSource("getQF_UFIDLFiles") fun parseQF_UFIDL(file: File) = parse(file)

  fun getQF_UFIDLFiles(): Stream<Arguments> = loadResource("/full/QF_UFIDL/")

  @ParameterizedTest @MethodSource("getQF_UFLIAFiles") fun parseQF_UFLIA(file: File) = parse(file)

  fun getQF_UFLIAFiles(): Stream<Arguments> = loadResource("/full/QF_UFLIA/")

  @ParameterizedTest @MethodSource("getQF_UFLRAFiles") fun parseQF_UFLRA(file: File) = parse(file)

  fun getQF_UFLRAFiles(): Stream<Arguments> = loadResource("/full/QF_UFLRA/")

  @ParameterizedTest @MethodSource("getQF_UFNIAFiles") fun parseQF_UFNIA(file: File) = parse(file)

  fun getQF_UFNIAFiles(): Stream<Arguments> = loadResource("/full/QF_UFNIA/")

  @ParameterizedTest @MethodSource("getQF_UFNRAFiles") fun parseQF_UFNRA(file: File) = parse(file)

  fun getQF_UFNRAFiles(): Stream<Arguments> = loadResource("/full/QF_UFNRA/")

  @ParameterizedTest @MethodSource("getUFFiles") fun parseUF(file: File) = parse(file)

  fun getUFFiles(): Stream<Arguments> = loadResource("/full/UF/")

  @Disabled @ParameterizedTest @MethodSource("getUFBVFiles") fun parseUFBV(file: File) = parse(file)

  fun getUFBVFiles(): Stream<Arguments> = loadResource("/full/UFBV/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getUFBVDTFiles")
  fun parseUFBVDT(file: File) = parse(file)

  fun getUFBVDTFiles(): Stream<Arguments> = loadResource("/full/UFBVDT/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getUFBVFPFiles")
  fun parseUFBVFP(file: File) = parse(file)

  fun getUFBVFPFiles(): Stream<Arguments> = loadResource("/full/UFBVFP/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getUFBVLIAFiles")
  fun parseUFBVLIA(file: File) = parse(file)

  fun getUFBVLIAFiles(): Stream<Arguments> = loadResource("/full/UFBVLIA/")

  @Disabled @ParameterizedTest @MethodSource("getUFDTFiles") fun parseUFDT(file: File) = parse(file)

  fun getUFDTFiles(): Stream<Arguments> = loadResource("/full/UFDT/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getUFDTLIAFiles")
  fun parseUFDTLIA(file: File) = parse(file)

  fun getUFDTLIAFiles(): Stream<Arguments> = loadResource("/full/UFDTLIA/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getUFDTLIRAFiles")
  fun parseUFDTLIRA(file: File) = parse(file)

  fun getUFDTLIRAFiles(): Stream<Arguments> = loadResource("/full/UFDTLIRA/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getUFDTNIAFiles")
  fun parseUFDTNIA(file: File) = parse(file)

  fun getUFDTNIAFiles(): Stream<Arguments> = loadResource("/full/UFDTNIA/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getUFDTNIRAFiles")
  fun parseUFDTNIRA(file: File) = parse(file)

  fun getUFDTNIRAFiles(): Stream<Arguments> = loadResource("/full/UFDTNIRA/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getUFFPDTNIRAFiles")
  fun parseUFFPDTNIRA(file: File) = parse(file)

  fun getUFFPDTNIRAFiles(): Stream<Arguments> = loadResource("/full/UFFPDTNIRA/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getUFIDLFiles")
  fun parseUFIDL(file: File) = parse(file)

  fun getUFIDLFiles(): Stream<Arguments> = loadResource("/full/UFIDL/")

  @ParameterizedTest @MethodSource("getUFLIAFiles") fun parseUFLIA(file: File) = parse(file)

  fun getUFLIAFiles(): Stream<Arguments> = loadResource("/full/UFLIA/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getUFLRAFiles")
  fun parseUFLRA(file: File) = parse(file)

  fun getUFLRAFiles(): Stream<Arguments> = loadResource("/full/UFLRA/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getUFNIAFiles")
  fun parseUFNIA(file: File) = parse(file)

  fun getUFNIAFiles(): Stream<Arguments> = loadResource("/full/UFNIA/")

  @Disabled
  @ParameterizedTest
  @MethodSource("getUFNIRAFiles")
  fun parseUFNIRA(file: File) = parse(file)

  fun getUFNIRAFiles(): Stream<Arguments> = loadResource("/full/UFNIRA/")
}

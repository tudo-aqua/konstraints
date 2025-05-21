package tools.aqua.konstraints

import org.junit.jupiter.api.Assertions.assertDoesNotThrow
import org.junit.jupiter.api.Assumptions.assumeTrue
import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.Timeout
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import tools.aqua.konstraints.parser.Parser
import java.io.BufferedReader
import java.io.File
import java.util.concurrent.TimeUnit
import java.util.stream.Stream
import kotlin.streams.asStream
import kotlin.use

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
            Parser().parse(file.bufferedReader().use(BufferedReader::readLines).joinToString(""))
        }
    }

    @Disabled
    @ParameterizedTest
    @MethodSource("getABVFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseABV(file: File) = parse(file)
    fun getABVFiles(): Stream<Arguments> = loadResource("/full/ABV/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getABVFPFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseABVFP(file: File) = parse(file)
    fun getABVFPFiles(): Stream<Arguments> = loadResource("/full/ABVFP/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getABVFPLRAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseABVFPLRA(file: File) = parse(file)
    fun getABVFPLRAFiles(): Stream<Arguments> = loadResource("/full/ABVFPLRA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getALIAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseALIA(file: File) = parse(file)
    fun getALIAFiles(): Stream<Arguments> = loadResource("/full/ALIA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getANIAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseANIA(file: File) = parse(file)
    fun getANIAFiles(): Stream<Arguments> = loadResource("/full/ANIA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getAUFBVFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseAUFBV(file: File) = parse(file)
    fun getAUFBVFiles(): Stream<Arguments> = loadResource("/full/AUFBV/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getAUFBVDTLIAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseAUFBVDTLIA(file: File) = parse(file)
    fun getAUFBVDTLIAFiles(): Stream<Arguments> = loadResource("/full/AUFBVDTLIA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getAUFBVDTNIAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseAUFBVDTNIA(file: File) = parse(file)
    fun getAUFBVDTNIAFiles(): Stream<Arguments> = loadResource("/full/AUFBVDTNIA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getAUFBVDTNIRAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseAUFBVDTNIRA(file: File) = parse(file)
    fun getAUFBVDTNIRAFiles(): Stream<Arguments> = loadResource("/full/AUFBVDTNIRA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getAUFBVFPFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseAUFBVFP(file: File) = parse(file)
    fun getAUFBVFPFiles(): Stream<Arguments> = loadResource("/full/AUFBVFP/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getAUFDTLIAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseAUFDTLIA(file: File) = parse(file)
    fun getAUFDTLIAFiles(): Stream<Arguments> = loadResource("/full/AUFDTLIA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getAUFDTLIRAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseAUFDTLIRA(file: File) = parse(file)
    fun getAUFDTLIRAFiles(): Stream<Arguments> = loadResource("/full/AUFDTLIRA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getAUFDTNIRAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseAUFDTNIRA(file: File) = parse(file)
    fun getAUFDTNIRAFiles(): Stream<Arguments> = loadResource("/full/AUFDTNIRA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getAUFFPDTNIRAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseAUFFPDTNIRA(file: File) = parse(file)
    fun getAUFFPDTNIRAFiles(): Stream<Arguments> = loadResource("/full/AUFFPDTNIRA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getAUFLIAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseAUFLIA(file: File) = parse(file)
    fun getAUFLIAFiles(): Stream<Arguments> = loadResource("/full/AUFLIA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getAUFLIRAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseAUFLIRA(file: File) = parse(file)
    fun getAUFLIRAFiles(): Stream<Arguments> = loadResource("/full/AUFLIRA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getAUFNIAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseAUFNIA(file: File) = parse(file)
    fun getAUFNIAFiles(): Stream<Arguments> = loadResource("/full/AUFNIA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getAUFNIRAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseAUFNIRA(file: File) = parse(file)
    fun getAUFNIRAFiles(): Stream<Arguments> = loadResource("/full/AUFNIRA/")

    /* @Disabled */
    @ParameterizedTest
    @MethodSource("getBVFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseBV(file: File) = parse(file)
    fun getBVFiles(): Stream<Arguments> = loadResource("/full/BV/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getBVFPFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseBVFP(file: File) = parse(file)
    fun getBVFPFiles(): Stream<Arguments> = loadResource("/full/BVFP/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getBVFPLRAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseBVFPLRA(file: File) = parse(file)
    fun getBVFPLRAFiles(): Stream<Arguments> = loadResource("/full/BVFPLRA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getFPFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseFP(file: File) = parse(file)
    fun getFPFiles(): Stream<Arguments> = loadResource("/full/FP/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getFPLRAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseFPLRA(file: File) = parse(file)
    fun getFPLRAFiles(): Stream<Arguments> = loadResource("/full/FPLRA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getLIAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseLIA(file: File) = parse(file)
    fun getLIAFiles(): Stream<Arguments> = loadResource("/full/LIA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getLRAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseLRA(file: File) = parse(file)
    fun getLRAFiles(): Stream<Arguments> = loadResource("/full/LRA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getNIAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseNIA(file: File) = parse(file)
    fun getNIAFiles(): Stream<Arguments> = loadResource("/full/NIA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getNRAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseNRA(file: File) = parse(file)
    fun getNRAFiles(): Stream<Arguments> = loadResource("/full/NRA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_ABVFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_ABV(file: File) = parse(file)
    fun getQF_ABVFiles(): Stream<Arguments> = loadResource("/full/QF_ABV/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_ABVFPFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_ABVFP(file: File) = parse(file)
    fun getQF_ABVFPFiles(): Stream<Arguments> = loadResource("/full/QF_ABVFP/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_ABVFPLRAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_ABVFPLRA(file: File) = parse(file)
    fun getQF_ABVFPLRAFiles(): Stream<Arguments> = loadResource("/full/QF_ABVFPLRA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_ALIAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_ALIA(file: File) = parse(file)
    fun getQF_ALIAFiles(): Stream<Arguments> = loadResource("/full/QF_ALIA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_ANIAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_ANIA(file: File) = parse(file)
    fun getQF_ANIAFiles(): Stream<Arguments> = loadResource("/full/QF_ANIA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_AUFBVFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_AUFBV(file: File) = parse(file)
    fun getQF_AUFBVFiles(): Stream<Arguments> = loadResource("/full/QF_AUFBV/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_AUFBVFPFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_AUFBVFP(file: File) = parse(file)
    fun getQF_AUFBVFPFiles(): Stream<Arguments> = loadResource("/full/QF_AUFBVFP/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_AUFLIAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_AUFLIA(file: File) = parse(file)
    fun getQF_AUFLIAFiles(): Stream<Arguments> = loadResource("/full/QF_AUFLIA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_AUFNIAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_AUFNIA(file: File) = parse(file)
    fun getQF_AUFNIAFiles(): Stream<Arguments> = loadResource("/full/QF_AUFNIA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_AXFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_AX(file: File) = parse(file)
    fun getQF_AXFiles(): Stream<Arguments> = loadResource("/full/QF_AX/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_BVFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_BV(file: File) = parse(file)
    fun getQF_BVFiles(): Stream<Arguments> = loadResource("/full/QF_BV/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_BVFPFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_BVFP(file: File) = parse(file)
    fun getQF_BVFPFiles(): Stream<Arguments> = loadResource("/full/QF_BVFP/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_BVFPLRAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_BVFPLRA(file: File) = parse(file)
    fun getQF_BVFPLRAFiles(): Stream<Arguments> = loadResource("/full/QF_BVFPLRA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_DTFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_DT(file: File) = parse(file)
    fun getQF_DTFiles(): Stream<Arguments> = loadResource("/full/QF_DT/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_FPFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_FP(file: File) = parse(file)
    fun getQF_FPFiles(): Stream<Arguments> = loadResource("/full/QF_FP/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_FPLRAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_FPLRA(file: File) = parse(file)
    fun getQF_FPLRAFiles(): Stream<Arguments> = loadResource("/full/QF_FPLRA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_IDLFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_IDL(file: File) = parse(file)
    fun getQF_IDLFiles(): Stream<Arguments> = loadResource("/full/QF_IDL/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_LIAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_LIA(file: File) = parse(file)
    fun getQF_LIAFiles(): Stream<Arguments> = loadResource("/full/QF_LIA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_LIRAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_LIRA(file: File) = parse(file)
    fun getQF_LIRAFiles(): Stream<Arguments> = loadResource("/full/QF_LIRA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_LRAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_LRA(file: File) = parse(file)
    fun getQF_LRAFiles(): Stream<Arguments> = loadResource("/full/QF_LRA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_NIAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_NIA(file: File) = parse(file)
    fun getQF_NIAFiles(): Stream<Arguments> = loadResource("/full/QF_NIA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_NIRAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_NIRA(file: File) = parse(file)
    fun getQF_NIRAFiles(): Stream<Arguments> = loadResource("/full/QF_NIRA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_NRAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_NRA(file: File) = parse(file)
    fun getQF_NRAFiles(): Stream<Arguments> = loadResource("/full/QF_NRA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_RDLFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_RDL(file: File) = parse(file)
    fun getQF_RDLFiles(): Stream<Arguments> = loadResource("/full/QF_RDL/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_SFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_S(file: File) = parse(file)
    fun getQF_SFiles(): Stream<Arguments> = loadResource("/full/QF_S/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_SLIAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_SLIA(file: File) = parse(file)
    fun getQF_SLIAFiles(): Stream<Arguments> = loadResource("/full/QF_SLIA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_SNIAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_SNIA(file: File) = parse(file)
    fun getQF_SNIAFiles(): Stream<Arguments> = loadResource("/full/QF_SNIA/")

    /* @Disabled */
    @ParameterizedTest
    @MethodSource("getQF_UFFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_UF(file: File) = parse(file)
    fun getQF_UFFiles(): Stream<Arguments> = loadResource("/full/QF_UF/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_UFBVFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_UFBV(file: File) = parse(file)
    fun getQF_UFBVFiles(): Stream<Arguments> = loadResource("/full/QF_UFBV/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_UFBVDTFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_UFBVDT(file: File) = parse(file)
    fun getQF_UFBVDTFiles(): Stream<Arguments> = loadResource("/full/QF_UFBVDT/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_UFDTFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_UFDT(file: File) = parse(file)
    fun getQF_UFDTFiles(): Stream<Arguments> = loadResource("/full/QF_UFDT/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_UFDTLIAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_UFDTLIA(file: File) = parse(file)
    fun getQF_UFDTLIAFiles(): Stream<Arguments> = loadResource("/full/QF_UFDTLIA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_UFDTLIRAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_UFDTLIRA(file: File) = parse(file)
    fun getQF_UFDTLIRAFiles(): Stream<Arguments> = loadResource("/full/QF_UFDTLIRA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_UFDTNIAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_UFDTNIA(file: File) = parse(file)
    fun getQF_UFDTNIAFiles(): Stream<Arguments> = loadResource("/full/QF_UFDTNIA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_UFFPFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_UFFP(file: File) = parse(file)
    fun getQF_UFFPFiles(): Stream<Arguments> = loadResource("/full/QF_UFFP/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_UFFPDTNIRAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_UFFPDTNIRA(file: File) = parse(file)
    fun getQF_UFFPDTNIRAFiles(): Stream<Arguments> = loadResource("/full/QF_UFFPDTNIRA/")

    /* @Disabled */
    @ParameterizedTest
    @MethodSource("getQF_UFIDLFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_UFIDL(file: File) = parse(file)
    fun getQF_UFIDLFiles(): Stream<Arguments> = loadResource("/full/QF_UFIDL/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_UFLIAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_UFLIA(file: File) = parse(file)
    fun getQF_UFLIAFiles(): Stream<Arguments> = loadResource("/full/QF_UFLIA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_UFLRAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_UFLRA(file: File) = parse(file)
    fun getQF_UFLRAFiles(): Stream<Arguments> = loadResource("/full/QF_UFLRA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_UFNIAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_UFNIA(file: File) = parse(file)
    fun getQF_UFNIAFiles(): Stream<Arguments> = loadResource("/full/QF_UFNIA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getQF_UFNRAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseQF_UFNRA(file: File) = parse(file)
    fun getQF_UFNRAFiles(): Stream<Arguments> = loadResource("/full/QF_UFNRA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getUFFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseUF(file: File) = parse(file)
    fun getUFFiles(): Stream<Arguments> = loadResource("/full/UF/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getUFBVFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseUFBV(file: File) = parse(file)
    fun getUFBVFiles(): Stream<Arguments> = loadResource("/full/UFBV/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getUFBVDTFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseUFBVDT(file: File) = parse(file)
    fun getUFBVDTFiles(): Stream<Arguments> = loadResource("/full/UFBVDT/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getUFBVFPFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseUFBVFP(file: File) = parse(file)
    fun getUFBVFPFiles(): Stream<Arguments> = loadResource("/full/UFBVFP/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getUFBVLIAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseUFBVLIA(file: File) = parse(file)
    fun getUFBVLIAFiles(): Stream<Arguments> = loadResource("/full/UFBVLIA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getUFDTFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseUFDT(file: File) = parse(file)
    fun getUFDTFiles(): Stream<Arguments> = loadResource("/full/UFDT/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getUFDTLIAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseUFDTLIA(file: File) = parse(file)
    fun getUFDTLIAFiles(): Stream<Arguments> = loadResource("/full/UFDTLIA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getUFDTLIRAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseUFDTLIRA(file: File) = parse(file)
    fun getUFDTLIRAFiles(): Stream<Arguments> = loadResource("/full/UFDTLIRA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getUFDTNIAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseUFDTNIA(file: File) = parse(file)
    fun getUFDTNIAFiles(): Stream<Arguments> = loadResource("/full/UFDTNIA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getUFDTNIRAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseUFDTNIRA(file: File) = parse(file)
    fun getUFDTNIRAFiles(): Stream<Arguments> = loadResource("/full/UFDTNIRA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getUFFPDTNIRAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseUFFPDTNIRA(file: File) = parse(file)
    fun getUFFPDTNIRAFiles(): Stream<Arguments> = loadResource("/full/UFFPDTNIRA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getUFIDLFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseUFIDL(file: File) = parse(file)
    fun getUFIDLFiles(): Stream<Arguments> = loadResource("/full/UFIDL/")

    /* @Disabled */
    @ParameterizedTest
    @MethodSource("getUFLIAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseUFLIA(file: File) = parse(file)
    fun getUFLIAFiles(): Stream<Arguments> = loadResource("/full/UFLIA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getUFLRAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseUFLRA(file: File) = parse(file)
    fun getUFLRAFiles(): Stream<Arguments> = loadResource("/full/UFLRA/")

    /* @Disabled */
    @ParameterizedTest
    @MethodSource("getUFNIAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseUFNIA(file: File) = parse(file)
    fun getUFNIAFiles(): Stream<Arguments> = loadResource("/full/UFNIA/")

    @Disabled
    @ParameterizedTest
    @MethodSource("getUFNIRAFiles")
    @Timeout(value = 1, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    fun parseUFNIRA(file: File) = parse(file)
    fun getUFNIRAFiles(): Stream<Arguments> = loadResource("/full/UFNIRA/")
}
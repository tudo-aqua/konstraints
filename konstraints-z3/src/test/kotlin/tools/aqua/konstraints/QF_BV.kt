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

package tools.aqua.konstraints.util

import java.io.BufferedReader
import java.io.File
import java.util.concurrent.TimeUnit
import java.util.stream.Stream
import kotlin.streams.asStream
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Assumptions
import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.TestInstance
import org.junit.jupiter.api.Timeout
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import tools.aqua.konstraints.parser.Parser
import tools.aqua.konstraints.smt.SymbolAttributeValue
import tools.aqua.konstraints.solvers.z3.Z3Solver

@Disabled
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class QF_BV {
  private fun loadResource(path: String) =
      File(javaClass.getResource(path)!!.file)
          .walk()
          .filter { file: File -> file.isFile }
          .map { file: File -> Arguments.arguments(file) }
          .asStream()

  private fun solve(file: File) {
    Assumptions.assumeTrue(
        file.length() < 5000000,
        "Skipped due to file size exceeding limit of 5000000",
    )

    val solver = Z3Solver()
    val result = Parser(file.bufferedReader().use(BufferedReader::readLines).joinToString(""))

    Assumptions.assumeTrue(
        (result.info("status") as SymbolAttributeValue).symbol.toString() != "unknown",
        "Skipped due to unknown sat status.",
    )

    solver.use {
      result.commands.map { solver.visit(it) }

      // verify we get the correct status for the test
      Assertions.assertEquals(
          (result.info("status") as SymbolAttributeValue).symbol.toString(),
          solver.status.toString(),
      )
    }
  }

  @ParameterizedTest
  @MethodSource("getQFBV2017_BuchwaldFried")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_2017_BuchwaldFried(file: File) = solve(file)

  fun getQFBV2017_BuchwaldFried(): Stream<Arguments> = loadResource("/QF_BV/2017-BuchwaldFried/")

  @ParameterizedTest
  @MethodSource("getQFBV20170501_Heizmann_UltimateAutomizer")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_20170501_Heizmann_UltimateAutomizer(file: File) = solve(file)

  fun getQFBV20170501_Heizmann_UltimateAutomizer(): Stream<Arguments> =
      loadResource("/QF_BV/20170501-Heizmann-UltimateAutomizer/")

  @ParameterizedTest
  @MethodSource("getQFBV20170531_Hansen_Check")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_20170531_Hansen_Check(file: File) = solve(file)

  fun getQFBV20170531_Hansen_Check(): Stream<Arguments> =
      loadResource("/QF_BV/20170531-Hansen-Check/")

  @ParameterizedTest
  @MethodSource("getQFBV2018_Goel_hwbench")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_2018_Goel_hwbench(file: File) = solve(file)

  fun getQFBV2018_Goel_hwbench(): Stream<Arguments> = loadResource("/QF_BV/2018-Goel-hwbench/")

  @ParameterizedTest
  @MethodSource("getQFBV2018_Mann")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_2018_Mann(file: File) = solve(file)

  fun getQFBV2018_Mann(): Stream<Arguments> = loadResource("/QF_BV/2018-Mann/")

  @ParameterizedTest
  @MethodSource("getQFBV2019_Mann")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_2019_Mann(file: File) = solve(file)

  fun getQFBV2019_Mann(): Stream<Arguments> = loadResource("/QF_BV/2019-Mann/")

  @ParameterizedTest
  @MethodSource("getQFBV2019_Wolf_fmbench")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_2019_Wolf_fmbench(file: File) = solve(file)

  fun getQFBV2019_Wolf_fmbench(): Stream<Arguments> = loadResource("/QF_BV/2019-Wolf-fmbench/")

  @ParameterizedTest
  @MethodSource("getQFBV20190311_bv_term_small_rw_Noetzli")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_20190311_bv_term_small_rw_Noetzli(file: File) = solve(file)

  fun getQFBV20190311_bv_term_small_rw_Noetzli(): Stream<Arguments> =
      loadResource("/QF_BV/20190311-bv-term-small-rw-Noetzli/")

  @ParameterizedTest
  @MethodSource("getQFBV20190429_UltimateAutomizerSvcomp2019")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_20190429_UltimateAutomizerSvcomp2019(file: File) = solve(file)

  fun getQFBV20190429_UltimateAutomizerSvcomp2019(): Stream<Arguments> =
      loadResource("/QF_BV/20190429-UltimateAutomizerSvcomp2019/")

  @ParameterizedTest
  @MethodSource("getQFBV2020_Weber")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_2020_Weber(file: File) = solve(file)

  fun getQFBV2020_Weber(): Stream<Arguments> = loadResource("/QF_BV/2020-Weber/")

  @ParameterizedTest
  @MethodSource("getQFBV20200328_Favaro")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_20200328_Favaro(file: File) = solve(file)

  fun getQFBV20200328_Favaro(): Stream<Arguments> = loadResource("/QF_BV/20200328-Favaro/")

  @ParameterizedTest
  @MethodSource("getQFBV20200415_Yurichev")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_20200415_Yurichev(file: File) = solve(file)

  fun getQFBV20200415_Yurichev(): Stream<Arguments> = loadResource("/QF_BV/20200415-Yurichev/")

  @ParameterizedTest
  @MethodSource("getQFBV20210219_Sydr")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_20210219_Sydr(file: File) = solve(file)

  fun getQFBV20210219_Sydr(): Stream<Arguments> = loadResource("/QF_BV/20210219-Sydr/")

  @ParameterizedTest
  @MethodSource("getQFBV20210312_Bouvier")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_20210312_Bouvier(file: File) = solve(file)

  fun getQFBV20210312_Bouvier(): Stream<Arguments> = loadResource("/QF_BV/20210312-Bouvier/")

  @ParameterizedTest
  @MethodSource("getQFBV20220315_ecrw")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_20220315_ecrw(file: File) = solve(file)

  fun getQFBV20220315_ecrw(): Stream<Arguments> = loadResource("/QF_BV/20220315-ecrw/")

  @ParameterizedTest
  @MethodSource("getQFBV20221012_MCMPC")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_20221012_MCMPC(file: File) = solve(file)

  fun getQFBV20221012_MCMPC(): Stream<Arguments> = loadResource("/QF_BV/20221012-MCMPC/")

  @ParameterizedTest
  @MethodSource("getQFBV20221214_p4dfa_XiaoqiChen")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_20221214_p4dfa_XiaoqiChen(file: File) = solve(file)

  fun getQFBV20221214_p4dfa_XiaoqiChen(): Stream<Arguments> =
      loadResource("/QF_BV/20221214-p4dfa-XiaoqiChen/")

  @ParameterizedTest
  @MethodSource("getQFBV20230221_oisc_gurtner")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_20230221_oisc_gurtner(file: File) = solve(file)

  fun getQFBV20230221_oisc_gurtner(): Stream<Arguments> =
      loadResource("/QF_BV/20230221-oisc-gurtner/")

  @ParameterizedTest
  @MethodSource("getQFBV20230224_grsbits_truby")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_20230224_grsbits_truby(file: File) = solve(file)

  fun getQFBV20230224_grsbits_truby(): Stream<Arguments> =
      loadResource("/QF_BV/20230224-grsbits-truby/")

  @ParameterizedTest
  @MethodSource("getQFBV20230321_UltimateAutomizerSvcomp2023")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_20230321_UltimateAutomizerSvcomp2023(file: File) = solve(file)

  fun getQFBV20230321_UltimateAutomizerSvcomp2023(): Stream<Arguments> =
      loadResource("/QF_BV/20230321-UltimateAutomizerSvcomp2023/")

  @ParameterizedTest
  @MethodSource("getQFBVasp")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_asp(file: File) = solve(file)

  fun getQFBVasp(): Stream<Arguments> = loadResource("/QF_BV/asp/")

  @ParameterizedTest
  @MethodSource("getQFBVbench_ab")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_bench_ab(file: File) = solve(file)

  fun getQFBVbench_ab(): Stream<Arguments> = loadResource("/QF_BV/bench_ab/")

  @ParameterizedTest
  @MethodSource("getQFBVbmc_bv")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_bmc_bv(file: File) = solve(file)

  fun getQFBVbmc_bv(): Stream<Arguments> = loadResource("/QF_BV/bmc-bv/")

  @ParameterizedTest
  @MethodSource("getQFBVbmc_bv_svcomp14")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_bmc_bv_svcomp14(file: File) = solve(file)

  fun getQFBVbmc_bv_svcomp14(): Stream<Arguments> = loadResource("/QF_BV/bmc-bv-svcomp14/")

  @ParameterizedTest
  @MethodSource("getQFBVbrummayerbiere")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_brummayerbiere(file: File) = solve(file)

  fun getQFBVbrummayerbiere(): Stream<Arguments> = loadResource("/QF_BV/brummayerbiere/")

  @ParameterizedTest
  @MethodSource("getQFBVbrummayerbiere2")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_brummayerbiere2(file: File) = solve(file)

  fun getQFBVbrummayerbiere2(): Stream<Arguments> = loadResource("/QF_BV/brummayerbiere2/")

  @ParameterizedTest
  @MethodSource("getQFBVbrummayerbiere3")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_brummayerbiere3(file: File) = solve(file)

  fun getQFBVbrummayerbiere3(): Stream<Arguments> = loadResource("/QF_BV/brummayerbiere3/")

  @ParameterizedTest
  @MethodSource("getQFBVbrummayerbiere4")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_brummayerbiere4(file: File) = solve(file)

  fun getQFBVbrummayerbiere4(): Stream<Arguments> = loadResource("/QF_BV/brummayerbiere4/")

  @ParameterizedTest
  @MethodSource("getQFBVbruttomesso")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_bruttomesso(file: File) = solve(file)

  fun getQFBVbruttomesso(): Stream<Arguments> = loadResource("/QF_BV/bruttomesso/")

  @ParameterizedTest
  @MethodSource("getQFBVcalypto")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_calypto(file: File) = solve(file)

  fun getQFBVcalypto(): Stream<Arguments> = loadResource("/QF_BV/calypto/")

  @ParameterizedTest
  @MethodSource("getQFBVchallenge")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_challenge(file: File) = solve(file)

  fun getQFBVchallenge(): Stream<Arguments> = loadResource("/QF_BV/challenge/")

  @ParameterizedTest
  @MethodSource("getQFBVcheck2")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_check2(file: File) = solve(file)

  fun getQFBVcheck2(): Stream<Arguments> = loadResource("/QF_BV/check2/")

  @ParameterizedTest
  @MethodSource("getQFBVcrafted")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_crafted(file: File) = solve(file)

  fun getQFBVcrafted(): Stream<Arguments> = loadResource("/QF_BV/crafted/")

  @ParameterizedTest
  @MethodSource("getQFBVdwp_formulas")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_dwp_formulas(file: File) = solve(file)

  fun getQFBVdwp_formulas(): Stream<Arguments> = loadResource("/QF_BV/dwp_formulas/")

  @ParameterizedTest
  @MethodSource("getQFBVecc")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_ecc(file: File) = solve(file)

  fun getQFBVecc(): Stream<Arguments> = loadResource("/QF_BV/ecc/")

  @ParameterizedTest
  @MethodSource("getQFBVfft")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_fft(file: File) = solve(file)

  fun getQFBVfft(): Stream<Arguments> = loadResource("/QF_BV/fft/")

  @ParameterizedTest
  @MethodSource("getQFBVfloat")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_float(file: File) = solve(file)

  fun getQFBVfloat(): Stream<Arguments> = loadResource("/QF_BV/float/")

  @ParameterizedTest
  @MethodSource("getQFBVgalois")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_galois(file: File) = solve(file)

  fun getQFBVgalois(): Stream<Arguments> = loadResource("/QF_BV/galois/")

  @ParameterizedTest
  @MethodSource("getQFBVgulwani_pldi08")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_gulwani_pldi08(file: File) = solve(file)

  fun getQFBVgulwani_pldi08(): Stream<Arguments> = loadResource("/QF_BV/gulwani-pldi08/")

  @ParameterizedTest
  @MethodSource("getQFBVlog_slicing")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_log_slicing(file: File) = solve(file)

  fun getQFBVlog_slicing(): Stream<Arguments> = loadResource("/QF_BV/log-slicing/")

  @ParameterizedTest
  @MethodSource("getQFBVmcm")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_mcm(file: File) = solve(file)

  fun getQFBVmcm(): Stream<Arguments> = loadResource("/QF_BV/mcm/")

  @ParameterizedTest
  @MethodSource("getQFBVModels")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_Models(file: File) = solve(file)

  fun getQFBVModels(): Stream<Arguments> = loadResource("/QF_BV/Models/")

  @ParameterizedTest
  @MethodSource("getQFBVpipe")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_pipe(file: File) = solve(file)

  fun getQFBVpipe(): Stream<Arguments> = loadResource("/QF_BV/pipe/")

  @ParameterizedTest
  @MethodSource("getQFBVpspace")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_pspace(file: File) = solve(file)

  fun getQFBVpspace(): Stream<Arguments> = loadResource("/QF_BV/pspace/")

  @ParameterizedTest
  @MethodSource("getQFBVrubik")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_rubik(file: File) = solve(file)

  fun getQFBVrubik(): Stream<Arguments> = loadResource("/QF_BV/rubik/")

  @ParameterizedTest
  @MethodSource("getQFBVRWS")
  @Timeout(value = 30, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_RWS(file: File) = solve(file)

  fun getQFBVRWS(): Stream<Arguments> = loadResource("/QF_BV/RWS/")

  @ParameterizedTest
  @MethodSource("getQFBVsage")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_sage(file: File) = solve(file)

  fun getQFBVsage(): Stream<Arguments> = loadResource("/QF_BV/sage/")

  @ParameterizedTest
  @MethodSource("getQFBVSage2")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_Sage2(file: File) = solve(file)

  fun getQFBVSage2(): Stream<Arguments> = loadResource("/QF_BV/Sage2/")

  @ParameterizedTest
  @MethodSource("getQFBVspear")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_spear(file: File) = solve(file)

  fun getQFBVspear(): Stream<Arguments> = loadResource("/QF_BV/spear/")

  @ParameterizedTest
  @MethodSource("getQFBVstp")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_stp(file: File) = solve(file)

  fun getQFBVstp(): Stream<Arguments> = loadResource("/QF_BV/stp/")

  @ParameterizedTest
  @MethodSource("getQFBVstp_samples")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_stp_samples(file: File) = solve(file)

  fun getQFBVstp_samples(): Stream<Arguments> = loadResource("/QF_BV/stp_samples/")

  @ParameterizedTest
  @MethodSource("getQFBVtacas07")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_tacas07(file: File) = solve(file)

  fun getQFBVtacas07(): Stream<Arguments> = loadResource("/QF_BV/tacas07/")

  @ParameterizedTest
  @MethodSource("getQFBVuclid")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_uclid(file: File) = solve(file)

  fun getQFBVuclid(): Stream<Arguments> = loadResource("/QF_BV/uclid/")

  @ParameterizedTest
  @MethodSource("getQFBVuclid_contrib_smtcomp09")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_uclid_contrib_smtcomp09(file: File) = solve(file)

  fun getQFBVuclid_contrib_smtcomp09(): Stream<Arguments> =
      loadResource("/QF_BV/uclid_contrib_smtcomp09/")

  @ParameterizedTest
  @MethodSource("getQFBVuum")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_uum(file: File) = solve(file)

  fun getQFBVuum(): Stream<Arguments> = loadResource("/QF_BV/uum/")

  @ParameterizedTest
  @MethodSource("getQFBVVS3")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_VS3(file: File) = solve(file)

  fun getQFBVVS3(): Stream<Arguments> = loadResource("/QF_BV/VS3/")

  @ParameterizedTest
  @MethodSource("getQFBVwienand_cav2008")
  @Timeout(value = 5, unit = TimeUnit.SECONDS, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
  fun QF_BV_wienand_cav2008(file: File) = solve(file)

  fun getQFBVwienand_cav2008(): Stream<Arguments> = loadResource("/QF_BV/wienand-cav2008/")
}

(set-info :smt-lib-version 2.6)
(set-logic QF_UF)
(set-info :source |
Generated by: Aman Goel (amangoel@umich.edu), Karem A. Sakallah (karem@umich.edu)
Generated on: 2018-04-06

Generated by the tool Averroes 2 (successor of [1]) which implements safety property
verification on hardware systems.

This SMT problem belongs to a set of SMT problems generated by applying Averroes 2
to benchmarks derived from [2-5].

A total of 412 systems (345 from [2], 19 from [3], 26 from [4], 22 from [5]) were
syntactically converted from their original formats (using [6, 7]), and given to 
Averroes 2 to perform property checking with abstraction (wide bit-vectors -> terms, 
wide operators -> UF) using SMT solvers [8, 9].

[1] Lee S., Sakallah K.A. (2014) Unbounded Scalable Verification Based on Approximate
Property-Directed Reachability and Datapath Abstraction. In: Biere A., Bloem R. (eds)
Computer Aided Verification. CAV 2014. Lecture Notes in Computer Science, vol 8559.
Springer, Cham
[2] http://fmv.jku.at/aiger/index.html#beem
[3] http://www.cs.cmu.edu/~modelcheck/vcegar
[4] http://www.cprover.org/hardware/v2c
[5] http://github.com/aman-goel/verilogbench
[6] http://www.clifford.at/yosys
[7] http://github.com/chengyinwu/V3
[8] http://github.com/Z3Prover/z3
[9] http://github.com/SRI-CSL/yices2

id: itc99_b13
query-maker: "Yices 2"
query-time: 6.767000 ms
query-class: abstract
query-category: oneshot
query-type: cti
status: unsat
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")

;
(set-info :status unsat)
(declare-sort utt$2 0)
(declare-sort utt$3 0)
(declare-sort utt$4 0)
(declare-sort utt$8 0)
(declare-sort utt$10 0)
(declare-sort utt$22 0)
(declare-sort utt$24 0)
(declare-sort utt$30 0)
(declare-sort utt$31 0)
(declare-sort utt$32 0)
(declare-fun Add_32_32_32 (utt$32 utt$32 ) utt$32)
(declare-fun Concat_32_10_22 (utt$10 utt$22 ) utt$32)
(declare-fun Concat_32_1_31 (Bool utt$31 ) utt$32)
(declare-fun Concat_32_2_30 (utt$2 utt$30 ) utt$32)
(declare-fun Concat_32_8_24 (utt$8 utt$24 ) utt$32)
(declare-fun Concat_4_1_3 (Bool utt$3 ) utt$4)
(declare-fun Extract_10_9_0_32 (utt$32 ) utt$10)
(declare-fun Extract_1_3_3_4 (utt$4 ) Bool)
(declare-fun Extract_1_6_6_8 (utt$8 ) Bool)
(declare-fun Extract_2_9_8_10 (utt$10 ) utt$2)
(declare-fun Gr_1_32_32 (utt$32 utt$32 ) Bool)
(declare-fun y$1 () Bool)
(declare-fun y$10 () Bool)
(declare-fun y$102 () Bool)
(declare-fun y$106 () Bool)
(declare-fun y$113 () Bool)
(declare-fun y$115 () Bool)
(declare-fun y$12 () Bool)
(declare-fun y$130 () Bool)
(declare-fun y$14 () Bool)
(declare-fun y$140 () Bool)
(declare-fun y$142 () Bool)
(declare-fun y$151 () Bool)
(declare-fun y$159 () Bool)
(declare-fun y$16 () Bool)
(declare-fun y$163 () Bool)
(declare-fun y$167 () Bool)
(declare-fun y$175 () Bool)
(declare-fun y$177 () Bool)
(declare-fun y$18 () Bool)
(declare-fun y$185 () Bool)
(declare-fun y$187 () Bool)
(declare-fun y$195 () Bool)
(declare-fun y$199 () Bool)
(declare-fun y$20 () Bool)
(declare-fun y$201 () Bool)
(declare-fun y$203 () Bool)
(declare-fun y$205 () Bool)
(declare-fun y$209 () Bool)
(declare-fun y$213 () Bool)
(declare-fun y$215 () Bool)
(declare-fun y$217 () Bool)
(declare-fun y$218 () Bool)
(declare-fun y$22 () Bool)
(declare-fun y$223 () Bool)
(declare-fun y$225 () Bool)
(declare-fun y$228 () Bool)
(declare-fun y$231 () Bool)
(declare-fun y$236 () Bool)
(declare-fun y$239 () utt$2)
(declare-fun y$24 () Bool)
(declare-fun y$244 () Bool)
(declare-fun y$251 () Bool)
(declare-fun y$254 () Bool)
(declare-fun y$259 () Bool)
(declare-fun y$26 () Bool)
(declare-fun y$263 () Bool)
(declare-fun y$270 () Bool)
(declare-fun y$273 () Bool)
(declare-fun y$280 () Bool)
(declare-fun y$289 () Bool)
(declare-fun y$292 () Bool)
(declare-fun y$3 () Bool)
(declare-fun y$30 () Bool)
(declare-fun y$303 () Bool)
(declare-fun y$313 () Bool)
(declare-fun y$32 () Bool)
(declare-fun y$320 () Bool)
(declare-fun y$325 () Bool)
(declare-fun y$334 () Bool)
(declare-fun y$337 () Bool)
(declare-fun y$34 () Bool)
(declare-fun y$346 () Bool)
(declare-fun y$347 () Bool)
(declare-fun y$354 () Bool)
(declare-fun y$36 () Bool)
(declare-fun y$360 () Bool)
(declare-fun y$369 () Bool)
(declare-fun y$374 () Bool)
(declare-fun y$377 () Bool)
(declare-fun y$38 () Bool)
(declare-fun y$385 () Bool)
(declare-fun y$390 () Bool)
(declare-fun y$397 () Bool)
(declare-fun y$398 () Bool)
(declare-fun y$40 () Bool)
(declare-fun y$401 () Bool)
(declare-fun y$404 () Bool)
(declare-fun y$407 () Bool)
(declare-fun y$411 () Bool)
(declare-fun y$414 () utt$2)
(declare-fun y$418 () Bool)
(declare-fun y$42 () Bool)
(declare-fun y$423 () Bool)
(declare-fun y$426 () Bool)
(declare-fun y$431 () Bool)
(declare-fun y$434 () Bool)
(declare-fun y$435 () Bool)
(declare-fun y$44 () Bool)
(declare-fun y$442 () Bool)
(declare-fun y$445 () Bool)
(declare-fun y$452 () Bool)
(declare-fun y$461 () Bool)
(declare-fun y$464 () Bool)
(declare-fun y$47 () Bool)
(declare-fun y$475 () Bool)
(declare-fun y$484 () Bool)
(declare-fun y$489 () Bool)
(declare-fun y$49 () Bool)
(declare-fun y$492 () Bool)
(declare-fun y$499 () Bool)
(declare-fun y$5 () Bool)
(declare-fun y$502 () Bool)
(declare-fun y$509 () Bool)
(declare-fun y$510 () Bool)
(declare-fun y$517 () Bool)
(declare-fun y$522 () Bool)
(declare-fun y$529 () Bool)
(declare-fun y$534 () Bool)
(declare-fun y$537 () Bool)
(declare-fun y$544 () Bool)
(declare-fun y$549 () Bool)
(declare-fun y$550 () Bool)
(declare-fun y$552 () Bool)
(declare-fun y$554 () Bool)
(declare-fun y$556 () Bool)
(declare-fun y$560 () Bool)
(declare-fun y$58 () Bool)
(declare-fun y$582 () Bool)
(declare-fun y$59 () Bool)
(declare-fun y$605 () Bool)
(declare-fun y$606 () Bool)
(declare-fun y$607 () Bool)
(declare-fun y$608 () Bool)
(declare-fun y$609 () Bool)
(declare-fun y$610 () Bool)
(declare-fun y$613 () Bool)
(declare-fun y$627 () Bool)
(declare-fun y$628 () Bool)
(declare-fun y$629 () Bool)
(declare-fun y$630 () Bool)
(declare-fun y$631 () Bool)
(declare-fun y$632 () Bool)
(declare-fun y$645 () Bool)
(declare-fun y$662 () Bool)
(declare-fun y$663 () Bool)
(declare-fun y$664 () Bool)
(declare-fun y$665 () Bool)
(declare-fun y$666 () Bool)
(declare-fun y$667 () Bool)
(declare-fun y$678 () Bool)
(declare-fun y$688 () Bool)
(declare-fun y$689 () Bool)
(declare-fun y$690 () Bool)
(declare-fun y$691 () Bool)
(declare-fun y$692 () Bool)
(declare-fun y$693 () Bool)
(declare-fun y$701 () Bool)
(declare-fun y$705 () Bool)
(declare-fun y$706 () Bool)
(declare-fun y$707 () Bool)
(declare-fun y$708 () Bool)
(declare-fun y$709 () Bool)
(declare-fun y$716 () Bool)
(declare-fun y$717 () Bool)
(declare-fun y$718 () Bool)
(declare-fun y$719 () Bool)
(declare-fun y$720 () Bool)
(declare-fun y$725 () Bool)
(declare-fun y$727 () Bool)
(declare-fun y$728 () Bool)
(declare-fun y$730 () Bool)
(declare-fun y$734 () Bool)
(declare-fun y$738 () Bool)
(declare-fun y$742 () Bool)
(declare-fun y$747 () Bool)
(declare-fun y$75 () Bool)
(declare-fun y$758 () Bool)
(declare-fun y$762 () Bool)
(declare-fun y$776 () Bool)
(declare-fun y$786 () Bool)
(declare-fun y$787 () Bool)
(declare-fun y$788 () Bool)
(declare-fun y$795 () Bool)
(declare-fun y$8 () Bool)
(declare-fun y$800 () Bool)
(declare-fun y$801 () Bool)
(declare-fun y$802 () Bool)
(declare-fun y$807 () Bool)
(declare-fun y$812 () Bool)
(declare-fun y$813 () Bool)
(declare-fun y$814 () Bool)
(declare-fun y$817 () Bool)
(declare-fun y$826 () Bool)
(declare-fun y$835 () Bool)
(declare-fun y$852 () Bool)
(declare-fun y$853 () Bool)
(declare-fun y$857 () Bool)
(declare-fun y$860 () Bool)
(declare-fun y$861 () Bool)
(declare-fun y$862 () Bool)
(declare-fun y$863 () Bool)
(declare-fun y$864 () Bool)
(declare-fun y$865 () Bool)
(declare-fun y$866 () Bool)
(declare-fun y$87 () Bool)
(declare-fun y$871 () Bool)
(declare-fun y$878 () Bool)
(declare-fun y$881 () Bool)
(declare-fun y$882 () Bool)
(declare-fun y$883 () Bool)
(declare-fun y$884 () Bool)
(declare-fun y$885 () Bool)
(declare-fun y$886 () Bool)
(declare-fun y$889 () Bool)
(declare-fun y$89 () Bool)
(declare-fun y$890 () Bool)
(declare-fun y$891 () Bool)
(declare-fun y$892 () Bool)
(declare-fun y$901 () Bool)
(declare-fun y$907 () Bool)
(declare-fun y$908 () Bool)
(declare-fun y$909 () Bool)
(declare-fun y$910 () Bool)
(declare-fun y$911 () Bool)
(declare-fun y$912 () Bool)
(declare-fun y$913 () Bool)
(declare-fun y$94 () utt$10)
(declare-fun y$S1 () Bool)
(declare-fun y$S1$next () Bool)
(declare-fun y$S1$next_rhs () Bool)
(declare-fun y$S1$next_rhs_op () Bool)
(declare-fun y$S2 () Bool)
(declare-fun y$S2$next () Bool)
(declare-fun y$S2$next_rhs () Bool)
(declare-fun y$S2$next_rhs_op () Bool)
(declare-fun y$add_mpx2 () Bool)
(declare-fun y$add_mpx2$next () Bool)
(declare-fun y$canale () utt$4)
(declare-fun y$canale$next () utt$4)
(declare-fun y$confirm () Bool)
(declare-fun y$confirm$next () Bool)
(declare-fun y$confirm$next_rhs () Bool)
(declare-fun y$confirm$next_rhs_op () Bool)
(declare-fun y$conta_tmp () utt$4)
(declare-fun y$conta_tmp$next () utt$4)
(declare-fun y$data_in () utt$8)
(declare-fun y$data_out () Bool)
(declare-fun y$data_out$next () Bool)
(declare-fun y$data_out$next_rhs () Bool)
(declare-fun y$data_out$next_rhs_op () Bool)
(declare-fun y$dsr () Bool)
(declare-fun y$dsr$next () Bool)
(declare-fun y$error () Bool)
(declare-fun y$error$next () Bool)
(declare-fun y$error$next_rhs () Bool)
(declare-fun y$error$next_rhs_op () Bool)
(declare-fun y$itfc_state () Bool)
(declare-fun y$itfc_state$next () Bool)
(declare-fun y$itfc_state$next_rhs () Bool)
(declare-fun y$itfc_state$next_rhs_op () Bool)
(declare-fun y$load () Bool)
(declare-fun y$load$next () Bool)
(declare-fun y$load$next_rhs () Bool)
(declare-fun y$load$next_rhs_op () Bool)
(declare-fun y$load_dato () Bool)
(declare-fun y$load_dato$next () Bool)
(declare-fun y$mpx () Bool)
(declare-fun y$mpx$next () Bool)
(declare-fun y$mux_en () Bool)
(declare-fun y$mux_en$next () Bool)
(declare-fun y$mux_en$next_rhs () Bool)
(declare-fun y$mux_en$next_rhs_op () Bool)
(declare-fun y$n0s1 () Bool)
(declare-fun y$n0s10 () utt$10)
(declare-fun y$n0s22 () utt$22)
(declare-fun y$n0s24 () utt$24)
(declare-fun y$n0s3 () utt$3)
(declare-fun y$n0s30 () utt$30)
(declare-fun y$n0s31 () utt$31)
(declare-fun y$n0s32 () utt$32)
(declare-fun y$n0s4 () utt$4)
(declare-fun y$n0s8 () utt$8)
(declare-fun y$n104s32 () utt$32)
(declare-fun y$n1s1 () Bool)
(declare-fun y$n1s32 () utt$32)
(declare-fun y$n1s4 () utt$4)
(declare-fun y$next_bit () Bool)
(declare-fun y$next_bit$next () Bool)
(declare-fun y$next_bit$next_rhs () Bool)
(declare-fun y$next_bit$next_rhs_op () Bool)
(declare-fun y$out_reg () utt$8)
(declare-fun y$out_reg$next () utt$8)
(declare-fun y$out_reg$next_rhs () utt$8)
(declare-fun y$out_reg$next_rhs_op () utt$8)
(declare-fun y$prop () Bool)
(declare-fun y$prop$next () Bool)
(declare-fun y$prop0 () Bool)
(declare-fun y$prop0$next () Bool)
(declare-fun y$prop0$next_op () Bool)
(declare-fun y$prop0_op () Bool)
(declare-fun y$prop_1 () Bool)
(declare-fun y$prop_1$next () Bool)
(declare-fun y$prop_1$next_op () Bool)
(declare-fun y$prop_10 () Bool)
(declare-fun y$prop_10$next () Bool)
(declare-fun y$prop_10$next_op () Bool)
(declare-fun y$prop_10_op () Bool)
(declare-fun y$prop_11 () Bool)
(declare-fun y$prop_11$next () Bool)
(declare-fun y$prop_11$next_op () Bool)
(declare-fun y$prop_11_op () Bool)
(declare-fun y$prop_12 () Bool)
(declare-fun y$prop_12$next () Bool)
(declare-fun y$prop_12$next_op () Bool)
(declare-fun y$prop_12_op () Bool)
(declare-fun y$prop_13 () Bool)
(declare-fun y$prop_13$next () Bool)
(declare-fun y$prop_13$next_op () Bool)
(declare-fun y$prop_13_op () Bool)
(declare-fun y$prop_14 () Bool)
(declare-fun y$prop_14$next () Bool)
(declare-fun y$prop_14$next_op () Bool)
(declare-fun y$prop_14_op () Bool)
(declare-fun y$prop_15 () Bool)
(declare-fun y$prop_15$next () Bool)
(declare-fun y$prop_15$next_op () Bool)
(declare-fun y$prop_15_op () Bool)
(declare-fun y$prop_16 () Bool)
(declare-fun y$prop_16$next () Bool)
(declare-fun y$prop_16$next_op () Bool)
(declare-fun y$prop_16_op () Bool)
(declare-fun y$prop_17 () Bool)
(declare-fun y$prop_17$next () Bool)
(declare-fun y$prop_17$next_op () Bool)
(declare-fun y$prop_17_op () Bool)
(declare-fun y$prop_18 () Bool)
(declare-fun y$prop_18$next () Bool)
(declare-fun y$prop_18$next_op () Bool)
(declare-fun y$prop_18_op () Bool)
(declare-fun y$prop_19 () Bool)
(declare-fun y$prop_19$next () Bool)
(declare-fun y$prop_19$next_op () Bool)
(declare-fun y$prop_19_op () Bool)
(declare-fun y$prop_1_op () Bool)
(declare-fun y$prop_20 () Bool)
(declare-fun y$prop_20$next () Bool)
(declare-fun y$prop_20$next_op () Bool)
(declare-fun y$prop_20_op () Bool)
(declare-fun y$prop_21 () Bool)
(declare-fun y$prop_21$next () Bool)
(declare-fun y$prop_21$next_op () Bool)
(declare-fun y$prop_21_op () Bool)
(declare-fun y$prop_22 () Bool)
(declare-fun y$prop_22$next () Bool)
(declare-fun y$prop_22$next_op () Bool)
(declare-fun y$prop_22_op () Bool)
(declare-fun y$prop_4 () Bool)
(declare-fun y$prop_4$next () Bool)
(declare-fun y$prop_4$next_op () Bool)
(declare-fun y$prop_4_op () Bool)
(declare-fun y$prop_6 () Bool)
(declare-fun y$prop_6$next () Bool)
(declare-fun y$prop_6$next_op () Bool)
(declare-fun y$prop_6_op () Bool)
(declare-fun y$prop_7 () Bool)
(declare-fun y$prop_7$next () Bool)
(declare-fun y$prop_7$next_op () Bool)
(declare-fun y$prop_7_op () Bool)
(declare-fun y$prop_8 () Bool)
(declare-fun y$prop_8$next () Bool)
(declare-fun y$prop_8$next_op () Bool)
(declare-fun y$prop_8_op () Bool)
(declare-fun y$prop_9 () Bool)
(declare-fun y$prop_9$next () Bool)
(declare-fun y$prop_9$next_op () Bool)
(declare-fun y$prop_9_op () Bool)
(declare-fun y$rdy () Bool)
(declare-fun y$rdy$next () Bool)
(declare-fun y$rdy$next_rhs () Bool)
(declare-fun y$rdy$next_rhs_op () Bool)
(declare-fun y$s$100 () Bool)
(declare-fun y$s$100$next () Bool)
(declare-fun y$s$100$next_op () Bool)
(declare-fun y$s$100_op () Bool)
(declare-fun y$s$101 () Bool)
(declare-fun y$s$101$next () Bool)
(declare-fun y$s$101$next_op () Bool)
(declare-fun y$s$101_op () Bool)
(declare-fun y$s$102 () Bool)
(declare-fun y$s$102$next () Bool)
(declare-fun y$s$102$next_op () Bool)
(declare-fun y$s$102_op () Bool)
(declare-fun y$s$103 () Bool)
(declare-fun y$s$103$next () Bool)
(declare-fun y$s$103$next_op () Bool)
(declare-fun y$s$103_op () Bool)
(declare-fun y$s$104 () Bool)
(declare-fun y$s$104$next () Bool)
(declare-fun y$s$104$next_op () Bool)
(declare-fun y$s$104_op () Bool)
(declare-fun y$s$105 () Bool)
(declare-fun y$s$105$next () Bool)
(declare-fun y$s$105$next_op () Bool)
(declare-fun y$s$105_op () Bool)
(declare-fun y$s$106 () Bool)
(declare-fun y$s$106$next () Bool)
(declare-fun y$s$106$next_op () Bool)
(declare-fun y$s$106_op () Bool)
(declare-fun y$s$110 () Bool)
(declare-fun y$s$110_op () Bool)
(declare-fun y$s$122 () Bool)
(declare-fun y$s$122_op () Bool)
(declare-fun y$s$124 () Bool)
(declare-fun y$s$124_op () Bool)
(declare-fun y$s$127 () utt$10)
(declare-fun y$s$127_op () utt$10)
(declare-fun y$s$129 () Bool)
(declare-fun y$s$129_op () Bool)
(declare-fun y$s$130 () Bool)
(declare-fun y$s$130_op () Bool)
(declare-fun y$s$131 () Bool)
(declare-fun y$s$131_op () Bool)
(declare-fun y$s$132 () Bool)
(declare-fun y$s$132_op () Bool)
(declare-fun y$s$133 () Bool)
(declare-fun y$s$133_op () Bool)
(declare-fun y$s$134 () Bool)
(declare-fun y$s$134_op () Bool)
(declare-fun y$s$135 () utt$8)
(declare-fun y$s$135_op () utt$8)
(declare-fun y$s$136 () Bool)
(declare-fun y$s$136_op () Bool)
(declare-fun y$s$139 () Bool)
(declare-fun y$s$139_op () Bool)
(declare-fun y$s$141 () Bool)
(declare-fun y$s$141_op () Bool)
(declare-fun y$s$143 () Bool)
(declare-fun y$s$143_op () Bool)
(declare-fun y$s$24 () Bool)
(declare-fun y$s$24_op () Bool)
(declare-fun y$s$25 () Bool)
(declare-fun y$s$25_op () Bool)
(declare-fun y$s$26 () Bool)
(declare-fun y$s$26_op () Bool)
(declare-fun y$s$27 () Bool)
(declare-fun y$s$27_op () Bool)
(declare-fun y$s$29 () Bool)
(declare-fun y$s$29_op () Bool)
(declare-fun y$s$30 () Bool)
(declare-fun y$s$30_op () Bool)
(declare-fun y$s$31 () Bool)
(declare-fun y$s$31_op () Bool)
(declare-fun y$s$32 () Bool)
(declare-fun y$s$32_op () Bool)
(declare-fun y$s$33 () Bool)
(declare-fun y$s$33_op () Bool)
(declare-fun y$s$34 () utt$8)
(declare-fun y$s$34_op () utt$8)
(declare-fun y$s$35 () Bool)
(declare-fun y$s$35_op () Bool)
(declare-fun y$s$36 () utt$10)
(declare-fun y$s$36_op () utt$10)
(declare-fun y$s$38 () Bool)
(declare-fun y$s$38_op () Bool)
(declare-fun y$s$39 () Bool)
(declare-fun y$s$39_op () Bool)
(declare-fun y$s$40 () Bool)
(declare-fun y$s$40_op () Bool)
(declare-fun y$s$41 () Bool)
(declare-fun y$s$41_op () Bool)
(declare-fun y$s$43 () Bool)
(declare-fun y$s$43_op () Bool)
(declare-fun y$s$44 () utt$32)
(declare-fun y$s$44$next () utt$32)
(declare-fun y$s$44$next_op () utt$32)
(declare-fun y$s$44_op () utt$32)
(declare-fun y$s$46 () Bool)
(declare-fun y$s$46_op () Bool)
(declare-fun y$s$86 () Bool)
(declare-fun y$s$86$next () Bool)
(declare-fun y$s$86$next_op () Bool)
(declare-fun y$s$86_op () Bool)
(declare-fun y$s$87 () Bool)
(declare-fun y$s$87$next () Bool)
(declare-fun y$s$87$next_op () Bool)
(declare-fun y$s$87_op () Bool)
(declare-fun y$s$88 () Bool)
(declare-fun y$s$88$next () Bool)
(declare-fun y$s$88$next_op () Bool)
(declare-fun y$s$88_op () Bool)
(declare-fun y$s$89 () Bool)
(declare-fun y$s$89$next () Bool)
(declare-fun y$s$89$next_op () Bool)
(declare-fun y$s$89_op () Bool)
(declare-fun y$s$90 () Bool)
(declare-fun y$s$90$next () Bool)
(declare-fun y$s$90$next_op () Bool)
(declare-fun y$s$90_op () Bool)
(declare-fun y$s$91 () Bool)
(declare-fun y$s$91$next () Bool)
(declare-fun y$s$91$next_op () Bool)
(declare-fun y$s$91_op () Bool)
(declare-fun y$s$92 () Bool)
(declare-fun y$s$92$next () Bool)
(declare-fun y$s$92$next_op () Bool)
(declare-fun y$s$92_op () Bool)
(declare-fun y$s$93 () Bool)
(declare-fun y$s$93$next () Bool)
(declare-fun y$s$93$next_op () Bool)
(declare-fun y$s$93_op () Bool)
(declare-fun y$s$94 () Bool)
(declare-fun y$s$94$next () Bool)
(declare-fun y$s$94$next_op () Bool)
(declare-fun y$s$94_op () Bool)
(declare-fun y$s$95 () Bool)
(declare-fun y$s$95$next () Bool)
(declare-fun y$s$95$next_op () Bool)
(declare-fun y$s$95_op () Bool)
(declare-fun y$s$96 () Bool)
(declare-fun y$s$96$next () Bool)
(declare-fun y$s$96$next_op () Bool)
(declare-fun y$s$96_op () Bool)
(declare-fun y$s$97 () Bool)
(declare-fun y$s$97$next () Bool)
(declare-fun y$s$97$next_op () Bool)
(declare-fun y$s$97_op () Bool)
(declare-fun y$s$98 () Bool)
(declare-fun y$s$98$next () Bool)
(declare-fun y$s$98$next_op () Bool)
(declare-fun y$s$98_op () Bool)
(declare-fun y$s$99 () Bool)
(declare-fun y$s$99$next () Bool)
(declare-fun y$s$99$next_op () Bool)
(declare-fun y$s$99_op () Bool)
(declare-fun y$send () Bool)
(declare-fun y$send$next () Bool)
(declare-fun y$send$next_rhs () Bool)
(declare-fun y$send$next_rhs_op () Bool)
(declare-fun y$send_data () Bool)
(declare-fun y$send_data$next () Bool)
(declare-fun y$send_en () Bool)
(declare-fun y$send_en$next () Bool)
(declare-fun y$send_en$next_rhs () Bool)
(declare-fun y$send_en$next_rhs_op () Bool)
(declare-fun y$shot () Bool)
(declare-fun y$shot$next () Bool)
(declare-fun y$shot$next_rhs () Bool)
(declare-fun y$shot$next_rhs_op () Bool)
(declare-fun y$soc () Bool)
(declare-fun y$soc$next () Bool)
(declare-fun y$tre () Bool)
(declare-fun y$tre$next () Bool)
(declare-fun y$tre$next_rhs () Bool)
(declare-fun y$tre$next_rhs_op () Bool)
(declare-fun y$tx_conta () utt$10)
(declare-fun y$tx_conta$next () utt$10)
(declare-fun y$tx_conta$next_rhs () utt$10)
(declare-fun y$tx_conta$next_rhs_op () utt$10)
(declare-fun y$tx_end () Bool)
(declare-fun y$tx_end$next () Bool)
(declare-fun y$w$1 () utt$10)
(declare-fun y$w$10 () utt$32)
(declare-fun y$w$10$next () utt$32)
(declare-fun y$w$10$next_op () utt$32)
(declare-fun y$w$10_op () utt$32)
(declare-fun y$w$11 () utt$32)
(declare-fun y$w$11$next () utt$32)
(declare-fun y$w$11$next_op () utt$32)
(declare-fun y$w$11_op () utt$32)
(declare-fun y$w$12 () utt$32)
(declare-fun y$w$12$next () utt$32)
(declare-fun y$w$12$next_op () utt$32)
(declare-fun y$w$12_op () utt$32)
(declare-fun y$w$13 () utt$32)
(declare-fun y$w$13$next () utt$32)
(declare-fun y$w$13$next_op () utt$32)
(declare-fun y$w$13_op () utt$32)
(declare-fun y$w$14 () utt$32)
(declare-fun y$w$14$next () utt$32)
(declare-fun y$w$14$next_op () utt$32)
(declare-fun y$w$14_op () utt$32)
(declare-fun y$w$15 () utt$4)
(declare-fun y$w$15$next () utt$4)
(declare-fun y$w$15$next_op () utt$4)
(declare-fun y$w$15_op () utt$4)
(declare-fun y$w$16 () utt$32)
(declare-fun y$w$16$next () utt$32)
(declare-fun y$w$16$next_op () utt$32)
(declare-fun y$w$16_op () utt$32)
(declare-fun y$w$17 () utt$32)
(declare-fun y$w$17$next () utt$32)
(declare-fun y$w$17$next_op () utt$32)
(declare-fun y$w$17_op () utt$32)
(declare-fun y$w$18 () utt$32)
(declare-fun y$w$18$next () utt$32)
(declare-fun y$w$18$next_op () utt$32)
(declare-fun y$w$18_op () utt$32)
(declare-fun y$w$19 () utt$32)
(declare-fun y$w$19$next () utt$32)
(declare-fun y$w$19$next_op () utt$32)
(declare-fun y$w$19_op () utt$32)
(declare-fun y$w$2 () utt$32)
(declare-fun y$w$2$next () utt$32)
(declare-fun y$w$2$next_op () utt$32)
(declare-fun y$w$20 () utt$32)
(declare-fun y$w$20$next () utt$32)
(declare-fun y$w$20$next_op () utt$32)
(declare-fun y$w$20_op () utt$32)
(declare-fun y$w$21 () utt$32)
(declare-fun y$w$21$next () utt$32)
(declare-fun y$w$21$next_op () utt$32)
(declare-fun y$w$21_op () utt$32)
(declare-fun y$w$22 () utt$32)
(declare-fun y$w$22$next () utt$32)
(declare-fun y$w$22$next_op () utt$32)
(declare-fun y$w$22_op () utt$32)
(declare-fun y$w$23 () utt$32)
(declare-fun y$w$23$next () utt$32)
(declare-fun y$w$23$next_op () utt$32)
(declare-fun y$w$23_op () utt$32)
(declare-fun y$w$24 () Bool)
(declare-fun y$w$2_op () utt$32)
(declare-fun y$w$3 () utt$32)
(declare-fun y$w$3$next () utt$32)
(declare-fun y$w$3$next_op () utt$32)
(declare-fun y$w$3_op () utt$32)
(declare-fun y$w$4 () Bool)
(declare-fun y$w$4$next () Bool)
(declare-fun y$w$5 () utt$32)
(declare-fun y$w$5$next () utt$32)
(declare-fun y$w$5$next_op () utt$32)
(declare-fun y$w$5_op () utt$32)
(declare-fun y$w$6 () utt$2)
(declare-fun y$w$6$next () utt$2)
(declare-fun y$w$7 () utt$32)
(declare-fun y$w$7$next () utt$32)
(declare-fun y$w$7$next_op () utt$32)
(declare-fun y$w$7_op () utt$32)
(declare-fun y$w$8 () utt$32)
(declare-fun y$w$8$next () utt$32)
(declare-fun y$w$8$next_op () utt$32)
(declare-fun y$w$8_op () utt$32)
(declare-fun y$w$9 () utt$32)
(declare-fun y$w$9$next () utt$32)
(declare-fun y$w$9$next_op () utt$32)
(declare-fun y$w$9_op () utt$32)
(assert (not (= y$n0s4 y$n1s4)))
(assert (distinct y$n104s32 y$n1s32 y$n0s32))
(assert (= y$w$2_op (Concat_32_1_31 y$error y$n0s31)))
(assert (= y$225 (not (= y$n1s32 y$w$2_op))))
(assert (= y$w$3_op (Concat_32_1_31 y$tre y$n0s31)))
(assert (= y$228 (= y$n1s32 y$w$3_op)))
(assert (= y$prop_1_op (or y$225 y$228)))
(assert (= y$231 (Extract_1_3_3_4 y$canale)))
(assert (= y$w$5_op (Concat_32_1_31 y$231 y$n0s31)))
(assert (= y$236 (= y$n0s32 y$w$5_op)))
(assert (= y$s$87_op (and y$prop_1_op y$236)))
(assert (= y$239 (Extract_2_9_8_10 y$tx_conta)))
(assert (= y$w$7_op (Concat_32_2_30 y$239 y$n0s30)))
(assert (= y$244 (= y$n0s32 y$w$7_op)))
(assert (= y$s$88_op (and y$s$87_op y$244)))
(assert (= y$w$8_op (Concat_32_1_31 y$mpx y$n0s31)))
(assert (= y$251 (not (= y$n1s32 y$w$8_op))))
(assert (= y$w$9_op (Concat_32_1_31 y$rdy y$n0s31)))
(assert (= y$254 (= y$n1s32 y$w$9_op)))
(assert (= y$prop_4_op (or y$251 y$254)))
(assert (= y$s$89_op (and y$s$88_op y$prop_4_op)))
(assert (= y$259 (= y$canale y$conta_tmp)))
(assert (= y$s$90_op (and y$s$89_op y$259)))
(assert (= (not (= y$n1s32 y$w$3_op)) y$263))
(assert (= (= y$n1s32 y$w$2_op) y$223))
(assert (= y$prop_6_op (or y$263 y$223)))
(assert (= y$s$91_op (and y$s$90_op y$prop_6_op)))
(assert (= y$w$10_op (Concat_32_1_31 y$load y$n0s31)))
(assert (= y$270 (= y$n0s32 y$w$10_op)))
(assert (= y$w$11_op (Concat_32_1_31 y$send y$n0s31)))
(assert (= y$273 (= y$n0s32 y$w$11_op)))
(assert (= y$prop_7_op (or y$270 y$273)))
(assert (= y$s$92_op (and y$s$91_op y$prop_7_op)))
(assert (= y$w$12_op (Concat_32_1_31 y$confirm y$n0s31)))
(assert (= y$280 (= y$n0s32 y$w$12_op)))
(assert (= y$prop_8_op (or y$270 y$280)))
(assert (= y$s$93_op (and y$s$92_op y$prop_8_op)))
(assert (= y$prop_9_op (or y$273 y$280)))
(assert (= y$s$94_op (and y$s$93_op y$prop_9_op)))
(assert (= y$289 (= y$n0s32 y$w$2_op)))
(assert (= y$w$13_op (Concat_32_1_31 y$send_en y$n0s31)))
(assert (= y$292 (= y$n0s32 y$w$13_op)))
(assert (= y$prop_10_op (or y$289 y$292)))
(assert (= y$s$95_op (and y$s$94_op y$prop_10_op)))
(assert (= y$prop_11_op (or y$280 y$289)))
(assert (= y$s$96_op (and y$s$95_op y$prop_11_op)))
(assert (= y$w$14_op (Concat_32_1_31 y$tx_end y$n0s31)))
(assert (= y$303 (= y$n0s32 y$w$14_op)))
(assert (= y$prop_12_op (or y$289 y$303)))
(assert (= y$s$97_op (and y$s$96_op y$prop_12_op)))
(assert (= y$prop_13_op (or y$280 y$292)))
(assert (= y$s$98_op (and y$s$97_op y$prop_13_op)))
(assert (= (not (= y$n0s32 y$w$13_op)) y$313))
(assert (= y$prop_14_op (or y$303 y$313)))
(assert (= y$s$99_op (and y$s$98_op y$prop_14_op)))
(assert (= y$320 (not (= y$n1s32 y$w$14_op))))
(assert (= y$w$15_op (Concat_4_1_3 y$next_bit y$n0s3)))
(assert (= y$325 (= y$n1s4 y$w$15_op)))
(assert (= y$prop_15_op (or y$320 y$325)))
(assert (= y$s$100_op (and y$s$99_op y$prop_15_op)))
(assert (= y$w$16_op (Concat_32_1_31 y$load_dato y$n0s31)))
(assert (= y$334 (not (= y$n1s32 y$w$16_op))))
(assert (= y$w$17_op (Concat_32_1_31 y$soc y$n0s31)))
(assert (= y$337 (= y$n1s32 y$w$17_op)))
(assert (= y$prop_16_op (or y$334 y$337)))
(assert (= y$s$101_op (and y$s$100_op y$prop_16_op)))
(assert (= y$w$18_op (Concat_32_1_31 y$send_data y$n0s31)))
(assert (= y$346 (not (= y$n0s32 y$w$18_op))))
(assert (= y$347 (= y$n0s32 y$w$17_op)))
(assert (= y$prop_17_op (or y$346 y$347)))
(assert (= y$s$102_op (and y$s$101_op y$prop_17_op)))
(assert (= y$w$19_op (Concat_32_1_31 y$add_mpx2 y$n0s31)))
(assert (= y$354 (= y$n1s32 y$w$19_op)))
(assert (= y$prop_18_op (or y$251 y$354)))
(assert (= y$s$103_op (and y$s$102_op y$prop_18_op)))
(assert (= (not (= y$n1s32 y$w$19_op)) y$360))
(assert (= y$prop_19_op (or y$228 y$360)))
(assert (= y$s$104_op (and y$s$103_op y$prop_19_op)))
(assert (= y$w$20_op (Concat_32_1_31 y$shot y$n0s31)))
(assert (= y$369 (not (= y$n1s32 y$w$20_op))))
(assert (= y$prop_20_op (or y$254 y$369)))
(assert (= y$s$105_op (and y$s$104_op y$prop_20_op)))
(assert (= y$374 (= y$n0s32 y$w$16_op)))
(assert (= y$w$21_op (Concat_32_1_31 y$mux_en y$n0s31)))
(assert (= y$377 (= y$n0s32 y$w$21_op)))
(assert (= y$prop_21_op (or y$374 y$377)))
(assert (= y$s$106_op (and y$s$105_op y$prop_21_op)))
(assert (= y$w$22_op (Concat_32_8_24 y$out_reg y$n0s24)))
(assert (= y$385 (= y$n0s32 y$w$22_op)))
(assert (= y$prop_22_op (or y$228 y$385)))
(assert (= y$prop0_op (and y$s$106_op y$prop_22_op)))
(assert (= y$390 (= y$prop y$prop0_op)))
(assert (= y$w$23_op (Concat_32_10_22 y$tx_conta y$n0s22)))
(assert (= y$s$86_op (Gr_1_32_32 y$w$23_op y$n104s32)))
(assert (= y$next_bit (not y$58)))
(assert (= y$59 (Extract_1_6_6_8 y$out_reg)))
(assert (= y$s$46_op (and y$58 y$59)))
(assert (= y$s$124_op (and y$s$86_op y$s$46_op)))
(assert (= y$s$38_op (and y$send_en y$s$124_op)))
(assert (= y$s$130_op (=> y$s$86_op y$s$38_op)))
(assert (= y$s$29_op (and y$send_en y$s$130_op)))
(assert (= y$data_out$next_rhs_op (=> y$send_en y$s$29_op)))
(assert (= y$75 (= y$data_out$next y$data_out$next_rhs_op)))
(assert (= y$s$86_op y$s$122_op))
(assert (= y$s$39_op (and y$send_en y$s$122_op)))
(assert (= y$s$129_op (ite y$s$86_op y$s$39_op y$next_bit)))
(assert (= y$s$33_op (and y$send_en y$s$129_op)))
(assert (= y$next_bit$next_rhs_op (ite y$send_en y$s$33_op y$next_bit)))
(assert (= y$87 (= y$next_bit$next y$next_bit$next_rhs_op)))
(assert (= y$tx_end$next (not y$89)))
(assert (= y$s$44_op (Add_32_32_32 y$w$23_op y$n1s32)))
(assert (= y$94 (Extract_10_9_0_32 y$s$44_op)))
(assert (= y$s$127_op (ite y$s$86_op y$n0s10 y$94)))
(assert (= y$s$36_op (ite y$send_en y$s$127_op y$n0s10)))
(assert (= y$tx_conta$next_rhs_op (ite y$send_en y$s$36_op y$tx_conta)))
(assert (= y$102 (= y$tx_conta$next y$tx_conta$next_rhs_op)))
(assert (= y$s$26_op (or y$tre y$tx_end)))
(assert (= y$s$26_op (not y$106)))
(assert (= y$s$134_op (or y$s$26_op y$106)))
(assert (= y$s$41_op (and y$load y$s$134_op)))
(assert (= y$tre$next_rhs_op (ite y$load y$s$41_op y$s$26_op)))
(assert (= y$tre$next_rhs_op (not y$113)))
(assert (= y$dsr (not y$115)))
(assert (= y$s$110_op (or y$113 y$115)))
(assert (= y$s$110_op y$s$131_op))
(assert (= y$s$43_op (and y$send y$s$131_op)))
(assert (= y$106 (not y$s$133_op)))
(assert (= y$s$30_op (and y$load y$s$133_op)))
(assert (= y$s$24_op (ite y$load y$s$30_op y$error)))
(assert (= y$error$next_rhs_op (ite y$send y$s$43_op y$s$24_op)))
(assert (= y$130 (= y$error$next y$error$next_rhs_op)))
(assert (= y$s$25_op (and y$send_en (not y$tx_end))))
(assert (= y$s$132_op (=> y$s$110_op y$s$25_op)))
(assert (= y$s$40_op (and y$send y$s$132_op)))
(assert (= y$send_en$next_rhs_op (ite y$send y$s$40_op y$s$25_op)))
(assert (= y$140 (= y$send_en$next y$send_en$next_rhs_op)))
(assert (= y$142 (= y$tre$next_rhs_op y$tre$next)))
(assert (= y$s$135_op (ite y$106 y$data_in y$out_reg)))
(assert (= y$s$34_op (ite y$load y$s$135_op y$n0s8)))
(assert (= y$out_reg$next_rhs_op (ite y$load y$s$34_op y$out_reg)))
(assert (= y$151 (= y$out_reg$next y$out_reg$next_rhs_op)))
(assert (= y$itfc_state (not y$18)))
(assert (= y$shot y$s$136_op))
(assert (= y$s$31_op (and y$18 y$s$136_op)))
(assert (= y$itfc_state$next_rhs_op (and (not y$itfc_state) y$s$31_op)))
(assert (= y$159 (= y$itfc_state$next y$itfc_state$next_rhs_op)))
(assert (= y$confirm$next_rhs_op (and y$confirm y$itfc_state)))
(assert (= y$163 (= y$confirm$next y$confirm$next_rhs_op)))
(assert (= y$send$next_rhs_op (or y$itfc_state y$send)))
(assert (= y$167 (= y$send$next y$send$next_rhs_op)))
(assert (= y$s$139_op (or y$load y$shot)))
(assert (= y$s$32_op (and y$18 y$s$139_op)))
(assert (= y$load$next_rhs_op (and (not y$itfc_state) y$s$32_op)))
(assert (= y$175 (= y$load$next y$load$next_rhs_op)))
(assert (= y$177 (= y$add_mpx2 y$add_mpx2$next)))
(assert (= y$S2 (not y$3)))
(assert (= y$send_data y$s$141_op))
(assert (= y$s$27_op (and y$3 y$s$141_op)))
(assert (= y$S2$next_rhs_op (and (not y$S2) y$s$27_op)))
(assert (= y$185 (= y$S2$next y$S2$next_rhs_op)))
(assert (= y$187 (= y$mpx y$mpx$next)))
(assert (= y$s$143_op (or y$rdy y$send_data)))
(assert (= y$s$35_op (and y$3 y$s$143_op)))
(assert (= y$rdy$next_rhs_op (ite y$S2 y$rdy y$s$35_op)))
(assert (= y$195 (= y$rdy$next y$rdy$next_rhs_op)))
(assert (= y$shot$next_rhs_op (or y$S2 y$shot)))
(assert (= y$199 (= y$shot$next y$shot$next_rhs_op)))
(assert (= y$201 (= y$soc y$soc$next)))
(assert (= y$203 (= y$load_dato y$load_dato$next)))
(assert (= y$205 (= y$canale y$canale$next)))
(assert (= y$mux_en$next_rhs_op (=> y$S1 y$mux_en)))
(assert (= y$209 (= y$mux_en$next y$mux_en$next_rhs_op)))
(assert (= y$S1 (not y$S1$next_rhs_op)))
(assert (= y$213 (= y$S1$next y$S1$next_rhs_op)))
(assert (= y$215 (= y$send_data y$send_data$next)))
(assert (= y$217 (= y$conta_tmp y$conta_tmp$next)))
(assert (= y$218 (and y$75 y$87 y$89 y$102 y$130 y$140 y$142 y$151 y$159 y$163 y$167 y$175 y$177 y$185 y$187 y$195 y$199 y$201 y$203 y$205 y$209 y$213 y$215 y$217)))
(assert (= y$w$2$next_op (Concat_32_1_31 y$error$next y$n0s31)))
(assert (= y$401 (not (= y$n1s32 y$w$2$next_op))))
(assert (= y$w$3$next_op (Concat_32_1_31 y$tre$next y$n0s31)))
(assert (= y$404 (= y$n1s32 y$w$3$next_op)))
(assert (= y$prop_1$next_op (or y$401 y$404)))
(assert (= y$407 (Extract_1_3_3_4 y$canale$next)))
(assert (= y$w$5$next_op (Concat_32_1_31 y$407 y$n0s31)))
(assert (= (= y$n0s32 y$w$5$next_op) y$411))
(assert (= y$s$87$next_op (and y$prop_1$next_op y$411)))
(assert (= y$414 (Extract_2_9_8_10 y$tx_conta$next)))
(assert (= y$w$7$next_op (Concat_32_2_30 y$414 y$n0s30)))
(assert (= (= y$n0s32 y$w$7$next_op) y$418))
(assert (= y$s$88$next_op (and y$s$87$next_op y$418)))
(assert (= y$w$8$next_op (Concat_32_1_31 y$mpx$next y$n0s31)))
(assert (= y$423 (not (= y$n1s32 y$w$8$next_op))))
(assert (= y$w$9$next_op (Concat_32_1_31 y$rdy$next y$n0s31)))
(assert (= y$426 (= y$n1s32 y$w$9$next_op)))
(assert (= y$prop_4$next_op (or y$423 y$426)))
(assert (= y$s$89$next_op (and y$s$88$next_op y$prop_4$next_op)))
(assert (= y$431 (= y$canale$next y$conta_tmp$next)))
(assert (= y$s$90$next_op (and y$s$89$next_op y$431)))
(assert (= (not (= y$n1s32 y$w$3$next_op)) y$434))
(assert (= (= y$n1s32 y$w$2$next_op) y$435))
(assert (= y$prop_6$next_op (or y$434 y$435)))
(assert (= y$s$91$next_op (and y$s$90$next_op y$prop_6$next_op)))
(assert (= y$w$10$next_op (Concat_32_1_31 y$load$next y$n0s31)))
(assert (= (= y$n0s32 y$w$10$next_op) y$442))
(assert (= y$w$11$next_op (Concat_32_1_31 y$send$next y$n0s31)))
(assert (= y$445 (= y$n0s32 y$w$11$next_op)))
(assert (= y$prop_7$next_op (or y$442 y$445)))
(assert (= y$s$92$next_op (and y$s$91$next_op y$prop_7$next_op)))
(assert (= y$w$12$next_op (Concat_32_1_31 y$confirm$next y$n0s31)))
(assert (= y$452 (= y$n0s32 y$w$12$next_op)))
(assert (= y$prop_8$next_op (or y$442 y$452)))
(assert (= y$s$93$next_op (and y$s$92$next_op y$prop_8$next_op)))
(assert (= y$prop_9$next_op (or y$445 y$452)))
(assert (= y$s$94$next_op (and y$s$93$next_op y$prop_9$next_op)))
(assert (= y$461 (= y$n0s32 y$w$2$next_op)))
(assert (= y$w$13$next_op (Concat_32_1_31 y$send_en$next y$n0s31)))
(assert (= y$464 (= y$n0s32 y$w$13$next_op)))
(assert (= y$prop_10$next_op (or y$461 y$464)))
(assert (= y$s$95$next_op (and y$s$94$next_op y$prop_10$next_op)))
(assert (= y$prop_11$next_op (or y$452 y$461)))
(assert (= y$s$96$next_op (and y$s$95$next_op y$prop_11$next_op)))
(assert (= y$w$14$next_op (Concat_32_1_31 y$tx_end$next y$n0s31)))
(assert (= y$475 (= y$n0s32 y$w$14$next_op)))
(assert (= y$prop_12$next_op (or y$461 y$475)))
(assert (= y$s$97$next_op (and y$s$96$next_op y$prop_12$next_op)))
(assert (= y$prop_13$next_op (or y$452 y$464)))
(assert (= y$s$98$next_op (and y$s$97$next_op y$prop_13$next_op)))
(assert (= (not (= y$n0s32 y$w$13$next_op)) y$484))
(assert (= y$prop_14$next_op (or y$475 y$484)))
(assert (= y$s$99$next_op (and y$s$98$next_op y$prop_14$next_op)))
(assert (= y$489 (not (= y$n1s32 y$w$14$next_op))))
(assert (= y$w$15$next_op (Concat_4_1_3 y$next_bit$next y$n0s3)))
(assert (= y$492 (= y$n1s4 y$w$15$next_op)))
(assert (= y$prop_15$next_op (or y$489 y$492)))
(assert (= y$s$100$next_op (and y$s$99$next_op y$prop_15$next_op)))
(assert (= y$w$16$next_op (Concat_32_1_31 y$load_dato$next y$n0s31)))
(assert (= y$499 (not (= y$n1s32 y$w$16$next_op))))
(assert (= y$w$17$next_op (Concat_32_1_31 y$soc$next y$n0s31)))
(assert (= y$502 (= y$n1s32 y$w$17$next_op)))
(assert (= y$prop_16$next_op (or y$499 y$502)))
(assert (= y$s$101$next_op (and y$s$100$next_op y$prop_16$next_op)))
(assert (= y$w$18$next_op (Concat_32_1_31 y$send_data$next y$n0s31)))
(assert (= y$509 (not (= y$n0s32 y$w$18$next_op))))
(assert (= y$510 (= y$n0s32 y$w$17$next_op)))
(assert (= y$prop_17$next_op (or y$509 y$510)))
(assert (= y$s$102$next_op (and y$s$101$next_op y$prop_17$next_op)))
(assert (= y$w$19$next_op (Concat_32_1_31 y$add_mpx2$next y$n0s31)))
(assert (= y$517 (= y$n1s32 y$w$19$next_op)))
(assert (= y$prop_18$next_op (or y$423 y$517)))
(assert (= y$s$103$next_op (and y$s$102$next_op y$prop_18$next_op)))
(assert (= (not (= y$n1s32 y$w$19$next_op)) y$522))
(assert (= y$prop_19$next_op (or y$404 y$522)))
(assert (= y$s$104$next_op (and y$s$103$next_op y$prop_19$next_op)))
(assert (= y$w$20$next_op (Concat_32_1_31 y$shot$next y$n0s31)))
(assert (= y$529 (not (= y$n1s32 y$w$20$next_op))))
(assert (= y$prop_20$next_op (or y$426 y$529)))
(assert (= y$s$105$next_op (and y$s$104$next_op y$prop_20$next_op)))
(assert (= y$534 (= y$n0s32 y$w$16$next_op)))
(assert (= y$w$21$next_op (Concat_32_1_31 y$mux_en$next y$n0s31)))
(assert (= y$537 (= y$n0s32 y$w$21$next_op)))
(assert (= y$prop_21$next_op (or y$534 y$537)))
(assert (= y$s$106$next_op (and y$s$105$next_op y$prop_21$next_op)))
(assert (= y$w$22$next_op (Concat_32_8_24 y$out_reg$next y$n0s24)))
(assert (= (= y$n0s32 y$w$22$next_op) y$544))
(assert (= y$prop_22$next_op (or y$404 y$544)))
(assert (= y$prop0$next_op (and y$s$106$next_op y$prop_22$next_op)))
(assert (= y$549 (= y$prop$next y$prop0$next_op)))
(assert (= y$prop$next (not y$398)))
(assert (= y$407 (not y$606)))
(assert (= y$607 (not (= y$n0s32 y$w$5$next_op))))
(assert (= y$608 (and y$606 y$607)))
(assert (= y$608 (not y$610)))
(assert (= y$231 (not y$552)))
(assert (= (not (= y$n0s32 y$w$5_op)) y$554))
(assert (= y$605 (and y$552 y$554)))
(assert (= y$605 (not y$609)))
(assert (= y$628 (= y$n0s10 y$tx_conta$next)))
(assert (= y$629 (not (= y$n0s32 y$w$7$next_op))))
(assert (= y$630 (and y$628 y$629)))
(assert (= y$630 (not y$632)))
(assert (= y$47 (= y$tx_conta y$n0s10)))
(assert (= (not (= y$n0s32 y$w$7_op)) y$556))
(assert (= y$627 (and y$47 y$556)))
(assert (= y$627 (not y$631)))
(assert (= y$663 (= y$n0s8 y$out_reg$next)))
(assert (= y$664 (not (= y$n0s32 y$w$22$next_op))))
(assert (= y$665 (and y$663 y$664)))
(assert (= y$665 (not y$667)))
(assert (= y$30 (= y$out_reg y$n0s8)))
(assert (= (not (= y$n0s32 y$w$22_op)) y$582))
(assert (= y$662 (and y$30 y$582)))
(assert (= y$662 (not y$666)))
(assert (= y$load$next (not y$689)))
(assert (= y$690 (not (= y$n0s32 y$w$10$next_op))))
(assert (= y$691 (and y$689 y$690)))
(assert (= y$691 (not y$693)))
(assert (= y$load (not y$20)))
(assert (= (not (= y$n0s32 y$w$10_op)) y$560))
(assert (= y$688 (and y$20 y$560)))
(assert (= y$688 (not y$692)))
(assert (= y$706 (= y$n0s4 y$canale$next)))
(assert (= y$707 (and y$407 y$706)))
(assert (= y$707 (not y$709)))
(assert (= y$8 (= y$n0s4 y$canale)))
(assert (= y$705 (and y$8 y$231)))
(assert (= y$705 (not y$708)))
(assert (= y$load_dato (not y$22)))
(assert (= y$tx_end (not y$49)))
(assert (= y$tre (not y$44)))
(assert (= y$send_en (not y$38)))
(assert (= y$send (not y$34)))
(assert (= y$rdy (not y$32)))
(assert (= y$890 (and y$S2 y$32)))
(assert (= y$890 (not y$892)))
(assert (= y$909 (and y$18 y$20 y$22 y$34 y$38 y$44 y$49 y$prop y$390 y$610 y$609 y$632 y$631 y$667 y$666 y$693 y$692 y$709 y$708 y$218 y$549 y$398 y$892)))
(assert y$909)
(assert (not (= y$n0s4 y$n1s4)))
(assert (distinct y$n104s32 y$n1s32 y$n0s32))
(check-sat)
(exit)
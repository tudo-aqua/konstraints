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

id: driving_phils.3.prop1
query-maker: "Yices 2"
query-time: 0.198000 ms
query-class: abstract
query-category: oneshot
query-type: regular
status: sat
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")

;
(set-info :status sat)
(declare-sort utt$8 0)
(declare-sort utt$16 0)
(declare-sort utt$32 0)
(declare-fun BitWiseNot_32_32 (utt$32 ) utt$32)
(declare-fun Concat_32_16_16 (utt$16 utt$16 ) utt$32)
(declare-fun Extract_1_15_15_16 (utt$16 ) Bool)
(declare-fun ShiftR_32_32_32 (utt$32 utt$32 ) utt$32)
(declare-fun y$1 () Bool)
(declare-fun y$11 () Bool)
(declare-fun y$13 () Bool)
(declare-fun y$15 () Bool)
(declare-fun y$17 () Bool)
(declare-fun y$179 () Bool)
(declare-fun y$19 () Bool)
(declare-fun y$207 () Bool)
(declare-fun y$21 () Bool)
(declare-fun y$23 () Bool)
(declare-fun y$244 () Bool)
(declare-fun y$25 () Bool)
(declare-fun y$2660 () Bool)
(declare-fun y$2663 () Bool)
(declare-fun y$2666 () Bool)
(declare-fun y$2669 () Bool)
(declare-fun y$2670 () Bool)
(declare-fun y$27 () Bool)
(declare-fun y$2725 () Bool)
(declare-fun y$2779 () Bool)
(declare-fun y$2805 () Bool)
(declare-fun y$2809 () Bool)
(declare-fun y$2810 () Bool)
(declare-fun y$2811 () Bool)
(declare-fun y$2812 () Bool)
(declare-fun y$2813 () Bool)
(declare-fun y$2814 () Bool)
(declare-fun y$2828 () Bool)
(declare-fun y$29 () Bool)
(declare-fun y$3 () Bool)
(declare-fun y$31 () Bool)
(declare-fun y$33 () Bool)
(declare-fun y$35 () Bool)
(declare-fun y$37 () Bool)
(declare-fun y$40 () Bool)
(declare-fun y$42 () Bool)
(declare-fun y$44 () Bool)
(declare-fun y$46 () Bool)
(declare-fun y$49 () Bool)
(declare-fun y$5 () Bool)
(declare-fun y$51 () Bool)
(declare-fun y$53 () Bool)
(declare-fun y$55 () Bool)
(declare-fun y$57 () Bool)
(declare-fun y$59 () Bool)
(declare-fun y$61 () Bool)
(declare-fun y$63 () Bool)
(declare-fun y$65 () Bool)
(declare-fun y$67 () Bool)
(declare-fun y$69 () Bool)
(declare-fun y$7 () Bool)
(declare-fun y$71 () Bool)
(declare-fun y$73 () Bool)
(declare-fun y$75 () Bool)
(declare-fun y$77 () Bool)
(declare-fun y$79 () Bool)
(declare-fun y$81 () Bool)
(declare-fun y$9 () Bool)
(declare-fun y$a_action_phil_0 () Bool)
(declare-fun y$a_action_phil_1 () Bool)
(declare-fun y$a_action_phil_2 () Bool)
(declare-fun y$a_action_round_about () Bool)
(declare-fun y$a_begin0 () Bool)
(declare-fun y$a_begin1 () Bool)
(declare-fun y$a_begin2 () Bool)
(declare-fun y$a_begin3 () Bool)
(declare-fun y$a_end0 () Bool)
(declare-fun y$a_end1 () Bool)
(declare-fun y$a_end2 () Bool)
(declare-fun y$a_end_phil_0 () Bool)
(declare-fun y$a_end_phil_1 () Bool)
(declare-fun y$a_end_phil_2 () Bool)
(declare-fun y$a_mutex_phil_0 () Bool)
(declare-fun y$a_mutex_phil_1 () Bool)
(declare-fun y$a_mutex_phil_2 () Bool)
(declare-fun y$a_reset () Bool)
(declare-fun y$dve_invalid () Bool)
(declare-fun y$id56 () Bool)
(declare-fun y$id56_op () Bool)
(declare-fun y$n0s16 () utt$16)
(declare-fun y$n0s32 () utt$32)
(declare-fun y$n0s8 () utt$8)
(declare-fun y$n15s32 () utt$32)
(declare-fun y$n16s32 () utt$32)
(declare-fun y$n1s16 () utt$16)
(declare-fun y$n1s32 () utt$32)
(declare-fun y$n1s8 () utt$8)
(declare-fun y$n2s32 () utt$32)
(declare-fun y$n2s8 () utt$8)
(declare-fun y$n3s32 () utt$32)
(declare-fun y$n3s8 () utt$8)
(declare-fun y$n4294967295s32 () utt$32)
(declare-fun y$n5s32 () utt$32)
(declare-fun y$n65535s16 () utt$16)
(declare-fun y$prop () Bool)
(declare-fun y$s$10 () utt$32)
(declare-fun y$s$10_op () utt$32)
(declare-fun y$s$5 () utt$32)
(declare-fun y$s$5_op () utt$32)
(declare-fun y$s$6 () utt$32)
(declare-fun y$s$6_op () utt$32)
(declare-fun y$s$7 () utt$32)
(declare-fun y$s$7_op () utt$32)
(declare-fun y$s$8 () utt$32)
(declare-fun y$s$8_op () utt$32)
(declare-fun y$s$9 () utt$32)
(declare-fun y$s$9_op () utt$32)
(declare-fun y$v3_1517448494_47 () utt$32)
(declare-fun y$v3_1517448494_47_op () utt$32)
(declare-fun y$v3_1517448494_48 () utt$32)
(declare-fun y$v3_1517448494_48_op () utt$32)
(declare-fun y$v3_1517448494_49 () utt$32)
(declare-fun y$v3_1517448494_49_op () utt$32)
(declare-fun y$v3_1517448494_52 () utt$32)
(declare-fun y$v3_1517448494_52_op () utt$32)
(declare-fun y$v3_1517448494_53 () utt$32)
(declare-fun y$v3_1517448494_53$next () utt$32)
(declare-fun y$v3_1517448494_53$next_op () utt$32)
(declare-fun y$v3_1517448494_53_op () utt$32)
(declare-fun y$v3_1517448494_54 () utt$32)
(declare-fun y$v3_1517448494_54_op () utt$32)
(declare-fun y$v3_1517448494_58 () utt$32)
(declare-fun y$v3_1517448494_58_op () utt$32)
(declare-fun y$v3_1517448494_59 () utt$32)
(declare-fun y$v3_1517448494_59_op () utt$32)
(declare-fun y$v3_1517448494_60 () utt$32)
(declare-fun y$v3_1517448494_60_op () utt$32)
(declare-fun y$v3_1517448494_64 () Bool)
(declare-fun y$v3_1517448494_64_op () Bool)
(declare-fun y$v_acquiring_0 () utt$16)
(declare-fun y$v_acquiring_1 () utt$16)
(declare-fun y$v_acquiring_2 () utt$16)
(declare-fun y$v_entryRound () utt$16)
(declare-fun y$v_fire () utt$8)
(declare-fun y$v_i_phil_0 () utt$16)
(declare-fun y$v_i_phil_1 () utt$16)
(declare-fun y$v_i_phil_2 () utt$16)
(declare-fun y$v_i_round_about () utt$16)
(declare-fun y$v_phase () utt$8)
(declare-fun y$v_request_0 () utt$8)
(declare-fun y$v_request_1 () utt$8)
(declare-fun y$v_request_2 () utt$8)
(declare-fun y$v_res0_0 () utt$16)
(declare-fun y$v_res0_1 () utt$16)
(declare-fun y$v_res0_1$next () utt$16)
(declare-fun y$v_res0_2 () utt$16)
(declare-fun y$v_res1_0 () utt$16)
(declare-fun y$v_res1_1 () utt$16)
(declare-fun y$v_res1_2 () utt$16)
(declare-fun y$v_resources_0 () utt$8)
(declare-fun y$v_resources_1 () utt$8)
(declare-fun y$w$28 () Bool)
(declare-fun y$w$29 () utt$32)
(declare-fun y$w$29_op () utt$32)
(declare-fun y$w$30 () Bool)
(declare-fun y$w$31 () utt$32)
(declare-fun y$w$31$next () utt$32)
(declare-fun y$w$31$next_op () utt$32)
(declare-fun y$w$31_op () utt$32)
(declare-fun y$w$32 () Bool)
(declare-fun y$w$33 () utt$32)
(declare-fun y$w$33_op () utt$32)
(assert (distinct y$n0s8 y$n2s8 y$n1s8 y$n3s8))
(assert (distinct y$n0s16 y$n1s16 y$n65535s16))
(assert (distinct y$n0s32 y$n16s32 y$n1s32 y$n2s32 y$n4294967295s32 y$n3s32 y$n5s32 y$n15s32))
(assert (= y$a_action_phil_0 (not y$1)))
(assert (= y$a_action_phil_1 (not y$3)))
(assert (= y$a_action_phil_2 (not y$5)))
(assert (= y$a_action_round_about (not y$7)))
(assert (= y$a_begin0 (not y$9)))
(assert (= y$a_begin1 (not y$11)))
(assert (= y$a_begin2 (not y$13)))
(assert (= y$a_begin3 (not y$15)))
(assert (= y$a_end0 (not y$17)))
(assert (= y$a_end1 (not y$19)))
(assert (= y$a_end2 (not y$21)))
(assert (= y$a_end_phil_0 (not y$23)))
(assert (= y$a_end_phil_1 (not y$25)))
(assert (= y$a_end_phil_2 (not y$27)))
(assert (= y$a_mutex_phil_0 (not y$29)))
(assert (= y$a_mutex_phil_1 (not y$31)))
(assert (= y$a_mutex_phil_2 (not y$33)))
(assert (= y$a_reset (not y$35)))
(assert (= y$dve_invalid (not y$37)))
(assert (= y$40 (= y$n0s16 y$v_acquiring_0)))
(assert (= y$42 (= y$n0s16 y$v_acquiring_1)))
(assert (= y$44 (= y$n0s16 y$v_acquiring_2)))
(assert (= y$46 (= y$n0s16 y$v_entryRound)))
(assert (= y$49 (= y$n0s8 y$v_fire)))
(assert (= y$51 (= y$n0s16 y$v_i_phil_0)))
(assert (= y$53 (= y$n0s16 y$v_i_phil_1)))
(assert (= y$55 (= y$n0s16 y$v_i_phil_2)))
(assert (= y$57 (= y$n0s16 y$v_i_round_about)))
(assert (= y$59 (= y$n0s8 y$v_phase)))
(assert (= y$61 (= y$n0s8 y$v_request_0)))
(assert (= y$63 (= y$n0s8 y$v_request_1)))
(assert (= y$65 (= y$n0s8 y$v_request_2)))
(assert (= y$67 (= y$n0s16 y$v_res0_0)))
(assert (= y$69 (= y$n0s16 y$v_res0_1)))
(assert (= y$71 (= y$n0s16 y$v_res0_2)))
(assert (= y$73 (= y$n0s16 y$v_res1_0)))
(assert (= y$75 (= y$n0s16 y$v_res1_1)))
(assert (= y$77 (= y$n0s16 y$v_res1_2)))
(assert (= y$79 (= y$n0s8 y$v_resources_0)))
(assert (= y$81 (= y$n0s8 y$v_resources_1)))
(assert (= y$prop (not y$2725)))
(assert (= y$179 (Extract_1_15_15_16 y$v_res0_1)))
(assert (= y$w$31_op (Concat_32_16_16 y$n0s16 y$v_res0_1)))
(assert (= y$s$8_op (BitWiseNot_32_32 y$w$31_op)))
(assert (= y$v3_1517448494_54_op (ShiftR_32_32_32 y$s$8_op y$n16s32)))
(assert (= y$s$7_op (BitWiseNot_32_32 y$v3_1517448494_54_op)))
(assert (= y$v3_1517448494_53_op (ShiftR_32_32_32 y$w$31_op y$n16s32)))
(assert (= y$v3_1517448494_52_op (ite y$179 y$s$7_op y$v3_1517448494_53_op)))
(assert (= y$207 (Extract_1_15_15_16 y$v_res0_0)))
(assert (= y$w$29_op (Concat_32_16_16 y$n0s16 y$v_res0_0)))
(assert (= y$s$6_op (BitWiseNot_32_32 y$w$29_op)))
(assert (= y$v3_1517448494_49_op (ShiftR_32_32_32 y$s$6_op y$n16s32)))
(assert (= y$s$5_op (BitWiseNot_32_32 y$v3_1517448494_49_op)))
(assert (= y$v3_1517448494_48_op (ShiftR_32_32_32 y$w$29_op y$n16s32)))
(assert (= y$v3_1517448494_47_op (ite y$207 y$s$5_op y$v3_1517448494_48_op)))
(assert (= y$2660 (not (= y$v3_1517448494_52_op y$v3_1517448494_47_op))))
(assert (= y$244 (Extract_1_15_15_16 y$v_res1_1)))
(assert (= y$w$33_op (Concat_32_16_16 y$n0s16 y$v_res1_1)))
(assert (= y$s$10_op (BitWiseNot_32_32 y$w$33_op)))
(assert (= y$v3_1517448494_60_op (ShiftR_32_32_32 y$s$10_op y$n16s32)))
(assert (= y$s$9_op (BitWiseNot_32_32 y$v3_1517448494_60_op)))
(assert (= y$v3_1517448494_59_op (ShiftR_32_32_32 y$w$33_op y$n16s32)))
(assert (= y$v3_1517448494_58_op (ite y$244 y$s$9_op y$v3_1517448494_59_op)))
(assert (= y$2663 (not (= y$v3_1517448494_47_op y$v3_1517448494_58_op))))
(assert (= y$v3_1517448494_64_op (and y$2660 y$2663)))
(assert (= y$v3_1517448494_64_op (not y$2666)))
(assert (= y$id56_op (and y$37 y$2666)))
(assert (= y$id56_op (not y$2669)))
(assert (= y$2670 (= y$prop y$2669)))
(assert (= y$2810 (= y$n0s16 y$v_res0_1$next)))
(assert (= y$w$31$next_op (Concat_32_16_16 y$n0s16 y$v_res0_1$next)))
(assert (= y$v3_1517448494_53$next_op (ShiftR_32_32_32 y$w$31$next_op y$n16s32)))
(assert (= y$2811 (not (= y$w$31$next_op y$v3_1517448494_53$next_op))))
(assert (= y$2812 (and y$2810 y$2811)))
(assert (= y$2812 (not y$2814)))
(assert (= y$2805 (not (= y$w$31_op y$v3_1517448494_53_op))))
(assert (= y$2809 (and y$69 y$2805)))
(assert (= y$2809 (not y$2813)))
(assert (= y$2828 (and y$1 y$3 y$5 y$7 y$9 y$11 y$13 y$15 y$17 y$19 y$21 y$23 y$25 y$27 y$29 y$31 y$33 y$35 y$37 y$40 y$42 y$44 y$46 y$49 y$51 y$53 y$55 y$57 y$59 y$61 y$63 y$65 y$67 y$69 y$71 y$73 y$75 y$77 y$79 y$81 y$2725 y$2670 y$2814 y$2813)))
(assert y$2828)
(check-sat)
(exit)

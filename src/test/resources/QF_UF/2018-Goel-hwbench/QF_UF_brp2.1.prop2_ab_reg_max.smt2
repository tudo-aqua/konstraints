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

id: brp2.1.prop2
query-maker: "Yices 2"
query-time: 0.001000 ms
query-class: abstract
query-category: oneshot
query-type: regular
status: unsat
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")

;
(set-info :status unsat)
(declare-sort utt$8 0)
(declare-sort utt$16 0)
(declare-sort utt$32 0)
(declare-fun BitWiseNot_32_32 (utt$32 ) utt$32)
(declare-fun BitWiseXor_16_16_16 (utt$16 utt$16 ) utt$16)
(declare-fun Concat_32_16_16 (utt$16 utt$16 ) utt$32)
(declare-fun Extract_1_15_15_16 (utt$16 ) Bool)
(declare-fun ShiftR_32_32_32 (utt$32 utt$32 ) utt$32)
(declare-fun y$1 () Bool)
(declare-fun y$11 () Bool)
(declare-fun y$114 () Bool)
(declare-fun y$13 () Bool)
(declare-fun y$15 () Bool)
(declare-fun y$17 () Bool)
(declare-fun y$19 () Bool)
(declare-fun y$2072 () Bool)
(declare-fun y$2073 () Bool)
(declare-fun y$21 () Bool)
(declare-fun y$2113 () Bool)
(declare-fun y$2155 () Bool)
(declare-fun y$23 () Bool)
(declare-fun y$25 () Bool)
(declare-fun y$27 () Bool)
(declare-fun y$29 () Bool)
(declare-fun y$3 () Bool)
(declare-fun y$31 () Bool)
(declare-fun y$33 () Bool)
(declare-fun y$35 () Bool)
(declare-fun y$37 () Bool)
(declare-fun y$39 () Bool)
(declare-fun y$41 () Bool)
(declare-fun y$43 () Bool)
(declare-fun y$45 () Bool)
(declare-fun y$47 () Bool)
(declare-fun y$49 () Bool)
(declare-fun y$5 () Bool)
(declare-fun y$51 () Bool)
(declare-fun y$53 () Bool)
(declare-fun y$56 () Bool)
(declare-fun y$58 () Bool)
(declare-fun y$60 () Bool)
(declare-fun y$62 () Bool)
(declare-fun y$64 () Bool)
(declare-fun y$66 () Bool)
(declare-fun y$69 () Bool)
(declare-fun y$7 () Bool)
(declare-fun y$71 () Bool)
(declare-fun y$73 () Bool)
(declare-fun y$75 () Bool)
(declare-fun y$77 () Bool)
(declare-fun y$79 () Bool)
(declare-fun y$81 () Bool)
(declare-fun y$83 () Bool)
(declare-fun y$879 () Bool)
(declare-fun y$9 () Bool)
(declare-fun y$979 () Bool)
(declare-fun y$a_BAD_K () Bool)
(declare-fun y$a_BAD_L () Bool)
(declare-fun y$a_dk () Bool)
(declare-fun y$a_error () Bool)
(declare-fun y$a_file_req () Bool)
(declare-fun y$a_first_safe_frame () Bool)
(declare-fun y$a_frame_received () Bool)
(declare-fun y$a_frame_reported () Bool)
(declare-fun y$a_idle_Receiver () Bool)
(declare-fun y$a_idle_Sender () Bool)
(declare-fun y$a_in_transit_K () Bool)
(declare-fun y$a_in_transit_L () Bool)
(declare-fun y$a_inc () Bool)
(declare-fun y$a_init_state () Bool)
(declare-fun y$a_new_file () Bool)
(declare-fun y$a_next_frame () Bool)
(declare-fun y$a_nok_RClient () Bool)
(declare-fun y$a_nok_SClient () Bool)
(declare-fun y$a_ok_RClient () Bool)
(declare-fun y$a_ok_SClient () Bool)
(declare-fun y$a_send_req () Bool)
(declare-fun y$a_start_K () Bool)
(declare-fun y$a_start_L () Bool)
(declare-fun y$a_success () Bool)
(declare-fun y$a_time () Bool)
(declare-fun y$a_wait_ack () Bool)
(declare-fun y$dve_invalid () Bool)
(declare-fun y$id57 () Bool)
(declare-fun y$id57_op () Bool)
(declare-fun y$n0s16 () utt$16)
(declare-fun y$n0s32 () utt$32)
(declare-fun y$n0s8 () utt$8)
(declare-fun y$n16s32 () utt$32)
(declare-fun y$n1s32 () utt$32)
(declare-fun y$n1s8 () utt$8)
(declare-fun y$n2s32 () utt$32)
(declare-fun y$n31s16 () utt$16)
(declare-fun y$n31s32 () utt$32)
(declare-fun y$n32s16 () utt$16)
(declare-fun y$n3s16 () utt$16)
(declare-fun y$n3s32 () utt$32)
(declare-fun y$n3s8 () utt$8)
(declare-fun y$n4s32 () utt$32)
(declare-fun y$n5s32 () utt$32)
(declare-fun y$n6s32 () utt$32)
(declare-fun y$prop () Bool)
(declare-fun y$s$10 () utt$32)
(declare-fun y$s$10_op () utt$32)
(declare-fun y$s$7 () utt$32)
(declare-fun y$s$7_op () utt$32)
(declare-fun y$s$8 () utt$32)
(declare-fun y$s$8_op () utt$32)
(declare-fun y$s$9 () utt$32)
(declare-fun y$s$9_op () utt$32)
(declare-fun y$v3_1517448493_48 () utt$32)
(declare-fun y$v3_1517448493_48_op () utt$32)
(declare-fun y$v3_1517448493_49 () utt$32)
(declare-fun y$v3_1517448493_49_op () utt$32)
(declare-fun y$v3_1517448493_50 () utt$32)
(declare-fun y$v3_1517448493_50_op () utt$32)
(declare-fun y$v3_1517448493_53 () utt$16)
(declare-fun y$v3_1517448493_53_op () utt$16)
(declare-fun y$v3_1517448493_55 () utt$32)
(declare-fun y$v3_1517448493_55_op () utt$32)
(declare-fun y$v3_1517448493_56 () utt$32)
(declare-fun y$v3_1517448493_56_op () utt$32)
(declare-fun y$v3_1517448493_57 () utt$32)
(declare-fun y$v3_1517448493_57_op () utt$32)
(declare-fun y$v3_1517448493_60 () Bool)
(declare-fun y$v3_1517448493_60_op () Bool)
(declare-fun y$v3_1517448493_61 () Bool)
(declare-fun y$v3_1517448493_61_op () Bool)
(declare-fun y$v_SYNC () utt$16)
(declare-fun y$v_U () utt$16)
(declare-fun y$v_V () utt$16)
(declare-fun y$v_W () utt$16)
(declare-fun y$v_X () utt$16)
(declare-fun y$v_Z () utt$16)
(declare-fun y$v_ab () utt$8)
(declare-fun y$v_exp_ab () utt$8)
(declare-fun y$v_i () utt$8)
(declare-fun y$v_maxtime () utt$16)
(declare-fun y$v_n () utt$16)
(declare-fun y$v_rc () utt$8)
(declare-fun y$v_triple_K () utt$8)
(declare-fun y$v_triple_Receiver () utt$8)
(declare-fun y$w$1 () Bool)
(declare-fun y$w$2 () utt$32)
(declare-fun y$w$21 () Bool)
(declare-fun y$w$22 () utt$32)
(declare-fun y$w$22_op () utt$32)
(declare-fun y$w$2_op () utt$32)
(assert (distinct y$n0s8 y$n1s8 y$n3s8))
(assert (distinct y$n0s16 y$n3s16 y$n31s16 y$n32s16))
(assert (distinct y$n16s32 y$n1s32 y$n0s32 y$n4s32 y$n2s32 y$n31s32 y$n5s32 y$n3s32 y$n6s32))
(assert (= y$a_BAD_K (not y$1)))
(assert (= y$a_BAD_L (not y$3)))
(assert (= y$a_dk (not y$5)))
(assert (= y$a_error (not y$7)))
(assert (= y$a_file_req (not y$9)))
(assert (= y$a_first_safe_frame (not y$11)))
(assert (= y$a_frame_received (not y$13)))
(assert (= y$a_frame_reported (not y$15)))
(assert (= y$a_idle_Receiver (not y$17)))
(assert (= y$a_idle_Sender (not y$19)))
(assert (= y$a_in_transit_K (not y$21)))
(assert (= y$a_in_transit_L (not y$23)))
(assert (= y$a_inc (not y$25)))
(assert (= y$a_init_state (not y$27)))
(assert (= y$a_new_file (not y$29)))
(assert (= y$a_next_frame (not y$31)))
(assert (= y$a_nok_RClient (not y$33)))
(assert (= y$a_nok_SClient (not y$35)))
(assert (= y$a_ok_RClient (not y$37)))
(assert (= y$a_ok_SClient (not y$39)))
(assert (= y$a_send_req (not y$41)))
(assert (= y$a_start_K (not y$43)))
(assert (= y$a_start_L (not y$45)))
(assert (= y$a_success (not y$47)))
(assert (= y$a_time (not y$49)))
(assert (= y$a_wait_ack (not y$51)))
(assert (= y$dve_invalid (not y$53)))
(assert (= y$56 (= y$n0s16 y$v_SYNC)))
(assert (= y$58 (= y$n0s16 y$v_U)))
(assert (= y$60 (= y$n0s16 y$v_V)))
(assert (= y$62 (= y$n0s16 y$v_W)))
(assert (= y$64 (= y$n0s16 y$v_X)))
(assert (= y$66 (= y$n0s16 y$v_Z)))
(assert (= y$69 (= y$n0s8 y$v_ab)))
(assert (= y$71 (= y$n0s8 y$v_exp_ab)))
(assert (= y$73 (= y$n0s8 y$v_i)))
(assert (= y$75 (= y$n0s16 y$v_maxtime)))
(assert (= y$77 (= y$n0s16 y$v_n)))
(assert (= y$79 (= y$n0s8 y$v_rc)))
(assert (= y$81 (= y$n0s8 y$v_triple_K)))
(assert (= y$83 (= y$n0s8 y$v_triple_Receiver)))
(assert (= y$prop (not y$2113)))
(assert (= y$114 (Extract_1_15_15_16 y$v_X)))
(assert (= y$w$22_op (Concat_32_16_16 y$n0s16 y$v_X)))
(assert (= y$s$8_op (BitWiseNot_32_32 y$w$22_op)))
(assert (= y$v3_1517448493_50_op (ShiftR_32_32_32 y$s$8_op y$n16s32)))
(assert (= y$s$7_op (BitWiseNot_32_32 y$v3_1517448493_50_op)))
(assert (= y$v3_1517448493_49_op (ShiftR_32_32_32 y$w$22_op y$n16s32)))
(assert (= y$v3_1517448493_48_op (ite y$114 y$s$7_op y$v3_1517448493_49_op)))
(assert (= y$v3_1517448493_53_op (BitWiseXor_16_16_16 y$n31s16 y$v_SYNC)))
(assert (= y$879 (Extract_1_15_15_16 y$v3_1517448493_53_op)))
(assert (= y$w$2_op (Concat_32_16_16 y$n0s16 y$v3_1517448493_53_op)))
(assert (= y$s$10_op (BitWiseNot_32_32 y$w$2_op)))
(assert (= y$v3_1517448493_57_op (ShiftR_32_32_32 y$s$10_op y$n16s32)))
(assert (= y$s$9_op (BitWiseNot_32_32 y$v3_1517448493_57_op)))
(assert (= y$v3_1517448493_56_op (ShiftR_32_32_32 y$w$2_op y$n16s32)))
(assert (= y$v3_1517448493_55_op (ite y$879 y$s$9_op y$v3_1517448493_56_op)))
(assert (= y$979 (= y$v3_1517448493_48_op y$v3_1517448493_55_op)))
(assert (= y$v3_1517448493_60_op (and y$a_error y$979)))
(assert (= y$v3_1517448493_61_op (and y$a_new_file y$v3_1517448493_60_op)))
(assert (= y$id57_op (and y$53 y$v3_1517448493_61_op)))
(assert (= y$id57_op (not y$2072)))
(assert (= y$2073 (= y$prop y$2072)))
(assert (= y$2155 (and y$1 y$3 y$5 y$7 y$9 y$11 y$13 y$15 y$17 y$19 y$21 y$23 y$25 y$27 y$29 y$31 y$33 y$35 y$37 y$39 y$41 y$43 y$45 y$47 y$49 y$51 y$53 y$56 y$58 y$60 y$62 y$64 y$66 y$69 y$71 y$73 y$75 y$77 y$79 y$81 y$83 y$2113 y$2073)))
(assert y$2155)
(check-sat)
(exit)

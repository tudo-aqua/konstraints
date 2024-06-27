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

id: anderson.1.prop1
query-maker: "Yices 2"
query-time: 0.019000 ms
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
(declare-sort utt$32 0)
(declare-fun Add_32_32_32 (utt$32 utt$32 ) utt$32)
(declare-fun GrEq_1_32_32 (utt$32 utt$32 ) Bool)
(declare-fun y$1 () Bool)
(declare-fun y$11 () Bool)
(declare-fun y$13 () Bool)
(declare-fun y$15 () Bool)
(declare-fun y$17 () Bool)
(declare-fun y$19 () Bool)
(declare-fun y$21 () Bool)
(declare-fun y$24 () Bool)
(declare-fun y$26 () Bool)
(declare-fun y$28 () Bool)
(declare-fun y$3 () Bool)
(declare-fun y$30 () Bool)
(declare-fun y$32 () Bool)
(declare-fun y$5 () Bool)
(declare-fun y$7 () Bool)
(declare-fun y$720 () Bool)
(declare-fun y$723 () Bool)
(declare-fun y$724 () Bool)
(declare-fun y$743 () Bool)
(declare-fun y$759 () Bool)
(declare-fun y$9 () Bool)
(declare-fun y$a_CS_P_0 () Bool)
(declare-fun y$a_CS_P_1 () Bool)
(declare-fun y$a_NCS_P_0 () Bool)
(declare-fun y$a_NCS_P_1 () Bool)
(declare-fun y$a_p1_P_0 () Bool)
(declare-fun y$a_p1_P_1 () Bool)
(declare-fun y$a_p2_P_0 () Bool)
(declare-fun y$a_p2_P_1 () Bool)
(declare-fun y$a_p3_P_0 () Bool)
(declare-fun y$a_p3_P_1 () Bool)
(declare-fun y$dve_invalid () Bool)
(declare-fun y$id24 () Bool)
(declare-fun y$id24_op () Bool)
(declare-fun y$n0s32 () utt$32)
(declare-fun y$n0s8 () utt$8)
(declare-fun y$n1s32 () utt$32)
(declare-fun y$n1s8 () utt$8)
(declare-fun y$n2s32 () utt$32)
(declare-fun y$prop () Bool)
(declare-fun y$v3_1517448492_19 () utt$32)
(declare-fun y$v3_1517448492_19_op () utt$32)
(declare-fun y$v3_1517448492_20 () utt$32)
(declare-fun y$v3_1517448492_20_op () utt$32)
(declare-fun y$v3_1517448492_21 () utt$32)
(declare-fun y$v3_1517448492_21_op () utt$32)
(declare-fun y$v3_1517448492_22 () Bool)
(declare-fun y$v3_1517448492_22_op () Bool)
(declare-fun y$v_Slot_0 () utt$8)
(declare-fun y$v_Slot_1 () utt$8)
(declare-fun y$v_my_place_P_0 () utt$8)
(declare-fun y$v_my_place_P_1 () utt$8)
(declare-fun y$v_next () utt$8)
(assert (not (= y$n0s8 y$n1s8)))
(assert (distinct y$n0s32 y$n1s32 y$n2s32))
(assert (= y$a_CS_P_0 (not y$1)))
(assert (= y$a_CS_P_1 (not y$3)))
(assert (= y$a_NCS_P_0 (not y$5)))
(assert (= y$a_NCS_P_1 (not y$7)))
(assert (= y$a_p1_P_0 (not y$9)))
(assert (= y$a_p1_P_1 (not y$11)))
(assert (= y$a_p2_P_0 (not y$13)))
(assert (= y$a_p2_P_1 (not y$15)))
(assert (= y$a_p3_P_0 (not y$17)))
(assert (= y$a_p3_P_1 (not y$19)))
(assert (= y$dve_invalid (not y$21)))
(assert (= y$24 (= y$n0s8 y$v_Slot_0)))
(assert (= y$26 (= y$n0s8 y$v_Slot_1)))
(assert (= y$28 (= y$n0s8 y$v_my_place_P_0)))
(assert (= y$30 (= y$n0s8 y$v_my_place_P_1)))
(assert (= y$32 (= y$n0s8 y$v_next)))
(assert (= y$prop (not y$743)))
(assert (= y$v3_1517448492_19_op (ite y$a_CS_P_0 y$n1s32 y$n0s32)))
(assert (= y$v3_1517448492_20_op (ite y$a_CS_P_1 y$n1s32 y$n0s32)))
(assert (= y$v3_1517448492_21_op (Add_32_32_32 y$v3_1517448492_19_op y$v3_1517448492_20_op)))
(assert (= y$v3_1517448492_22_op (GrEq_1_32_32 y$n1s32 y$v3_1517448492_21_op)))
(assert (= y$v3_1517448492_22_op (not y$720)))
(assert (= y$id24_op (and y$21 y$720)))
(assert (= y$id24_op (not y$723)))
(assert (= y$724 (= y$prop y$723)))
(assert (= y$759 (and y$1 y$3 y$5 y$7 y$9 y$11 y$13 y$15 y$17 y$19 y$21 y$24 y$26 y$28 y$30 y$32 y$743 y$724)))
(assert y$759)
(check-sat)
(exit)

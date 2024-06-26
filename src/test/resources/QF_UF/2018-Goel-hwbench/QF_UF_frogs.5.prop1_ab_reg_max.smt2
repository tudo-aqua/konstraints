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

id: frogs.5.prop1
query-maker: "Yices 2"
query-time: 0.002000 ms
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
(declare-sort utt$32 0)
(declare-fun y$1 () Bool)
(declare-fun y$12 () Bool)
(declare-fun y$14 () Bool)
(declare-fun y$16 () Bool)
(declare-fun y$18 () Bool)
(declare-fun y$20 () Bool)
(declare-fun y$22 () Bool)
(declare-fun y$24 () Bool)
(declare-fun y$26 () Bool)
(declare-fun y$28 () Bool)
(declare-fun y$3 () Bool)
(declare-fun y$30 () Bool)
(declare-fun y$32 () Bool)
(declare-fun y$34 () Bool)
(declare-fun y$36 () Bool)
(declare-fun y$38 () Bool)
(declare-fun y$40 () Bool)
(declare-fun y$4174 () Bool)
(declare-fun y$4175 () Bool)
(declare-fun y$4191 () Bool)
(declare-fun y$4198 () Bool)
(declare-fun y$42 () Bool)
(declare-fun y$44 () Bool)
(declare-fun y$46 () Bool)
(declare-fun y$48 () Bool)
(declare-fun y$5 () Bool)
(declare-fun y$50 () Bool)
(declare-fun y$52 () Bool)
(declare-fun y$54 () Bool)
(declare-fun y$56 () Bool)
(declare-fun y$58 () Bool)
(declare-fun y$60 () Bool)
(declare-fun y$62 () Bool)
(declare-fun y$64 () Bool)
(declare-fun y$66 () Bool)
(declare-fun y$68 () Bool)
(declare-fun y$7 () Bool)
(declare-fun y$70 () Bool)
(declare-fun y$72 () Bool)
(declare-fun y$74 () Bool)
(declare-fun y$9 () Bool)
(declare-fun y$a_done () Bool)
(declare-fun y$a_not_done () Bool)
(declare-fun y$a_q_Frog () Bool)
(declare-fun y$a_q_Toad () Bool)
(declare-fun y$dve_invalid () Bool)
(declare-fun y$id39 () Bool)
(declare-fun y$id39_op () Bool)
(declare-fun y$n0s32 () utt$32)
(declare-fun y$n0s8 () utt$8)
(declare-fun y$n10s32 () utt$32)
(declare-fun y$n11s32 () utt$32)
(declare-fun y$n12s32 () utt$32)
(declare-fun y$n13s32 () utt$32)
(declare-fun y$n14s32 () utt$32)
(declare-fun y$n15s32 () utt$32)
(declare-fun y$n16s32 () utt$32)
(declare-fun y$n17s32 () utt$32)
(declare-fun y$n18s32 () utt$32)
(declare-fun y$n19s32 () utt$32)
(declare-fun y$n1s32 () utt$32)
(declare-fun y$n1s8 () utt$8)
(declare-fun y$n20s32 () utt$32)
(declare-fun y$n21s32 () utt$32)
(declare-fun y$n22s32 () utt$32)
(declare-fun y$n23s32 () utt$32)
(declare-fun y$n24s32 () utt$32)
(declare-fun y$n25s32 () utt$32)
(declare-fun y$n26s32 () utt$32)
(declare-fun y$n27s32 () utt$32)
(declare-fun y$n28s32 () utt$32)
(declare-fun y$n29s32 () utt$32)
(declare-fun y$n2s32 () utt$32)
(declare-fun y$n2s8 () utt$8)
(declare-fun y$n3s32 () utt$32)
(declare-fun y$n4s32 () utt$32)
(declare-fun y$n5s32 () utt$32)
(declare-fun y$n6s32 () utt$32)
(declare-fun y$n7s32 () utt$32)
(declare-fun y$n8s32 () utt$32)
(declare-fun y$n9s32 () utt$32)
(declare-fun y$prop () Bool)
(declare-fun y$v_a_0 () utt$8)
(declare-fun y$v_a_1 () utt$8)
(declare-fun y$v_a_10 () utt$8)
(declare-fun y$v_a_11 () utt$8)
(declare-fun y$v_a_12 () utt$8)
(declare-fun y$v_a_13 () utt$8)
(declare-fun y$v_a_14 () utt$8)
(declare-fun y$v_a_15 () utt$8)
(declare-fun y$v_a_16 () utt$8)
(declare-fun y$v_a_17 () utt$8)
(declare-fun y$v_a_18 () utt$8)
(declare-fun y$v_a_19 () utt$8)
(declare-fun y$v_a_2 () utt$8)
(declare-fun y$v_a_20 () utt$8)
(declare-fun y$v_a_21 () utt$8)
(declare-fun y$v_a_22 () utt$8)
(declare-fun y$v_a_23 () utt$8)
(declare-fun y$v_a_24 () utt$8)
(declare-fun y$v_a_25 () utt$8)
(declare-fun y$v_a_26 () utt$8)
(declare-fun y$v_a_27 () utt$8)
(declare-fun y$v_a_28 () utt$8)
(declare-fun y$v_a_29 () utt$8)
(declare-fun y$v_a_3 () utt$8)
(declare-fun y$v_a_4 () utt$8)
(declare-fun y$v_a_5 () utt$8)
(declare-fun y$v_a_6 () utt$8)
(declare-fun y$v_a_7 () utt$8)
(declare-fun y$v_a_8 () utt$8)
(declare-fun y$v_a_9 () utt$8)
(declare-fun y$v_x () utt$8)
(declare-fun y$v_y () utt$8)
(assert (distinct y$n0s8 y$n1s8 y$n2s8))
(assert (distinct y$n0s32 y$n6s32 y$n2s32 y$n1s32 y$n3s32 y$n4s32 y$n5s32 y$n7s32 y$n8s32 y$n9s32 y$n20s32 y$n10s32 y$n11s32 y$n12s32 y$n13s32 y$n14s32 y$n15s32 y$n16s32 y$n17s32 y$n18s32 y$n19s32 y$n21s32 y$n22s32 y$n23s32 y$n24s32 y$n25s32 y$n26s32 y$n27s32 y$n28s32 y$n29s32))
(assert (= y$a_done (not y$1)))
(assert (= y$a_not_done (not y$3)))
(assert (= y$a_q_Frog (not y$5)))
(assert (= y$a_q_Toad (not y$7)))
(assert (= y$dve_invalid (not y$9)))
(assert (= y$12 (= y$n0s8 y$v_a_0)))
(assert (= y$14 (= y$n0s8 y$v_a_1)))
(assert (= y$16 (= y$n0s8 y$v_a_10)))
(assert (= y$18 (= y$n0s8 y$v_a_11)))
(assert (= y$20 (= y$n0s8 y$v_a_12)))
(assert (= y$22 (= y$n0s8 y$v_a_13)))
(assert (= y$24 (= y$n0s8 y$v_a_14)))
(assert (= y$26 (= y$n0s8 y$v_a_15)))
(assert (= y$28 (= y$n0s8 y$v_a_16)))
(assert (= y$30 (= y$n0s8 y$v_a_17)))
(assert (= y$32 (= y$n0s8 y$v_a_18)))
(assert (= y$34 (= y$n0s8 y$v_a_19)))
(assert (= y$36 (= y$n0s8 y$v_a_2)))
(assert (= y$38 (= y$n0s8 y$v_a_20)))
(assert (= y$40 (= y$n0s8 y$v_a_21)))
(assert (= y$42 (= y$n0s8 y$v_a_22)))
(assert (= y$44 (= y$n0s8 y$v_a_23)))
(assert (= y$46 (= y$n0s8 y$v_a_24)))
(assert (= y$48 (= y$n0s8 y$v_a_25)))
(assert (= y$50 (= y$n0s8 y$v_a_26)))
(assert (= y$52 (= y$n0s8 y$v_a_27)))
(assert (= y$54 (= y$n0s8 y$v_a_28)))
(assert (= y$56 (= y$n0s8 y$v_a_29)))
(assert (= y$58 (= y$n0s8 y$v_a_3)))
(assert (= y$60 (= y$n0s8 y$v_a_4)))
(assert (= y$62 (= y$n0s8 y$v_a_5)))
(assert (= y$64 (= y$n0s8 y$v_a_6)))
(assert (= y$66 (= y$n0s8 y$v_a_7)))
(assert (= y$68 (= y$n0s8 y$v_a_8)))
(assert (= y$70 (= y$n0s8 y$v_a_9)))
(assert (= y$72 (= y$n0s8 y$v_x)))
(assert (= y$74 (= y$n0s8 y$v_y)))
(assert (= y$prop (not y$4191)))
(assert (= y$id39_op (and y$a_done y$9)))
(assert (= y$id39_op (not y$4174)))
(assert (= y$4175 (= y$prop y$4174)))
(assert (= y$4198 (and y$1 y$3 y$5 y$7 y$9 y$12 y$14 y$16 y$18 y$20 y$22 y$24 y$26 y$28 y$30 y$32 y$34 y$36 y$38 y$40 y$42 y$44 y$46 y$48 y$50 y$52 y$54 y$56 y$58 y$60 y$62 y$64 y$66 y$68 y$70 y$72 y$74 y$4191 y$4175)))
(assert y$4198)
(check-sat)
(exit)

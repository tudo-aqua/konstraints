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

id: h_traffic_light_example
query-maker: "Yices 2"
query-time: 1.435000 ms
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
(declare-sort utt$8 0)
(declare-sort utt$32 0)
(declare-fun Extract_2_1_0_32 (utt$32 ) utt$2)
(declare-fun Sub_8_8_8 (utt$8 utt$8 ) utt$8)
(declare-fun y$10 () Bool)
(declare-fun y$101 () Bool)
(declare-fun y$102 () Bool)
(declare-fun y$12 () Bool)
(declare-fun y$122 () Bool)
(declare-fun y$123 () Bool)
(declare-fun y$124 () Bool)
(declare-fun y$125 () Bool)
(declare-fun y$128 () Bool)
(declare-fun y$131 () Bool)
(declare-fun y$132 () Bool)
(declare-fun y$133 () Bool)
(declare-fun y$134 () Bool)
(declare-fun y$19 () utt$2)
(declare-fun y$2 () Bool)
(declare-fun y$22 () utt$2)
(declare-fun y$27 () utt$2)
(declare-fun y$29 () utt$2)
(declare-fun y$35 () utt$2)
(declare-fun y$36 () utt$2)
(declare-fun y$44 () Bool)
(declare-fun y$5 () Bool)
(declare-fun y$63 () Bool)
(declare-fun y$64 () Bool)
(declare-fun y$67 () Bool)
(declare-fun y$68 () Bool)
(declare-fun y$76 () Bool)
(declare-fun y$77 () Bool)
(declare-fun y$78 () Bool)
(declare-fun y$79 () Bool)
(declare-fun y$80 () Bool)
(declare-fun y$81 () Bool)
(declare-fun y$82 () Bool)
(declare-fun y$83 () Bool)
(declare-fun y$84 () Bool)
(declare-fun y$89 () Bool)
(declare-fun y$94 () Bool)
(declare-fun y$96 () Bool)
(declare-fun y$97 () Bool)
(declare-fun y$98 () Bool)
(declare-fun y$Counter () utt$8)
(declare-fun y$Counter$next () utt$8)
(declare-fun y$Counter$next_rhs () utt$8)
(declare-fun y$Counter$next_rhs_op () utt$8)
(declare-fun y$Light_Sign () utt$2)
(declare-fun y$Light_Sign$next () utt$2)
(declare-fun y$Light_Sign$next_rhs () utt$2)
(declare-fun y$Light_Sign$next_rhs_op () utt$2)
(declare-fun y$n0s2 () utt$2)
(declare-fun y$n0s32 () utt$32)
(declare-fun y$n0s8 () utt$8)
(declare-fun y$n1s2 () utt$2)
(declare-fun y$n1s32 () utt$32)
(declare-fun y$n1s8 () utt$8)
(declare-fun y$n255s8 () utt$8)
(declare-fun y$n2s2 () utt$2)
(declare-fun y$n2s32 () utt$32)
(declare-fun y$n63s8 () utt$8)
(declare-fun y$n7s8 () utt$8)
(declare-fun y$prop () Bool)
(declare-fun y$prop$next () Bool)
(declare-fun y$reset () Bool)
(declare-fun y$reset$next () Bool)
(declare-fun y$s$2 () Bool)
(declare-fun y$s$24 () utt$8)
(declare-fun y$s$24$next () utt$8)
(declare-fun y$s$24$next_op () utt$8)
(declare-fun y$s$24_op () utt$8)
(declare-fun y$s$25 () utt$32)
(declare-fun y$s$25_op () utt$32)
(declare-fun y$s$26 () utt$32)
(declare-fun y$s$26_op () utt$32)
(declare-fun y$s$27 () utt$32)
(declare-fun y$s$27_op () utt$32)
(declare-fun y$s$28 () utt$8)
(declare-fun y$s$28_op () utt$8)
(declare-fun y$s$29 () utt$8)
(declare-fun y$s$29_op () utt$8)
(declare-fun y$s$2_op () Bool)
(declare-fun y$s$4 () utt$8)
(declare-fun y$s$4_op () utt$8)
(declare-fun y$s$5 () utt$8)
(declare-fun y$s$5_op () utt$8)
(declare-fun y$s$6 () utt$8)
(declare-fun y$s$6_op () utt$8)
(declare-fun y$s$7 () utt$2)
(declare-fun y$s$7_op () utt$2)
(declare-fun y$s$8 () utt$2)
(declare-fun y$s$8_op () utt$2)
(declare-fun y$s$9 () utt$2)
(declare-fun y$s$9_op () utt$2)
(declare-fun y$w$1 () utt$2)
(declare-fun y$w$2 () utt$2)
(declare-fun y$w$3 () utt$2)
(assert (distinct y$n0s2 y$n1s2 y$n2s2))
(assert (distinct y$n0s8 y$n63s8 y$n1s8 y$n7s8 y$n255s8))
(assert (distinct y$n0s32 y$n2s32 y$n1s32))
(assert (= y$67 (not (= y$n255s8 y$Counter))))
(assert (= y$68 (= y$prop y$67)))
(assert (= y$10 (= y$n1s2 y$Light_Sign)))
(assert (= y$12 (= y$n2s2 y$Light_Sign)))
(assert (= y$s$2_op (or y$10 y$12)))
(assert (= y$2 (= y$n0s8 y$Counter)))
(assert (= y$s$27_op (ite y$2 y$n0s32 y$n2s32)))
(assert (= y$22 (ite y$2 y$n0s2 y$n2s2)))
(assert (= y$19 (Extract_2_1_0_32 y$s$27_op)))
(assert (= y$22 y$19))
(assert (= y$s$26_op (ite y$2 y$n2s32 y$n1s32)))
(assert (= y$29 (ite y$2 y$n2s2 y$n1s2)))
(assert (= y$27 (Extract_2_1_0_32 y$s$26_op)))
(assert (= y$29 y$27))
(assert (= y$s$7_op (ite y$12 y$19 y$27)))
(assert (= y$5 (= y$n0s2 y$Light_Sign)))
(assert (= y$s$25_op (ite y$2 y$n1s32 y$n0s32)))
(assert (= y$36 (ite y$2 y$n1s2 y$n0s2)))
(assert (= y$35 (Extract_2_1_0_32 y$s$25_op)))
(assert (= y$36 y$35))
(assert (= y$s$8_op (ite y$5 y$35 y$Light_Sign)))
(assert (= y$s$9_op (ite y$s$2_op y$s$7_op y$s$8_op)))
(assert (= y$Light_Sign$next_rhs_op (ite y$reset y$n0s2 y$s$9_op)))
(assert (= y$44 (= y$Light_Sign$next y$Light_Sign$next_rhs_op)))
(assert (= y$s$24_op (Sub_8_8_8 y$Counter y$n1s8)))
(assert (= y$s$28_op (ite y$2 y$n63s8 y$s$24_op)))
(assert (= y$s$29_op (ite y$2 y$n7s8 y$s$24_op)))
(assert (= y$s$4_op (ite y$12 y$s$28_op y$s$29_op)))
(assert (= y$s$5_op (ite y$5 y$s$28_op y$Counter)))
(assert (= y$s$6_op (ite y$s$2_op y$s$4_op y$s$5_op)))
(assert (= y$Counter$next_rhs_op (ite y$reset y$n0s8 y$s$6_op)))
(assert (= y$63 (= y$Counter$next y$Counter$next_rhs_op)))
(assert (= y$64 (and y$44 y$63)))
(assert (= y$78 (not (= y$n255s8 y$Counter$next))))
(assert (= y$79 (= y$prop$next y$78)))
(assert (= y$prop$next (not y$77)))
(assert (= y$98 (not (= y$n0s8 y$Counter$next))))
(assert (= y$s$24$next_op (Sub_8_8_8 y$Counter$next y$n1s8)))
(assert (= y$101 (= y$n255s8 y$s$24$next_op)))
(assert (= y$123 (and y$98 y$101)))
(assert (= y$123 (not y$125)))
(assert (= (not (= y$n0s8 y$Counter)) y$89))
(assert (= y$94 (= y$n255s8 y$s$24_op)))
(assert (= y$122 (and y$89 y$94)))
(assert (= y$122 (not y$124)))
(assert (= y$132 (and y$prop y$68 y$64 y$79 y$77 y$125 y$124)))
(assert y$132)
(assert (distinct y$n0s2 y$n1s2 y$n2s2))
(assert (distinct y$n0s8 y$n63s8 y$n1s8 y$n7s8 y$n255s8))
(assert (distinct y$n0s32 y$n2s32 y$n1s32))
(check-sat)
(exit)

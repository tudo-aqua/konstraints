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

id: cav14_example_v
query-maker: "Yices 2"
query-time: 0.283000 ms
query-class: abstract
query-category: oneshot
query-type: cti
status: sat
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")

;
(set-info :status sat)
(declare-sort utt$4 0)
(declare-fun Add_4_4_4 (utt$4 utt$4 ) utt$4)
(declare-fun Gr_1_4_4 (utt$4 utt$4 ) Bool)
(declare-fun y$108 () Bool)
(declare-fun y$109 () Bool)
(declare-fun y$110 () Bool)
(declare-fun y$111 () Bool)
(declare-fun y$112 () Bool)
(declare-fun y$121 () Bool)
(declare-fun y$14 () Bool)
(declare-fun y$2 () Bool)
(declare-fun y$21 () Bool)
(declare-fun y$31 () Bool)
(declare-fun y$32 () Bool)
(declare-fun y$34 () Bool)
(declare-fun y$35 () Bool)
(declare-fun y$42 () Bool)
(declare-fun y$43 () Bool)
(declare-fun y$46 () Bool)
(declare-fun y$47 () Bool)
(declare-fun y$48 () Bool)
(declare-fun y$5 () Bool)
(declare-fun y$51 () Bool)
(declare-fun y$52 () Bool)
(declare-fun y$53 () Bool)
(declare-fun y$54 () Bool)
(declare-fun y$55 () Bool)
(declare-fun y$56 () Bool)
(declare-fun y$66 () Bool)
(declare-fun y$67 () Bool)
(declare-fun y$68 () Bool)
(declare-fun y$69 () Bool)
(declare-fun y$70 () Bool)
(declare-fun y$78 () Bool)
(declare-fun y$79 () Bool)
(declare-fun y$8 () Bool)
(declare-fun y$80 () Bool)
(declare-fun y$84 () Bool)
(declare-fun y$91 () Bool)
(declare-fun y$92 () Bool)
(declare-fun y$X () utt$4)
(declare-fun y$X$next () utt$4)
(declare-fun y$X$next_rhs () utt$4)
(declare-fun y$X$next_rhs_op () utt$4)
(declare-fun y$Y () utt$4)
(declare-fun y$Y$next () utt$4)
(declare-fun y$Y$next_rhs () utt$4)
(declare-fun y$Y$next_rhs_op () utt$4)
(declare-fun y$n0s4 () utt$4)
(declare-fun y$n14s4 () utt$4)
(declare-fun y$n15s4 () utt$4)
(declare-fun y$n1s4 () utt$4)
(declare-fun y$prop () Bool)
(declare-fun y$prop$next () Bool)
(declare-fun y$s$10 () Bool)
(declare-fun y$s$10_op () Bool)
(declare-fun y$s$13 () utt$4)
(declare-fun y$s$13_op () utt$4)
(declare-fun y$s$14 () utt$4)
(declare-fun y$s$14_op () utt$4)
(declare-fun y$s$2 () utt$4)
(declare-fun y$s$2$next () utt$4)
(declare-fun y$s$2$next_op () utt$4)
(declare-fun y$s$2_op () utt$4)
(declare-fun y$s$3 () utt$4)
(declare-fun y$s$3_op () utt$4)
(declare-fun y$s$8 () Bool)
(declare-fun y$s$8$next () Bool)
(declare-fun y$s$8$next_op () Bool)
(declare-fun y$s$8_op () Bool)
(declare-fun y$s$9 () Bool)
(declare-fun y$s$9_op () Bool)
(assert (distinct y$n1s4 y$n0s4 y$n15s4))
(assert (= y$s$8_op (Gr_1_4_4 y$Y y$X)))
(assert (= y$s$8_op (not y$34)))
(assert (= y$35 (= y$prop y$34)))
(assert (= y$8 (= y$X y$Y)))
(assert (= y$s$3_op (Add_4_4_4 y$Y y$n1s4)))
(assert (= y$14 (not (= y$n15s4 y$X))))
(assert (= y$s$10_op (or y$s$8_op y$14)))
(assert (= y$s$14_op (ite y$s$10_op y$Y y$X)))
(assert (= y$Y$next_rhs_op (ite y$8 y$s$3_op y$s$14_op)))
(assert (= y$21 (= y$Y$next y$Y$next_rhs_op)))
(assert (= y$s$9_op (or y$8 y$14)))
(assert (= y$s$2_op (Add_4_4_4 y$X y$n1s4)))
(assert (= y$s$13_op (ite y$s$9_op y$s$2_op y$Y)))
(assert (= y$X$next_rhs_op (ite y$s$8_op y$X y$s$13_op)))
(assert (= y$31 (= y$X$next y$X$next_rhs_op)))
(assert (= y$32 (and y$21 y$31)))
(assert (= y$s$8$next_op (Gr_1_4_4 y$Y$next y$X$next)))
(assert (= y$s$8$next_op (not y$46)))
(assert (= y$47 (= y$prop$next y$46)))
(assert (= y$prop$next (not y$43)))
(assert (= y$52 (= y$n0s4 y$Y$next)))
(assert (= y$53 (and y$s$8$next_op y$52)))
(assert (= y$53 (not y$55)))
(assert (= y$5 (= y$n0s4 y$Y)))
(assert (= y$51 (and y$5 y$s$8_op)))
(assert (= y$51 (not y$54)))
(assert (= y$68 (and y$prop y$35 y$55 y$54 y$32 y$47 y$43)))
(assert y$68)
(assert (distinct y$n1s4 y$n0s4 y$n15s4))
(assert (= y$92 (= y$n1s4 y$X$next)))
(assert (= y$s$2$next_op (Add_4_4_4 y$X$next y$n1s4)))
(assert (= y$91 (= y$n15s4 y$s$2$next_op)))
(assert (= y$109 (and y$92 y$91)))
(assert (= y$109 (not y$111)))
(assert y$111)
(assert (= y$2 (= y$n1s4 y$X)))
(assert (= y$s$2_op (Add_4_4_4 y$X y$n1s4)))
(assert (= y$84 (= y$n15s4 y$s$2_op)))
(assert (= y$108 (and y$2 y$84)))
(assert (= y$108 (not y$110)))
(assert y$110)
(assert (distinct y$n1s4 y$n0s4 y$n15s4 y$n14s4))
(check-sat)
(exit)
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

id: h_b04
query-maker: "Yices 2"
query-time: 1.368000 ms
query-class: abstract
query-category: oneshot
query-type: cti
status: unsat
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")

;
(set-info :status unsat)
(declare-sort utt$8 0)
(declare-sort utt$31 0)
(declare-sort utt$32 0)
(declare-fun Concat_32_1_31 (Bool utt$31 ) utt$32)
(declare-fun Extract_1_7_7_8 (utt$8 ) Bool)
(declare-fun y$13 () Bool)
(declare-fun y$19 () Bool)
(declare-fun y$2 () Bool)
(declare-fun y$24 () Bool)
(declare-fun y$28 () Bool)
(declare-fun y$29 () Bool)
(declare-fun y$31 () Bool)
(declare-fun y$39 () Bool)
(declare-fun y$4 () Bool)
(declare-fun y$40 () Bool)
(declare-fun y$44 () Bool)
(declare-fun y$47 () Bool)
(declare-fun y$53 () Bool)
(declare-fun y$54 () Bool)
(declare-fun y$55 () Bool)
(declare-fun y$59 () Bool)
(declare-fun y$6 () Bool)
(declare-fun y$60 () Bool)
(declare-fun y$64 () Bool)
(declare-fun y$67 () Bool)
(declare-fun y$68 () Bool)
(declare-fun y$69 () Bool)
(declare-fun y$70 () Bool)
(declare-fun y$71 () Bool)
(declare-fun y$72 () Bool)
(declare-fun y$73 () Bool)
(declare-fun y$8 () Bool)
(declare-fun y$DATA_IN () utt$8)
(declare-fun y$DATA_OUT () utt$8)
(declare-fun y$DATA_OUT$next () utt$8)
(declare-fun y$DATA_OUT$next_rhs () utt$8)
(declare-fun y$DATA_OUT$next_rhs_op () utt$8)
(declare-fun y$RMAX () utt$8)
(declare-fun y$RMAX$next () utt$8)
(declare-fun y$RMAX$next_rhs () utt$8)
(declare-fun y$RMAX$next_rhs_op () utt$8)
(declare-fun y$RMIN () utt$8)
(declare-fun y$RMIN$next () utt$8)
(declare-fun y$RMIN$next_rhs () utt$8)
(declare-fun y$RMIN$next_rhs_op () utt$8)
(declare-fun y$n0s1 () Bool)
(declare-fun y$n0s31 () utt$31)
(declare-fun y$n0s8 () utt$8)
(declare-fun y$n1s1 () Bool)
(declare-fun y$n1s32 () utt$32)
(declare-fun y$prop () Bool)
(declare-fun y$prop$next () Bool)
(declare-fun y$prop0 () Bool)
(declare-fun y$prop0$next () Bool)
(declare-fun y$prop0$next_op () Bool)
(declare-fun y$prop0_op () Bool)
(declare-fun y$stato () Bool)
(declare-fun y$stato$next () Bool)
(declare-fun y$stato$next_rhs () Bool)
(declare-fun y$stato$next_rhs_op () Bool)
(declare-fun y$w$1 () Bool)
(declare-fun y$w$1$next () Bool)
(declare-fun y$w$2 () utt$32)
(declare-fun y$w$2$next () utt$32)
(declare-fun y$w$2$next_op () utt$32)
(declare-fun y$w$2_op () utt$32)
(declare-fun y$w$3 () Bool)
(declare-fun y$w$3$next () Bool)
(declare-fun y$w$4 () utt$32)
(declare-fun y$w$4$next () utt$32)
(declare-fun y$w$4$next_op () utt$32)
(declare-fun y$w$4_op () utt$32)
(assert (= y$31 (Extract_1_7_7_8 y$RMAX)))
(assert (= y$w$2_op (Concat_32_1_31 y$31 y$n0s31)))
(assert (= y$39 (not (= y$w$2_op y$n1s32))))
(assert (= y$40 (Extract_1_7_7_8 y$RMIN)))
(assert (= y$w$4_op (Concat_32_1_31 y$40 y$n0s31)))
(assert (= y$44 (= y$n1s32 y$w$4_op)))
(assert (= y$prop0_op (or y$39 y$44)))
(assert (= y$47 (= y$prop y$prop0_op)))
(assert (= y$DATA_OUT$next_rhs_op (ite y$stato y$n0s8 y$DATA_OUT)))
(assert (= y$13 (= y$DATA_OUT$next y$DATA_OUT$next_rhs_op)))
(assert (= y$stato (not y$stato$next_rhs_op)))
(assert (= y$19 (= y$stato$next y$stato$next_rhs_op)))
(assert (= y$RMAX$next_rhs_op (ite y$stato y$DATA_IN y$RMAX)))
(assert (= y$24 (= y$RMAX$next y$RMAX$next_rhs_op)))
(assert (= y$RMIN$next_rhs_op (ite y$stato y$DATA_IN y$RMIN)))
(assert (= y$28 (= y$RMIN$next y$RMIN$next_rhs_op)))
(assert (= y$29 (and y$13 y$19 y$24 y$28)))
(assert (= y$55 (Extract_1_7_7_8 y$RMAX$next)))
(assert (= y$w$2$next_op (Concat_32_1_31 y$55 y$n0s31)))
(assert (= y$59 (not (= y$n1s32 y$w$2$next_op))))
(assert (= y$60 (Extract_1_7_7_8 y$RMIN$next)))
(assert (= y$w$4$next_op (Concat_32_1_31 y$60 y$n0s31)))
(assert (= y$64 (= y$n1s32 y$w$4$next_op)))
(assert (= y$prop0$next_op (or y$59 y$64)))
(assert (= y$67 (= y$prop$next y$prop0$next_op)))
(assert (= y$prop$next (not y$54)))
(assert (= y$70 (and y$prop y$47 y$29 y$67 y$54)))
(assert y$70)
(check-sat)
(exit)

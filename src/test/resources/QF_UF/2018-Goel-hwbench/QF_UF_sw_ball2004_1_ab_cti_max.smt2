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

id: sw_ball2004_1
query-maker: "Yices 2"
query-time: 0.135000 ms
query-class: abstract
query-category: oneshot
query-type: cti
status: sat
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")

;
(set-info :status sat)
(declare-sort utt$3 0)
(declare-fun Le_1_3_3 (utt$3 utt$3 ) Bool)
(declare-fun y$114 () Bool)
(declare-fun y$115 () Bool)
(declare-fun y$117 () Bool)
(declare-fun y$127 () Bool)
(declare-fun y$128 () Bool)
(declare-fun y$129 () Bool)
(declare-fun y$13 () Bool)
(declare-fun y$130 () Bool)
(declare-fun y$131 () Bool)
(declare-fun y$132 () Bool)
(declare-fun y$133 () Bool)
(declare-fun y$134 () Bool)
(declare-fun y$135 () Bool)
(declare-fun y$16 () Bool)
(declare-fun y$19 () Bool)
(declare-fun y$2 () Bool)
(declare-fun y$24 () Bool)
(declare-fun y$32 () Bool)
(declare-fun y$4 () Bool)
(declare-fun y$40 () Bool)
(declare-fun y$44 () Bool)
(declare-fun y$51 () Bool)
(declare-fun y$53 () Bool)
(declare-fun y$58 () Bool)
(declare-fun y$6 () Bool)
(declare-fun y$69 () Bool)
(declare-fun y$79 () Bool)
(declare-fun y$8 () Bool)
(declare-fun y$L0 () Bool)
(declare-fun y$L0$next () Bool)
(declare-fun y$L0$next_rhs () Bool)
(declare-fun y$L0$next_rhs_op () Bool)
(declare-fun y$L1 () Bool)
(declare-fun y$L1$next () Bool)
(declare-fun y$L1$next_rhs () Bool)
(declare-fun y$L1$next_rhs_op () Bool)
(declare-fun y$L2 () Bool)
(declare-fun y$L2$next () Bool)
(declare-fun y$L2$next_rhs () Bool)
(declare-fun y$L2$next_rhs_op () Bool)
(declare-fun y$L3 () Bool)
(declare-fun y$L3$next () Bool)
(declare-fun y$L3$next_rhs () Bool)
(declare-fun y$L3$next_rhs_op () Bool)
(declare-fun y$L4 () Bool)
(declare-fun y$L4$next () Bool)
(declare-fun y$L4$next_rhs () Bool)
(declare-fun y$L4$next_rhs_op () Bool)
(declare-fun y$LoneHot () Bool)
(declare-fun y$LoneHot$next () Bool)
(declare-fun y$LoneHot$next_rhs () Bool)
(declare-fun y$LoneHot$next_rhs_op () Bool)
(declare-fun y$X () utt$3)
(declare-fun y$X$next () utt$3)
(declare-fun y$Y () utt$3)
(declare-fun y$Y$next () utt$3)
(declare-fun y$Z () utt$3)
(declare-fun y$Z$next () utt$3)
(declare-fun y$n0s1 () Bool)
(declare-fun y$prop () Bool)
(declare-fun y$prop$next () Bool)
(declare-fun y$s$10 () Bool)
(declare-fun y$s$10_op () Bool)
(declare-fun y$s$11 () Bool)
(declare-fun y$s$11_op () Bool)
(declare-fun y$s$12 () Bool)
(declare-fun y$s$12_op () Bool)
(declare-fun y$s$13 () Bool)
(declare-fun y$s$13_op () Bool)
(declare-fun y$s$15 () Bool)
(declare-fun y$s$15_op () Bool)
(declare-fun y$s$16 () Bool)
(declare-fun y$s$16_op () Bool)
(declare-fun y$s$17 () Bool)
(declare-fun y$s$17_op () Bool)
(declare-fun y$s$20 () Bool)
(declare-fun y$s$20_op () Bool)
(declare-fun y$s$21 () Bool)
(declare-fun y$s$21_op () Bool)
(declare-fun y$s$22 () Bool)
(declare-fun y$s$22_op () Bool)
(declare-fun y$s$23 () Bool)
(declare-fun y$s$23_op () Bool)
(declare-fun y$s$24 () Bool)
(declare-fun y$s$24_op () Bool)
(declare-fun y$s$25 () Bool)
(declare-fun y$s$25_op () Bool)
(declare-fun y$s$26 () Bool)
(declare-fun y$s$26_op () Bool)
(declare-fun y$s$27 () Bool)
(declare-fun y$s$27_op () Bool)
(declare-fun y$s$28 () Bool)
(declare-fun y$s$28_op () Bool)
(declare-fun y$s$29 () Bool)
(declare-fun y$s$29_op () Bool)
(declare-fun y$s$30 () Bool)
(declare-fun y$s$30_op () Bool)
(declare-fun y$s$31 () Bool)
(declare-fun y$s$31_op () Bool)
(declare-fun y$s$55 () Bool)
(declare-fun y$s$55_op () Bool)
(declare-fun y$s$56 () Bool)
(declare-fun y$s$56_op () Bool)
(declare-fun y$s$57 () Bool)
(declare-fun y$s$57_op () Bool)
(declare-fun y$s$58 () Bool)
(declare-fun y$s$58_op () Bool)
(declare-fun y$s$59 () Bool)
(declare-fun y$s$59_op () Bool)
(declare-fun y$s$6 () Bool)
(declare-fun y$s$60 () Bool)
(declare-fun y$s$60_op () Bool)
(declare-fun y$s$61 () Bool)
(declare-fun y$s$61_op () Bool)
(declare-fun y$s$65 () Bool)
(declare-fun y$s$65_op () Bool)
(declare-fun y$s$66 () Bool)
(declare-fun y$s$66_op () Bool)
(declare-fun y$s$67 () Bool)
(declare-fun y$s$67_op () Bool)
(declare-fun y$s$6_op () Bool)
(declare-fun y$s$7 () Bool)
(declare-fun y$s$7_op () Bool)
(declare-fun y$s$8 () Bool)
(declare-fun y$s$8_op () Bool)
(declare-fun y$s$9 () Bool)
(declare-fun y$s$9_op () Bool)
(assert (= y$L3 (not y$6)))
(assert (= y$117 (= y$6 y$prop)))
(assert (= y$13 (= y$Y$next y$Y)))
(assert (= y$16 (= y$X$next y$X)))
(assert (= y$19 (= y$Z$next y$Z)))
(assert (= y$L0$next_rhs_op (and y$L0 (not y$LoneHot))))
(assert (= y$24 (= y$L0$next y$L0$next_rhs_op)))
(assert (= y$s$65_op (Le_1_3_3 y$X y$Y)))
(assert (= y$s$26_op (and y$L0 y$s$65_op)))
(assert (= y$L1$next_rhs_op (ite y$LoneHot y$s$26_op y$L1)))
(assert (= y$32 (= y$L1$next y$L1$next_rhs_op)))
(assert (= y$s$66_op (Le_1_3_3 y$Y y$Z)))
(assert (= y$s$27_op (and y$L1 y$s$66_op)))
(assert (= y$L2$next_rhs_op (ite y$LoneHot y$s$27_op y$L2)))
(assert (= y$40 (= y$L2$next y$L2$next_rhs_op)))
(assert (= y$s$67_op (Le_1_3_3 y$X y$Z)))
(assert (= y$s$67_op (not y$44)))
(assert (= y$s$28_op (and y$L2 y$44)))
(assert (= y$s$58_op (or y$L3 y$s$28_op)))
(assert (= y$L3$next_rhs_op (ite y$LoneHot y$s$58_op y$L3)))
(assert (= y$51 (= y$L3$next y$L3$next_rhs_op)))
(assert (= y$s$65_op (not y$53)))
(assert (= y$s$29_op (and y$L0 y$53)))
(assert (= y$s$59_op (or y$L4 y$s$29_op)))
(assert (= y$s$66_op (not y$58)))
(assert (= y$s$30_op (and y$L1 y$58)))
(assert (= y$s$60_op (or y$s$59_op y$s$30_op)))
(assert (= y$s$31_op (and y$L2 y$s$67_op)))
(assert (= y$s$61_op (or y$s$60_op y$s$31_op)))
(assert (= y$L4$next_rhs_op (ite y$LoneHot y$s$61_op y$L4)))
(assert (= y$69 (= y$L4$next y$L4$next_rhs_op)))
(assert (= y$L1 (not y$2)))
(assert (= y$s$6_op (and y$L0 y$2)))
(assert (= y$L2 (not y$4)))
(assert (= y$s$7_op (and y$4 y$s$6_op)))
(assert (= y$s$8_op (and y$6 y$s$7_op)))
(assert (= y$L4 (not y$8)))
(assert (= y$s$9_op (and y$8 y$s$8_op)))
(assert (= y$L0 (not y$79)))
(assert (= y$s$10_op (and y$L1 y$79)))
(assert (= y$s$11_op (and y$4 y$s$10_op)))
(assert (= y$s$12_op (and y$6 y$s$11_op)))
(assert (= y$s$13_op (and y$8 y$s$12_op)))
(assert (= y$s$55_op (or y$s$9_op y$s$13_op)))
(assert (= y$s$22_op (and y$2 y$79)))
(assert (= y$s$15_op (and y$L2 y$s$22_op)))
(assert (= y$s$16_op (and y$6 y$s$15_op)))
(assert (= y$s$17_op (and y$8 y$s$16_op)))
(assert (= y$s$56_op (or y$s$55_op y$s$17_op)))
(assert (= y$s$23_op (and y$4 y$s$22_op)))
(assert (= y$s$20_op (and y$L3 y$s$23_op)))
(assert (= y$s$21_op (and y$8 y$s$20_op)))
(assert (= y$s$57_op (or y$s$56_op y$s$21_op)))
(assert (= y$s$24_op (and y$6 y$s$23_op)))
(assert (= y$s$25_op (and y$L4 y$s$24_op)))
(assert (= y$LoneHot$next_rhs_op (or y$s$57_op y$s$25_op)))
(assert (= y$114 (= y$LoneHot$next y$LoneHot$next_rhs_op)))
(assert (= y$115 (and y$13 y$16 y$19 y$24 y$32 y$40 y$51 y$69 y$114)))
(assert (= y$L3$next (not y$129)))
(assert (= y$130 (= y$prop$next y$129)))
(assert (= y$prop$next (not y$128)))
(assert (= y$133 (and y$prop y$117 y$115 y$130 y$128)))
(assert y$133)
(check-sat)
(exit)

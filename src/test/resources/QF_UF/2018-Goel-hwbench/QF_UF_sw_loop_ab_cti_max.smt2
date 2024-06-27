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

id: sw_loop
query-maker: "Yices 2"
query-time: 0.294000 ms
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
(declare-fun Add_3_3_3 (utt$3 utt$3 ) utt$3)
(declare-fun Le_1_3_3 (utt$3 utt$3 ) Bool)
(declare-fun p$0 () Bool)
(declare-fun p$1 () Bool)
(declare-fun p$2 () Bool)
(declare-fun p$3 () Bool)
(declare-fun p$4 () Bool)
(declare-fun y$10 () Bool)
(declare-fun y$12 () Bool)
(declare-fun y$16 () Bool)
(declare-fun y$164 () Bool)
(declare-fun y$165 () Bool)
(declare-fun y$167 () Bool)
(declare-fun y$174 () Bool)
(declare-fun y$175 () Bool)
(declare-fun y$176 () Bool)
(declare-fun y$177 () Bool)
(declare-fun y$178 () Bool)
(declare-fun y$179 () Bool)
(declare-fun y$180 () Bool)
(declare-fun y$181 () Bool)
(declare-fun y$182 () Bool)
(declare-fun y$183 () Bool)
(declare-fun y$191 () Bool)
(declare-fun y$193 () Bool)
(declare-fun y$195 () Bool)
(declare-fun y$196 () Bool)
(declare-fun y$2 () Bool)
(declare-fun y$200 () Bool)
(declare-fun y$201 () Bool)
(declare-fun y$211 () Bool)
(declare-fun y$212 () Bool)
(declare-fun y$213 () Bool)
(declare-fun y$216 () Bool)
(declare-fun y$217 () Bool)
(declare-fun y$219 () Bool)
(declare-fun y$224 () Bool)
(declare-fun y$225 () Bool)
(declare-fun y$226 () Bool)
(declare-fun y$227 () Bool)
(declare-fun y$228 () Bool)
(declare-fun y$229 () Bool)
(declare-fun y$230 () Bool)
(declare-fun y$31 () Bool)
(declare-fun y$36 () Bool)
(declare-fun y$4 () Bool)
(declare-fun y$47 () Bool)
(declare-fun y$53 () Bool)
(declare-fun y$57 () Bool)
(declare-fun y$59 () Bool)
(declare-fun y$6 () Bool)
(declare-fun y$64 () Bool)
(declare-fun y$72 () Bool)
(declare-fun y$74 () Bool)
(declare-fun y$8 () Bool)
(declare-fun y$85 () Bool)
(declare-fun y$99 () Bool)
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
(declare-fun y$L5 () Bool)
(declare-fun y$L5$next () Bool)
(declare-fun y$L5$next_rhs () Bool)
(declare-fun y$L5$next_rhs_op () Bool)
(declare-fun y$L6 () Bool)
(declare-fun y$L6$next () Bool)
(declare-fun y$L6$next_rhs () Bool)
(declare-fun y$L6$next_rhs_op () Bool)
(declare-fun y$LoneHot () Bool)
(declare-fun y$LoneHot$next () Bool)
(declare-fun y$LoneHot$next_rhs () Bool)
(declare-fun y$LoneHot$next_rhs_op () Bool)
(declare-fun y$X () utt$3)
(declare-fun y$X$next () utt$3)
(declare-fun y$X$next_rhs () utt$3)
(declare-fun y$X$next_rhs_op () utt$3)
(declare-fun y$n0s1 () Bool)
(declare-fun y$n0s3 () utt$3)
(declare-fun y$n3s3 () utt$3)
(declare-fun y$n5s3 () utt$3)
(declare-fun y$n7s3 () utt$3)
(declare-fun y$prop () Bool)
(declare-fun y$prop$next () Bool)
(declare-fun y$s$10 () Bool)
(declare-fun y$s$103 () Bool)
(declare-fun y$s$103_op () Bool)
(declare-fun y$s$104 () Bool)
(declare-fun y$s$104_op () Bool)
(declare-fun y$s$105 () Bool)
(declare-fun y$s$105_op () Bool)
(declare-fun y$s$106 () Bool)
(declare-fun y$s$106_op () Bool)
(declare-fun y$s$107 () Bool)
(declare-fun y$s$107_op () Bool)
(declare-fun y$s$108 () Bool)
(declare-fun y$s$108_op () Bool)
(declare-fun y$s$109 () Bool)
(declare-fun y$s$109_op () Bool)
(declare-fun y$s$10_op () Bool)
(declare-fun y$s$11 () Bool)
(declare-fun y$s$110 () Bool)
(declare-fun y$s$110_op () Bool)
(declare-fun y$s$111 () Bool)
(declare-fun y$s$111_op () Bool)
(declare-fun y$s$115 () Bool)
(declare-fun y$s$115_op () Bool)
(declare-fun y$s$118 () Bool)
(declare-fun y$s$118$next () Bool)
(declare-fun y$s$118$next_op () Bool)
(declare-fun y$s$118_op () Bool)
(declare-fun y$s$119 () utt$3)
(declare-fun y$s$119_op () utt$3)
(declare-fun y$s$11_op () Bool)
(declare-fun y$s$12 () Bool)
(declare-fun y$s$120 () utt$3)
(declare-fun y$s$120_op () utt$3)
(declare-fun y$s$12_op () Bool)
(declare-fun y$s$13 () Bool)
(declare-fun y$s$13_op () Bool)
(declare-fun y$s$14 () Bool)
(declare-fun y$s$14_op () Bool)
(declare-fun y$s$15 () Bool)
(declare-fun y$s$15_op () Bool)
(declare-fun y$s$16 () Bool)
(declare-fun y$s$16_op () Bool)
(declare-fun y$s$17 () Bool)
(declare-fun y$s$17_op () Bool)
(declare-fun y$s$18 () Bool)
(declare-fun y$s$18_op () Bool)
(declare-fun y$s$19 () Bool)
(declare-fun y$s$19_op () Bool)
(declare-fun y$s$20 () Bool)
(declare-fun y$s$20_op () Bool)
(declare-fun y$s$21 () Bool)
(declare-fun y$s$21_op () Bool)
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
(declare-fun y$s$30 () Bool)
(declare-fun y$s$30_op () Bool)
(declare-fun y$s$31 () Bool)
(declare-fun y$s$31_op () Bool)
(declare-fun y$s$32 () Bool)
(declare-fun y$s$32_op () Bool)
(declare-fun y$s$33 () Bool)
(declare-fun y$s$33_op () Bool)
(declare-fun y$s$37 () Bool)
(declare-fun y$s$37_op () Bool)
(declare-fun y$s$38 () Bool)
(declare-fun y$s$38_op () Bool)
(declare-fun y$s$39 () Bool)
(declare-fun y$s$39_op () Bool)
(declare-fun y$s$44 () Bool)
(declare-fun y$s$44_op () Bool)
(declare-fun y$s$45 () Bool)
(declare-fun y$s$45_op () Bool)
(declare-fun y$s$46 () Bool)
(declare-fun y$s$46_op () Bool)
(declare-fun y$s$47 () Bool)
(declare-fun y$s$47_op () Bool)
(declare-fun y$s$48 () Bool)
(declare-fun y$s$48_op () Bool)
(declare-fun y$s$49 () Bool)
(declare-fun y$s$49_op () Bool)
(declare-fun y$s$50 () Bool)
(declare-fun y$s$50_op () Bool)
(declare-fun y$s$51 () Bool)
(declare-fun y$s$51_op () Bool)
(declare-fun y$s$52 () Bool)
(declare-fun y$s$52_op () Bool)
(declare-fun y$s$53 () Bool)
(declare-fun y$s$53_op () Bool)
(declare-fun y$s$54 () Bool)
(declare-fun y$s$54_op () Bool)
(declare-fun y$s$55 () Bool)
(declare-fun y$s$55_op () Bool)
(declare-fun y$s$56 () Bool)
(declare-fun y$s$56_op () Bool)
(declare-fun y$s$57 () Bool)
(declare-fun y$s$57_op () Bool)
(declare-fun y$s$9 () utt$3)
(declare-fun y$s$9_op () utt$3)
(assert (distinct y$n0s3 y$n7s3 y$n3s3 y$n5s3))
(assert (= y$L6 (not y$12)))
(assert (= y$167 (= y$12 y$prop)))
(assert (= y$s$118_op (Le_1_3_3 y$X y$n7s3)))
(assert (= y$s$9_op (Add_3_3_3 y$X y$n3s3)))
(assert (= y$s$119_op (ite y$s$118_op y$s$9_op y$X)))
(assert (= y$s$120_op (ite y$L1 y$s$119_op y$X)))
(assert (= y$X$next_rhs_op (ite y$LoneHot y$s$120_op y$X)))
(assert (= y$31 (= y$X$next y$X$next_rhs_op)))
(assert (= y$L0$next_rhs_op (and y$L0 (not y$LoneHot))))
(assert (= y$36 (= y$L0$next y$L0$next_rhs_op)))
(assert (= y$s$115_op (Le_1_3_3 y$X y$n5s3)))
(assert (= y$s$52_op (and y$L3 y$s$115_op)))
(assert (= y$s$108_op (or y$L0 y$s$52_op)))
(assert (= y$L1$next_rhs_op (ite y$LoneHot y$s$108_op y$L1)))
(assert (= y$47 (= y$L1$next y$L1$next_rhs_op)))
(assert (= y$s$53_op (and y$L1 y$s$118_op)))
(assert (= y$L2$next_rhs_op (ite y$LoneHot y$s$53_op y$L2)))
(assert (= y$53 (= y$L2$next y$L2$next_rhs_op)))
(assert (= y$L3$next_rhs_op (ite y$LoneHot y$L2 y$L3)))
(assert (= y$57 (= y$L3$next y$L3$next_rhs_op)))
(assert (= y$s$115_op (not y$59)))
(assert (= y$s$54_op (and y$L3 y$59)))
(assert (= y$L4$next_rhs_op (ite y$LoneHot y$s$54_op y$L4)))
(assert (= y$64 (= y$L4$next y$L4$next_rhs_op)))
(assert (= y$s$55_op (and y$L4 y$s$118_op)))
(assert (= y$s$109_op (or y$L5 y$s$55_op)))
(assert (= y$L5$next_rhs_op (ite y$LoneHot y$s$109_op y$L5)))
(assert (= y$72 (= y$L5$next y$L5$next_rhs_op)))
(assert (= y$s$118_op (not y$74)))
(assert (= y$s$56_op (and y$L1 y$74)))
(assert (= y$s$110_op (or y$L6 y$s$56_op)))
(assert (= y$s$57_op (and y$L4 y$74)))
(assert (= y$s$111_op (or y$s$110_op y$s$57_op)))
(assert (= y$L6$next_rhs_op (ite y$LoneHot y$s$111_op y$L6)))
(assert (= y$85 (= y$L6$next y$L6$next_rhs_op)))
(assert (= y$L1 (not y$2)))
(assert (= y$s$12_op (and y$L0 y$2)))
(assert (= y$L2 (not y$4)))
(assert (= y$s$13_op (and y$4 y$s$12_op)))
(assert (= y$L3 (not y$6)))
(assert (= y$s$14_op (and y$6 y$s$13_op)))
(assert (= y$L4 (not y$8)))
(assert (= y$s$15_op (and y$8 y$s$14_op)))
(assert (= y$L5 (not y$10)))
(assert (= y$s$10_op (and y$10 y$s$15_op)))
(assert (= y$s$11_op (and y$12 y$s$10_op)))
(assert (= y$L0 (not y$99)))
(assert (= y$s$16_op (and y$L1 y$99)))
(assert (= y$s$17_op (and y$4 y$s$16_op)))
(assert (= y$s$18_op (and y$6 y$s$17_op)))
(assert (= y$s$19_op (and y$8 y$s$18_op)))
(assert (= y$s$20_op (and y$10 y$s$19_op)))
(assert (= y$s$21_op (and y$12 y$s$20_op)))
(assert (= y$s$103_op (or y$s$11_op y$s$21_op)))
(assert (= y$s$46_op (and y$2 y$99)))
(assert (= y$s$23_op (and y$L2 y$s$46_op)))
(assert (= y$s$24_op (and y$6 y$s$23_op)))
(assert (= y$s$25_op (and y$8 y$s$24_op)))
(assert (= y$s$26_op (and y$10 y$s$25_op)))
(assert (= y$s$27_op (and y$12 y$s$26_op)))
(assert (= y$s$104_op (or y$s$103_op y$s$27_op)))
(assert (= y$s$47_op (and y$4 y$s$46_op)))
(assert (= y$s$30_op (and y$L3 y$s$47_op)))
(assert (= y$s$31_op (and y$8 y$s$30_op)))
(assert (= y$s$32_op (and y$10 y$s$31_op)))
(assert (= y$s$33_op (and y$12 y$s$32_op)))
(assert (= y$s$105_op (or y$s$104_op y$s$33_op)))
(assert (= y$s$48_op (and y$6 y$s$47_op)))
(assert (= y$s$37_op (and y$L4 y$s$48_op)))
(assert (= y$s$38_op (and y$10 y$s$37_op)))
(assert (= y$s$39_op (and y$12 y$s$38_op)))
(assert (= y$s$106_op (or y$s$105_op y$s$39_op)))
(assert (= y$s$49_op (and y$8 y$s$48_op)))
(assert (= y$s$44_op (and y$L5 y$s$49_op)))
(assert (= y$s$45_op (and y$12 y$s$44_op)))
(assert (= y$s$107_op (or y$s$106_op y$s$45_op)))
(assert (= y$s$50_op (and y$10 y$s$49_op)))
(assert (= y$s$51_op (and y$L6 y$s$50_op)))
(assert (= y$LoneHot$next_rhs_op (or y$s$107_op y$s$51_op)))
(assert (= y$164 (= y$LoneHot$next y$LoneHot$next_rhs_op)))
(assert (= y$165 (and y$31 y$36 y$47 y$53 y$57 y$64 y$72 y$85 y$164)))
(assert (= y$L6$next (not y$176)))
(assert (= y$177 (= y$prop$next y$176)))
(assert (= y$prop$next (not y$175)))
(assert (= y$s$118_op (not y$183)))
(assert (= y$191 (not (= y$n7s3 y$X))))
(assert (= y$211 (and y$183 y$191)))
(assert (= y$211 (not y$213)))
(assert (= y$s$118$next_op (Le_1_3_3 y$X$next y$n7s3)))
(assert (= y$s$118$next_op (not y$193)))
(assert (= y$196 (not (= y$n7s3 y$X$next))))
(assert (= y$212 (and y$193 y$196)))
(assert (= y$212 (not y$216)))
(assert (= y$227 (and y$prop y$167 y$165 y$177 y$175 y$213 y$216)))
(assert y$227)
(assert (distinct y$n0s3 y$n7s3 y$n3s3 y$n5s3))
(check-sat)
(exit)

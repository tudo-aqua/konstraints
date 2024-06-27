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

id: h_b02
query-maker: "Yices 2"
query-time: 1.729000 ms
query-class: abstract
query-category: incremental
query-type: br
status: sat
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")

;
(set-info :status sat)
(declare-sort utt$3 0)
(declare-sort utt$29 0)
(declare-sort utt$31 0)
(declare-sort utt$32 0)
(declare-fun Concat_32_1_31 (Bool utt$31 ) utt$32)
(declare-fun Concat_32_3_29 (utt$3 utt$29 ) utt$32)
(declare-fun y$1 () Bool)
(declare-fun y$10 () Bool)
(declare-fun y$102 () Bool)
(declare-fun y$103 () Bool)
(declare-fun y$115 () Bool)
(declare-fun y$116 () Bool)
(declare-fun y$117 () Bool)
(declare-fun y$118 () Bool)
(declare-fun y$119 () Bool)
(declare-fun y$12 () Bool)
(declare-fun y$120 () Bool)
(declare-fun y$127 () Bool)
(declare-fun y$128 () Bool)
(declare-fun y$129 () Bool)
(declare-fun y$130 () Bool)
(declare-fun y$131 () Bool)
(declare-fun y$133 () Bool)
(declare-fun y$137 () Bool)
(declare-fun y$14 () Bool)
(declare-fun y$141 () Bool)
(declare-fun y$153 () Bool)
(declare-fun y$157 () Bool)
(declare-fun y$162 () Bool)
(declare-fun y$164 () Bool)
(declare-fun y$165 () Bool)
(declare-fun y$166 () Bool)
(declare-fun y$167 () Bool)
(declare-fun y$169 () Bool)
(declare-fun y$172 () Bool)
(declare-fun y$177 () Bool)
(declare-fun y$178 () Bool)
(declare-fun y$180 () Bool)
(declare-fun y$182 () Bool)
(declare-fun y$183 () Bool)
(declare-fun y$186 () Bool)
(declare-fun y$190 () Bool)
(declare-fun y$191 () Bool)
(declare-fun y$192 () Bool)
(declare-fun y$195 () Bool)
(declare-fun y$26 () Bool)
(declare-fun y$28 () Bool)
(declare-fun y$37 () Bool)
(declare-fun y$4 () Bool)
(declare-fun y$44 () Bool)
(declare-fun y$71 () Bool)
(declare-fun y$72 () Bool)
(declare-fun y$77 () Bool)
(declare-fun y$79 () Bool)
(declare-fun y$8 () Bool)
(declare-fun y$83 () Bool)
(declare-fun y$86 () Bool)
(declare-fun y$92 () Bool)
(declare-fun y$93 () Bool)
(declare-fun y$96 () Bool)
(declare-fun y$99 () Bool)
(declare-fun y$LINEA () Bool)
(declare-fun y$LINEA$next () Bool)
(declare-fun y$U () Bool)
(declare-fun y$U$next () Bool)
(declare-fun y$U$next_rhs () Bool)
(declare-fun y$U$next_rhs_op () Bool)
(declare-fun y$n0s1 () Bool)
(declare-fun y$n0s29 () utt$29)
(declare-fun y$n0s3 () utt$3)
(declare-fun y$n0s31 () utt$31)
(declare-fun y$n0s32 () utt$32)
(declare-fun y$n1s1 () Bool)
(declare-fun y$n1s3 () utt$3)
(declare-fun y$n1s32 () utt$32)
(declare-fun y$n2s3 () utt$3)
(declare-fun y$n3s3 () utt$3)
(declare-fun y$n4s3 () utt$3)
(declare-fun y$n5s3 () utt$3)
(declare-fun y$n6s3 () utt$3)
(declare-fun y$prop () Bool)
(declare-fun y$prop$next () Bool)
(declare-fun y$prop0 () Bool)
(declare-fun y$prop0$next () Bool)
(declare-fun y$prop0$next_op () Bool)
(declare-fun y$prop0_op () Bool)
(declare-fun y$s$10 () Bool)
(declare-fun y$s$10_op () Bool)
(declare-fun y$s$11 () utt$3)
(declare-fun y$s$11_op () utt$3)
(declare-fun y$s$13 () Bool)
(declare-fun y$s$13_op () Bool)
(declare-fun y$s$14 () Bool)
(declare-fun y$s$14_op () Bool)
(declare-fun y$s$16 () Bool)
(declare-fun y$s$16_op () Bool)
(declare-fun y$s$17 () Bool)
(declare-fun y$s$17_op () Bool)
(declare-fun y$s$18 () utt$3)
(declare-fun y$s$18_op () utt$3)
(declare-fun y$s$19 () utt$3)
(declare-fun y$s$19_op () utt$3)
(declare-fun y$s$2 () utt$3)
(declare-fun y$s$20 () utt$3)
(declare-fun y$s$20_op () utt$3)
(declare-fun y$s$21 () utt$3)
(declare-fun y$s$21_op () utt$3)
(declare-fun y$s$22 () utt$3)
(declare-fun y$s$22_op () utt$3)
(declare-fun y$s$29 () utt$3)
(declare-fun y$s$29_op () utt$3)
(declare-fun y$s$2_op () utt$3)
(declare-fun y$s$3 () utt$3)
(declare-fun y$s$31 () utt$3)
(declare-fun y$s$31_op () utt$3)
(declare-fun y$s$33 () utt$3)
(declare-fun y$s$33_op () utt$3)
(declare-fun y$s$3_op () utt$3)
(declare-fun y$s$4 () utt$3)
(declare-fun y$s$4_op () utt$3)
(declare-fun y$s$5 () Bool)
(declare-fun y$s$5_op () Bool)
(declare-fun y$s$7 () Bool)
(declare-fun y$s$7_op () Bool)
(declare-fun y$stato () utt$3)
(declare-fun y$stato$next () utt$3)
(declare-fun y$stato$next_rhs () utt$3)
(declare-fun y$stato$next_rhs_op () utt$3)
(declare-fun y$w$1 () utt$32)
(declare-fun y$w$1$next () utt$32)
(declare-fun y$w$1$next_op () utt$32)
(declare-fun y$w$1_op () utt$32)
(declare-fun y$w$2 () utt$32)
(declare-fun y$w$2$next () utt$32)
(declare-fun y$w$2$next_op () utt$32)
(declare-fun y$w$2_op () utt$32)
(declare-fun y$w$3 () utt$32)
(declare-fun y$w$3$next () utt$32)
(declare-fun y$w$3$next_op () utt$32)
(declare-fun y$w$3_op () utt$32)
(assert (distinct y$n0s3 y$n3s3 y$n4s3 y$n5s3 y$n6s3 y$n1s3 y$n2s3))
(assert (not (= y$n0s32 y$n1s32)))
(assert (= (not (= y$n4s3 y$stato)) y$164))
(assert (= y$w$1_op (Concat_32_1_31 y$U y$n0s31)))
(assert (= y$79 (not (= y$n1s32 y$w$1_op))))
(assert (= y$w$2_op (Concat_32_3_29 y$stato y$n0s29)))
(assert (= y$83 (= y$n1s32 y$w$2_op)))
(assert (= y$prop0_op (or y$79 y$83)))
(assert (= y$86 (= y$prop y$prop0_op)))
(assert (= y$w$1$next_op (Concat_32_1_31 y$U$next y$n0s31)))
(assert (= (not (= y$n1s32 y$w$1$next_op)) y$96))
(assert (= y$w$2$next_op (Concat_32_3_29 y$stato$next y$n0s29)))
(assert (= y$99 (= y$n1s32 y$w$2$next_op)))
(assert (= y$prop0$next_op (or y$96 y$99)))
(assert (= y$102 (= y$prop$next y$prop0$next_op)))
(assert (= y$116 (= y$n1s32 y$w$1$next_op)))
(assert (= y$U$next (not y$117)))
(assert (= y$118 (and y$116 y$117)))
(assert (= y$118 (not y$120)))
(assert (= (= y$n1s32 y$w$1_op) y$77))
(assert (= y$U (not y$1)))
(assert (= y$115 (and y$1 y$77)))
(assert (= y$115 (not y$119)))
(assert (= y$166 (and y$prop y$86 y$120 y$119 y$102 y$164)))
(assert y$166)
(assert (distinct y$n0s3 y$n3s3 y$n4s3 y$n5s3 y$n6s3 y$n1s3 y$n2s3))
(assert (not (= y$n0s32 y$n1s32)))
(assert (= y$8 (= y$n3s3 y$stato)))
(assert (= y$10 (= y$n4s3 y$stato)))
(assert (= y$12 (= y$n5s3 y$stato)))
(assert (= y$14 (= y$n6s3 y$stato)))
(assert (= y$s$10_op (or y$12 y$14)))
(assert (= y$s$5_op (or y$8 y$10 y$s$10_op)))
(assert (= y$w$3_op (Concat_32_1_31 y$LINEA y$n0s31)))
(assert (= y$44 (= y$n0s32 y$w$3_op)))
(assert (= y$s$29_op (ite y$44 y$n4s3 y$n0s3)))
(assert (= y$s$4_op (ite y$14 y$s$29_op y$n0s3)))
(assert (= y$s$18_op (ite y$14 y$s$4_op y$n6s3)))
(assert (= y$s$19_op (ite y$10 y$n1s3 y$n4s3)))
(assert (= y$s$20_op (ite y$s$10_op y$s$18_op y$s$19_op)))
(assert (= y$26 (= y$n1s3 y$stato)))
(assert (= y$28 (= y$n2s3 y$stato)))
(assert (= y$s$7_op (or y$26 y$28)))
(assert (= y$s$31_op (ite y$44 y$n3s3 y$n6s3)))
(assert (= y$s$3_op (ite y$28 y$s$31_op y$n0s3)))
(assert (= y$s$33_op (ite y$44 y$n2s3 y$n5s3)))
(assert (= y$s$2_op (ite y$26 y$s$33_op y$n0s3)))
(assert (= y$s$21_op (ite y$28 y$s$3_op y$s$2_op)))
(assert (= y$4 (= y$n0s3 y$stato)))
(assert (= y$s$22_op (ite y$4 y$n1s3 y$stato)))
(assert (= y$s$11_op (ite y$s$7_op y$s$21_op y$s$22_op)))
(assert (= y$stato$next_rhs_op (ite y$s$5_op y$s$20_op y$s$11_op)))
(assert (= y$71 (= y$stato$next y$stato$next_rhs_op)))
(assert y$71)
(assert (= y$169 (= y$n3s3 y$stato$next)))
(assert y$169)
(check-sat)
(exit)

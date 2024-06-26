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

id: sw_ball2001
query-maker: "Yices 2"
query-time: 0.460000 ms
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
(declare-fun y$10 () Bool)
(declare-fun y$106 () Bool)
(declare-fun y$108 () Bool)
(declare-fun y$115 () Bool)
(declare-fun y$12 () Bool)
(declare-fun y$133 () Bool)
(declare-fun y$14 () Bool)
(declare-fun y$16 () Bool)
(declare-fun y$2 () Bool)
(declare-fun y$21 () Bool)
(declare-fun y$236 () Bool)
(declare-fun y$237 () Bool)
(declare-fun y$239 () Bool)
(declare-fun y$25 () Bool)
(declare-fun y$250 () Bool)
(declare-fun y$251 () Bool)
(declare-fun y$252 () Bool)
(declare-fun y$253 () Bool)
(declare-fun y$254 () Bool)
(declare-fun y$255 () Bool)
(declare-fun y$256 () Bool)
(declare-fun y$257 () Bool)
(declare-fun y$258 () Bool)
(declare-fun y$38 () Bool)
(declare-fun y$4 () Bool)
(declare-fun y$40 () Bool)
(declare-fun y$52 () Bool)
(declare-fun y$54 () Bool)
(declare-fun y$59 () Bool)
(declare-fun y$6 () Bool)
(declare-fun y$67 () Bool)
(declare-fun y$71 () Bool)
(declare-fun y$77 () Bool)
(declare-fun y$8 () Bool)
(declare-fun y$81 () Bool)
(declare-fun y$83 () Bool)
(declare-fun y$90 () Bool)
(declare-fun y$92 () Bool)
(declare-fun y$97 () Bool)
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
(declare-fun y$L7 () Bool)
(declare-fun y$L7$next () Bool)
(declare-fun y$L7$next_rhs () Bool)
(declare-fun y$L7$next_rhs_op () Bool)
(declare-fun y$L8 () Bool)
(declare-fun y$L8$next () Bool)
(declare-fun y$L8$next_rhs () Bool)
(declare-fun y$L8$next_rhs_op () Bool)
(declare-fun y$LoneHot () Bool)
(declare-fun y$LoneHot$next () Bool)
(declare-fun y$LoneHot$next_rhs () Bool)
(declare-fun y$LoneHot$next_rhs_op () Bool)
(declare-fun y$W () utt$3)
(declare-fun y$W$next () utt$3)
(declare-fun y$X () utt$3)
(declare-fun y$X$next () utt$3)
(declare-fun y$X$next_rhs () utt$3)
(declare-fun y$X$next_rhs_op () utt$3)
(declare-fun y$Y () utt$3)
(declare-fun y$Y$next () utt$3)
(declare-fun y$Z () utt$3)
(declare-fun y$Z$next () utt$3)
(declare-fun y$Z$next_rhs () utt$3)
(declare-fun y$Z$next_rhs_op () utt$3)
(declare-fun y$n0s1 () Bool)
(declare-fun y$n0s3 () utt$3)
(declare-fun y$n1s3 () utt$3)
(declare-fun y$prop () Bool)
(declare-fun y$prop$next () Bool)
(declare-fun y$s$12 () utt$3)
(declare-fun y$s$12_op () utt$3)
(declare-fun y$s$16 () Bool)
(declare-fun y$s$166 () Bool)
(declare-fun y$s$166_op () Bool)
(declare-fun y$s$167 () Bool)
(declare-fun y$s$167_op () Bool)
(declare-fun y$s$168 () Bool)
(declare-fun y$s$168_op () Bool)
(declare-fun y$s$169 () Bool)
(declare-fun y$s$169_op () Bool)
(declare-fun y$s$16_op () Bool)
(declare-fun y$s$17 () Bool)
(declare-fun y$s$170 () Bool)
(declare-fun y$s$170_op () Bool)
(declare-fun y$s$171 () Bool)
(declare-fun y$s$171_op () Bool)
(declare-fun y$s$172 () Bool)
(declare-fun y$s$172_op () Bool)
(declare-fun y$s$173 () Bool)
(declare-fun y$s$173_op () Bool)
(declare-fun y$s$174 () Bool)
(declare-fun y$s$174_op () Bool)
(declare-fun y$s$175 () Bool)
(declare-fun y$s$175_op () Bool)
(declare-fun y$s$176 () Bool)
(declare-fun y$s$176_op () Bool)
(declare-fun y$s$17_op () Bool)
(declare-fun y$s$18 () Bool)
(declare-fun y$s$182 () utt$3)
(declare-fun y$s$182_op () utt$3)
(declare-fun y$s$183 () utt$3)
(declare-fun y$s$183_op () utt$3)
(declare-fun y$s$184 () utt$3)
(declare-fun y$s$184_op () utt$3)
(declare-fun y$s$185 () utt$3)
(declare-fun y$s$185_op () utt$3)
(declare-fun y$s$186 () utt$3)
(declare-fun y$s$186_op () utt$3)
(declare-fun y$s$187 () utt$3)
(declare-fun y$s$187_op () utt$3)
(declare-fun y$s$188 () utt$3)
(declare-fun y$s$188_op () utt$3)
(declare-fun y$s$18_op () Bool)
(declare-fun y$s$19 () Bool)
(declare-fun y$s$19_op () Bool)
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
(declare-fun y$s$33 () Bool)
(declare-fun y$s$33_op () Bool)
(declare-fun y$s$34 () Bool)
(declare-fun y$s$34_op () Bool)
(declare-fun y$s$35 () Bool)
(declare-fun y$s$35_op () Bool)
(declare-fun y$s$36 () Bool)
(declare-fun y$s$36_op () Bool)
(declare-fun y$s$37 () Bool)
(declare-fun y$s$37_op () Bool)
(declare-fun y$s$38 () Bool)
(declare-fun y$s$38_op () Bool)
(declare-fun y$s$39 () Bool)
(declare-fun y$s$39_op () Bool)
(declare-fun y$s$42 () Bool)
(declare-fun y$s$42_op () Bool)
(declare-fun y$s$43 () Bool)
(declare-fun y$s$43_op () Bool)
(declare-fun y$s$44 () Bool)
(declare-fun y$s$44_op () Bool)
(declare-fun y$s$45 () Bool)
(declare-fun y$s$45_op () Bool)
(declare-fun y$s$46 () Bool)
(declare-fun y$s$46_op () Bool)
(declare-fun y$s$47 () Bool)
(declare-fun y$s$47_op () Bool)
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
(declare-fun y$s$61 () Bool)
(declare-fun y$s$61_op () Bool)
(declare-fun y$s$62 () Bool)
(declare-fun y$s$62_op () Bool)
(declare-fun y$s$63 () Bool)
(declare-fun y$s$63_op () Bool)
(declare-fun y$s$69 () Bool)
(declare-fun y$s$69_op () Bool)
(declare-fun y$s$70 () Bool)
(declare-fun y$s$70_op () Bool)
(declare-fun y$s$71 () Bool)
(declare-fun y$s$71_op () Bool)
(declare-fun y$s$78 () Bool)
(declare-fun y$s$78_op () Bool)
(declare-fun y$s$79 () Bool)
(declare-fun y$s$79_op () Bool)
(declare-fun y$s$80 () Bool)
(declare-fun y$s$80_op () Bool)
(declare-fun y$s$81 () Bool)
(declare-fun y$s$81_op () Bool)
(declare-fun y$s$82 () Bool)
(declare-fun y$s$82_op () Bool)
(declare-fun y$s$83 () Bool)
(declare-fun y$s$83_op () Bool)
(declare-fun y$s$84 () Bool)
(declare-fun y$s$84_op () Bool)
(declare-fun y$s$85 () Bool)
(declare-fun y$s$85_op () Bool)
(declare-fun y$s$86 () Bool)
(declare-fun y$s$86_op () Bool)
(declare-fun y$s$87 () Bool)
(declare-fun y$s$87_op () Bool)
(declare-fun y$s$88 () Bool)
(declare-fun y$s$88_op () Bool)
(declare-fun y$s$89 () Bool)
(declare-fun y$s$89_op () Bool)
(declare-fun y$s$90 () Bool)
(declare-fun y$s$90_op () Bool)
(declare-fun y$s$91 () Bool)
(declare-fun y$s$91_op () Bool)
(declare-fun y$s$92 () Bool)
(declare-fun y$s$92_op () Bool)
(declare-fun y$s$93 () Bool)
(declare-fun y$s$93_op () Bool)
(assert (not (= y$n0s3 y$n1s3)))
(assert (= y$L7 (not y$14)))
(assert (= y$239 (= y$14 y$prop)))
(assert (= y$21 (= y$Y$next y$Y)))
(assert (= y$25 (not (= y$n0s3 y$W))))
(assert (= y$s$12_op (Add_3_3_3 y$X y$n1s3)))
(assert (= y$s$182_op (ite y$25 y$s$12_op y$X)))
(assert (= y$s$183_op (ite y$L2 y$s$182_op y$X)))
(assert (= y$s$184_op (ite y$L1 y$Y y$s$183_op)))
(assert (= y$X$next_rhs_op (ite y$LoneHot y$s$184_op y$X)))
(assert (= y$38 (= y$X$next y$X$next_rhs_op)))
(assert (= y$40 (not (= y$Y y$X))))
(assert (= y$s$185_op (ite y$40 y$n0s3 y$Z)))
(assert (= y$s$186_op (ite y$L5 y$s$185_op y$Z)))
(assert (= y$s$187_op (ite y$L3 y$n1s3 y$s$186_op)))
(assert (= y$s$188_op (ite y$L0 y$n0s3 y$s$187_op)))
(assert (= y$Z$next_rhs_op (ite y$LoneHot y$s$188_op y$Z)))
(assert (= y$52 (= y$Z$next y$Z$next_rhs_op)))
(assert (= y$54 (= y$W y$W$next)))
(assert (= y$L0$next_rhs_op (and y$L0 (not y$LoneHot))))
(assert (= y$59 (= y$L0$next y$L0$next_rhs_op)))
(assert (= y$s$88_op (and y$L5 y$40)))
(assert (= y$s$173_op (or y$L0 y$s$88_op)))
(assert (= y$L1$next_rhs_op (ite y$LoneHot y$s$173_op y$L1)))
(assert (= y$67 (= y$L1$next y$L1$next_rhs_op)))
(assert (= y$L2$next_rhs_op (ite y$LoneHot y$L1 y$L2)))
(assert (= y$71 (= y$L2$next y$L2$next_rhs_op)))
(assert (= y$s$89_op (and y$L2 y$25)))
(assert (= y$L3$next_rhs_op (ite y$LoneHot y$s$89_op y$L3)))
(assert (= y$77 (= y$L3$next y$L3$next_rhs_op)))
(assert (= y$L4$next_rhs_op (ite y$LoneHot y$L3 y$L4)))
(assert (= y$81 (= y$L4$next y$L4$next_rhs_op)))
(assert (= (= y$n0s3 y$W) y$83))
(assert (= y$s$90_op (and y$L2 y$83)))
(assert (= y$s$174_op (or y$L4 y$s$90_op)))
(assert (= y$L5$next_rhs_op (ite y$LoneHot y$s$174_op y$L5)))
(assert (= y$90 (= y$L5$next y$L5$next_rhs_op)))
(assert (= (= y$Y y$X) y$92))
(assert (= y$s$91_op (and y$L5 y$92)))
(assert (= y$L6$next_rhs_op (ite y$LoneHot y$s$91_op y$L6)))
(assert (= y$97 (= y$L6$next y$L6$next_rhs_op)))
(assert (= y$99 (not (= y$n0s3 y$Z))))
(assert (= y$s$92_op (and y$L6 y$99)))
(assert (= y$s$175_op (or y$L7 y$s$92_op)))
(assert (= y$L7$next_rhs_op (ite y$LoneHot y$s$175_op y$L7)))
(assert (= y$106 (= y$L7$next y$L7$next_rhs_op)))
(assert (= (= y$n0s3 y$Z) y$108))
(assert (= y$s$93_op (and y$L6 y$108)))
(assert (= y$s$176_op (or y$L8 y$s$93_op)))
(assert (= y$L8$next_rhs_op (ite y$LoneHot y$s$176_op y$L8)))
(assert (= y$115 (= y$L8$next y$L8$next_rhs_op)))
(assert (= y$L1 (not y$2)))
(assert (= y$s$20_op (and y$L0 y$2)))
(assert (= y$L2 (not y$4)))
(assert (= y$s$21_op (and y$4 y$s$20_op)))
(assert (= y$L3 (not y$6)))
(assert (= y$s$22_op (and y$6 y$s$21_op)))
(assert (= y$L4 (not y$8)))
(assert (= y$s$23_op (and y$8 y$s$22_op)))
(assert (= y$L5 (not y$10)))
(assert (= y$s$16_op (and y$10 y$s$23_op)))
(assert (= y$L6 (not y$12)))
(assert (= y$s$17_op (and y$12 y$s$16_op)))
(assert (= y$s$18_op (and y$14 y$s$17_op)))
(assert (= y$L8 (not y$16)))
(assert (= y$s$19_op (and y$16 y$s$18_op)))
(assert (= y$L0 (not y$133)))
(assert (= y$s$24_op (and y$L1 y$133)))
(assert (= y$s$25_op (and y$4 y$s$24_op)))
(assert (= y$s$26_op (and y$6 y$s$25_op)))
(assert (= y$s$27_op (and y$8 y$s$26_op)))
(assert (= y$s$28_op (and y$10 y$s$27_op)))
(assert (= y$s$29_op (and y$12 y$s$28_op)))
(assert (= y$s$30_op (and y$14 y$s$29_op)))
(assert (= y$s$31_op (and y$16 y$s$30_op)))
(assert (= y$s$166_op (or y$s$19_op y$s$31_op)))
(assert (= y$s$80_op (and y$2 y$133)))
(assert (= y$s$33_op (and y$L2 y$s$80_op)))
(assert (= y$s$34_op (and y$6 y$s$33_op)))
(assert (= y$s$35_op (and y$8 y$s$34_op)))
(assert (= y$s$36_op (and y$10 y$s$35_op)))
(assert (= y$s$37_op (and y$12 y$s$36_op)))
(assert (= y$s$38_op (and y$14 y$s$37_op)))
(assert (= y$s$39_op (and y$16 y$s$38_op)))
(assert (= y$s$167_op (or y$s$166_op y$s$39_op)))
(assert (= y$s$81_op (and y$4 y$s$80_op)))
(assert (= y$s$42_op (and y$L3 y$s$81_op)))
(assert (= y$s$43_op (and y$8 y$s$42_op)))
(assert (= y$s$44_op (and y$10 y$s$43_op)))
(assert (= y$s$45_op (and y$12 y$s$44_op)))
(assert (= y$s$46_op (and y$14 y$s$45_op)))
(assert (= y$s$47_op (and y$16 y$s$46_op)))
(assert (= y$s$168_op (or y$s$167_op y$s$47_op)))
(assert (= y$s$82_op (and y$6 y$s$81_op)))
(assert (= y$s$51_op (and y$L4 y$s$82_op)))
(assert (= y$s$52_op (and y$10 y$s$51_op)))
(assert (= y$s$53_op (and y$12 y$s$52_op)))
(assert (= y$s$54_op (and y$14 y$s$53_op)))
(assert (= y$s$55_op (and y$16 y$s$54_op)))
(assert (= y$s$169_op (or y$s$168_op y$s$55_op)))
(assert (= y$s$83_op (and y$8 y$s$82_op)))
(assert (= y$s$61_op (and y$L5 y$s$83_op)))
(assert (= y$s$62_op (and y$12 y$s$61_op)))
(assert (= y$s$63_op (and y$14 y$s$62_op)))
(assert (= y$s$56_op (and y$16 y$s$63_op)))
(assert (= y$s$170_op (or y$s$169_op y$s$56_op)))
(assert (= y$s$84_op (and y$10 y$s$83_op)))
(assert (= y$s$69_op (and y$L6 y$s$84_op)))
(assert (= y$s$70_op (and y$14 y$s$69_op)))
(assert (= y$s$71_op (and y$16 y$s$70_op)))
(assert (= y$s$171_op (or y$s$170_op y$s$71_op)))
(assert (= y$s$85_op (and y$12 y$s$84_op)))
(assert (= y$s$78_op (and y$L7 y$s$85_op)))
(assert (= y$s$79_op (and y$16 y$s$78_op)))
(assert (= y$s$172_op (or y$s$171_op y$s$79_op)))
(assert (= y$s$86_op (and y$14 y$s$85_op)))
(assert (= y$s$87_op (and y$L8 y$s$86_op)))
(assert (= y$LoneHot$next_rhs_op (or y$s$172_op y$s$87_op)))
(assert (= y$236 (= y$LoneHot$next y$LoneHot$next_rhs_op)))
(assert (= y$237 (and y$21 y$38 y$52 y$54 y$59 y$67 y$71 y$77 y$81 y$90 y$97 y$106 y$115 y$236)))
(assert (= y$L7$next (not y$252)))
(assert (= y$253 (= y$prop$next y$252)))
(assert (= y$prop$next (not y$251)))
(assert (= y$256 (and y$prop y$239 y$237 y$253 y$251)))
(assert y$256)
(assert (not (= y$n0s3 y$n1s3)))
(check-sat)
(exit)

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

id: at.1.prop1
query-maker: "Yices 2"
query-time: 0.126000 ms
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
(declare-fun y$2244 () Bool)
(declare-fun y$2247 () Bool)
(declare-fun y$2248 () Bool)
(declare-fun y$2298 () Bool)
(declare-fun y$23 () Bool)
(declare-fun y$2318 () Bool)
(declare-fun y$2326 () Bool)
(declare-fun y$2331 () Bool)
(declare-fun y$2332 () Bool)
(declare-fun y$2333 () Bool)
(declare-fun y$2334 () Bool)
(declare-fun y$2335 () Bool)
(declare-fun y$2336 () Bool)
(declare-fun y$2337 () Bool)
(declare-fun y$2346 () Bool)
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
(declare-fun y$55 () Bool)
(declare-fun y$57 () Bool)
(declare-fun y$59 () Bool)
(declare-fun y$61 () Bool)
(declare-fun y$63 () Bool)
(declare-fun y$65 () Bool)
(declare-fun y$67 () Bool)
(declare-fun y$69 () Bool)
(declare-fun y$7 () Bool)
(declare-fun y$71 () Bool)
(declare-fun y$73 () Bool)
(declare-fun y$75 () Bool)
(declare-fun y$78 () Bool)
(declare-fun y$80 () Bool)
(declare-fun y$82 () Bool)
(declare-fun y$84 () Bool)
(declare-fun y$86 () Bool)
(declare-fun y$88 () Bool)
(declare-fun y$9 () Bool)
(declare-fun y$a_CS_P_0 () Bool)
(declare-fun y$a_CS_P_0$next () Bool)
(declare-fun y$a_CS_P_1 () Bool)
(declare-fun y$a_CS_P_1$next () Bool)
(declare-fun y$a_CS_P_2 () Bool)
(declare-fun y$a_NCS_P_0 () Bool)
(declare-fun y$a_NCS_P_1 () Bool)
(declare-fun y$a_NCS_P_2 () Bool)
(declare-fun y$a_p12_P_0 () Bool)
(declare-fun y$a_p12_P_1 () Bool)
(declare-fun y$a_p12_P_2 () Bool)
(declare-fun y$a_p13_P_0 () Bool)
(declare-fun y$a_p13_P_1 () Bool)
(declare-fun y$a_p13_P_2 () Bool)
(declare-fun y$a_p2_P_0 () Bool)
(declare-fun y$a_p2_P_1 () Bool)
(declare-fun y$a_p2_P_2 () Bool)
(declare-fun y$a_p3_P_0 () Bool)
(declare-fun y$a_p3_P_1 () Bool)
(declare-fun y$a_p3_P_2 () Bool)
(declare-fun y$a_p4_P_0 () Bool)
(declare-fun y$a_p4_P_1 () Bool)
(declare-fun y$a_p4_P_2 () Bool)
(declare-fun y$a_p5_P_0 () Bool)
(declare-fun y$a_p5_P_1 () Bool)
(declare-fun y$a_p5_P_2 () Bool)
(declare-fun y$a_p6_P_0 () Bool)
(declare-fun y$a_p6_P_1 () Bool)
(declare-fun y$a_p6_P_2 () Bool)
(declare-fun y$a_p7_P_0 () Bool)
(declare-fun y$a_p7_P_1 () Bool)
(declare-fun y$a_p7_P_2 () Bool)
(declare-fun y$a_p8_P_0 () Bool)
(declare-fun y$a_p8_P_1 () Bool)
(declare-fun y$a_p8_P_2 () Bool)
(declare-fun y$a_p9_P_0 () Bool)
(declare-fun y$a_p9_P_1 () Bool)
(declare-fun y$a_p9_P_2 () Bool)
(declare-fun y$a_q () Bool)
(declare-fun y$dve_invalid () Bool)
(declare-fun y$id54 () Bool)
(declare-fun y$id54_op () Bool)
(declare-fun y$n0s32 () utt$32)
(declare-fun y$n0s8 () utt$8)
(declare-fun y$n1s32 () utt$32)
(declare-fun y$n1s8 () utt$8)
(declare-fun y$n255s32 () utt$32)
(declare-fun y$n255s8 () utt$8)
(declare-fun y$n2s8 () utt$8)
(declare-fun y$n5s8 () utt$8)
(declare-fun y$prop () Bool)
(declare-fun y$v3_1517448492_47 () utt$32)
(declare-fun y$v3_1517448492_47$next () utt$32)
(declare-fun y$v3_1517448492_47$next_op () utt$32)
(declare-fun y$v3_1517448492_47_op () utt$32)
(declare-fun y$v3_1517448492_48 () utt$32)
(declare-fun y$v3_1517448492_48$next () utt$32)
(declare-fun y$v3_1517448492_48$next_op () utt$32)
(declare-fun y$v3_1517448492_48_op () utt$32)
(declare-fun y$v3_1517448492_49 () utt$32)
(declare-fun y$v3_1517448492_49$next () utt$32)
(declare-fun y$v3_1517448492_49$next_op () utt$32)
(declare-fun y$v3_1517448492_49_op () utt$32)
(declare-fun y$v3_1517448492_50 () utt$32)
(declare-fun y$v3_1517448492_50_op () utt$32)
(declare-fun y$v3_1517448492_51 () utt$32)
(declare-fun y$v3_1517448492_51_op () utt$32)
(declare-fun y$v3_1517448492_52 () Bool)
(declare-fun y$v3_1517448492_52_op () Bool)
(declare-fun y$v_t_0 () utt$8)
(declare-fun y$v_t_1 () utt$8)
(declare-fun y$v_t_2 () utt$8)
(declare-fun y$v_x () utt$8)
(declare-fun y$v_y () utt$8)
(declare-fun y$v_z () utt$8)
(assert (distinct y$n0s8 y$n2s8 y$n1s8 y$n255s8 y$n5s8))
(assert (distinct y$n1s32 y$n255s32 y$n0s32))
(assert (= y$a_CS_P_0 (not y$1)))
(assert (= y$a_CS_P_1 (not y$3)))
(assert (= y$a_CS_P_2 (not y$5)))
(assert (= y$a_NCS_P_0 (not y$7)))
(assert (= y$a_NCS_P_1 (not y$9)))
(assert (= y$a_NCS_P_2 (not y$11)))
(assert (= y$a_p12_P_0 (not y$13)))
(assert (= y$a_p12_P_1 (not y$15)))
(assert (= y$a_p12_P_2 (not y$17)))
(assert (= y$a_p13_P_0 (not y$19)))
(assert (= y$a_p13_P_1 (not y$21)))
(assert (= y$a_p13_P_2 (not y$23)))
(assert (= y$a_p2_P_0 (not y$25)))
(assert (= y$a_p2_P_1 (not y$27)))
(assert (= y$a_p2_P_2 (not y$29)))
(assert (= y$a_p3_P_0 (not y$31)))
(assert (= y$a_p3_P_1 (not y$33)))
(assert (= y$a_p3_P_2 (not y$35)))
(assert (= y$a_p4_P_0 (not y$37)))
(assert (= y$a_p4_P_1 (not y$39)))
(assert (= y$a_p4_P_2 (not y$41)))
(assert (= y$a_p5_P_0 (not y$43)))
(assert (= y$a_p5_P_1 (not y$45)))
(assert (= y$a_p5_P_2 (not y$47)))
(assert (= y$a_p6_P_0 (not y$49)))
(assert (= y$a_p6_P_1 (not y$51)))
(assert (= y$a_p6_P_2 (not y$53)))
(assert (= y$a_p7_P_0 (not y$55)))
(assert (= y$a_p7_P_1 (not y$57)))
(assert (= y$a_p7_P_2 (not y$59)))
(assert (= y$a_p8_P_0 (not y$61)))
(assert (= y$a_p8_P_1 (not y$63)))
(assert (= y$a_p8_P_2 (not y$65)))
(assert (= y$a_p9_P_0 (not y$67)))
(assert (= y$a_p9_P_1 (not y$69)))
(assert (= y$a_p9_P_2 (not y$71)))
(assert (= y$a_q (not y$73)))
(assert (= y$dve_invalid (not y$75)))
(assert (= y$78 (= y$n0s8 y$v_t_0)))
(assert (= y$80 (= y$n0s8 y$v_t_1)))
(assert (= y$82 (= y$n0s8 y$v_t_2)))
(assert (= y$84 (= y$n0s8 y$v_x)))
(assert (= y$86 (= y$n0s8 y$v_y)))
(assert (= y$88 (= y$n0s8 y$v_z)))
(assert (= y$prop (not y$2298)))
(assert (= y$v3_1517448492_47_op (ite y$a_CS_P_0 y$n1s32 y$n0s32)))
(assert (= y$v3_1517448492_48_op (ite y$a_CS_P_1 y$n1s32 y$n0s32)))
(assert (= y$v3_1517448492_49_op (Add_32_32_32 y$v3_1517448492_47_op y$v3_1517448492_48_op)))
(assert (= y$v3_1517448492_50_op (ite y$a_CS_P_2 y$n1s32 y$n0s32)))
(assert (= y$v3_1517448492_51_op (Add_32_32_32 y$v3_1517448492_49_op y$v3_1517448492_50_op)))
(assert (= y$v3_1517448492_52_op (GrEq_1_32_32 y$n1s32 y$v3_1517448492_51_op)))
(assert (= y$v3_1517448492_52_op (not y$2244)))
(assert (= y$id54_op (and y$75 y$2244)))
(assert (= y$id54_op (not y$2247)))
(assert (= y$2248 (= y$prop y$2247)))
(assert (= y$a_CS_P_0$next (not y$2332)))
(assert (= y$a_CS_P_1$next (not y$2333)))
(assert (= y$v3_1517448492_47$next_op (ite y$a_CS_P_0$next y$n1s32 y$n0s32)))
(assert (= y$v3_1517448492_48$next_op (ite y$a_CS_P_1$next y$n1s32 y$n0s32)))
(assert (= y$v3_1517448492_49$next_op (Add_32_32_32 y$v3_1517448492_47$next_op y$v3_1517448492_48$next_op)))
(assert (= y$2334 (not (= y$n0s32 y$v3_1517448492_49$next_op))))
(assert (= y$2335 (and y$2332 y$2333 y$2334)))
(assert (= y$2335 (not y$2337)))
(assert (= y$2326 (not (= y$n0s32 y$v3_1517448492_49_op))))
(assert (= y$2331 (and y$1 y$3 y$2326)))
(assert (= y$2331 (not y$2336)))
(assert (= y$2346 (and y$1 y$3 y$5 y$7 y$9 y$11 y$13 y$15 y$17 y$19 y$21 y$23 y$25 y$27 y$29 y$31 y$33 y$35 y$37 y$39 y$41 y$43 y$45 y$47 y$49 y$51 y$53 y$55 y$57 y$59 y$61 y$63 y$65 y$67 y$69 y$71 y$73 y$75 y$78 y$80 y$82 y$84 y$86 y$88 y$2298 y$2248 y$2337 y$2336)))
(assert y$2346)
(check-sat)
(exit)

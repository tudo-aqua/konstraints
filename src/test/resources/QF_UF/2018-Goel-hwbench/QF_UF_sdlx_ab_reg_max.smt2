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

id: sdlx
query-maker: "Yices 2"
query-time: 0.199000 ms
query-class: abstract
query-category: oneshot
query-type: regular
status: sat
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")

;
(set-info :status sat)
(declare-sort utt$2 0)
(declare-sort utt$6 0)
(declare-sort utt$31 0)
(declare-sort utt$32 0)
(declare-fun Concat_32_1_31 (Bool utt$31 ) utt$32)
(declare-fun Extract_1_0_0_6 (utt$6 ) Bool)
(declare-fun Extract_1_1_1_6 (utt$6 ) Bool)
(declare-fun Extract_1_2_2_6 (utt$6 ) Bool)
(declare-fun y$1 () Bool)
(declare-fun y$10 () Bool)
(declare-fun y$1002 () Bool)
(declare-fun y$1005 () Bool)
(declare-fun y$1009 () Bool)
(declare-fun y$1014 () Bool)
(declare-fun y$1017 () Bool)
(declare-fun y$1020 () Bool)
(declare-fun y$1023 () Bool)
(declare-fun y$1028 () Bool)
(declare-fun y$1033 () Bool)
(declare-fun y$1038 () Bool)
(declare-fun y$1043 () Bool)
(declare-fun y$1048 () Bool)
(declare-fun y$1053 () Bool)
(declare-fun y$1058 () Bool)
(declare-fun y$1063 () Bool)
(declare-fun y$1068 () Bool)
(declare-fun y$1075 () Bool)
(declare-fun y$1153 () Bool)
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
(declare-fun y$31 () Bool)
(declare-fun y$33 () Bool)
(declare-fun y$35 () Bool)
(declare-fun y$37 () Bool)
(declare-fun y$39 () Bool)
(declare-fun y$41 () Bool)
(declare-fun y$43 () Bool)
(declare-fun y$45 () Bool)
(declare-fun y$47 () Bool)
(declare-fun y$6 () Bool)
(declare-fun y$8 () Bool)
(declare-fun y$992 () Bool)
(declare-fun y$997 () Bool)
(declare-fun y$998 () Bool)
(declare-fun y$ALUInA () Bool)
(declare-fun y$ALUInB () Bool)
(declare-fun y$ALUOp () utt$2)
(declare-fun y$ALUoutRW () Bool)
(declare-fun y$ARW () Bool)
(declare-fun y$BCRW () Bool)
(declare-fun y$BRW () Bool)
(declare-fun y$BraE () Bool)
(declare-fun y$IRRW () Bool)
(declare-fun y$IRW () Bool)
(declare-fun y$JmpE () Bool)
(declare-fun y$MDRW () Bool)
(declare-fun y$MemRW () Bool)
(declare-fun y$NPCRW () Bool)
(declare-fun y$NextState () utt$6)
(declare-fun y$PCRW () Bool)
(declare-fun y$RegDst () Bool)
(declare-fun y$RegRW () Bool)
(declare-fun y$SESel () Bool)
(declare-fun y$State () utt$6)
(declare-fun y$WBSel () Bool)
(declare-fun y$ZSel () Bool)
(declare-fun y$monitor_nop () Bool)
(declare-fun y$n0s2 () utt$2)
(declare-fun y$n0s31 () utt$31)
(declare-fun y$n0s32 () utt$32)
(declare-fun y$n0s6 () utt$6)
(declare-fun y$n1s2 () utt$2)
(declare-fun y$n1s32 () utt$32)
(declare-fun y$n1s6 () utt$6)
(declare-fun y$n2s2 () utt$2)
(declare-fun y$n2s32 () utt$32)
(declare-fun y$n2s6 () utt$6)
(declare-fun y$n35s6 () utt$6)
(declare-fun y$n3s2 () utt$2)
(declare-fun y$n3s32 () utt$32)
(declare-fun y$n3s6 () utt$6)
(declare-fun y$n43s6 () utt$6)
(declare-fun y$n4s32 () utt$32)
(declare-fun y$n4s6 () utt$6)
(declare-fun y$n5s32 () utt$32)
(declare-fun y$n5s6 () utt$6)
(declare-fun y$n8s6 () utt$6)
(declare-fun y$prop () Bool)
(declare-fun y$prop0 () Bool)
(declare-fun y$prop0_op () Bool)
(declare-fun y$s$145 () Bool)
(declare-fun y$s$145_op () Bool)
(declare-fun y$s$146 () Bool)
(declare-fun y$s$146_op () Bool)
(declare-fun y$s$147 () Bool)
(declare-fun y$s$147_op () Bool)
(declare-fun y$s$148 () Bool)
(declare-fun y$s$148_op () Bool)
(declare-fun y$s$149 () Bool)
(declare-fun y$s$149_op () Bool)
(declare-fun y$s$150 () Bool)
(declare-fun y$s$150_op () Bool)
(declare-fun y$s$151 () Bool)
(declare-fun y$s$151_op () Bool)
(declare-fun y$s$152 () Bool)
(declare-fun y$s$152_op () Bool)
(declare-fun y$s$153 () Bool)
(declare-fun y$s$153_op () Bool)
(declare-fun y$s$154 () Bool)
(declare-fun y$s$154_op () Bool)
(declare-fun y$s$155 () Bool)
(declare-fun y$s$155_op () Bool)
(declare-fun y$s$156 () Bool)
(declare-fun y$s$156_op () Bool)
(declare-fun y$w$15 () Bool)
(declare-fun y$w$16 () utt$32)
(declare-fun y$w$16_op () utt$32)
(declare-fun y$w$17 () Bool)
(declare-fun y$w$18 () utt$32)
(declare-fun y$w$18_op () utt$32)
(declare-fun y$w$19 () Bool)
(declare-fun y$w$20 () utt$32)
(declare-fun y$w$20_op () utt$32)
(declare-fun y$w$21 () utt$32)
(declare-fun y$w$21_op () utt$32)
(declare-fun y$w$22 () utt$32)
(declare-fun y$w$22_op () utt$32)
(declare-fun y$w$23 () utt$32)
(declare-fun y$w$23_op () utt$32)
(declare-fun y$w$24 () utt$32)
(declare-fun y$w$24_op () utt$32)
(declare-fun y$w$25 () utt$32)
(declare-fun y$w$25_op () utt$32)
(declare-fun y$w$26 () utt$32)
(declare-fun y$w$26_op () utt$32)
(declare-fun y$w$27 () utt$32)
(declare-fun y$w$27_op () utt$32)
(declare-fun y$w$28 () utt$32)
(declare-fun y$w$28_op () utt$32)
(declare-fun y$w$29 () utt$32)
(declare-fun y$w$29_op () utt$32)
(declare-fun y$w$30 () utt$32)
(declare-fun y$w$30_op () utt$32)
(declare-fun y$w$31 () utt$32)
(declare-fun y$w$31_op () utt$32)
(assert (distinct y$n0s2 y$n3s2 y$n1s2 y$n2s2))
(assert (distinct y$n0s6 y$n3s6 y$n4s6 y$n5s6 y$n8s6 y$n35s6 y$n2s6 y$n43s6 y$n1s6))
(assert (distinct y$n0s32 y$n1s32 y$n5s32 y$n4s32 y$n3s32 y$n2s32))
(assert (= y$ALUInA (not y$1)))
(assert (= y$ALUInB (not y$3)))
(assert (= y$6 (= y$n0s2 y$ALUOp)))
(assert (= y$ALUoutRW (not y$8)))
(assert (= y$ARW (not y$10)))
(assert (= y$BCRW (not y$12)))
(assert (= y$BRW (not y$14)))
(assert (= y$BraE (not y$16)))
(assert (= y$IRRW (not y$18)))
(assert (= y$IRW (not y$20)))
(assert (= y$JmpE (not y$22)))
(assert (= y$MDRW (not y$24)))
(assert (= y$MemRW (not y$26)))
(assert (= y$NPCRW (not y$28)))
(assert (= y$31 (= y$n0s6 y$NextState)))
(assert (= y$PCRW (not y$33)))
(assert (= y$RegDst (not y$35)))
(assert (= y$RegRW (not y$37)))
(assert (= y$SESel (not y$39)))
(assert (= y$41 (= y$n0s6 y$State)))
(assert (= y$WBSel (not y$43)))
(assert (= y$ZSel (not y$45)))
(assert (= y$monitor_nop (not y$47)))
(assert (= y$prop (not y$1075)))
(assert (= y$992 (Extract_1_0_0_6 y$State)))
(assert (= y$w$16_op (Concat_32_1_31 y$992 y$n0s31)))
(assert (= y$997 (= y$n0s32 y$w$16_op)))
(assert (= y$998 (Extract_1_1_1_6 y$State)))
(assert (= y$w$18_op (Concat_32_1_31 y$998 y$n0s31)))
(assert (= y$1002 (= y$n1s32 y$w$18_op)))
(assert (= y$s$145_op (and y$997 y$1002)))
(assert (= y$1005 (Extract_1_2_2_6 y$State)))
(assert (= y$w$20_op (Concat_32_1_31 y$1005 y$n0s31)))
(assert (= y$1009 (= y$n0s32 y$w$20_op)))
(assert (= y$s$146_op (and y$s$145_op y$1009)))
(assert (= y$w$21_op (Concat_32_1_31 y$monitor_nop y$n0s31)))
(assert (= y$1014 (= y$n0s32 y$w$21_op)))
(assert (= y$s$147_op (and y$s$146_op y$1014)))
(assert (= y$s$147_op (not y$1017)))
(assert (= y$w$22_op (Concat_32_1_31 y$ARW y$n0s31)))
(assert (= y$1020 (= y$n1s32 y$w$22_op)))
(assert (= y$w$23_op (Concat_32_1_31 y$BRW y$n0s31)))
(assert (= y$1023 (= y$n1s32 y$w$23_op)))
(assert (= y$s$148_op (and y$1020 y$1023)))
(assert (= y$w$24_op (Concat_32_1_31 y$RegRW y$n0s31)))
(assert (= y$1028 (= y$n0s32 y$w$24_op)))
(assert (= y$s$149_op (and y$s$148_op y$1028)))
(assert (= y$w$25_op (Concat_32_1_31 y$IRW y$n0s31)))
(assert (= y$1033 (= y$n1s32 y$w$25_op)))
(assert (= y$s$150_op (and y$s$149_op y$1033)))
(assert (= y$w$26_op (Concat_32_1_31 y$IRRW y$n0s31)))
(assert (= y$1038 (= y$n0s32 y$w$26_op)))
(assert (= y$s$151_op (and y$s$150_op y$1038)))
(assert (= y$w$27_op (Concat_32_1_31 y$PCRW y$n0s31)))
(assert (= y$1043 (= y$n1s32 y$w$27_op)))
(assert (= y$s$152_op (and y$s$151_op y$1043)))
(assert (= y$w$28_op (Concat_32_1_31 y$NPCRW y$n0s31)))
(assert (= y$1048 (= y$n0s32 y$w$28_op)))
(assert (= y$s$153_op (and y$s$152_op y$1048)))
(assert (= y$w$29_op (Concat_32_1_31 y$ALUoutRW y$n0s31)))
(assert (= y$1053 (= y$n0s32 y$w$29_op)))
(assert (= y$s$154_op (and y$s$153_op y$1053)))
(assert (= y$w$30_op (Concat_32_1_31 y$MDRW y$n0s31)))
(assert (= y$1058 (= y$n0s32 y$w$30_op)))
(assert (= y$s$155_op (and y$s$154_op y$1058)))
(assert (= y$w$31_op (Concat_32_1_31 y$BCRW y$n0s31)))
(assert (= y$1063 (= y$n0s32 y$w$31_op)))
(assert (= y$s$156_op (and y$s$155_op y$1063)))
(assert (= y$prop0_op (or y$1017 y$s$156_op)))
(assert (= y$1068 (= y$prop y$prop0_op)))
(assert (= y$1153 (and y$1 y$3 y$6 y$8 y$10 y$12 y$14 y$16 y$18 y$20 y$22 y$24 y$26 y$28 y$31 y$33 y$35 y$37 y$39 y$41 y$43 y$45 y$47 y$1075 y$1068)))
(assert y$1153)
(check-sat)
(exit)

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

id: collision.6.prop1
query-maker: "Yices 2"
query-time: 0.001000 ms
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
(declare-sort utt$16 0)
(declare-sort utt$32 0)
(declare-fun y$1 () Bool)
(declare-fun y$101 () Bool)
(declare-fun y$11 () Bool)
(declare-fun y$13 () Bool)
(declare-fun y$15 () Bool)
(declare-fun y$17 () Bool)
(declare-fun y$19 () Bool)
(declare-fun y$21 () Bool)
(declare-fun y$23 () Bool)
(declare-fun y$25 () Bool)
(declare-fun y$27 () Bool)
(declare-fun y$29 () Bool)
(declare-fun y$3 () Bool)
(declare-fun y$31 () Bool)
(declare-fun y$33 () Bool)
(declare-fun y$3352 () Bool)
(declare-fun y$3353 () Bool)
(declare-fun y$3424 () Bool)
(declare-fun y$3431 () Bool)
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
(declare-fun y$76 () Bool)
(declare-fun y$79 () Bool)
(declare-fun y$81 () Bool)
(declare-fun y$83 () Bool)
(declare-fun y$85 () Bool)
(declare-fun y$87 () Bool)
(declare-fun y$89 () Bool)
(declare-fun y$9 () Bool)
(declare-fun y$91 () Bool)
(declare-fun y$93 () Bool)
(declare-fun y$95 () Bool)
(declare-fun y$97 () Bool)
(declare-fun y$99 () Bool)
(declare-fun y$a_broadcast () Bool)
(declare-fun y$a_collision () Bool)
(declare-fun y$a_enquire_Slave1 () Bool)
(declare-fun y$a_enquire_Slave2 () Bool)
(declare-fun y$a_enquire_Slave3 () Bool)
(declare-fun y$a_enquire_Slave4 () Bool)
(declare-fun y$a_enquire_Slave5 () Bool)
(declare-fun y$a_got_Medium () Bool)
(declare-fun y$a_got_Slave1 () Bool)
(declare-fun y$a_got_Slave2 () Bool)
(declare-fun y$a_got_Slave3 () Bool)
(declare-fun y$a_got_Slave4 () Bool)
(declare-fun y$a_got_Slave5 () Bool)
(declare-fun y$a_got_User1 () Bool)
(declare-fun y$a_got_User2 () Bool)
(declare-fun y$a_got_User3 () Bool)
(declare-fun y$a_got_User4 () Bool)
(declare-fun y$a_got_User5 () Bool)
(declare-fun y$a_send () Bool)
(declare-fun y$a_wait_Master () Bool)
(declare-fun y$a_wait_Medium () Bool)
(declare-fun y$a_wait_Slave1 () Bool)
(declare-fun y$a_wait_Slave2 () Bool)
(declare-fun y$a_wait_Slave3 () Bool)
(declare-fun y$a_wait_Slave4 () Bool)
(declare-fun y$a_wait_Slave5 () Bool)
(declare-fun y$a_wait_User1 () Bool)
(declare-fun y$a_wait_User2 () Bool)
(declare-fun y$a_wait_User3 () Bool)
(declare-fun y$a_wait_User4 () Bool)
(declare-fun y$a_wait_User5 () Bool)
(declare-fun y$a_wrong_data_User1 () Bool)
(declare-fun y$a_wrong_data_User2 () Bool)
(declare-fun y$a_wrong_data_User3 () Bool)
(declare-fun y$a_wrong_data_User4 () Bool)
(declare-fun y$a_wrong_data_User5 () Bool)
(declare-fun y$dve_invalid () Bool)
(declare-fun y$id53 () Bool)
(declare-fun y$id53_op () Bool)
(declare-fun y$n0s16 () utt$16)
(declare-fun y$n0s32 () utt$32)
(declare-fun y$n0s8 () utt$8)
(declare-fun y$n100s32 () utt$32)
(declare-fun y$n10s32 () utt$32)
(declare-fun y$n11s16 () utt$16)
(declare-fun y$n16s32 () utt$32)
(declare-fun y$n1s32 () utt$32)
(declare-fun y$n1s8 () utt$8)
(declare-fun y$n22s16 () utt$16)
(declare-fun y$n2s32 () utt$32)
(declare-fun y$n2s8 () utt$8)
(declare-fun y$n33s16 () utt$16)
(declare-fun y$n3s32 () utt$32)
(declare-fun y$n3s8 () utt$8)
(declare-fun y$n44s16 () utt$16)
(declare-fun y$n4s32 () utt$32)
(declare-fun y$n4s8 () utt$8)
(declare-fun y$n55s16 () utt$16)
(declare-fun y$n5s32 () utt$32)
(declare-fun y$n5s8 () utt$8)
(declare-fun y$n6s8 () utt$8)
(declare-fun y$prop () Bool)
(declare-fun y$v_i () utt$8)
(declare-fun y$v_m_Medium () utt$16)
(declare-fun y$v_m_Slave1 () utt$16)
(declare-fun y$v_m_Slave2 () utt$16)
(declare-fun y$v_m_Slave3 () utt$16)
(declare-fun y$v_m_Slave4 () utt$16)
(declare-fun y$v_m_Slave5 () utt$16)
(declare-fun y$v_m_User1 () utt$16)
(declare-fun y$v_m_User2 () utt$16)
(declare-fun y$v_m_User3 () utt$16)
(declare-fun y$v_m_User4 () utt$16)
(declare-fun y$v_m_User5 () utt$16)
(declare-fun y$v_next () utt$8)
(assert (distinct y$n0s8 y$n1s8 y$n6s8 y$n2s8 y$n3s8 y$n4s8 y$n5s8))
(assert (distinct y$n0s16 y$n22s16 y$n33s16 y$n44s16 y$n55s16 y$n11s16))
(assert (distinct y$n10s32 y$n5s32 y$n16s32 y$n1s32 y$n100s32 y$n4s32 y$n3s32 y$n2s32 y$n0s32))
(assert (= y$a_broadcast (not y$1)))
(assert (= y$a_collision (not y$3)))
(assert (= y$a_enquire_Slave1 (not y$5)))
(assert (= y$a_enquire_Slave2 (not y$7)))
(assert (= y$a_enquire_Slave3 (not y$9)))
(assert (= y$a_enquire_Slave4 (not y$11)))
(assert (= y$a_enquire_Slave5 (not y$13)))
(assert (= y$a_got_Medium (not y$15)))
(assert (= y$a_got_Slave1 (not y$17)))
(assert (= y$a_got_Slave2 (not y$19)))
(assert (= y$a_got_Slave3 (not y$21)))
(assert (= y$a_got_Slave4 (not y$23)))
(assert (= y$a_got_Slave5 (not y$25)))
(assert (= y$a_got_User1 (not y$27)))
(assert (= y$a_got_User2 (not y$29)))
(assert (= y$a_got_User3 (not y$31)))
(assert (= y$a_got_User4 (not y$33)))
(assert (= y$a_got_User5 (not y$35)))
(assert (= y$a_send (not y$37)))
(assert (= y$a_wait_Master (not y$39)))
(assert (= y$a_wait_Medium (not y$41)))
(assert (= y$a_wait_Slave1 (not y$43)))
(assert (= y$a_wait_Slave2 (not y$45)))
(assert (= y$a_wait_Slave3 (not y$47)))
(assert (= y$a_wait_Slave4 (not y$49)))
(assert (= y$a_wait_Slave5 (not y$51)))
(assert (= y$a_wait_User1 (not y$53)))
(assert (= y$a_wait_User2 (not y$55)))
(assert (= y$a_wait_User3 (not y$57)))
(assert (= y$a_wait_User4 (not y$59)))
(assert (= y$a_wait_User5 (not y$61)))
(assert (= y$a_wrong_data_User1 (not y$63)))
(assert (= y$a_wrong_data_User2 (not y$65)))
(assert (= y$a_wrong_data_User3 (not y$67)))
(assert (= y$a_wrong_data_User4 (not y$69)))
(assert (= y$a_wrong_data_User5 (not y$71)))
(assert (= y$dve_invalid (not y$73)))
(assert (= y$76 (= y$n0s8 y$v_i)))
(assert (= y$79 (= y$n0s16 y$v_m_Medium)))
(assert (= y$81 (= y$n0s16 y$v_m_Slave1)))
(assert (= y$83 (= y$n0s16 y$v_m_Slave2)))
(assert (= y$85 (= y$n0s16 y$v_m_Slave3)))
(assert (= y$87 (= y$n0s16 y$v_m_Slave4)))
(assert (= y$89 (= y$n0s16 y$v_m_Slave5)))
(assert (= y$91 (= y$n0s16 y$v_m_User1)))
(assert (= y$93 (= y$n0s16 y$v_m_User2)))
(assert (= y$95 (= y$n0s16 y$v_m_User3)))
(assert (= y$97 (= y$n0s16 y$v_m_User4)))
(assert (= y$99 (= y$n0s16 y$v_m_User5)))
(assert (= y$101 (= y$n0s8 y$v_next)))
(assert (= y$prop (not y$3424)))
(assert (= y$id53_op (and y$a_collision y$73)))
(assert (= y$id53_op (not y$3352)))
(assert (= y$3353 (= y$prop y$3352)))
(assert (= y$3431 (and y$1 y$3 y$5 y$7 y$9 y$11 y$13 y$15 y$17 y$19 y$21 y$23 y$25 y$27 y$29 y$31 y$33 y$35 y$37 y$39 y$41 y$43 y$45 y$47 y$49 y$51 y$53 y$55 y$57 y$59 y$61 y$63 y$65 y$67 y$69 y$71 y$73 y$76 y$79 y$81 y$83 y$85 y$87 y$89 y$91 y$93 y$95 y$97 y$99 y$101 y$3424 y$3353)))
(assert y$3431)
(check-sat)
(exit)

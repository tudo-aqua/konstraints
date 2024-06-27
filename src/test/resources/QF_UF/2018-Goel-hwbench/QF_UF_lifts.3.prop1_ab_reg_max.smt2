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

id: lifts.3.prop1
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
(declare-sort utt$32 0)
(declare-fun y$1 () Bool)
(declare-fun y$101 () Bool)
(declare-fun y$103 () Bool)
(declare-fun y$105 () Bool)
(declare-fun y$107 () Bool)
(declare-fun y$109 () Bool)
(declare-fun y$11 () Bool)
(declare-fun y$111 () Bool)
(declare-fun y$113 () Bool)
(declare-fun y$115 () Bool)
(declare-fun y$117 () Bool)
(declare-fun y$119 () Bool)
(declare-fun y$121 () Bool)
(declare-fun y$123 () Bool)
(declare-fun y$125 () Bool)
(declare-fun y$127 () Bool)
(declare-fun y$129 () Bool)
(declare-fun y$13 () Bool)
(declare-fun y$131 () Bool)
(declare-fun y$133 () Bool)
(declare-fun y$135 () Bool)
(declare-fun y$137 () Bool)
(declare-fun y$139 () Bool)
(declare-fun y$141 () Bool)
(declare-fun y$143 () Bool)
(declare-fun y$146 () Bool)
(declare-fun y$148 () Bool)
(declare-fun y$15 () Bool)
(declare-fun y$150 () Bool)
(declare-fun y$152 () Bool)
(declare-fun y$154 () Bool)
(declare-fun y$156 () Bool)
(declare-fun y$158 () Bool)
(declare-fun y$160 () Bool)
(declare-fun y$162 () Bool)
(declare-fun y$164 () Bool)
(declare-fun y$166 () Bool)
(declare-fun y$168 () Bool)
(declare-fun y$17 () Bool)
(declare-fun y$170 () Bool)
(declare-fun y$172 () Bool)
(declare-fun y$174 () Bool)
(declare-fun y$176 () Bool)
(declare-fun y$178 () Bool)
(declare-fun y$180 () Bool)
(declare-fun y$182 () Bool)
(declare-fun y$184 () Bool)
(declare-fun y$186 () Bool)
(declare-fun y$188 () Bool)
(declare-fun y$19 () Bool)
(declare-fun y$190 () Bool)
(declare-fun y$21 () Bool)
(declare-fun y$23 () Bool)
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
(declare-fun y$77 () Bool)
(declare-fun y$79 () Bool)
(declare-fun y$81 () Bool)
(declare-fun y$83 () Bool)
(declare-fun y$85 () Bool)
(declare-fun y$87 () Bool)
(declare-fun y$89 () Bool)
(declare-fun y$9 () Bool)
(declare-fun y$91 () Bool)
(declare-fun y$9192 () Bool)
(declare-fun y$9193 () Bool)
(declare-fun y$93 () Bool)
(declare-fun y$9401 () Bool)
(declare-fun y$9408 () Bool)
(declare-fun y$95 () Bool)
(declare-fun y$97 () Bool)
(declare-fun y$99 () Bool)
(declare-fun y$a_a_move_Lift_0 () Bool)
(declare-fun y$a_a_move_Lift_1 () Bool)
(declare-fun y$a_a_move_Lift_2 () Bool)
(declare-fun y$a_a_msg_Lift_0 () Bool)
(declare-fun y$a_a_msg_Lift_1 () Bool)
(declare-fun y$a_a_msg_Lift_2 () Bool)
(declare-fun y$a_a_send_Lift_0 () Bool)
(declare-fun y$a_a_send_Lift_1 () Bool)
(declare-fun y$a_a_send_Lift_2 () Bool)
(declare-fun y$a_active_Lift_0 () Bool)
(declare-fun y$a_active_Lift_1 () Bool)
(declare-fun y$a_active_Lift_2 () Bool)
(declare-fun y$a_error_state_Lift_0 () Bool)
(declare-fun y$a_error_state_Lift_1 () Bool)
(declare-fun y$a_error_state_Lift_2 () Bool)
(declare-fun y$a_error_state_Wheels () Bool)
(declare-fun y$a_in () Bool)
(declare-fun y$a_moving_down () Bool)
(declare-fun y$a_moving_up () Bool)
(declare-fun y$a_p_msg_Lift_0 () Bool)
(declare-fun y$a_p_msg_Lift_1 () Bool)
(declare-fun y$a_p_msg_Lift_2 () Bool)
(declare-fun y$a_p_send_Lift_0 () Bool)
(declare-fun y$a_p_send_Lift_1 () Bool)
(declare-fun y$a_p_send_Lift_2 () Bool)
(declare-fun y$a_passive_Lift_0 () Bool)
(declare-fun y$a_passive_Lift_1 () Bool)
(declare-fun y$a_passive_Lift_2 () Bool)
(declare-fun y$a_pressed_down_0 () Bool)
(declare-fun y$a_pressed_down_1 () Bool)
(declare-fun y$a_pressed_down_2 () Bool)
(declare-fun y$a_pressed_up_0 () Bool)
(declare-fun y$a_pressed_up_1 () Bool)
(declare-fun y$a_pressed_up_2 () Bool)
(declare-fun y$a_q1_Environment () Bool)
(declare-fun y$a_q1_Lift_0 () Bool)
(declare-fun y$a_q1_Lift_1 () Bool)
(declare-fun y$a_q1_Lift_2 () Bool)
(declare-fun y$a_q2_Environment () Bool)
(declare-fun y$a_q2_Lift_0 () Bool)
(declare-fun y$a_q2_Lift_1 () Bool)
(declare-fun y$a_q2_Lift_2 () Bool)
(declare-fun y$a_q3_Environment () Bool)
(declare-fun y$a_q3_Lift_0 () Bool)
(declare-fun y$a_q3_Lift_1 () Bool)
(declare-fun y$a_q3_Lift_2 () Bool)
(declare-fun y$a_q4_Lift_0 () Bool)
(declare-fun y$a_q4_Lift_1 () Bool)
(declare-fun y$a_q4_Lift_2 () Bool)
(declare-fun y$a_q5_Lift_0 () Bool)
(declare-fun y$a_q5_Lift_1 () Bool)
(declare-fun y$a_q5_Lift_2 () Bool)
(declare-fun y$a_r1_Lift_0 () Bool)
(declare-fun y$a_r1_Lift_1 () Bool)
(declare-fun y$a_r1_Lift_2 () Bool)
(declare-fun y$a_r2_Lift_0 () Bool)
(declare-fun y$a_r2_Lift_1 () Bool)
(declare-fun y$a_r2_Lift_2 () Bool)
(declare-fun y$a_r3_Lift_0 () Bool)
(declare-fun y$a_r3_Lift_1 () Bool)
(declare-fun y$a_r3_Lift_2 () Bool)
(declare-fun y$a_r4_Lift_0 () Bool)
(declare-fun y$a_r4_Lift_1 () Bool)
(declare-fun y$a_r4_Lift_2 () Bool)
(declare-fun y$a_send_down () Bool)
(declare-fun y$a_send_up () Bool)
(declare-fun y$a_staying () Bool)
(declare-fun y$a_wait_Bus () Bool)
(declare-fun y$a_wait_Lift_0 () Bool)
(declare-fun y$a_wait_Lift_1 () Bool)
(declare-fun y$a_wait_Lift_2 () Bool)
(declare-fun y$dve_invalid () Bool)
(declare-fun y$id97 () Bool)
(declare-fun y$id97_op () Bool)
(declare-fun y$n0s32 () utt$32)
(declare-fun y$n0s8 () utt$8)
(declare-fun y$n1s32 () utt$32)
(declare-fun y$n1s8 () utt$8)
(declare-fun y$n24s32 () utt$32)
(declare-fun y$n2s32 () utt$32)
(declare-fun y$n2s8 () utt$8)
(declare-fun y$n32s32 () utt$32)
(declare-fun y$n3s32 () utt$32)
(declare-fun y$n4s32 () utt$32)
(declare-fun y$n8s32 () utt$32)
(declare-fun y$prop () Bool)
(declare-fun y$v_atomic () utt$8)
(declare-fun y$v_count_Lift_0 () utt$8)
(declare-fun y$v_count_Lift_1 () utt$8)
(declare-fun y$v_count_Lift_2 () utt$8)
(declare-fun y$v_count_Wheels () utt$8)
(declare-fun y$v_j () utt$8)
(declare-fun y$v_m_Bus () utt$8)
(declare-fun y$v_m_Lift_0 () utt$8)
(declare-fun y$v_m_Lift_1 () utt$8)
(declare-fun y$v_m_Lift_2 () utt$8)
(declare-fun y$v_nos_Lift_0 () utt$8)
(declare-fun y$v_nos_Lift_1 () utt$8)
(declare-fun y$v_nos_Lift_2 () utt$8)
(declare-fun y$v_pos_Lift_0 () utt$8)
(declare-fun y$v_pos_Lift_1 () utt$8)
(declare-fun y$v_pos_Lift_2 () utt$8)
(declare-fun y$v_relay_0 () utt$8)
(declare-fun y$v_relay_1 () utt$8)
(declare-fun y$v_relay_2 () utt$8)
(declare-fun y$v_sender () utt$8)
(declare-fun y$v_status_Lift_0 () utt$8)
(declare-fun y$v_status_Lift_1 () utt$8)
(declare-fun y$v_status_Lift_2 () utt$8)
(assert (distinct y$n0s8 y$n1s8 y$n2s8))
(assert (distinct y$n3s32 y$n1s32 y$n8s32 y$n24s32 y$n32s32 y$n0s32 y$n4s32 y$n2s32))
(assert (= y$a_a_move_Lift_0 (not y$1)))
(assert (= y$a_a_move_Lift_1 (not y$3)))
(assert (= y$a_a_move_Lift_2 (not y$5)))
(assert (= y$a_a_msg_Lift_0 (not y$7)))
(assert (= y$a_a_msg_Lift_1 (not y$9)))
(assert (= y$a_a_msg_Lift_2 (not y$11)))
(assert (= y$a_a_send_Lift_0 (not y$13)))
(assert (= y$a_a_send_Lift_1 (not y$15)))
(assert (= y$a_a_send_Lift_2 (not y$17)))
(assert (= y$a_active_Lift_0 (not y$19)))
(assert (= y$a_active_Lift_1 (not y$21)))
(assert (= y$a_active_Lift_2 (not y$23)))
(assert (= y$a_error_state_Lift_0 (not y$25)))
(assert (= y$a_error_state_Lift_1 (not y$27)))
(assert (= y$a_error_state_Lift_2 (not y$29)))
(assert (= y$a_error_state_Wheels (not y$31)))
(assert (= y$a_in (not y$33)))
(assert (= y$a_moving_down (not y$35)))
(assert (= y$a_moving_up (not y$37)))
(assert (= y$a_p_msg_Lift_0 (not y$39)))
(assert (= y$a_p_msg_Lift_1 (not y$41)))
(assert (= y$a_p_msg_Lift_2 (not y$43)))
(assert (= y$a_p_send_Lift_0 (not y$45)))
(assert (= y$a_p_send_Lift_1 (not y$47)))
(assert (= y$a_p_send_Lift_2 (not y$49)))
(assert (= y$a_passive_Lift_0 (not y$51)))
(assert (= y$a_passive_Lift_1 (not y$53)))
(assert (= y$a_passive_Lift_2 (not y$55)))
(assert (= y$a_pressed_down_0 (not y$57)))
(assert (= y$a_pressed_down_1 (not y$59)))
(assert (= y$a_pressed_down_2 (not y$61)))
(assert (= y$a_pressed_up_0 (not y$63)))
(assert (= y$a_pressed_up_1 (not y$65)))
(assert (= y$a_pressed_up_2 (not y$67)))
(assert (= y$a_q1_Environment (not y$69)))
(assert (= y$a_q1_Lift_0 (not y$71)))
(assert (= y$a_q1_Lift_1 (not y$73)))
(assert (= y$a_q1_Lift_2 (not y$75)))
(assert (= y$a_q2_Environment (not y$77)))
(assert (= y$a_q2_Lift_0 (not y$79)))
(assert (= y$a_q2_Lift_1 (not y$81)))
(assert (= y$a_q2_Lift_2 (not y$83)))
(assert (= y$a_q3_Environment (not y$85)))
(assert (= y$a_q3_Lift_0 (not y$87)))
(assert (= y$a_q3_Lift_1 (not y$89)))
(assert (= y$a_q3_Lift_2 (not y$91)))
(assert (= y$a_q4_Lift_0 (not y$93)))
(assert (= y$a_q4_Lift_1 (not y$95)))
(assert (= y$a_q4_Lift_2 (not y$97)))
(assert (= y$a_q5_Lift_0 (not y$99)))
(assert (= y$a_q5_Lift_1 (not y$101)))
(assert (= y$a_q5_Lift_2 (not y$103)))
(assert (= y$a_r1_Lift_0 (not y$105)))
(assert (= y$a_r1_Lift_1 (not y$107)))
(assert (= y$a_r1_Lift_2 (not y$109)))
(assert (= y$a_r2_Lift_0 (not y$111)))
(assert (= y$a_r2_Lift_1 (not y$113)))
(assert (= y$a_r2_Lift_2 (not y$115)))
(assert (= y$a_r3_Lift_0 (not y$117)))
(assert (= y$a_r3_Lift_1 (not y$119)))
(assert (= y$a_r3_Lift_2 (not y$121)))
(assert (= y$a_r4_Lift_0 (not y$123)))
(assert (= y$a_r4_Lift_1 (not y$125)))
(assert (= y$a_r4_Lift_2 (not y$127)))
(assert (= y$a_send_down (not y$129)))
(assert (= y$a_send_up (not y$131)))
(assert (= y$a_staying (not y$133)))
(assert (= y$a_wait_Bus (not y$135)))
(assert (= y$a_wait_Lift_0 (not y$137)))
(assert (= y$a_wait_Lift_1 (not y$139)))
(assert (= y$a_wait_Lift_2 (not y$141)))
(assert (= y$dve_invalid (not y$143)))
(assert (= y$146 (= y$n0s8 y$v_atomic)))
(assert (= y$148 (= y$n0s8 y$v_count_Lift_0)))
(assert (= y$150 (= y$n0s8 y$v_count_Lift_1)))
(assert (= y$152 (= y$n0s8 y$v_count_Lift_2)))
(assert (= y$154 (= y$n0s8 y$v_count_Wheels)))
(assert (= y$156 (= y$n0s8 y$v_j)))
(assert (= y$158 (= y$n0s8 y$v_m_Bus)))
(assert (= y$160 (= y$n0s8 y$v_m_Lift_0)))
(assert (= y$162 (= y$n0s8 y$v_m_Lift_1)))
(assert (= y$164 (= y$n0s8 y$v_m_Lift_2)))
(assert (= y$166 (= y$n0s8 y$v_nos_Lift_0)))
(assert (= y$168 (= y$n0s8 y$v_nos_Lift_1)))
(assert (= y$170 (= y$n0s8 y$v_nos_Lift_2)))
(assert (= y$172 (= y$n0s8 y$v_pos_Lift_0)))
(assert (= y$174 (= y$n0s8 y$v_pos_Lift_1)))
(assert (= y$176 (= y$n0s8 y$v_pos_Lift_2)))
(assert (= y$178 (= y$n0s8 y$v_relay_0)))
(assert (= y$180 (= y$n0s8 y$v_relay_1)))
(assert (= y$182 (= y$n0s8 y$v_relay_2)))
(assert (= y$184 (= y$n0s8 y$v_sender)))
(assert (= y$186 (= y$n0s8 y$v_status_Lift_0)))
(assert (= y$188 (= y$n0s8 y$v_status_Lift_1)))
(assert (= y$190 (= y$n0s8 y$v_status_Lift_2)))
(assert (= y$prop (not y$9401)))
(assert (= y$id97_op (and y$a_error_state_Wheels y$143)))
(assert (= y$id97_op (not y$9192)))
(assert (= y$9193 (= y$prop y$9192)))
(assert (= y$9408 (and y$1 y$3 y$5 y$7 y$9 y$11 y$13 y$15 y$17 y$19 y$21 y$23 y$25 y$27 y$29 y$31 y$33 y$35 y$37 y$39 y$41 y$43 y$45 y$47 y$49 y$51 y$53 y$55 y$57 y$59 y$61 y$63 y$65 y$67 y$69 y$71 y$73 y$75 y$77 y$79 y$81 y$83 y$85 y$87 y$89 y$91 y$93 y$95 y$97 y$99 y$101 y$103 y$105 y$107 y$109 y$111 y$113 y$115 y$117 y$119 y$121 y$123 y$125 y$127 y$129 y$131 y$133 y$135 y$137 y$139 y$141 y$143 y$146 y$148 y$150 y$152 y$154 y$156 y$158 y$160 y$162 y$164 y$166 y$168 y$170 y$172 y$174 y$176 y$178 y$180 y$182 y$184 y$186 y$188 y$190 y$9401 y$9193)))
(assert y$9408)
(check-sat)
(exit)

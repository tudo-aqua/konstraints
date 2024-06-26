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

id: usb_phy
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
(declare-sort utt$2 0)
(declare-sort utt$3 0)
(declare-sort utt$5 0)
(declare-sort utt$8 0)
(declare-sort utt$31 0)
(declare-sort utt$32 0)
(declare-fun Concat_32_1_31 (Bool utt$31 ) utt$32)
(declare-fun y$101 () Bool)
(declare-fun y$103 () Bool)
(declare-fun y$105 () Bool)
(declare-fun y$107 () Bool)
(declare-fun y$11 () Bool)
(declare-fun y$111 () Bool)
(declare-fun y$113 () Bool)
(declare-fun y$116 () Bool)
(declare-fun y$118 () Bool)
(declare-fun y$13 () Bool)
(declare-fun y$15 () Bool)
(declare-fun y$17 () Bool)
(declare-fun y$2 () Bool)
(declare-fun y$20 () Bool)
(declare-fun y$22 () Bool)
(declare-fun y$24 () Bool)
(declare-fun y$26 () Bool)
(declare-fun y$28 () Bool)
(declare-fun y$30 () Bool)
(declare-fun y$32 () Bool)
(declare-fun y$34 () Bool)
(declare-fun y$36 () Bool)
(declare-fun y$38 () Bool)
(declare-fun y$40 () Bool)
(declare-fun y$42 () Bool)
(declare-fun y$44 () Bool)
(declare-fun y$46 () Bool)
(declare-fun y$48 () Bool)
(declare-fun y$5 () Bool)
(declare-fun y$50 () Bool)
(declare-fun y$52 () Bool)
(declare-fun y$54 () Bool)
(declare-fun y$56 () Bool)
(declare-fun y$58 () Bool)
(declare-fun y$60 () Bool)
(declare-fun y$62 () Bool)
(declare-fun y$64 () Bool)
(declare-fun y$66 () Bool)
(declare-fun y$68 () Bool)
(declare-fun y$7 () Bool)
(declare-fun y$70 () Bool)
(declare-fun y$72 () Bool)
(declare-fun y$74 () Bool)
(declare-fun y$76 () Bool)
(declare-fun y$78 () Bool)
(declare-fun y$80 () Bool)
(declare-fun y$82 () Bool)
(declare-fun y$84 () Bool)
(declare-fun y$86 () Bool)
(declare-fun y$88 () Bool)
(declare-fun y$9 () Bool)
(declare-fun y$90 () Bool)
(declare-fun y$93 () Bool)
(declare-fun y$941 () Bool)
(declare-fun y$944 () Bool)
(declare-fun y$947 () Bool)
(declare-fun y$95 () Bool)
(declare-fun y$967 () Bool)
(declare-fun y$97 () Bool)
(declare-fun y$978 () Bool)
(declare-fun y$99 () Bool)
(declare-fun y$i_rx_phy.bit_cnt () utt$3)
(declare-fun y$i_rx_phy.dpll_state () utt$2)
(declare-fun y$i_rx_phy.fs_ce () Bool)
(declare-fun y$i_rx_phy.fs_ce_d () Bool)
(declare-fun y$i_rx_phy.fs_ce_r1 () Bool)
(declare-fun y$i_rx_phy.fs_ce_r2 () Bool)
(declare-fun y$i_rx_phy.fs_ce_r3 () Bool)
(declare-fun y$i_rx_phy.fs_state () utt$3)
(declare-fun y$i_rx_phy.hold_reg () utt$8)
(declare-fun y$i_rx_phy.one_cnt () utt$3)
(declare-fun y$i_rx_phy.rx_active () Bool)
(declare-fun y$i_rx_phy.rx_en () Bool)
(declare-fun y$i_rx_phy.rx_valid () Bool)
(declare-fun y$i_rx_phy.rx_valid1 () Bool)
(declare-fun y$i_rx_phy.rx_valid_r () Bool)
(declare-fun y$i_rx_phy.rxd_s () Bool)
(declare-fun y$i_rx_phy.rxd_s1 () Bool)
(declare-fun y$i_rx_phy.rxd_t1 () Bool)
(declare-fun y$i_rx_phy.rxdn_s () Bool)
(declare-fun y$i_rx_phy.rxdn_s1 () Bool)
(declare-fun y$i_rx_phy.rxdn_s1r () Bool)
(declare-fun y$i_rx_phy.rxdn_t1 () Bool)
(declare-fun y$i_rx_phy.rxdp_s () Bool)
(declare-fun y$i_rx_phy.rxdp_s1 () Bool)
(declare-fun y$i_rx_phy.rxdp_s1r () Bool)
(declare-fun y$i_rx_phy.rxdp_t1 () Bool)
(declare-fun y$i_rx_phy.sd_nrzi () Bool)
(declare-fun y$i_rx_phy.sd_r () Bool)
(declare-fun y$i_rx_phy.shift_en () Bool)
(declare-fun y$i_rx_phy.synced_d () Bool)
(declare-fun y$i_tx_phy.TxReady_o () Bool)
(declare-fun y$i_tx_phy.append_eop () Bool)
(declare-fun y$i_tx_phy.append_eop_sync1 () Bool)
(declare-fun y$i_tx_phy.append_eop_sync2 () Bool)
(declare-fun y$i_tx_phy.append_eop_sync3 () Bool)
(declare-fun y$i_tx_phy.bit_cnt () utt$3)
(declare-fun y$i_tx_phy.data_done () Bool)
(declare-fun y$i_tx_phy.hold_reg () utt$8)
(declare-fun y$i_tx_phy.ld_data () Bool)
(declare-fun y$i_tx_phy.ld_data_d () Bool)
(declare-fun y$i_tx_phy.ld_eop_d () Bool)
(declare-fun y$i_tx_phy.ld_sop_d () Bool)
(declare-fun y$i_tx_phy.one_cnt () utt$3)
(declare-fun y$i_tx_phy.sd_bs_o () Bool)
(declare-fun y$i_tx_phy.sd_nrzi_o () Bool)
(declare-fun y$i_tx_phy.sd_raw_o () Bool)
(declare-fun y$i_tx_phy.sft_done () Bool)
(declare-fun y$i_tx_phy.sft_done_r () Bool)
(declare-fun y$i_tx_phy.state () utt$3)
(declare-fun y$i_tx_phy.tx_ip () Bool)
(declare-fun y$i_tx_phy.tx_ip_sync () Bool)
(declare-fun y$i_tx_phy.tx_ready_d () Bool)
(declare-fun y$i_tx_phy.txdn () Bool)
(declare-fun y$i_tx_phy.txdp () Bool)
(declare-fun y$i_tx_phy.txoe () Bool)
(declare-fun y$i_tx_phy.txoe_r1 () Bool)
(declare-fun y$i_tx_phy.txoe_r2 () Bool)
(declare-fun y$n0s2 () utt$2)
(declare-fun y$n0s3 () utt$3)
(declare-fun y$n0s31 () utt$31)
(declare-fun y$n0s5 () utt$5)
(declare-fun y$n0s8 () utt$8)
(declare-fun y$n128s8 () utt$8)
(declare-fun y$n1s2 () utt$2)
(declare-fun y$n1s3 () utt$3)
(declare-fun y$n1s32 () utt$32)
(declare-fun y$n1s5 () utt$5)
(declare-fun y$n2s2 () utt$2)
(declare-fun y$n2s3 () utt$3)
(declare-fun y$n31s5 () utt$5)
(declare-fun y$n3s2 () utt$2)
(declare-fun y$n3s3 () utt$3)
(declare-fun y$n4s3 () utt$3)
(declare-fun y$n5s3 () utt$3)
(declare-fun y$n6s3 () utt$3)
(declare-fun y$n7s3 () utt$3)
(declare-fun y$prop () Bool)
(declare-fun y$prop0 () Bool)
(declare-fun y$prop0_op () Bool)
(declare-fun y$rst_cnt () utt$5)
(declare-fun y$usb_rst () Bool)
(declare-fun y$w$1 () utt$32)
(declare-fun y$w$1_op () utt$32)
(declare-fun y$w$2 () utt$32)
(declare-fun y$w$2_op () utt$32)
(assert (distinct y$n1s2 y$n0s2 y$n2s2 y$n3s2))
(assert (distinct y$n0s3 y$n6s3 y$n7s3 y$n1s3 y$n4s3 y$n5s3 y$n2s3 y$n3s3))
(assert (distinct y$n0s5 y$n1s5 y$n31s5))
(assert (not (= y$n0s8 y$n128s8)))
(assert (= y$2 (= y$n0s3 y$i_rx_phy.bit_cnt)))
(assert (= y$5 (= y$n1s2 y$i_rx_phy.dpll_state)))
(assert (= y$i_rx_phy.fs_ce (not y$7)))
(assert (= y$i_rx_phy.fs_ce_d (not y$9)))
(assert (= y$i_rx_phy.fs_ce_r1 (not y$11)))
(assert (= y$i_rx_phy.fs_ce_r2 (not y$13)))
(assert (= y$i_rx_phy.fs_ce_r3 (not y$15)))
(assert (= y$17 (= y$n0s3 y$i_rx_phy.fs_state)))
(assert (= y$20 (= y$n0s8 y$i_rx_phy.hold_reg)))
(assert (= y$22 (= y$n0s3 y$i_rx_phy.one_cnt)))
(assert (= y$i_rx_phy.rx_active (not y$24)))
(assert (= y$i_rx_phy.rx_en (not y$26)))
(assert (= y$i_rx_phy.rx_valid (not y$28)))
(assert (= y$i_rx_phy.rx_valid1 (not y$30)))
(assert (= y$i_rx_phy.rx_valid_r (not y$32)))
(assert (= y$i_rx_phy.rxd_s (not y$34)))
(assert (= y$i_rx_phy.rxd_s1 (not y$36)))
(assert (= y$i_rx_phy.rxd_t1 (not y$38)))
(assert (= y$i_rx_phy.rxdn_s (not y$40)))
(assert (= y$i_rx_phy.rxdn_s1 (not y$42)))
(assert (= y$i_rx_phy.rxdn_s1r (not y$44)))
(assert (= y$i_rx_phy.rxdn_t1 (not y$46)))
(assert (= y$i_rx_phy.rxdp_s (not y$48)))
(assert (= y$i_rx_phy.rxdp_s1 (not y$50)))
(assert (= y$i_rx_phy.rxdp_s1r (not y$52)))
(assert (= y$i_rx_phy.rxdp_t1 (not y$54)))
(assert (= y$i_rx_phy.sd_nrzi (not y$56)))
(assert (= y$i_rx_phy.sd_r (not y$58)))
(assert (= y$i_rx_phy.shift_en (not y$60)))
(assert (= y$i_rx_phy.synced_d (not y$62)))
(assert (= y$i_tx_phy.TxReady_o (not y$64)))
(assert (= y$i_tx_phy.append_eop (not y$66)))
(assert (= y$i_tx_phy.append_eop_sync1 (not y$68)))
(assert (= y$i_tx_phy.append_eop_sync2 (not y$70)))
(assert (= y$i_tx_phy.append_eop_sync3 (not y$72)))
(assert (= y$74 (= y$n0s3 y$i_tx_phy.bit_cnt)))
(assert (= y$i_tx_phy.data_done (not y$76)))
(assert (= y$78 (= y$n0s8 y$i_tx_phy.hold_reg)))
(assert (= y$i_tx_phy.ld_data (not y$80)))
(assert (= y$i_tx_phy.ld_data_d (not y$82)))
(assert (= y$i_tx_phy.ld_eop_d (not y$84)))
(assert (= y$i_tx_phy.ld_sop_d (not y$86)))
(assert (= y$88 (= y$n0s3 y$i_tx_phy.one_cnt)))
(assert (= y$i_tx_phy.sd_bs_o (not y$90)))
(assert (= y$i_tx_phy.sd_raw_o (not y$93)))
(assert (= y$i_tx_phy.sft_done (not y$95)))
(assert (= y$i_tx_phy.sft_done_r (not y$97)))
(assert (= y$99 (= y$n0s3 y$i_tx_phy.state)))
(assert (= y$i_tx_phy.tx_ip (not y$101)))
(assert (= y$i_tx_phy.tx_ip_sync (not y$103)))
(assert (= y$i_tx_phy.tx_ready_d (not y$105)))
(assert (= y$i_tx_phy.txdn (not y$107)))
(assert (= y$i_tx_phy.txoe_r1 (not y$111)))
(assert (= y$i_tx_phy.txoe_r2 (not y$113)))
(assert (= y$116 (= y$n0s5 y$rst_cnt)))
(assert (= y$usb_rst (not y$118)))
(assert (= y$prop (not y$967)))
(assert (= y$w$1_op (Concat_32_1_31 y$i_rx_phy.rx_valid y$n0s31)))
(assert (= y$941 (not (= y$w$1_op y$n1s32))))
(assert (= y$w$2_op (Concat_32_1_31 y$i_rx_phy.rx_active y$n0s31)))
(assert (= y$944 (= y$n1s32 y$w$2_op)))
(assert (= y$prop0_op (or y$941 y$944)))
(assert (= y$947 (= y$prop y$prop0_op)))
(assert (= y$978 (and y$2 y$5 y$7 y$9 y$11 y$13 y$15 y$17 y$20 y$22 y$24 y$26 y$28 y$30 y$32 y$34 y$36 y$38 y$40 y$42 y$44 y$46 y$48 y$50 y$52 y$54 y$56 y$58 y$60 y$62 y$64 y$66 y$68 y$70 y$72 y$74 y$76 y$78 y$80 y$82 y$84 y$86 y$88 y$90 y$i_tx_phy.sd_nrzi_o y$93 y$95 y$97 y$99 y$101 y$103 y$105 y$107 y$i_tx_phy.txdp y$i_tx_phy.txoe y$111 y$113 y$116 y$118 y$967 y$947)))
(assert y$978)
(check-sat)
(exit)

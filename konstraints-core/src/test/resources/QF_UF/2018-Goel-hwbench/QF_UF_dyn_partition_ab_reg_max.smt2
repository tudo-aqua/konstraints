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

id: dyn_partition
query-maker: "Yices 2"
query-time: 0.017000 ms
query-class: abstract
query-category: oneshot
query-type: regular
status: sat
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")

;
(set-info :status sat)
(declare-sort utt$3 0)
(declare-fun LeEq_1_3_3 (utt$3 utt$3 ) Bool)
(declare-fun y$1 () Bool)
(declare-fun y$3 () Bool)
(declare-fun y$41 () Bool)
(declare-fun y$48 () Bool)
(declare-fun y$53 () Bool)
(declare-fun y$6 () Bool)
(declare-fun y$8 () Bool)
(declare-fun y$b0 () Bool)
(declare-fun y$b1 () Bool)
(declare-fun y$n0s3 () utt$3)
(declare-fun y$prop () Bool)
(declare-fun y$prop0 () Bool)
(declare-fun y$prop0_op () Bool)
(declare-fun y$x () utt$3)
(declare-fun y$y () utt$3)
(assert (= y$b0 (not y$1)))
(assert (= y$b1 (not y$3)))
(assert (= y$6 (= y$x y$n0s3)))
(assert (= y$8 (= y$n0s3 y$y)))
(assert (= y$prop (not y$48)))
(assert (= y$prop0_op (LeEq_1_3_3 y$y y$x)))
(assert (= y$41 (= y$prop y$prop0_op)))
(assert (= y$53 (and y$1 y$3 y$6 y$8 y$48 y$41)))
(assert y$53)
(check-sat)
(exit)
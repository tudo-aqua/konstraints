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

id: counter
query-maker: "Yices 2"
query-time: 0.242000 ms
query-class: abstract
query-category: oneshot
query-type: regular
status: sat
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")

;
(set-info :status sat)
(declare-sort utt$4 0)
(declare-fun Add_4_4_4 (utt$4 utt$4 ) utt$4)
(declare-fun y$100 () Bool)
(declare-fun y$101 () Bool)
(declare-fun y$102 () Bool)
(declare-fun y$103 () Bool)
(declare-fun y$105 () Bool)
(declare-fun y$106 () Bool)
(declare-fun y$109 () Bool)
(declare-fun y$110 () Bool)
(declare-fun y$111 () Bool)
(declare-fun y$112 () Bool)
(declare-fun y$121 () Bool)
(declare-fun y$122 () Bool)
(declare-fun y$123 () Bool)
(declare-fun y$124 () Bool)
(declare-fun y$125 () Bool)
(declare-fun y$13 () Bool)
(declare-fun y$16 () Bool)
(declare-fun y$18 () Bool)
(declare-fun y$19 () Bool)
(declare-fun y$2 () Bool)
(declare-fun y$27 () Bool)
(declare-fun y$28 () Bool)
(declare-fun y$29 () Bool)
(declare-fun y$30 () Bool)
(declare-fun y$31 () Bool)
(declare-fun y$32 () Bool)
(declare-fun y$34 () Bool)
(declare-fun y$36 () Bool)
(declare-fun y$37 () Bool)
(declare-fun y$38 () Bool)
(declare-fun y$41 () Bool)
(declare-fun y$46 () Bool)
(declare-fun y$47 () Bool)
(declare-fun y$48 () Bool)
(declare-fun y$49 () Bool)
(declare-fun y$51 () Bool)
(declare-fun y$6 () Bool)
(declare-fun y$62 () Bool)
(declare-fun y$63 () Bool)
(declare-fun y$64 () Bool)
(declare-fun y$65 () Bool)
(declare-fun y$67 () Bool)
(declare-fun y$68 () Bool)
(declare-fun y$73 () Bool)
(declare-fun y$78 () Bool)
(declare-fun y$79 () Bool)
(declare-fun y$80 () Bool)
(declare-fun y$81 () Bool)
(declare-fun y$89 () Bool)
(declare-fun y$90 () Bool)
(declare-fun y$X () utt$4)
(declare-fun y$X$next () utt$4)
(declare-fun y$X$next_rhs () utt$4)
(declare-fun y$X$next_rhs_op () utt$4)
(declare-fun y$en () Bool)
(declare-fun y$en$next () Bool)
(declare-fun y$n0s4 () utt$4)
(declare-fun y$n15s4 () utt$4)
(declare-fun y$n1s4 () utt$4)
(declare-fun y$prop () Bool)
(declare-fun y$prop$next () Bool)
(declare-fun y$s$1 () utt$4)
(declare-fun y$s$1$next () utt$4)
(declare-fun y$s$1$next_op () utt$4)
(declare-fun y$s$1_op () utt$4)
(declare-fun y$s$4 () utt$4)
(declare-fun y$s$4_op () utt$4)
(assert (distinct y$n1s4 y$n15s4 y$n0s4))
(assert (= y$18 (not (= y$n0s4 y$X))))
(assert (= y$19 (= y$prop y$18)))
(assert (= y$6 (= y$n15s4 y$X)))
(assert (= y$s$1_op (Add_4_4_4 y$X y$n1s4)))
(assert (= y$s$4_op (ite y$6 y$n1s4 y$s$1_op)))
(assert (= y$X$next_rhs_op (ite y$en y$s$4_op y$X)))
(assert (= y$13 (= y$X$next y$X$next_rhs_op)))
(assert (= y$prop$next (not y$28)))
(assert (= y$38 (= y$n1s4 y$X$next)))
(assert (= y$s$1$next_op (Add_4_4_4 y$X$next y$n1s4)))
(assert (= y$41 (= y$n0s4 y$s$1$next_op)))
(assert (= y$47 (and y$38 y$41)))
(assert (= y$47 (not y$49)))
(assert (= y$2 (= y$n1s4 y$X)))
(assert (= y$37 (= y$n0s4 y$s$1_op)))
(assert (= y$46 (and y$2 y$37)))
(assert (= y$46 (not y$48)))
(assert (= y$67 (not (= y$n1s4 y$s$1$next_op))))
(assert (= (= y$n0s4 y$X$next) y$36))
(assert (= y$78 (and y$67 y$36)))
(assert (= y$78 (not y$80)))
(assert (= y$73 (not (= y$n1s4 y$s$1_op))))
(assert (= (= y$n0s4 y$X) y$16))
(assert (= y$79 (and y$73 y$16)))
(assert (= y$79 (not y$89)))
(assert (= (not (= y$n15s4 y$X)) y$34))
(assert (= y$100 (and y$37 y$34)))
(assert (= y$100 (not y$102)))
(assert (= y$68 (not (= y$n15s4 y$X$next))))
(assert (= y$101 (and y$41 y$68)))
(assert (= y$101 (not y$105)))
(assert (= y$125 (and y$prop y$19 y$13 y$28 y$49 y$48 y$80 y$89 y$102 y$105)))
(assert y$125)
(check-sat)
(exit)

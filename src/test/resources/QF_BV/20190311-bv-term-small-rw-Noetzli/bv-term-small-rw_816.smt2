(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
Generated by: Andres Noetzli, Andrew Reynolds, Haniel Barbosa, Aina Niemetz, Mathias Preiner, Clark Barrett, Cesare Tinelli
Generated on: 2018-11-08
Generator: CVC4
Application: Rewrite rule verification
Publications: "Syntax-Guided Rewrite Rule Enumeration for SMT Solvers" by A. Noetzli, A. Reynolds, H. Barbosa, A. Niemetz, M. Preiner, C. Barrett, and C. Tinelli, SAT 2019.
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun s () (_ BitVec 32))
(declare-fun t () (_ BitVec 32))
(assert (not (= (bvshl s (bvshl (bvmul t t) s)) (bvshl s (bvmul t (bvshl t s))))))
(check-sat)
(exit)

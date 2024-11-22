(set-info :smt-lib-version 2.6)
(set-logic QF_ABV)
(set-info :source |
Bit-vector benchmarks from Dawson Engler's tool contributed by Vijay Ganesh
(vganesh@stanford.edu).  Translated into SMT-LIB format by Clark Barrett using
CVC3.

|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (not (bvslt ((_ sign_extend 24) (select a (_ bv1 32))) ((_ sign_extend 24) (select a (_ bv0 32))))))
(assert (bvslt ((_ sign_extend 24) (select a (_ bv2 32))) ((_ sign_extend 24) (select a (_ bv1 32)))))
(assert (bvslt ((_ sign_extend 24) (select a (_ bv2 32))) ((_ sign_extend 24) (select (store a (_ bv2 32) (select a (_ bv1 32))) (_ bv0 32)))))
(check-sat)
(exit)

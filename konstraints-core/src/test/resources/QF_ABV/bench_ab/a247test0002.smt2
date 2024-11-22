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
(declare-fun i () (_ BitVec 8))
(assert (let ((?v_0 (concat (_ bv0 24) i))) (and (bvule (_ bv0 32) ?v_0) (bvule ?v_0 (_ bv9 32)))))
(assert (= ((_ sign_extend 24) (select a (concat (_ bv0 24) i))) (_ bv11 32)))
(check-sat)
(exit)

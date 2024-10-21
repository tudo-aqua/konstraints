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
(assert (let ((?v_0 (concat (concat (concat (concat ((_ extract 5 0) (select a (_ bv3 32))) (select a (_ bv2 32))) (select a (_ bv1 32))) (select a (_ bv0 32))) (_ bv0 2)))) (not (and (bvule (_ bv0 32) ?v_0) (bvule ?v_0 (_ bv3 32))))))
(check-sat)
(exit)

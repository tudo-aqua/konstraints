(set-info :smt-lib-version 2.6)
(set-logic QF_ABV)
(set-info :source |
Bit-vector benchmarks from Dawson Engler's tool contributed by Vijay Ganesh
(vganesh@stanford.edu).  Translated into SMT-LIB format by Clark Barrett using
CVC3.

|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun x () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun y () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (= (bvand (bvlshr (concat (concat (concat (select x (_ bv3 32)) (select x (_ bv2 32))) (select x (_ bv1 32))) (select x (_ bv0 32))) (_ bv1 32)) (_ bv3 32)) (_ bv2 32)))
(assert (not (not (= (bvand (bvlshr (concat (concat (concat (select y (_ bv3 32)) (select y (_ bv2 32))) (select y (_ bv1 32))) (select y (_ bv0 32))) (_ bv3 32)) (_ bv1 32)) (_ bv0 32)))))
(check-sat)
(exit)

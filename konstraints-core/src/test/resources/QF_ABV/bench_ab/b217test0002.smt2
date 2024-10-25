(set-info :smt-lib-version 2.6)
(set-logic QF_ABV)
(set-info :source |
Bit-vector benchmarks from Dawson Engler's tool contributed by Vijay Ganesh
(vganesh@stanford.edu).  Translated into SMT-LIB format by Clark Barrett using
CVC3.

|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun a () (_ BitVec 32))
(declare-fun malloced_2 () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (= (select malloced_2 (_ bv0 32)) (_ bv0 8)))
(assert (= (select malloced_2 (_ bv1 32)) (_ bv0 8)))
(assert (= (select malloced_2 (_ bv2 32)) (_ bv0 8)))
(assert (= (select malloced_2 (_ bv3 32)) (_ bv0 8)))
(assert (let ((?v_0 (store (store (store (store malloced_2 (_ bv0 32) ((_ extract 7 0) a)) (bvadd (_ bv0 32) (_ bv1 32)) ((_ extract 15 8) a)) (bvadd (_ bv0 32) (_ bv2 32)) ((_ extract 23 16) a)) (bvadd (_ bv0 32) (_ bv3 32)) ((_ extract 31 24) a)))) (not (bvslt (_ bv10 32) (concat (concat (concat (select ?v_0 (_ bv3 32)) (select ?v_0 (_ bv2 32))) (select ?v_0 (_ bv1 32))) (select ?v_0 (_ bv0 32)))))))
(check-sat)
(exit)

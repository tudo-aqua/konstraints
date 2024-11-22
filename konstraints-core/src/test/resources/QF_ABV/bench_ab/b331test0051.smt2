(set-info :smt-lib-version 2.6)
(set-logic QF_ABV)
(set-info :source |
Bit-vector benchmarks from Dawson Engler's tool contributed by Vijay Ganesh
(vganesh@stanford.edu).  Translated into SMT-LIB format by Clark Barrett using
CVC3.

|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun utf8 () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (not (bvslt (concat (_ bv0 24) ((_ extract 7 0) (select utf8 (_ bv0 32)))) (_ bv128 32))))
(assert (not (bvslt (concat (_ bv0 24) ((_ extract 7 0) (select utf8 (_ bv0 32)))) (_ bv194 32))))
(assert (bvslt (concat (_ bv0 24) ((_ extract 7 0) (select utf8 (_ bv0 32)))) (_ bv224 32)))
(assert (not (not (= (bvand ((_ sign_extend 24) (select utf8 (_ bv1 32))) (_ bv192 32)) (_ bv128 32)))))
(check-sat)
(exit)

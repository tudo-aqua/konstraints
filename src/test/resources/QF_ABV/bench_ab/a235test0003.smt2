(set-info :smt-lib-version 2.6)
(set-logic QF_ABV)
(set-info :source |
Bit-vector benchmarks from Dawson Engler's tool contributed by Vijay Ganesh
(vganesh@stanford.edu).  Translated into SMT-LIB format by Clark Barrett using
CVC3.

|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun buf () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (not (= (concat (concat (concat (select buf (_ bv3 32)) (select buf (_ bv2 32))) (select buf (_ bv1 32))) (select buf (_ bv0 32))) (_ bv16 32))))
(assert (not (= (concat (concat (concat (select buf (_ bv7 32)) (select buf (_ bv6 32))) (select buf (_ bv5 32))) (select buf (_ bv4 32))) (_ bv16 32))))
(check-sat)
(exit)

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
(declare-fun malloced_3 () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (= (select malloced_3 (_ bv0 32)) (_ bv0 8)))
(assert (= (select malloced_3 (_ bv1 32)) (_ bv0 8)))
(assert (= (select malloced_3 (_ bv2 32)) (_ bv0 8)))
(assert (= (select malloced_3 (_ bv3 32)) (_ bv0 8)))
(check-sat)
(exit)

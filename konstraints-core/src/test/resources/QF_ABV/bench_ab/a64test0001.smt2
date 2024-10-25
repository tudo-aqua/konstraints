(set-info :smt-lib-version 2.6)
(set-logic QF_ABV)
(set-info :source |
Bit-vector benchmarks from Dawson Engler's tool contributed by Vijay Ganesh
(vganesh@stanford.edu).  Translated into SMT-LIB format by Clark Barrett using
CVC3.

|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun p () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (bvsle (_ bv48 32) (concat (_ bv0 24) (select p (_ bv0 32)))))
(assert (not (bvsle (concat (_ bv0 24) (select p (_ bv0 32))) (_ bv57 32))))
(check-sat)
(exit)

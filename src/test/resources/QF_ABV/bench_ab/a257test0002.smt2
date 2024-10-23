(set-info :smt-lib-version 2.6)
(set-logic QF_ABV)
(set-info :source |
Bit-vector benchmarks from Dawson Engler's tool contributed by Vijay Ganesh
(vganesh@stanford.edu).  Translated into SMT-LIB format by Clark Barrett using
CVC3.

|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun i () (_ BitVec 32))
(declare-fun buf () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (not (bvslt i (_ bv0 32))))
(assert (not (bvslt (_ bv4 32) i)))
(assert (and (bvule (_ bv0 32) i) (bvule i (_ bv3 32))))
(assert (not (= (concat (_ bv0 24) (select buf i)) (_ bv1 32))))
(assert (= (concat (_ bv0 24) (select buf i)) (_ bv2 32)))
(check-sat)
(exit)

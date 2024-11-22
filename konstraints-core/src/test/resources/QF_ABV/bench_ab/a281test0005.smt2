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
(assert (and (bvule (_ bv0 32) i) (bvule i (_ bv3 32))))
(assert (let ((?v_0 (concat (_ bv0 24) (select buf i)))) (and (bvule (_ bv0 32) ?v_0) (bvule ?v_0 (_ bv3 32)))))
(assert (let ((?v_0 (concat (_ bv0 24) (select buf (concat (_ bv0 24) (select buf i)))))) (and (bvule (_ bv0 32) ?v_0) (bvule ?v_0 (_ bv3 32)))))
(assert (let ((?v_0 (concat (_ bv0 24) (select buf (concat (_ bv0 24) (select buf (concat (_ bv0 24) (select buf i)))))))) (and (bvule (_ bv0 32) ?v_0) (bvule ?v_0 (_ bv3 32)))))
(assert (= (concat (_ bv0 24) (select buf (concat (_ bv0 24) (select buf (concat (_ bv0 24) (select buf (concat (_ bv0 24) (select buf i)))))))) (_ bv0 32)))
(check-sat)
(exit)

(set-info :smt-lib-version 2.6)
(set-logic QF_ABV)
(set-info :source |
Bit-vector benchmarks from Dawson Engler's tool contributed by Vijay Ganesh
(vganesh@stanford.edu).  Translated into SMT-LIB format by Clark Barrett using
CVC3.

|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun n () (_ BitVec 32))
(declare-fun malloced_2 () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (not (bvsle n (_ bv0 32))))
(assert (not (bvslt (_ bv4 32) n)))
(assert (let ((?v_0 (concat ((_ extract 29 0) n) (_ bv0 2)))) (not (and (bvule (_ bv0 32) ?v_0) (bvule ?v_0 (bvadd (_ bv4294967295 32) ?v_0))))))
(check-sat)
(exit)

(set-info :smt-lib-version 2.6)
(set-logic QF_ABV)
(set-info :source |
Bit-vector benchmarks from Dawson Engler's tool contributed by Vijay Ganesh
(vganesh@stanford.edu).  Translated into SMT-LIB format by Clark Barrett using
CVC3.

|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun s () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (not (= ((_ extract 4 0) (select s (_ bv0 32))) (_ bv0 5))))
(assert (not (not (= ((_ extract 4 0) ((_ extract 4 0) (bvadd (concat (_ bv0 27) ((_ extract 4 0) (select s (_ bv0 32)))) (_ bv10 32)))) (_ bv0 5)))))
(check-sat)
(exit)

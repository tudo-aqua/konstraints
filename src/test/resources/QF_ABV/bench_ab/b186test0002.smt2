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
(declare-fun ft_client_main_3 () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (= (select ft_client_main_3 (_ bv0 32)) (_ bv0 8)))
(assert (= (select ft_client_main_3 (_ bv1 32)) (_ bv0 8)))
(assert (= (select ft_client_main_3 (_ bv2 32)) (_ bv0 8)))
(assert (= (select ft_client_main_3 (_ bv3 32)) (_ bv0 8)))
(assert (let ((?v_0 (store (store (store (store ft_client_main_3 (_ bv0 32) (select buf (_ bv0 32))) (_ bv1 32) (select buf (_ bv1 32))) (_ bv2 32) (select buf (_ bv2 32))) (_ bv3 32) (select buf (_ bv3 32))))) (not (= (concat (concat (concat (select ?v_0 (_ bv3 32)) (select ?v_0 (_ bv2 32))) (select ?v_0 (_ bv1 32))) (select ?v_0 (_ bv0 32))) (_ bv305419896 32)))))
(check-sat)
(exit)

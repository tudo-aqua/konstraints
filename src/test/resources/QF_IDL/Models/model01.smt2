(set-logic QF_IDL)
(set-info :status sat)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (= a 1))
(assert (= b (- 1)))
(assert (= a (- b)))
(check-sat)
(get-model)
(set-logic QF_IDL)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (= a 1))
(assert (= b (- 1)))
(assert (= a (- b)))
(check-sat)
(get-model)
(set-logic QF_FP)
(set-info :status unsat)
(assert (= (_ -zero 3 5) (fp #b0 #b000 #b0000)))
(check-sat)
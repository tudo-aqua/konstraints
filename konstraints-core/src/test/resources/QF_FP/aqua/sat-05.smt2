(set-logic QF_FP)
(set-info :status sat)
(assert (= (fp.div RTZ (_ +zero 5 11) (_ +zero 5 11)) (_ NaN 5 11)))
(check-sat)
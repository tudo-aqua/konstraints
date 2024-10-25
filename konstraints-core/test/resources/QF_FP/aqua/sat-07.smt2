(set-logic QF_FP)
(set-info :status sat)
(assert (= (fp.to_real (fp #b0 #b10000110 #b00110001000000000000000)) 152.5))
(check-sat)
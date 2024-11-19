(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |
Hardware fixpoint check problems.
These benchmarks stem from an evaluation described in Wintersteiger, Hamadi, de Moura: Efficiently solving quantified bit-vector formulas, FMSD 42(1), 2013.
The hardware models that were used are from the VCEGAR benchmark suite (see www.cprover.org/hardware/).
|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun Verilog__main.impl_PC_valid_64_0_39_!4 (Bool Bool Bool Bool Bool Bool Bool Bool) Bool)
(declare-fun Verilog__main.reset_64_0_39_!3 (Bool Bool Bool Bool Bool Bool Bool Bool) Bool)
(declare-fun Verilog__main.impl_flush_64_0_39_!0 (Bool Bool Bool Bool Bool Bool Bool Bool) Bool)
(declare-fun Verilog__main.impl_flush_64_1_39_!1 (Bool Bool Bool Bool Bool Bool Bool Bool) Bool)
(declare-fun Verilog__main.impl_PC_valid_64_1_39_!2 (Bool Bool Bool Bool Bool Bool Bool Bool) Bool)
(assert (forall ((Verilog__main.impl_flush_64_0 Bool) (Verilog__main.impl_flush_64_1 Bool) (Verilog__main.impl_flush_64_2 Bool) (Verilog__main.impl_PC_valid_64_1 Bool) (Verilog__main.reset_64_0 Bool) (Verilog__main.impl_PC_valid_64_0 Bool) (Verilog__main.impl_PC_valid_64_2 Bool) (Verilog__main.reset_64_1 Bool)) (=> (and (= Verilog__main.impl_flush_64_0 false) (= Verilog__main.impl_flush_64_1 false) (= Verilog__main.impl_flush_64_2 false) (= Verilog__main.impl_PC_valid_64_1 (ite Verilog__main.reset_64_0 true (ite Verilog__main.impl_flush_64_0 false Verilog__main.impl_PC_valid_64_0))) (= Verilog__main.impl_PC_valid_64_2 (ite Verilog__main.reset_64_1 true (ite Verilog__main.impl_flush_64_1 false Verilog__main.impl_PC_valid_64_1)))) (and (= (Verilog__main.impl_flush_64_0_39_!0 Verilog__main.reset_64_1 Verilog__main.impl_PC_valid_64_2 Verilog__main.impl_PC_valid_64_0 Verilog__main.reset_64_0 Verilog__main.impl_PC_valid_64_1 Verilog__main.impl_flush_64_2 Verilog__main.impl_flush_64_1 Verilog__main.impl_flush_64_0) false) (= (Verilog__main.impl_flush_64_1_39_!1 Verilog__main.reset_64_1 Verilog__main.impl_PC_valid_64_2 Verilog__main.impl_PC_valid_64_0 Verilog__main.reset_64_0 Verilog__main.impl_PC_valid_64_1 Verilog__main.impl_flush_64_2 Verilog__main.impl_flush_64_1 Verilog__main.impl_flush_64_0) false) (= (Verilog__main.impl_PC_valid_64_1_39_!2 Verilog__main.reset_64_1 Verilog__main.impl_PC_valid_64_2 Verilog__main.impl_PC_valid_64_0 Verilog__main.reset_64_0 Verilog__main.impl_PC_valid_64_1 Verilog__main.impl_flush_64_2 Verilog__main.impl_flush_64_1 Verilog__main.impl_flush_64_0) (ite (Verilog__main.reset_64_0_39_!3 Verilog__main.reset_64_1 Verilog__main.impl_PC_valid_64_2 Verilog__main.impl_PC_valid_64_0 Verilog__main.reset_64_0 Verilog__main.impl_PC_valid_64_1 Verilog__main.impl_flush_64_2 Verilog__main.impl_flush_64_1 Verilog__main.impl_flush_64_0) true (ite (Verilog__main.impl_flush_64_0_39_!0 Verilog__main.reset_64_1 Verilog__main.impl_PC_valid_64_2 Verilog__main.impl_PC_valid_64_0 Verilog__main.reset_64_0 Verilog__main.impl_PC_valid_64_1 Verilog__main.impl_flush_64_2 Verilog__main.impl_flush_64_1 Verilog__main.impl_flush_64_0) false (Verilog__main.impl_PC_valid_64_0_39_!4 Verilog__main.reset_64_1 Verilog__main.impl_PC_valid_64_2 Verilog__main.impl_PC_valid_64_0 Verilog__main.reset_64_0 Verilog__main.impl_PC_valid_64_1 Verilog__main.impl_flush_64_2 Verilog__main.impl_flush_64_1 Verilog__main.impl_flush_64_0)))) (or (and (= Verilog__main.impl_flush_64_2 (Verilog__main.impl_flush_64_0_39_!0 Verilog__main.reset_64_1 Verilog__main.impl_PC_valid_64_2 Verilog__main.impl_PC_valid_64_0 Verilog__main.reset_64_0 Verilog__main.impl_PC_valid_64_1 Verilog__main.impl_flush_64_2 Verilog__main.impl_flush_64_1 Verilog__main.impl_flush_64_0)) (= Verilog__main.impl_PC_valid_64_2 (Verilog__main.impl_PC_valid_64_0_39_!4 Verilog__main.reset_64_1 Verilog__main.impl_PC_valid_64_2 Verilog__main.impl_PC_valid_64_0 Verilog__main.reset_64_0 Verilog__main.impl_PC_valid_64_1 Verilog__main.impl_flush_64_2 Verilog__main.impl_flush_64_1 Verilog__main.impl_flush_64_0))) (and (= Verilog__main.impl_flush_64_2 (Verilog__main.impl_flush_64_1_39_!1 Verilog__main.reset_64_1 Verilog__main.impl_PC_valid_64_2 Verilog__main.impl_PC_valid_64_0 Verilog__main.reset_64_0 Verilog__main.impl_PC_valid_64_1 Verilog__main.impl_flush_64_2 Verilog__main.impl_flush_64_1 Verilog__main.impl_flush_64_0)) (= Verilog__main.impl_PC_valid_64_2 (Verilog__main.impl_PC_valid_64_1_39_!2 Verilog__main.reset_64_1 Verilog__main.impl_PC_valid_64_2 Verilog__main.impl_PC_valid_64_0 Verilog__main.reset_64_0 Verilog__main.impl_PC_valid_64_1 Verilog__main.impl_flush_64_2 Verilog__main.impl_flush_64_1 Verilog__main.impl_flush_64_0)))))) ))
(check-sat)
(exit)
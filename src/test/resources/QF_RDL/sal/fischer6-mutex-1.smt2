(set-info :smt-lib-version 2.6)
(set-logic QF_RDL)
(set-info :source |
Source unknown
This benchmark was automatically translated into SMT-LIB format from
CVC format using CVC Lite
|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun cvclZero () Real)
(declare-fun x_0 () Bool)
(declare-fun x_1 () Bool)
(declare-fun x_2 () Bool)
(declare-fun x_3 () Bool)
(declare-fun x_4 () Bool)
(declare-fun x_5 () Bool)
(declare-fun x_6 () Bool)
(declare-fun x_7 () Bool)
(declare-fun x_8 () Bool)
(declare-fun x_9 () Bool)
(declare-fun x_10 () Bool)
(declare-fun x_11 () Bool)
(declare-fun x_12 () Real)
(declare-fun x_13 () Real)
(declare-fun x_14 () Real)
(declare-fun x_15 () Real)
(declare-fun x_16 () Real)
(declare-fun x_17 () Real)
(declare-fun x_18 () Real)
(declare-fun x_19 () Bool)
(declare-fun x_20 () Bool)
(declare-fun x_21 () Real)
(declare-fun x_22 () Bool)
(declare-fun x_23 () Bool)
(declare-fun x_24 () Bool)
(declare-fun x_25 () Bool)
(declare-fun x_26 () Bool)
(declare-fun x_27 () Bool)
(declare-fun x_28 () Real)
(declare-fun x_29 () Bool)
(declare-fun x_30 () Bool)
(declare-fun x_31 () Bool)
(declare-fun x_32 () Bool)
(declare-fun x_33 () Real)
(declare-fun x_34 () Real)
(declare-fun x_35 () Real)
(declare-fun x_36 () Real)
(declare-fun x_37 () Real)
(declare-fun x_38 () Real)
(declare-fun x_39 () Real)
(declare-fun x_40 () Real)
(declare-fun x_41 () Real)
(assert (let ((?v_71 (not x_19)) (?v_72 (not x_20))) (let ((?v_73 (and ?v_71 ?v_72)) (?v_83 (not x_22)) (?v_84 (not x_23))) (let ((?v_85 (and ?v_83 ?v_84)) (?v_56 (not x_24)) (?v_57 (not x_25))) (let ((?v_59 (and ?v_56 ?v_57)) (?v_27 (not x_26)) (?v_28 (not x_27))) (let ((?v_29 (and ?v_27 ?v_28)) (?v_95 (not x_29)) (?v_96 (not x_30))) (let ((?v_97 (and ?v_95 ?v_96)) (?v_107 (not x_31)) (?v_108 (not x_32))) (let ((?v_109 (and ?v_107 ?v_108)) (?v_68 (not x_4)) (?v_66 (not x_5))) (let ((?v_62 (and ?v_68 ?v_66)) (?v_80 (not x_6)) (?v_78 (not x_7))) (let ((?v_74 (and ?v_80 ?v_78)) (?v_34 (and (= x_22 x_6) (= x_23 x_7))) (?v_81 (and ?v_80 x_7)) (?v_36 (and (= x_29 x_8) (= x_30 x_9))) (?v_30 (and (= x_24 x_2) (= x_25 x_3))) (?v_92 (not x_8)) (?v_90 (not x_9))) (let ((?v_86 (and ?v_92 ?v_90)) (?v_32 (and (= x_19 x_4) (= x_20 x_5))) (?v_104 (not x_10))) (let ((?v_105 (and ?v_104 x_11)) (?v_52 (not x_2)) (?v_49 (not x_3))) (let ((?v_42 (and ?v_52 ?v_49)) (?v_38 (and (= x_31 x_10) (= x_32 x_11))) (?v_21 (and (= x_26 x_0) (= x_27 x_1))) (?v_54 (and ?v_52 x_3)) (?v_69 (and ?v_68 x_5)) (?v_24 (not x_0))) (let ((?v_25 (and ?v_24 x_1)) (?v_93 (and ?v_92 x_9)) (?v_22 (not x_1))) (let ((?v_14 (and ?v_24 ?v_22)) (?v_102 (not x_11))) (let ((?v_98 (and ?v_104 ?v_102)) (?v_15 (- cvclZero x_12))) (let ((?v_11 (< ?v_15 0)) (?v_43 (- cvclZero x_13))) (let ((?v_10 (< ?v_43 0)) (?v_63 (- cvclZero x_14))) (let ((?v_9 (< ?v_63 0)) (?v_75 (- cvclZero x_15))) (let ((?v_8 (< ?v_75 0)) (?v_87 (- cvclZero x_16))) (let ((?v_7 (< ?v_87 0)) (?v_99 (- cvclZero x_17))) (let ((?v_6 (< ?v_99 0)) (?v_0 (- x_18 cvclZero))) (let ((?v_16 (= ?v_0 0)) (?v_2 (< (- x_17 x_16) 0))) (let ((?v_3 (ite ?v_2 (< (- x_17 x_15) 0) (< (- x_16 x_15) 0)))) (let ((?v_4 (ite ?v_3 (ite ?v_2 (< (- x_17 x_14) 0) (< (- x_16 x_14) 0)) (< (- x_15 x_14) 0)))) (let ((?v_5 (ite ?v_4 (ite ?v_3 (ite ?v_2 (< (- x_17 x_13) 0) (< (- x_16 x_13) 0)) (< (- x_15 x_13) 0)) (< (- x_14 x_13) 0)))) (let ((?v_12 (ite ?v_5 (ite ?v_4 (ite ?v_3 (ite ?v_2 (< (- x_17 x_12) 0) (< (- x_16 x_12) 0)) (< (- x_15 x_12) 0)) (< (- x_14 x_12) 0)) (< (- x_13 x_12) 0))) (?v_61 (= (- x_38 x_12) 0)) (?v_31 (= (- x_37 x_13) 0)) (?v_33 (= (- x_35 x_14) 0)) (?v_35 (= (- x_36 x_15) 0)) (?v_37 (= (- x_33 x_16) 0)) (?v_39 (= (- x_34 x_17) 0)) (?v_17 (= (- x_28 x_18) 0)) (?v_18 (- x_21 cvclZero))) (let ((?v_41 (= ?v_18 0)) (?v_19 (= ?v_15 0)) (?v_23 (- cvclZero x_38))) (let ((?v_20 (< ?v_23 0)) (?v_44 (= ?v_18 1)) (?v_46 (not ?v_16)) (?v_48 (= ?v_18 2)) (?v_1 (- x_28 cvclZero))) (let ((?v_110 (= ?v_1 1)) (?v_51 (= ?v_18 3)) (?v_26 (= ?v_0 1)) (?v_53 (= ?v_18 4))) (let ((?v_116 (not ?v_26)) (?v_58 (= ?v_18 5)) (?v_60 (= ?v_1 0)) (?v_45 (= ?v_43 0)) (?v_50 (- cvclZero x_37))) (let ((?v_47 (< ?v_50 0)) (?v_111 (= ?v_1 2)) (?v_55 (= ?v_0 2))) (let ((?v_117 (not ?v_55)) (?v_64 (= ?v_63 0)) (?v_67 (- cvclZero x_35))) (let ((?v_65 (< ?v_67 0)) (?v_112 (= ?v_1 3)) (?v_70 (= ?v_0 3))) (let ((?v_118 (not ?v_70)) (?v_76 (= ?v_75 0)) (?v_79 (- cvclZero x_36))) (let ((?v_77 (< ?v_79 0)) (?v_113 (= ?v_1 4)) (?v_82 (= ?v_0 4))) (let ((?v_119 (not ?v_82)) (?v_88 (= ?v_87 0)) (?v_91 (- cvclZero x_33))) (let ((?v_89 (< ?v_91 0)) (?v_114 (= ?v_1 5)) (?v_94 (= ?v_0 5))) (let ((?v_120 (not ?v_94)) (?v_100 (= ?v_99 0)) (?v_103 (- cvclZero x_34))) (let ((?v_101 (< ?v_103 0)) (?v_115 (= ?v_1 6)) (?v_106 (= ?v_0 6))) (let ((?v_121 (not ?v_106)) (?v_13 (- x_39 cvclZero)) (?v_40 (- x_41 cvclZero))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (not (< ?v_0 0)) (<= ?v_0 6)) (not (< ?v_1 0))) (<= ?v_1 6)) ?v_14) ?v_42) ?v_62) ?v_74) ?v_86) ?v_98) ?v_11) ?v_10) ?v_9) ?v_8) ?v_7) ?v_6) ?v_16) (or (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (= ?v_13 0) (ite ?v_12 (ite ?v_5 (ite ?v_4 (ite ?v_3 (ite ?v_2 ?v_6 ?v_7) ?v_8) ?v_9) ?v_10) ?v_11)) (ite ?v_12 (ite ?v_5 (ite ?v_4 (ite ?v_3 (ite ?v_2 (= (- x_40 x_17) 0) (= (- x_40 x_16) 0)) (= (- x_40 x_15) 0)) (= (- x_40 x_14) 0)) (= (- x_40 x_13) 0)) (= (- x_40 x_12) 0))) ?v_21) ?v_30) ?v_32) ?v_34) ?v_36) ?v_38) ?v_61) ?v_31) ?v_33) ?v_35) ?v_37) ?v_39) ?v_17) (and (and (= ?v_13 1) (or (or (or (or (or (and (and (and (and (and (and (and (and (and (and (and (= ?v_40 1) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_41 ?v_14) ?v_19) ?v_16) x_26) ?v_28) ?v_20) (<= (- x_38 cvclZero) 2)) ?v_17) (and (and (and (and (and (and ?v_44 ?v_14) ?v_19) ?v_46) ?v_20) ?v_17) ?v_21)) (and (and (and (and (and (and (and ?v_48 x_0) ?v_22) ?v_19) ?v_27) x_27) ?v_110) (<= ?v_23 (- 4)))) (and (and (and (and (and (and (and ?v_51 ?v_25) ?v_19) ?v_26) x_26) x_27) ?v_20) ?v_17)) (and (and (and (and (and (and ?v_53 ?v_25) ?v_19) ?v_116) ?v_29) ?v_20) ?v_17)) (and (and (and (and (and (and ?v_58 x_0) x_1) ?v_19) ?v_29) ?v_60) ?v_20))) ?v_30) ?v_31) ?v_32) ?v_33) ?v_34) ?v_35) ?v_36) ?v_37) ?v_38) ?v_39) (and (and (and (and (and (and (and (and (and (and (and (= ?v_40 2) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_41 ?v_42) ?v_45) ?v_16) x_24) ?v_57) ?v_47) (<= (- x_37 cvclZero) 2)) ?v_17) (and (and (and (and (and (and ?v_44 ?v_42) ?v_45) ?v_46) ?v_47) ?v_17) ?v_30)) (and (and (and (and (and (and (and ?v_48 x_2) ?v_49) ?v_45) ?v_56) x_25) ?v_111) (<= ?v_50 (- 4)))) (and (and (and (and (and (and (and ?v_51 ?v_54) ?v_45) ?v_55) x_24) x_25) ?v_47) ?v_17)) (and (and (and (and (and (and ?v_53 ?v_54) ?v_45) ?v_117) ?v_59) ?v_47) ?v_17)) (and (and (and (and (and (and ?v_58 x_2) x_3) ?v_45) ?v_59) ?v_60) ?v_47))) ?v_21) ?v_61) ?v_32) ?v_33) ?v_34) ?v_35) ?v_36) ?v_37) ?v_38) ?v_39)) (and (and (and (and (and (and (and (and (and (and (and (= ?v_40 3) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_41 ?v_62) ?v_64) ?v_16) x_19) ?v_72) ?v_65) (<= (- x_35 cvclZero) 2)) ?v_17) (and (and (and (and (and (and ?v_44 ?v_62) ?v_64) ?v_46) ?v_65) ?v_17) ?v_32)) (and (and (and (and (and (and (and ?v_48 x_4) ?v_66) ?v_64) ?v_71) x_20) ?v_112) (<= ?v_67 (- 4)))) (and (and (and (and (and (and (and ?v_51 ?v_69) ?v_64) ?v_70) x_19) x_20) ?v_65) ?v_17)) (and (and (and (and (and (and ?v_53 ?v_69) ?v_64) ?v_118) ?v_73) ?v_65) ?v_17)) (and (and (and (and (and (and ?v_58 x_4) x_5) ?v_64) ?v_73) ?v_60) ?v_65))) ?v_21) ?v_61) ?v_30) ?v_31) ?v_34) ?v_35) ?v_36) ?v_37) ?v_38) ?v_39)) (and (and (and (and (and (and (and (and (and (and (and (= ?v_40 4) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_41 ?v_74) ?v_76) ?v_16) x_22) ?v_84) ?v_77) (<= (- x_36 cvclZero) 2)) ?v_17) (and (and (and (and (and (and ?v_44 ?v_74) ?v_76) ?v_46) ?v_77) ?v_17) ?v_34)) (and (and (and (and (and (and (and ?v_48 x_6) ?v_78) ?v_76) ?v_83) x_23) ?v_113) (<= ?v_79 (- 4)))) (and (and (and (and (and (and (and ?v_51 ?v_81) ?v_76) ?v_82) x_22) x_23) ?v_77) ?v_17)) (and (and (and (and (and (and ?v_53 ?v_81) ?v_76) ?v_119) ?v_85) ?v_77) ?v_17)) (and (and (and (and (and (and ?v_58 x_6) x_7) ?v_76) ?v_85) ?v_60) ?v_77))) ?v_21) ?v_61) ?v_30) ?v_31) ?v_32) ?v_33) ?v_36) ?v_37) ?v_38) ?v_39)) (and (and (and (and (and (and (and (and (and (and (and (= ?v_40 5) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_41 ?v_86) ?v_88) ?v_16) x_29) ?v_96) ?v_89) (<= (- x_33 cvclZero) 2)) ?v_17) (and (and (and (and (and (and ?v_44 ?v_86) ?v_88) ?v_46) ?v_89) ?v_17) ?v_36)) (and (and (and (and (and (and (and ?v_48 x_8) ?v_90) ?v_88) ?v_95) x_30) ?v_114) (<= ?v_91 (- 4)))) (and (and (and (and (and (and (and ?v_51 ?v_93) ?v_88) ?v_94) x_29) x_30) ?v_89) ?v_17)) (and (and (and (and (and (and ?v_53 ?v_93) ?v_88) ?v_120) ?v_97) ?v_89) ?v_17)) (and (and (and (and (and (and ?v_58 x_8) x_9) ?v_88) ?v_97) ?v_60) ?v_89))) ?v_21) ?v_61) ?v_30) ?v_31) ?v_32) ?v_33) ?v_34) ?v_35) ?v_38) ?v_39)) (and (and (and (and (and (and (and (and (and (and (and (= ?v_40 6) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_41 ?v_98) ?v_100) ?v_16) x_31) ?v_108) ?v_101) (<= (- x_34 cvclZero) 2)) ?v_17) (and (and (and (and (and (and ?v_44 ?v_98) ?v_100) ?v_46) ?v_101) ?v_17) ?v_38)) (and (and (and (and (and (and (and ?v_48 x_10) ?v_102) ?v_100) ?v_107) x_32) ?v_115) (<= ?v_103 (- 4)))) (and (and (and (and (and (and (and ?v_51 ?v_105) ?v_100) ?v_106) x_31) x_32) ?v_101) ?v_17)) (and (and (and (and (and (and ?v_53 ?v_105) ?v_100) ?v_121) ?v_109) ?v_101) ?v_17)) (and (and (and (and (and (and ?v_58 x_10) x_11) ?v_100) ?v_109) ?v_60) ?v_101))) ?v_21) ?v_61) ?v_30) ?v_31) ?v_32) ?v_33) ?v_34) ?v_35) ?v_36) ?v_37))) (= (- x_40 cvclZero) 0)))) (or (or (or (or (or (or (or (or (or (or (or (and (and x_26 x_27) (not ?v_110)) (and (and x_24 x_25) (not ?v_111))) (and (and x_19 x_20) (not ?v_112))) (and (and x_22 x_23) (not ?v_113))) (and (and x_29 x_30) (not ?v_114))) (and (and x_31 x_32) (not ?v_115))) (and (and x_0 x_1) ?v_116)) (and (and x_2 x_3) ?v_117)) (and (and x_4 x_5) ?v_118)) (and (and x_6 x_7) ?v_119)) (and (and x_8 x_9) ?v_120)) (and (and x_10 x_11) ?v_121))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
(exit)

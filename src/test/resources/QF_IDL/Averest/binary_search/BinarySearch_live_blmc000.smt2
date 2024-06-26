(set-info :smt-lib-version 2.6)
(set-logic QF_IDL)
(set-info :source |The Averest Framework (http://www.averest.org)|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun cvclZero () Int)
(declare-fun F14 () Int)
(declare-fun F16 () Int)
(declare-fun F18 () Int)
(declare-fun F20 () Int)
(declare-fun F22 () Int)
(declare-fun F36 () Int)
(declare-fun F37 () Int)
(declare-fun F38 () Int)
(declare-fun F39 () Int)
(declare-fun F40 () Int)
(declare-fun F43 () Int)
(declare-fun F44 () Int)
(declare-fun F45 () Int)
(declare-fun F46 () Int)
(declare-fun F47 () Int)
(declare-fun F54 () Int)
(declare-fun F55 () Int)
(declare-fun F56 () Int)
(declare-fun F57 () Int)
(declare-fun F58 () Int)
(declare-fun F61 () Int)
(declare-fun F62 () Int)
(declare-fun F63 () Int)
(declare-fun F64 () Int)
(declare-fun F65 () Int)
(declare-fun F74 () Int)
(declare-fun F75 () Int)
(declare-fun F76 () Int)
(declare-fun F77 () Int)
(declare-fun F78 () Int)
(declare-fun F85 () Int)
(declare-fun F86 () Int)
(declare-fun F87 () Int)
(declare-fun F88 () Int)
(declare-fun F89 () Int)
(declare-fun F92 () Int)
(declare-fun F93 () Int)
(declare-fun F94 () Int)
(declare-fun F95 () Int)
(declare-fun F96 () Int)
(declare-fun P10 () Bool)
(declare-fun P12 () Bool)
(declare-fun P24 () Bool)
(declare-fun P26 () Bool)
(declare-fun P28 () Bool)
(declare-fun P30 () Bool)
(declare-fun P32 () Bool)
(declare-fun P34 () Bool)
(declare-fun P41 () Bool)
(declare-fun P42 () Bool)
(declare-fun P48 () Bool)
(declare-fun P49 () Bool)
(declare-fun P50 () Bool)
(declare-fun P51 () Bool)
(declare-fun P52 () Bool)
(declare-fun P53 () Bool)
(declare-fun P59 () Bool)
(declare-fun P60 () Bool)
(declare-fun P66 () Bool)
(declare-fun P67 () Bool)
(declare-fun P68 () Bool)
(declare-fun P69 () Bool)
(declare-fun P70 () Bool)
(declare-fun P71 () Bool)
(declare-fun P72 () Bool)
(declare-fun P73 () Bool)
(declare-fun P79 () Bool)
(declare-fun P80 () Bool)
(declare-fun P81 () Bool)
(declare-fun P82 () Bool)
(declare-fun P83 () Bool)
(declare-fun P84 () Bool)
(declare-fun P90 () Bool)
(declare-fun P91 () Bool)
(declare-fun P97 () Bool)
(declare-fun P98 () Bool)
(declare-fun P99 () Bool)
(declare-fun P100 () Bool)
(declare-fun P101 () Bool)
(declare-fun P102 () Bool)
(assert (let ((?v_0 (not P90))) (let ((?v_2 (or (and P100 P90) ?v_0)) (?v_6 (and P98 P90))) (let ((?v_3 (= ?v_2 ?v_6)) (?v_1 (or (and P99 P90) ?v_0)) (?v_7 (and P97 P90))) (let ((?v_11 (not (= ?v_1 ?v_7))) (?v_8 (not ?v_3))) (let ((?v_4 (or (and ?v_3 (and ?v_1 ?v_11)) (and ?v_2 ?v_8)))) (let ((?v_5 (and ?v_4 P91))) (let ((?v_14 (not ?v_5)) (?v_10 (and ?v_1 ?v_7))) (let ((?v_9 (or (and ?v_2 ?v_6) (and ?v_10 ?v_8)))) (let ((?v_17 (or (and (or (and ?v_14 P102) (and ?v_5 ?v_9)) P90) (and ?v_9 ?v_0))) (?v_12 (not (= ?v_10 ?v_8))) (?v_13 (not ?v_9))) (let ((?v_15 (or (and ?v_12 ?v_13) (and (or (and ?v_9 ?v_11) (and (not (= ?v_9 ?v_11)) ?v_9)) (not (= ?v_12 ?v_13)))))) (let ((?v_16 (or (and (or (and ?v_5 ?v_15) (and P101 ?v_14)) P90) (and ?v_15 ?v_0)))) (let ((?v_18 (and ?v_16 ?v_0)) (?v_24 (not ?v_17))) (let ((?v_22 (and ?v_18 ?v_24)) (?v_21 (not ?v_16))) (let ((?v_25 (and ?v_21 ?v_0))) (let ((?v_20 (and ?v_17 ?v_25)) (?v_19 (and ?v_17 ?v_18)) (?v_23 (and ?v_16 P90))) (let ((?v_27 (and ?v_17 ?v_23)) (?v_26 (and ?v_21 P90))) (let ((?v_28 (and ?v_17 ?v_26)) (?v_29 (and ?v_23 ?v_24)) (?v_30 (and ?v_25 ?v_24)) (?v_31 (and ?v_24 ?v_26)) (?v_40 (not (= ?v_16 ?v_17))) (?v_44 (not P59))) (let ((?v_43 (or (and P59 P68) ?v_44)) (?v_48 (and P59 P66))) (let ((?v_54 (not (= ?v_43 ?v_48))) (?v_46 (or (and P59 P69) ?v_44)) (?v_47 (and P59 P67))) (let ((?v_45 (= ?v_46 ?v_47))) (let ((?v_49 (not ?v_45))) (let ((?v_51 (or (and (and ?v_54 ?v_43) ?v_45) (and ?v_49 ?v_46))) (?v_53 (and ?v_43 ?v_48))) (let ((?v_50 (or (and ?v_46 ?v_47) (and ?v_53 ?v_49))) (?v_52 (and ?v_51 P60))) (let ((?v_57 (not ?v_52))) (let ((?v_60 (or (and ?v_50 ?v_44) (and (or (and ?v_50 ?v_52) (and ?v_57 P71)) P59))) (?v_55 (not (= ?v_53 ?v_49))) (?v_56 (not ?v_50))) (let ((?v_58 (or (and ?v_55 ?v_56) (and (or (and ?v_50 ?v_54) (and ?v_50 (not (= ?v_50 ?v_54)))) (not (= ?v_55 ?v_56)))))) (let ((?v_61 (or (and P59 (or (and ?v_52 ?v_58) (and ?v_57 P70))) (and ?v_58 ?v_44)))) (let ((?v_59 (not ?v_61))) (let ((?v_66 (and ?v_59 ?v_44)) (?v_62 (not ?v_60))) (let ((?v_63 (and ?v_66 ?v_62)) (?v_64 (and ?v_61 ?v_44))) (let ((?v_68 (and ?v_60 ?v_64)) (?v_65 (and ?v_59 P59))) (let ((?v_74 (and ?v_65 ?v_62)) (?v_67 (and ?v_61 P59))) (let ((?v_73 (and ?v_62 ?v_67)) (?v_72 (and ?v_62 ?v_64)) (?v_71 (and ?v_60 ?v_65)) (?v_70 (and ?v_66 ?v_60)) (?v_69 (and ?v_60 ?v_67)) (?v_80 (not (= ?v_60 ?v_61))) (?v_88 (not P41))) (let ((?v_86 (or (and P41 P51) ?v_88)) (?v_92 (and P49 P41))) (let ((?v_87 (= ?v_92 ?v_86))) (let ((?v_90 (not ?v_87)) (?v_89 (or ?v_88 (and P41 P50))) (?v_91 (and P41 P48))) (let ((?v_97 (not (= ?v_91 ?v_89)))) (let ((?v_94 (or (and ?v_86 ?v_90) (and ?v_87 (and ?v_89 ?v_97)))) (?v_96 (and ?v_91 ?v_89))) (let ((?v_93 (or (and ?v_90 ?v_96) (and ?v_92 ?v_86))) (?v_95 (and ?v_94 P42))) (let ((?v_101 (not ?v_95))) (let ((?v_102 (or (and ?v_88 ?v_93) (and P41 (or (and ?v_93 ?v_95) (and P53 ?v_101))))) (?v_98 (not ?v_93)) (?v_99 (not (= ?v_90 ?v_96)))) (let ((?v_100 (or (and (not (= ?v_98 ?v_99)) (or (and ?v_93 (not (= ?v_97 ?v_93))) (and ?v_97 ?v_93))) (and ?v_98 ?v_99)))) (let ((?v_103 (or (and ?v_88 ?v_100) (and P41 (or (and ?v_95 ?v_100) (and P52 ?v_101))))) (?v_104 (not ?v_102))) (let ((?v_105 (not ?v_103))) (let ((?v_106 (and P41 ?v_105))) (let ((?v_110 (and ?v_104 ?v_106)) (?v_107 (and ?v_88 ?v_105))) (let ((?v_111 (and ?v_104 ?v_107)) (?v_108 (and P41 ?v_103))) (let ((?v_112 (and ?v_104 ?v_108)) (?v_109 (and ?v_88 ?v_103))) (let ((?v_113 (and ?v_104 ?v_109)) (?v_114 (and ?v_102 ?v_106)) (?v_115 (and ?v_102 ?v_107)) (?v_116 (and ?v_102 ?v_108)) (?v_117 (and ?v_102 ?v_109)) (?v_123 (not (= ?v_102 ?v_103))) (?v_32 (or (or (or (or (and (and ?v_22 P90) (> (- F96 F88) 0)) (or (or (and (and ?v_20 P90) (> (- F96 F87) 0)) (or (or (and (> (- F96 F86) 0) (and ?v_19 P90)) (or (or (or (or (or (or (or (and (< (- F86 F85) 0) (and ?v_19 ?v_0)) (and (< (- F92 F85) 0) (and ?v_27 ?v_0))) (and (< (- F87 F85) 0) (and ?v_20 ?v_0))) (and (< (- F93 F85) 0) (and ?v_28 ?v_0))) (and (< (- F88 F85) 0) (and ?v_22 ?v_0))) (and (< (- F94 F85) 0) (and ?v_29 ?v_0))) (and (< (- F89 F85) 0) (and ?v_30 ?v_0))) (and (< (- F95 F85) 0) (and ?v_31 ?v_0)))) (and (> (- F96 F92) 0) (and ?v_27 P90)))) (and (> (- F96 F93) 0) (and ?v_28 P90)))) (and (> (- F96 F94) 0) (and ?v_29 P90))) (and (> (- F96 F89) 0) (and ?v_30 P90))) (and (> (- F96 F95) 0) (and ?v_31 P90))))) (let ((?v_34 (and ?v_32 ?v_0))) (let ((?v_41 (not ?v_34)) (?v_33 (and ?v_5 ?v_32))) (let ((?v_42 (not ?v_33)) (?v_35 (not ?v_32))) (let ((?v_37 (and ?v_0 ?v_35))) (let ((?v_38 (not ?v_37)) (?v_36 (and ?v_5 ?v_35))) (let ((?v_39 (not ?v_36)) (?v_81 (or (or (and (and ?v_63 P59) (> (- F65 F58) 0)) (or (or (or (or (or (or (and (and P59 ?v_68) (> (- F65 F55) 0)) (or (and (and ?v_74 ?v_44) (< (- F64 F54) 0)) (or (and (and ?v_63 ?v_44) (< (- F58 F54) 0)) (or (and (and ?v_44 ?v_73) (< (- F63 F54) 0)) (or (and (and ?v_44 ?v_72) (< (- F57 F54) 0)) (or (and (and ?v_44 ?v_71) (< (- F62 F54) 0)) (or (and (and ?v_44 ?v_70) (< (- F56 F54) 0)) (or (and (and ?v_44 ?v_69) (< (- F61 F54) 0)) (and (and ?v_44 ?v_68) (< (- F55 F54) 0)))))))))) (and (and P59 ?v_69) (> (- F65 F61) 0))) (and (and P59 ?v_70) (> (- F65 F56) 0))) (and (and P59 ?v_71) (> (- F65 F62) 0))) (and (and P59 ?v_72) (> (- F65 F57) 0))) (and (and P59 ?v_73) (> (- F65 F63) 0)))) (and (and ?v_74 P59) (> (- F65 F64) 0))))) (let ((?v_76 (not ?v_81))) (let ((?v_75 (and ?v_44 ?v_76))) (let ((?v_78 (not ?v_75)) (?v_77 (and ?v_52 ?v_76))) (let ((?v_79 (not ?v_77)) (?v_83 (and ?v_44 ?v_81))) (let ((?v_84 (not ?v_83)) (?v_82 (and ?v_52 ?v_81))) (let ((?v_85 (not ?v_82)) (?v_118 (or (and (and P41 ?v_110) (> (- F47 F46) 0)) (or (and (and P41 ?v_111) (> (- F47 F40) 0)) (or (and (and P41 ?v_112) (> (- F47 F45) 0)) (or (and (> (- F47 F39) 0) (and P41 ?v_113)) (or (and (and ?v_114 P41) (> (- F47 F44) 0)) (or (and (and P41 ?v_115) (> (- F47 F38) 0)) (or (and (and P41 ?v_116) (> (- F47 F43) 0)) (or (and (and P41 ?v_117) (> (- F47 F37) 0)) (or (and (and ?v_88 ?v_110) (< (- F46 F36) 0)) (or (and (and ?v_88 ?v_111) (< (- F40 F36) 0)) (or (and (and ?v_88 ?v_112) (< (- F45 F36) 0)) (or (and (and ?v_88 ?v_113) (< (- F39 F36) 0)) (or (and (and ?v_114 ?v_88) (< (- F44 F36) 0)) (or (and (and ?v_88 ?v_115) (< (- F38 F36) 0)) (or (and (and ?v_88 ?v_116) (< (- F43 F36) 0)) (and (and ?v_88 ?v_117) (< (- F37 F36) 0))))))))))))))))))) (let ((?v_120 (and ?v_88 ?v_118)) (?v_119 (and ?v_95 ?v_118))) (let ((?v_121 (not ?v_119)) (?v_122 (not ?v_120)) (?v_124 (not ?v_118))) (let ((?v_126 (and ?v_124 ?v_88)) (?v_125 (and ?v_124 ?v_95))) (let ((?v_128 (not ?v_125)) (?v_127 (not ?v_126))) (not (or (not (and (and (and (and (not (and (not ?v_4) P91)) (and (and (and (not P101) (and (and (not P99) (and (and (and (= (- cvclZero F96) 0) (and (= (- cvclZero F95) 0) (and (= (- cvclZero F94) 0) (and (= (- cvclZero F93) 0) (and (= (- cvclZero F92) 0) (and (not P91) ?v_0)))))) (not P97)) (not P98))) (not P100))) (not P102)) (and (and (or (and (<= (- F88 F87) 0) ?v_0) (and (<= (- F94 F93) 0) P90)) (or (and (<= (- F87 F86) 0) ?v_0) (and (<= (- F93 F92) 0) P90))) (or (and (<= (- F89 F88) 0) ?v_0) (and (<= (- F95 F94) 0) P90))))) (and (= ?v_17 P71) (and (= ?v_16 P70) (and (and (= (or (and ?v_41 (or (and ?v_16 ?v_33) (and ?v_42 ?v_1))) (and ?v_16 ?v_34)) P68) (and (and (= (or (and ?v_38 (or (and ?v_21 ?v_36) (and ?v_39 ?v_7))) (and ?v_21 ?v_37)) P66) (and (and (or (and (= (- F89 F64) 0) ?v_0) (and (= (- F95 F64) 0) P90)) (and (or (and (= (- F94 F63) 0) P90) (and (= (- F88 F63) 0) ?v_0)) (and (and (and (= (or ?v_5 ?v_0) P60) P59) (or (and (= (- F86 F61) 0) ?v_0) (and (= (- F92 F61) 0) P90))) (or (and (= (- F87 F62) 0) ?v_0) (and (= (- F93 F62) 0) P90))))) (or (and (= (- F85 F65) 0) ?v_0) (and (= (- F96 F65) 0) P90)))) (= (or (and ?v_38 (or (and ?v_39 ?v_6) (and ?v_36 ?v_40))) (and ?v_40 ?v_37)) P67))) (= (or (and ?v_41 (or (and ?v_17 ?v_33) (and ?v_42 ?v_2))) (and ?v_17 ?v_34)) P69))))) (not (and (not ?v_51) P60))) (and (= P84 ?v_60) (and (and (and (and (and (and (and (or (and (= (- F77 F64) 0) P59) (and (= (- F77 F58) 0) ?v_44)) (and (and (and (or (and (= (- F74 F61) 0) P59) (and (= (- F74 F55) 0) ?v_44)) (and (= P73 (or ?v_52 ?v_44)) P72)) (or (and (= (- F75 F56) 0) ?v_44) (and (= (- F75 F62) 0) P59))) (or (and (= (- F76 F57) 0) ?v_44) (and (= (- F76 F63) 0) P59)))) (or (and (= (- F78 F54) 0) ?v_44) (and (= (- F78 F65) 0) P59))) (= P79 (or (and ?v_59 ?v_75) (and ?v_78 (or (and ?v_48 ?v_79) (and ?v_59 ?v_77)))))) (= P80 (or (and ?v_78 (or (and ?v_77 ?v_80) (and ?v_47 ?v_79))) (and ?v_80 ?v_75)))) (= P81 (or (and ?v_84 (or (and ?v_82 ?v_61) (and ?v_43 ?v_85))) (and ?v_61 ?v_83)))) (= P82 (or (and ?v_60 ?v_83) (and ?v_84 (or (and ?v_46 ?v_85) (and ?v_82 ?v_60)))))) (= P83 ?v_61))))) (not (and (and (not (and (not ?v_94) P42)) (and (and (or (and P41 (<= (- F46 F45) 0)) (and ?v_88 (<= (- F40 F39) 0))) (and (or (and P41 (<= (- F44 F43) 0)) (and ?v_88 (<= (- F38 F37) 0))) (or (and P41 (<= (- F45 F44) 0)) (and ?v_88 (<= (- F39 F38) 0))))) (and (not P53) (and (not P52) (and (not P51) (and (not P50) (and (not P49) (and (not P48) (and (and (and (and (= (- cvclZero F44) 0) (and (and ?v_88 (not P42)) (= (- cvclZero F43) 0))) (= (- cvclZero F45) 0)) (= (- cvclZero F46) 0)) (= (- cvclZero F47) 0)))))))))) (and (= P34 ?v_102) (and (= P32 ?v_103) (and (= (or (and ?v_102 ?v_120) (and (or (and ?v_86 ?v_121) (and ?v_102 ?v_119)) ?v_122)) P30) (and (= (or (and ?v_103 ?v_120) (and (or (and ?v_89 ?v_121) (and ?v_103 ?v_119)) ?v_122)) P28) (and (= P26 (or (and ?v_123 ?v_126) (and (or (and ?v_123 ?v_125) (and ?v_128 ?v_92)) ?v_127))) (and (= P24 (or (and ?v_126 ?v_105) (and ?v_127 (or (and ?v_128 ?v_91) (and ?v_125 ?v_105))))) (and (or (and ?v_88 (= (- F36 F22) 0)) (and P41 (= (- F47 F22) 0))) (and (or (and P41 (= (- F46 F20) 0)) (and ?v_88 (= (- F40 F20) 0))) (and (or (and P41 (= (- F45 F18) 0)) (and ?v_88 (= (- F39 F18) 0))) (and (or (and P41 (= (- F44 F16) 0)) (and ?v_88 (= (- F38 F16) 0))) (and (or (and P41 (= (- F43 F14) 0)) (and ?v_88 (= (- F37 F14) 0))) (and P10 (= P12 (or ?v_88 ?v_95))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
(exit)

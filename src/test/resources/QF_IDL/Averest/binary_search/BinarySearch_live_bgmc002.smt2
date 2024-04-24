(set-info :smt-lib-version 2.6)
(set-logic QF_IDL)
(set-info :source |The Averest Framework (http://www.averest.org)|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun cvclZero () Int)
(declare-fun F0 () Int)
(declare-fun F1 () Int)
(declare-fun F2 () Int)
(declare-fun F3 () Int)
(declare-fun F4 () Int)
(declare-fun F5 () Int)
(declare-fun F6 () Int)
(declare-fun F7 () Int)
(declare-fun F8 () Int)
(declare-fun F9 () Int)
(declare-fun F14 () Int)
(declare-fun F15 () Int)
(declare-fun F16 () Int)
(declare-fun F17 () Int)
(declare-fun F18 () Int)
(declare-fun F19 () Int)
(declare-fun F20 () Int)
(declare-fun F21 () Int)
(declare-fun F22 () Int)
(declare-fun F23 () Int)
(declare-fun F38 () Int)
(declare-fun F39 () Int)
(declare-fun F40 () Int)
(declare-fun F41 () Int)
(declare-fun F42 () Int)
(declare-fun P10 () Bool)
(declare-fun P11 () Bool)
(declare-fun P12 () Bool)
(declare-fun P13 () Bool)
(declare-fun P24 () Bool)
(declare-fun P25 () Bool)
(declare-fun P26 () Bool)
(declare-fun P27 () Bool)
(declare-fun P28 () Bool)
(declare-fun P29 () Bool)
(declare-fun P30 () Bool)
(declare-fun P31 () Bool)
(declare-fun P32 () Bool)
(declare-fun P33 () Bool)
(declare-fun P34 () Bool)
(declare-fun P35 () Bool)
(declare-fun P36 () Bool)
(declare-fun P37 () Bool)
(declare-fun P43 () Bool)
(declare-fun P44 () Bool)
(declare-fun P45 () Bool)
(declare-fun P46 () Bool)
(declare-fun P47 () Bool)
(declare-fun P48 () Bool)
(assert (let ((?v_0 (not P10))) (let ((?v_2 (or ?v_0 (and P10 P30))) (?v_8 (and P10 P26))) (let ((?v_3 (= ?v_2 ?v_8)) (?v_1 (or ?v_0 (and P10 P28))) (?v_7 (and P10 P24))) (let ((?v_10 (not (= ?v_1 ?v_7))) (?v_6 (not ?v_3))) (let ((?v_4 (or (and ?v_3 (and ?v_1 ?v_10)) (and ?v_2 ?v_6)))) (let ((?v_5 (and P12 ?v_4))) (let ((?v_15 (not ?v_5)) (?v_9 (and ?v_1 ?v_7))) (let ((?v_12 (not (= ?v_6 ?v_9))) (?v_11 (or (and ?v_2 ?v_8) (and ?v_6 ?v_9)))) (let ((?v_13 (not ?v_11))) (let ((?v_14 (or (and ?v_12 ?v_13) (and (or (and ?v_10 ?v_11) (and ?v_11 (not (= ?v_10 ?v_11)))) (not (= ?v_12 ?v_13)))))) (let ((?v_16 (or (and P10 (or (and P32 ?v_15) (and ?v_5 ?v_14))) (and ?v_0 ?v_14)))) (let ((?v_18 (not ?v_16)) (?v_17 (or (and P10 (or (and P34 ?v_15) (and ?v_5 ?v_11))) (and ?v_0 ?v_11))) (?v_19 (and ?v_0 ?v_16))) (let ((?v_24 (and ?v_17 ?v_19)) (?v_20 (and P10 ?v_16))) (let ((?v_25 (and ?v_17 ?v_20)) (?v_22 (and ?v_0 ?v_18))) (let ((?v_26 (and ?v_17 ?v_22)) (?v_23 (and P10 ?v_18))) (let ((?v_27 (and ?v_17 ?v_23)) (?v_21 (not ?v_17))) (let ((?v_28 (and ?v_19 ?v_21)) (?v_29 (and ?v_20 ?v_21)) (?v_30 (and ?v_22 ?v_21)) (?v_31 (and ?v_23 ?v_21)) (?v_37 (not (= ?v_17 ?v_16))) (?v_45 (not P11))) (let ((?v_43 (or ?v_45 (and P11 P31))) (?v_49 (and P11 P27))) (let ((?v_44 (= ?v_49 ?v_43))) (let ((?v_48 (not ?v_44)) (?v_46 (or (and P11 P29) ?v_45)) (?v_47 (and P11 P25))) (let ((?v_54 (not (= ?v_47 ?v_46)))) (let ((?v_51 (or (and ?v_43 ?v_48) (and ?v_44 (and ?v_46 ?v_54)))) (?v_53 (and ?v_47 ?v_46))) (let ((?v_50 (or (and ?v_53 ?v_48) (and ?v_49 ?v_43))) (?v_52 (and P13 ?v_51))) (let ((?v_58 (not ?v_52))) (let ((?v_59 (or (and ?v_45 ?v_50) (and P11 (or (and ?v_50 ?v_52) (and P35 ?v_58))))) (?v_55 (not ?v_50)) (?v_56 (not (= ?v_53 ?v_48)))) (let ((?v_57 (or (and (not (= ?v_55 ?v_56)) (or (and ?v_50 (not (= ?v_50 ?v_54))) (and ?v_50 ?v_54))) (and ?v_55 ?v_56)))) (let ((?v_60 (or (and ?v_45 ?v_57) (and P11 (or (and ?v_52 ?v_57) (and P33 ?v_58))))) (?v_61 (not ?v_59))) (let ((?v_62 (not ?v_60))) (let ((?v_63 (and P11 ?v_62))) (let ((?v_67 (and ?v_61 ?v_63)) (?v_64 (and ?v_45 ?v_62))) (let ((?v_68 (and ?v_61 ?v_64)) (?v_65 (and P11 ?v_60))) (let ((?v_69 (and ?v_61 ?v_65)) (?v_66 (and ?v_45 ?v_60))) (let ((?v_70 (and ?v_61 ?v_66)) (?v_71 (and ?v_59 ?v_63)) (?v_72 (and ?v_59 ?v_64)) (?v_73 (and ?v_59 ?v_65)) (?v_74 (and ?v_59 ?v_66)) (?v_81 (not (= ?v_59 ?v_60))) (?v_38 (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (and (< (- F2 F0) 0) (and ?v_0 ?v_24)) (and (< (- F14 F0) 0) (and ?v_0 ?v_25))) (and (< (- F4 F0) 0) (and ?v_0 ?v_26))) (and (< (- F16 F0) 0) (and ?v_0 ?v_27))) (and (< (- F6 F0) 0) (and ?v_0 ?v_28))) (and (< (- F18 F0) 0) (and ?v_0 ?v_29))) (and (< (- F8 F0) 0) (and ?v_0 ?v_30))) (and (< (- F20 F0) 0) (and ?v_0 ?v_31))) (and (> (- F22 F2) 0) (and P10 ?v_24))) (and (> (- F22 F14) 0) (and P10 ?v_25))) (and (> (- F22 F4) 0) (and P10 ?v_26))) (and (> (- F22 F16) 0) (and P10 ?v_27))) (and (> (- F22 F6) 0) (and P10 ?v_28))) (and (> (- F22 F18) 0) (and P10 ?v_29))) (and (> (- F22 F8) 0) (and P10 ?v_30))) (and (> (- F22 F20) 0) (and P10 ?v_31))))) (let ((?v_33 (not ?v_38))) (let ((?v_32 (and ?v_5 ?v_33))) (let ((?v_36 (not ?v_32)) (?v_34 (and ?v_0 ?v_33))) (let ((?v_35 (not ?v_34)) (?v_39 (and ?v_5 ?v_38))) (let ((?v_42 (not ?v_39)) (?v_40 (and ?v_0 ?v_38))) (let ((?v_41 (not ?v_40)) (?v_75 (or (and (and P11 ?v_67) (> (- F23 F21) 0)) (or (and (and P11 ?v_68) (> (- F23 F9) 0)) (or (and (and P11 ?v_69) (> (- F23 F19) 0)) (or (and (and P11 ?v_70) (> (- F23 F7) 0)) (or (and (and P11 ?v_71) (> (- F23 F17) 0)) (or (and (and P11 ?v_72) (> (- F23 F5) 0)) (or (and (and P11 ?v_73) (> (- F23 F15) 0)) (or (and (and P11 ?v_74) (> (- F23 F3) 0)) (or (and (and ?v_45 ?v_67) (< (- F21 F1) 0)) (or (and (and ?v_45 ?v_68) (< (- F9 F1) 0)) (or (and (and ?v_45 ?v_69) (< (- F19 F1) 0)) (or (and (and ?v_45 ?v_70) (< (- F7 F1) 0)) (or (and (and ?v_45 ?v_71) (< (- F17 F1) 0)) (or (and (and ?v_45 ?v_72) (< (- F5 F1) 0)) (or (and (and ?v_45 ?v_73) (< (- F15 F1) 0)) (and (and ?v_45 ?v_74) (< (- F3 F1) 0))))))))))))))))))) (let ((?v_77 (and ?v_45 ?v_75)) (?v_76 (and ?v_52 ?v_75))) (let ((?v_79 (not ?v_76)) (?v_78 (not ?v_77)) (?v_80 (not ?v_75))) (let ((?v_83 (and ?v_80 ?v_45)) (?v_82 (and ?v_80 ?v_52))) (let ((?v_85 (not ?v_82)) (?v_84 (not ?v_83))) (not (or (not (and (and (and (and (and (and (and (= (- cvclZero F22) 0) (and (= (- cvclZero F20) 0) (and (= (- cvclZero F18) 0) (and (and (= (- cvclZero F14) 0) (and ?v_0 (not P12))) (= (- cvclZero F16) 0))))) (not P24)) (not P26)) (not P28)) (not P30)) (not P32)) (not P34))) (or (not (and (and (or (and P10 (<= (- F18 F16) 0)) (and ?v_0 (<= (- F6 F4) 0))) (or (and P10 (<= (- F16 F14) 0)) (and ?v_0 (<= (- F4 F2) 0)))) (or (and ?v_0 (<= (- F8 F6) 0)) (and P10 (<= (- F20 F18) 0))))) (or (and P12 (not ?v_4)) (or (not (and (and (and (and (and (and (and (and (and (and (and (and P11 (= P13 (or ?v_0 ?v_5))) (or (and ?v_0 (= (- F15 F2) 0)) (and P10 (= (- F15 F14) 0)))) (or (and ?v_0 (= (- F17 F4) 0)) (and P10 (= (- F17 F16) 0)))) (or (and ?v_0 (= (- F19 F6) 0)) (and P10 (= (- F19 F18) 0)))) (or (and ?v_0 (= (- F21 F8) 0)) (and P10 (= (- F21 F20) 0)))) (or (and P10 (= (- F23 F22) 0)) (and ?v_0 (= (- F23 F0) 0)))) (= P25 (or (and (or (and ?v_18 ?v_32) (and ?v_7 ?v_36)) ?v_35) (and ?v_18 ?v_34)))) (= P27 (or (and ?v_35 (or (and ?v_8 ?v_36) (and ?v_32 ?v_37))) (and ?v_34 ?v_37)))) (= P29 (or (and (or (and ?v_16 ?v_39) (and ?v_1 ?v_42)) ?v_41) (and ?v_16 ?v_40)))) (= P31 (or (and ?v_41 (or (and ?v_17 ?v_39) (and ?v_2 ?v_42))) (and ?v_17 ?v_40)))) (= ?v_16 P33)) (= ?v_17 P35))) (or (and P13 (not ?v_51)) (not (and (= P48 ?v_59) (and (= P47 ?v_60) (and (= (or (and ?v_59 ?v_77) (and (or (and ?v_43 ?v_79) (and ?v_59 ?v_76)) ?v_78)) P46) (and (= (or (and ?v_60 ?v_77) (and ?v_78 (or (and ?v_46 ?v_79) (and ?v_60 ?v_76)))) P45) (and (= (or (and ?v_83 ?v_81) (and (or (and ?v_82 ?v_81) (and ?v_85 ?v_49)) ?v_84)) P44) (and (= (or (and ?v_83 ?v_62) (and ?v_84 (or (and ?v_85 ?v_47) (and ?v_82 ?v_62)))) P43) (and (or (and ?v_45 (= (- F42 F1) 0)) (and P11 (= (- F42 F23) 0))) (and (or (and P11 (= (- F41 F21) 0)) (and ?v_45 (= (- F41 F9) 0))) (and (or (and P11 (= (- F40 F19) 0)) (and ?v_45 (= (- F40 F7) 0))) (and (or (and P11 (= (- F39 F17) 0)) (and (= (- F39 F5) 0) ?v_45)) (and (or (and P11 (= (- F38 F15) 0)) (and ?v_45 (= (- F38 F3) 0))) (and (= (or ?v_45 ?v_52) P37) P36)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
(exit)

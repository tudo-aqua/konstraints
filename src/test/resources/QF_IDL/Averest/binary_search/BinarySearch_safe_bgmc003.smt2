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
(declare-fun P59 () Bool)
(declare-fun P60 () Bool)
(declare-fun P66 () Bool)
(declare-fun P67 () Bool)
(declare-fun P68 () Bool)
(declare-fun P69 () Bool)
(declare-fun P70 () Bool)
(declare-fun P71 () Bool)
(assert (let ((?v_0 (not P10))) (let ((?v_2 (or ?v_0 (and P10 P30))) (?v_4 (and P10 P26))) (let ((?v_3 (= ?v_2 ?v_4)) (?v_1 (or ?v_0 (and P10 P28))) (?v_5 (and P10 P24))) (let ((?v_32 (not (= ?v_1 ?v_5))) (?v_30 (not ?v_3))) (let ((?v_28 (or (and ?v_3 (and ?v_1 ?v_32)) (and ?v_2 ?v_30))) (?v_16 (and ?v_0 ?v_5))) (let ((?v_7 (and ?v_4 ?v_16)) (?v_19 (and P10 ?v_5))) (let ((?v_8 (and ?v_4 ?v_19)) (?v_12 (not ?v_5))) (let ((?v_22 (and ?v_0 ?v_12))) (let ((?v_11 (and ?v_4 ?v_22)) (?v_25 (and P10 ?v_12))) (let ((?v_14 (and ?v_4 ?v_25)) (?v_18 (not ?v_4))) (let ((?v_17 (and ?v_18 ?v_16)) (?v_21 (and ?v_18 ?v_19)) (?v_24 (and ?v_18 ?v_22)) (?v_26 (and ?v_18 ?v_25)) (?v_29 (and P12 ?v_28))) (let ((?v_38 (not ?v_29)) (?v_31 (and ?v_1 ?v_5))) (let ((?v_34 (not (= ?v_30 ?v_31))) (?v_33 (or (and ?v_2 ?v_4) (and ?v_30 ?v_31)))) (let ((?v_35 (not ?v_33))) (let ((?v_36 (or (and ?v_34 ?v_35) (and (or (and ?v_32 ?v_33) (and ?v_33 (not (= ?v_32 ?v_33)))) (not (= ?v_34 ?v_35)))))) (let ((?v_39 (or (and P10 (or (and P32 ?v_38) (and ?v_29 ?v_36))) (and ?v_0 ?v_36)))) (let ((?v_43 (not ?v_39)) (?v_41 (or (and P10 (or (and P34 ?v_38) (and ?v_29 ?v_33))) (and ?v_0 ?v_33))) (?v_46 (and ?v_0 ?v_39))) (let ((?v_55 (and ?v_41 ?v_46)) (?v_48 (and P10 ?v_39))) (let ((?v_57 (and ?v_41 ?v_48)) (?v_51 (and ?v_0 ?v_43))) (let ((?v_59 (and ?v_41 ?v_51)) (?v_53 (and P10 ?v_43))) (let ((?v_61 (and ?v_41 ?v_53)) (?v_49 (not ?v_41))) (let ((?v_63 (and ?v_46 ?v_49)) (?v_65 (and ?v_48 ?v_49)) (?v_67 (and ?v_51 ?v_49)) (?v_69 (and ?v_53 ?v_49)) (?v_75 (not (= ?v_41 ?v_39))) (?v_83 (not P11))) (let ((?v_81 (or ?v_83 (and P11 P31))) (?v_86 (and P11 P27))) (let ((?v_82 (= ?v_86 ?v_81))) (let ((?v_121 (not ?v_82)) (?v_84 (or ?v_83 (and P11 P29))) (?v_85 (and P11 P25))) (let ((?v_126 (not (= ?v_85 ?v_84)))) (let ((?v_123 (or (and ?v_81 ?v_121) (and ?v_82 (and ?v_84 ?v_126)))) (?v_88 (not ?v_85))) (let ((?v_93 (and P11 ?v_88)) (?v_89 (not ?v_86))) (let ((?v_87 (and ?v_93 ?v_89)) (?v_95 (and ?v_83 ?v_88))) (let ((?v_90 (and ?v_95 ?v_89)) (?v_97 (and P11 ?v_85))) (let ((?v_91 (and ?v_89 ?v_97)) (?v_99 (and ?v_83 ?v_85))) (let ((?v_92 (and ?v_89 ?v_99)) (?v_94 (and ?v_93 ?v_86)) (?v_96 (and ?v_95 ?v_86)) (?v_98 (and ?v_86 ?v_97)) (?v_100 (and ?v_86 ?v_99)) (?v_105 (and P59 P67)) (?v_103 (not P59))) (let ((?v_101 (or (and P69 P59) ?v_103))) (let ((?v_102 (= ?v_105 ?v_101)) (?v_104 (or ?v_103 (and P59 P68))) (?v_106 (and P66 P59)) (?v_107 (not ?v_105))) (let ((?v_108 (not ?v_106))) (let ((?v_109 (and ?v_108 P59))) (let ((?v_120 (and ?v_107 ?v_109)) (?v_110 (and ?v_108 ?v_103))) (let ((?v_119 (and ?v_107 ?v_110)) (?v_112 (and P59 ?v_106))) (let ((?v_118 (and ?v_107 ?v_112)) (?v_115 (and ?v_109 ?v_105)) (?v_114 (and ?v_110 ?v_105)) (?v_116 (and ?v_106 ?v_103))) (let ((?v_111 (and ?v_105 ?v_116)) (?v_113 (and ?v_112 ?v_105)) (?v_117 (and ?v_107 ?v_116)) (?v_125 (and ?v_85 ?v_84))) (let ((?v_122 (or (and ?v_86 ?v_81) (and ?v_125 ?v_121))) (?v_124 (and P13 ?v_123))) (let ((?v_130 (not ?v_124))) (let ((?v_131 (or (and ?v_83 ?v_122) (and P11 (or (and ?v_122 ?v_124) (and P35 ?v_130))))) (?v_127 (not ?v_122)) (?v_128 (not (= ?v_125 ?v_121)))) (let ((?v_129 (or (and (not (= ?v_127 ?v_128)) (or (and ?v_122 (not (= ?v_126 ?v_122))) (and ?v_126 ?v_122))) (and ?v_127 ?v_128)))) (let ((?v_132 (or (and ?v_83 ?v_129) (and P11 (or (and ?v_124 ?v_129) (and P33 ?v_130))))) (?v_134 (not ?v_131))) (let ((?v_135 (not ?v_132))) (let ((?v_139 (and P11 ?v_135))) (let ((?v_147 (and ?v_134 ?v_139)) (?v_141 (and ?v_83 ?v_135))) (let ((?v_149 (and ?v_134 ?v_141)) (?v_143 (and P11 ?v_132))) (let ((?v_151 (and ?v_134 ?v_143)) (?v_146 (and ?v_83 ?v_132))) (let ((?v_153 (and ?v_134 ?v_146)) (?v_155 (and ?v_131 ?v_139)) (?v_157 (and ?v_131 ?v_141)) (?v_159 (and ?v_131 ?v_143)) (?v_161 (and ?v_131 ?v_146)) (?v_168 (not (= ?v_131 ?v_132))) (?v_68 (- F22 F20))) (let ((?v_27 (= ?v_68 0)) (?v_50 (- F8 F0))) (let ((?v_23 (= ?v_50 0)) (?v_37 (- F2 F0))) (let ((?v_6 (= ?v_37 0)) (?v_56 (- F22 F14))) (let ((?v_9 (= ?v_56 0)) (?v_42 (- F4 F0))) (let ((?v_10 (= ?v_42 0)) (?v_60 (- F22 F16))) (let ((?v_13 (= ?v_60 0)) (?v_64 (- F22 F18))) (let ((?v_20 (= ?v_64 0)) (?v_45 (- F6 F0))) (let ((?v_15 (= ?v_45 0)) (?v_40 (- F14 F0)) (?v_44 (- F16 F0)) (?v_47 (- F18 F0)) (?v_52 (- F20 F0)) (?v_54 (- F22 F2)) (?v_58 (- F22 F4)) (?v_62 (- F22 F6)) (?v_66 (- F22 F8))) (let ((?v_76 (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (and (< ?v_37 0) (and ?v_0 ?v_55)) (and (< ?v_40 0) (and ?v_0 ?v_57))) (and (< ?v_42 0) (and ?v_0 ?v_59))) (and (< ?v_44 0) (and ?v_0 ?v_61))) (and (< ?v_45 0) (and ?v_0 ?v_63))) (and (< ?v_47 0) (and ?v_0 ?v_65))) (and (< ?v_50 0) (and ?v_0 ?v_67))) (and (< ?v_52 0) (and ?v_0 ?v_69))) (and (> ?v_54 0) (and P10 ?v_55))) (and (> ?v_56 0) (and P10 ?v_57))) (and (> ?v_58 0) (and P10 ?v_59))) (and (> ?v_60 0) (and P10 ?v_61))) (and (> ?v_62 0) (and P10 ?v_63))) (and (> ?v_64 0) (and P10 ?v_65))) (and (> ?v_66 0) (and P10 ?v_67))) (and (> ?v_68 0) (and P10 ?v_69))))) (let ((?v_71 (not ?v_76))) (let ((?v_70 (and ?v_29 ?v_71))) (let ((?v_74 (not ?v_70)) (?v_72 (and ?v_0 ?v_71))) (let ((?v_73 (not ?v_72)) (?v_77 (and ?v_29 ?v_76))) (let ((?v_80 (not ?v_77)) (?v_78 (and ?v_0 ?v_76))) (let ((?v_79 (not ?v_78)) (?v_133 (- F23 F21)) (?v_136 (- F23 F9)) (?v_137 (- F23 F19)) (?v_138 (- F23 F7)) (?v_140 (- F23 F17)) (?v_142 (- F23 F5)) (?v_144 (- F23 F15)) (?v_145 (- F23 F3)) (?v_148 (- F21 F1)) (?v_150 (- F9 F1)) (?v_152 (- F19 F1)) (?v_154 (- F7 F1)) (?v_156 (- F17 F1)) (?v_158 (- F5 F1)) (?v_160 (- F15 F1)) (?v_162 (- F3 F1))) (let ((?v_163 (or (and (and P11 ?v_147) (> ?v_133 0)) (or (and (and P11 ?v_149) (> ?v_136 0)) (or (and (and P11 ?v_151) (> ?v_137 0)) (or (and (and P11 ?v_153) (> ?v_138 0)) (or (and (and P11 ?v_155) (> ?v_140 0)) (or (and (and P11 ?v_157) (> ?v_142 0)) (or (and (and P11 ?v_159) (> ?v_144 0)) (or (and (> ?v_145 0) (and P11 ?v_161)) (or (and (and ?v_83 ?v_147) (< ?v_148 0)) (or (and (and ?v_83 ?v_149) (< ?v_150 0)) (or (and (and ?v_83 ?v_151) (< ?v_152 0)) (or (and (and ?v_83 ?v_153) (< ?v_154 0)) (or (and (and ?v_83 ?v_155) (< ?v_156 0)) (or (and (and ?v_83 ?v_157) (< ?v_158 0)) (or (and (and ?v_83 ?v_159) (< ?v_160 0)) (and (and ?v_83 ?v_161) (< ?v_162 0))))))))))))))))))) (let ((?v_165 (and ?v_83 ?v_163)) (?v_164 (and ?v_124 ?v_163))) (let ((?v_167 (not ?v_164)) (?v_166 (not ?v_165)) (?v_169 (not ?v_163))) (let ((?v_171 (and ?v_83 ?v_169)) (?v_170 (and ?v_124 ?v_169))) (let ((?v_173 (not ?v_170)) (?v_172 (not ?v_171))) (and (and (and (and (and (and (and (and (= (- cvclZero F22) 0) (and (= (- cvclZero F20) 0) (and (= (- cvclZero F18) 0) (and (and (= (- cvclZero F14) 0) (and ?v_0 (not P12))) (= (- cvclZero F16) 0))))) (not P24)) (not P26)) (not P28)) (not P30)) (not P32)) (not P34)) (and (and (and (and (or (and P10 (<= (- F18 F16) 0)) (and ?v_0 (<= (- F6 F4) 0))) (or (and P10 (<= (- F16 F14) 0)) (and ?v_0 (<= (- F4 F2) 0)))) (or (and ?v_0 (<= (- F8 F6) 0)) (and P10 (<= (- F20 F18) 0)))) (or (or (and P10 ?v_27) (and ?v_0 ?v_23)) (or (or (or (and ?v_0 ?v_6) (and P10 ?v_9)) (or (and ?v_0 ?v_10) (and P10 ?v_13))) (or (and P10 ?v_20) (and ?v_0 ?v_15))))) (or (not (or (not (and P12 (not ?v_28))) (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (and (and ?v_0 ?v_7) ?v_6) (and (and P10 ?v_7) (= ?v_54 0))) (and (and ?v_0 ?v_8) (= ?v_40 0))) (and (and P10 ?v_8) ?v_9)) (and (and ?v_0 ?v_11) ?v_10)) (and (= ?v_58 0) (and P10 ?v_11))) (and (and ?v_0 ?v_14) (= ?v_44 0))) (and ?v_13 (and P10 ?v_14))) (and ?v_15 (and ?v_0 ?v_17))) (and (= ?v_62 0) (and P10 ?v_17))) (and (= ?v_47 0) (and ?v_0 ?v_21))) (and ?v_20 (and P10 ?v_21))) (and (and ?v_0 ?v_24) ?v_23)) (and (and P10 ?v_24) (= ?v_66 0))) (and (and ?v_0 ?v_26) (= ?v_52 0))) (and (and P10 ?v_26) ?v_27)))) (and (and (and (and (and (and (and (and (and (and (and (and (and P11 (= P13 (or ?v_0 ?v_29))) (or (and ?v_0 (= (- F15 F2) 0)) (and P10 (= (- F15 F14) 0)))) (or (and ?v_0 (= (- F17 F4) 0)) (and P10 (= (- F17 F16) 0)))) (or (and ?v_0 (= (- F19 F6) 0)) (and P10 (= (- F19 F18) 0)))) (or (and ?v_0 (= (- F21 F8) 0)) (and P10 (= (- F21 F20) 0)))) (or (and P10 (= (- F23 F22) 0)) (and ?v_0 (= (- F23 F0) 0)))) (= P25 (or (and (or (and ?v_43 ?v_70) (and ?v_5 ?v_74)) ?v_73) (and ?v_43 ?v_72)))) (= P27 (or (and ?v_73 (or (and ?v_4 ?v_74) (and ?v_70 ?v_75))) (and ?v_72 ?v_75)))) (= P29 (or (and (or (and ?v_39 ?v_77) (and ?v_1 ?v_80)) ?v_79) (and ?v_39 ?v_78)))) (= P31 (or (and ?v_79 (or (and ?v_41 ?v_77) (and ?v_2 ?v_80))) (and ?v_41 ?v_78)))) (= ?v_39 P33)) (= ?v_41 P35)) (or (not (or (not (and P13 (not ?v_123))) (or (and (and P11 ?v_87) (= ?v_133 0)) (or (and (and ?v_83 ?v_87) (= ?v_148 0)) (or (and (= ?v_136 0) (and P11 ?v_90)) (or (and (= ?v_150 0) (and ?v_83 ?v_90)) (or (and (and P11 ?v_91) (= ?v_137 0)) (or (and (and ?v_83 ?v_91) (= ?v_152 0)) (or (and (and P11 ?v_92) (= ?v_138 0)) (or (and (and ?v_83 ?v_92) (= ?v_154 0)) (or (and (and P11 ?v_94) (= ?v_140 0)) (or (and (= ?v_156 0) (and ?v_83 ?v_94)) (or (and (and P11 ?v_96) (= ?v_142 0)) (or (and (= ?v_158 0) (and ?v_83 ?v_96)) (or (and (= ?v_144 0) (and P11 ?v_98)) (or (and (= ?v_160 0) (and ?v_83 ?v_98)) (or (and (= ?v_145 0) (and P11 ?v_100)) (and (= ?v_162 0) (and ?v_83 ?v_100))))))))))))))))))) (and (not (or (not (and P60 (not (or (and (not ?v_102) ?v_101) (and ?v_102 (and (not (= ?v_104 ?v_106)) ?v_104)))))) (or (or (and (and ?v_120 ?v_103) (= (- F64 F54) 0)) (or (or (and (= (- F58 F54) 0) (and ?v_103 ?v_119)) (or (or (and (= (- F63 F54) 0) (and ?v_118 ?v_103)) (or (or (or (and (and ?v_115 P59) (= (- F65 F62) 0)) (or (or (or (and (= (- F56 F54) 0) (and ?v_114 ?v_103)) (or (or (or (and (= (- F65 F55) 0) (and P59 ?v_111)) (and (= (- F55 F54) 0) (and ?v_103 ?v_111))) (and (= (- F61 F54) 0) (and ?v_113 ?v_103))) (and (= (- F65 F61) 0) (and ?v_113 P59)))) (and (= (- F65 F56) 0) (and ?v_114 P59))) (and (= (- F62 F54) 0) (and ?v_115 ?v_103)))) (and (= (- F57 F54) 0) (and ?v_103 ?v_117))) (and (= (- F65 F57) 0) (and P59 ?v_117)))) (and (= (- F65 F63) 0) (and ?v_118 P59)))) (and (and P59 ?v_119) (= (- F65 F58) 0)))) (and (= (- F65 F64) 0) (and ?v_120 P59))))) (and (= ?v_131 P71) (and (= P70 ?v_132) (and (= P69 (or (and ?v_131 ?v_165) (and (or (and ?v_81 ?v_167) (and ?v_131 ?v_164)) ?v_166))) (and (= (or (and ?v_132 ?v_165) (and ?v_166 (or (and ?v_84 ?v_167) (and ?v_132 ?v_164)))) P68) (and (= P67 (or (and ?v_168 ?v_171) (and (or (and ?v_168 ?v_170) (and ?v_86 ?v_173)) ?v_172))) (and (= P66 (or (and ?v_135 ?v_171) (and ?v_172 (or (and ?v_85 ?v_173) (and ?v_135 ?v_170))))) (and (or (and ?v_83 (= (- F65 F1) 0)) (and P11 (= (- F65 F23) 0))) (and (or (and P11 (= (- F64 F21) 0)) (and ?v_83 (= (- F64 F9) 0))) (and (or (and P11 (= (- F63 F19) 0)) (and ?v_83 (= (- F63 F7) 0))) (and (or (and P11 (= (- F62 F17) 0)) (and ?v_83 (= (- F62 F5) 0))) (and (or (and P11 (= (- F61 F15) 0)) (and ?v_83 (= (- F61 F3) 0))) (and P59 (= (or ?v_83 ?v_124) P60)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
(exit)

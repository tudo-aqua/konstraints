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
(declare-fun x_6 () Real)
(declare-fun x_7 () Real)
(declare-fun x_8 () Real)
(declare-fun x_9 () Real)
(declare-fun x_10 () Real)
(declare-fun x_11 () Bool)
(declare-fun x_12 () Bool)
(declare-fun x_13 () Real)
(declare-fun x_14 () Bool)
(declare-fun x_15 () Bool)
(declare-fun x_16 () Bool)
(declare-fun x_17 () Bool)
(declare-fun x_18 () Real)
(declare-fun x_19 () Real)
(declare-fun x_20 () Real)
(declare-fun x_21 () Real)
(declare-fun x_22 () Real)
(declare-fun x_23 () Real)
(declare-fun x_24 () Real)
(declare-fun x_25 () Bool)
(declare-fun x_26 () Bool)
(declare-fun x_27 () Real)
(declare-fun x_28 () Bool)
(declare-fun x_29 () Bool)
(declare-fun x_30 () Bool)
(declare-fun x_31 () Bool)
(declare-fun x_32 () Real)
(declare-fun x_33 () Real)
(declare-fun x_34 () Real)
(declare-fun x_35 () Real)
(declare-fun x_36 () Real)
(declare-fun x_37 () Real)
(declare-fun x_38 () Real)
(declare-fun x_39 () Bool)
(declare-fun x_40 () Bool)
(declare-fun x_41 () Real)
(declare-fun x_42 () Bool)
(declare-fun x_43 () Bool)
(declare-fun x_44 () Bool)
(declare-fun x_45 () Bool)
(declare-fun x_46 () Real)
(declare-fun x_47 () Real)
(declare-fun x_48 () Real)
(declare-fun x_49 () Real)
(declare-fun x_50 () Real)
(declare-fun x_51 () Real)
(declare-fun x_52 () Real)
(declare-fun x_53 () Bool)
(declare-fun x_54 () Bool)
(declare-fun x_55 () Real)
(declare-fun x_56 () Bool)
(declare-fun x_57 () Bool)
(declare-fun x_58 () Bool)
(declare-fun x_59 () Bool)
(declare-fun x_60 () Real)
(declare-fun x_61 () Real)
(declare-fun x_62 () Real)
(declare-fun x_63 () Real)
(declare-fun x_64 () Real)
(declare-fun x_65 () Real)
(declare-fun x_66 () Real)
(declare-fun x_67 () Bool)
(declare-fun x_68 () Bool)
(declare-fun x_69 () Real)
(declare-fun x_70 () Bool)
(declare-fun x_71 () Bool)
(declare-fun x_72 () Bool)
(declare-fun x_73 () Bool)
(declare-fun x_74 () Real)
(declare-fun x_75 () Real)
(declare-fun x_76 () Real)
(declare-fun x_77 () Real)
(declare-fun x_78 () Real)
(declare-fun x_79 () Real)
(assert (let ((?v_22 (not x_67)) (?v_23 (not x_68))) (let ((?v_24 (and ?v_22 ?v_23)) (?v_60 (not x_70)) (?v_61 (not x_71))) (let ((?v_62 (and ?v_60 ?v_61)) (?v_45 (not x_72)) (?v_46 (not x_73))) (let ((?v_48 (and ?v_45 ?v_46)) (?v_27 (and (= x_70 x_56) (= x_71 x_57))) (?v_57 (not x_56)) (?v_55 (not x_57))) (let ((?v_52 (and ?v_57 ?v_55)) (?v_16 (and (= x_67 x_53) (= x_68 x_54))) (?v_41 (not x_58)) (?v_38 (not x_59))) (let ((?v_33 (and ?v_41 ?v_38)) (?v_58 (and ?v_57 x_57)) (?v_25 (and (= x_72 x_58) (= x_73 x_59))) (?v_43 (and ?v_41 x_59)) (?v_19 (not x_53)) (?v_17 (not x_54))) (let ((?v_12 (and ?v_19 ?v_17)) (?v_20 (and ?v_19 x_54)) (?v_81 (and (= x_56 x_42) (= x_57 x_43))) (?v_107 (not x_42)) (?v_105 (not x_43))) (let ((?v_102 (and ?v_107 ?v_105)) (?v_73 (and (= x_53 x_39) (= x_54 x_40))) (?v_95 (not x_44)) (?v_92 (not x_45))) (let ((?v_87 (and ?v_95 ?v_92)) (?v_108 (and ?v_107 x_43)) (?v_79 (and (= x_58 x_44) (= x_59 x_45))) (?v_97 (and ?v_95 x_45)) (?v_76 (not x_39)) (?v_74 (not x_40))) (let ((?v_69 (and ?v_76 ?v_74)) (?v_77 (and ?v_76 x_40)) (?v_128 (and (= x_42 x_28) (= x_43 x_29))) (?v_154 (not x_28)) (?v_152 (not x_29))) (let ((?v_149 (and ?v_154 ?v_152)) (?v_120 (and (= x_39 x_25) (= x_40 x_26))) (?v_142 (not x_30)) (?v_139 (not x_31))) (let ((?v_134 (and ?v_142 ?v_139)) (?v_155 (and ?v_154 x_29)) (?v_126 (and (= x_44 x_30) (= x_45 x_31))) (?v_144 (and ?v_142 x_31)) (?v_123 (not x_25)) (?v_121 (not x_26))) (let ((?v_116 (and ?v_123 ?v_121)) (?v_124 (and ?v_123 x_26)) (?v_175 (and (= x_28 x_14) (= x_29 x_15))) (?v_201 (not x_14)) (?v_199 (not x_15))) (let ((?v_196 (and ?v_201 ?v_199)) (?v_167 (and (= x_25 x_11) (= x_26 x_12))) (?v_189 (not x_16)) (?v_186 (not x_17))) (let ((?v_181 (and ?v_189 ?v_186)) (?v_202 (and ?v_201 x_15)) (?v_173 (and (= x_30 x_16) (= x_31 x_17))) (?v_191 (and ?v_189 x_17)) (?v_170 (not x_11)) (?v_168 (not x_12))) (let ((?v_163 (and ?v_170 ?v_168)) (?v_171 (and ?v_170 x_12)) (?v_225 (and (= x_14 x_4) (= x_15 x_5))) (?v_251 (not x_4)) (?v_249 (not x_5))) (let ((?v_245 (and ?v_251 ?v_249)) (?v_217 (and (= x_11 x_0) (= x_12 x_1))) (?v_239 (not x_2)) (?v_236 (not x_3))) (let ((?v_229 (and ?v_239 ?v_236)) (?v_252 (and ?v_251 x_5)) (?v_223 (and (= x_16 x_2) (= x_17 x_3))) (?v_241 (and ?v_239 x_3)) (?v_220 (not x_0)) (?v_218 (not x_1))) (let ((?v_210 (and ?v_220 ?v_218)) (?v_221 (and ?v_220 x_1)) (?v_211 (- cvclZero x_6))) (let ((?v_207 (< ?v_211 0)) (?v_230 (- cvclZero x_7))) (let ((?v_206 (< ?v_230 0)) (?v_246 (- cvclZero x_8))) (let ((?v_205 (< ?v_246 0)) (?v_0 (- x_9 cvclZero))) (let ((?v_212 (= ?v_0 0)) (?v_6 (< (- x_60 x_61) 0))) (let ((?v_7 (ite ?v_6 (< (- x_60 x_62) 0) (< (- x_61 x_62) 0))) (?v_50 (= (- x_76 x_62) 0)) (?v_26 (= (- x_75 x_61) 0)) (?v_28 (= (- x_74 x_60) 0)) (?v_10 (= (- x_69 x_55) 0)) (?v_11 (- x_66 cvclZero))) (let ((?v_30 (= ?v_11 0)) (?v_9 (- x_64 x_62))) (let ((?v_13 (= ?v_9 0)) (?v_4 (- x_55 cvclZero))) (let ((?v_14 (= ?v_4 0)) (?v_18 (- x_64 x_76))) (let ((?v_15 (< ?v_18 0)) (?v_32 (= ?v_11 1)) (?v_35 (not ?v_14)) (?v_37 (= ?v_11 2)) (?v_5 (- x_69 cvclZero))) (let ((?v_254 (= ?v_5 1)) (?v_40 (= ?v_11 3)) (?v_21 (= ?v_4 1)) (?v_42 (= ?v_11 4))) (let ((?v_257 (not ?v_21)) (?v_47 (= ?v_11 5)) (?v_49 (= ?v_5 0)) (?v_31 (- x_64 x_61))) (let ((?v_34 (= ?v_31 0)) (?v_39 (- x_64 x_75))) (let ((?v_36 (< ?v_39 0)) (?v_255 (= ?v_5 2)) (?v_44 (= ?v_4 2))) (let ((?v_258 (not ?v_44)) (?v_51 (- x_64 x_60))) (let ((?v_53 (= ?v_51 0)) (?v_56 (- x_64 x_74))) (let ((?v_54 (< ?v_56 0)) (?v_256 (= ?v_5 3)) (?v_59 (= ?v_4 3))) (let ((?v_259 (not ?v_59)) (?v_63 (< (- x_46 x_47) 0))) (let ((?v_64 (ite ?v_63 (< (- x_46 x_48) 0) (< (- x_47 x_48) 0))) (?v_100 (= (- x_62 x_48) 0)) (?v_80 (= (- x_61 x_47) 0)) (?v_82 (= (- x_60 x_46) 0)) (?v_67 (= (- x_55 x_41) 0)) (?v_68 (- x_52 cvclZero))) (let ((?v_84 (= ?v_68 0)) (?v_66 (- x_50 x_48))) (let ((?v_70 (= ?v_66 0)) (?v_3 (- x_41 cvclZero))) (let ((?v_71 (= ?v_3 0)) (?v_75 (- x_50 x_62))) (let ((?v_72 (< ?v_75 0)) (?v_86 (= ?v_68 1)) (?v_89 (not ?v_71)) (?v_91 (= ?v_68 2)) (?v_94 (= ?v_68 3)) (?v_78 (= ?v_3 1)) (?v_96 (= ?v_68 4))) (let ((?v_260 (not ?v_78)) (?v_99 (= ?v_68 5)) (?v_85 (- x_50 x_47))) (let ((?v_88 (= ?v_85 0)) (?v_93 (- x_50 x_61))) (let ((?v_90 (< ?v_93 0)) (?v_98 (= ?v_3 2))) (let ((?v_261 (not ?v_98)) (?v_101 (- x_50 x_46))) (let ((?v_103 (= ?v_101 0)) (?v_106 (- x_50 x_60))) (let ((?v_104 (< ?v_106 0)) (?v_109 (= ?v_3 3))) (let ((?v_262 (not ?v_109)) (?v_110 (< (- x_32 x_33) 0))) (let ((?v_111 (ite ?v_110 (< (- x_32 x_34) 0) (< (- x_33 x_34) 0))) (?v_147 (= (- x_48 x_34) 0)) (?v_127 (= (- x_47 x_33) 0)) (?v_129 (= (- x_46 x_32) 0)) (?v_114 (= (- x_41 x_27) 0)) (?v_115 (- x_38 cvclZero))) (let ((?v_131 (= ?v_115 0)) (?v_113 (- x_36 x_34))) (let ((?v_117 (= ?v_113 0)) (?v_2 (- x_27 cvclZero))) (let ((?v_118 (= ?v_2 0)) (?v_122 (- x_36 x_48))) (let ((?v_119 (< ?v_122 0)) (?v_133 (= ?v_115 1)) (?v_136 (not ?v_118)) (?v_138 (= ?v_115 2)) (?v_141 (= ?v_115 3)) (?v_125 (= ?v_2 1)) (?v_143 (= ?v_115 4))) (let ((?v_263 (not ?v_125)) (?v_146 (= ?v_115 5)) (?v_132 (- x_36 x_33))) (let ((?v_135 (= ?v_132 0)) (?v_140 (- x_36 x_47))) (let ((?v_137 (< ?v_140 0)) (?v_145 (= ?v_2 2))) (let ((?v_264 (not ?v_145)) (?v_148 (- x_36 x_32))) (let ((?v_150 (= ?v_148 0)) (?v_153 (- x_36 x_46))) (let ((?v_151 (< ?v_153 0)) (?v_156 (= ?v_2 3))) (let ((?v_265 (not ?v_156)) (?v_157 (< (- x_18 x_19) 0))) (let ((?v_158 (ite ?v_157 (< (- x_18 x_20) 0) (< (- x_19 x_20) 0))) (?v_194 (= (- x_34 x_20) 0)) (?v_174 (= (- x_33 x_19) 0)) (?v_176 (= (- x_32 x_18) 0)) (?v_161 (= (- x_27 x_13) 0)) (?v_162 (- x_24 cvclZero))) (let ((?v_178 (= ?v_162 0)) (?v_160 (- x_22 x_20))) (let ((?v_164 (= ?v_160 0)) (?v_1 (- x_13 cvclZero))) (let ((?v_165 (= ?v_1 0)) (?v_169 (- x_22 x_34))) (let ((?v_166 (< ?v_169 0)) (?v_180 (= ?v_162 1)) (?v_183 (not ?v_165)) (?v_185 (= ?v_162 2)) (?v_188 (= ?v_162 3)) (?v_172 (= ?v_1 1)) (?v_190 (= ?v_162 4))) (let ((?v_266 (not ?v_172)) (?v_193 (= ?v_162 5)) (?v_179 (- x_22 x_19))) (let ((?v_182 (= ?v_179 0)) (?v_187 (- x_22 x_33))) (let ((?v_184 (< ?v_187 0)) (?v_192 (= ?v_1 2))) (let ((?v_267 (not ?v_192)) (?v_195 (- x_22 x_18))) (let ((?v_197 (= ?v_195 0)) (?v_200 (- x_22 x_32))) (let ((?v_198 (< ?v_200 0)) (?v_203 (= ?v_1 3))) (let ((?v_268 (not ?v_203)) (?v_204 (< (- x_8 x_7) 0))) (let ((?v_208 (ite ?v_204 (< (- x_8 x_6) 0) (< (- x_7 x_6) 0))) (?v_244 (= (- x_20 x_6) 0)) (?v_224 (= (- x_19 x_7) 0)) (?v_226 (= (- x_18 x_8) 0)) (?v_213 (= (- x_13 x_9) 0)) (?v_214 (- x_10 cvclZero))) (let ((?v_228 (= ?v_214 0)) (?v_215 (= ?v_211 0)) (?v_219 (- cvclZero x_20))) (let ((?v_216 (< ?v_219 0)) (?v_231 (= ?v_214 1)) (?v_233 (not ?v_212)) (?v_235 (= ?v_214 2)) (?v_238 (= ?v_214 3)) (?v_222 (= ?v_0 1)) (?v_240 (= ?v_214 4))) (let ((?v_269 (not ?v_222)) (?v_243 (= ?v_214 5)) (?v_232 (= ?v_230 0)) (?v_237 (- cvclZero x_19))) (let ((?v_234 (< ?v_237 0)) (?v_242 (= ?v_0 2))) (let ((?v_270 (not ?v_242)) (?v_247 (= ?v_246 0)) (?v_250 (- cvclZero x_18))) (let ((?v_248 (< ?v_250 0)) (?v_253 (= ?v_0 3))) (let ((?v_271 (not ?v_253)) (?v_8 (- x_77 cvclZero)) (?v_29 (- x_79 cvclZero)) (?v_65 (- x_63 cvclZero)) (?v_83 (- x_65 cvclZero)) (?v_112 (- x_49 cvclZero)) (?v_130 (- x_51 cvclZero)) (?v_159 (- x_35 cvclZero)) (?v_177 (- x_37 cvclZero)) (?v_209 (- x_21 cvclZero)) (?v_227 (- x_23 cvclZero))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (not (< ?v_0 0)) (<= ?v_0 3)) (not (< ?v_1 0))) (<= ?v_1 3)) (not (< ?v_2 0))) (<= ?v_2 3)) (not (< ?v_3 0))) (<= ?v_3 3)) (not (< ?v_4 0))) (<= ?v_4 3)) (not (< ?v_5 0))) (<= ?v_5 3)) ?v_210) ?v_229) ?v_245) ?v_207) ?v_206) ?v_205) ?v_212) (or (and (and (and (and (and (and (and (and (and (= ?v_8 0) (ite ?v_7 (ite ?v_6 (< ?v_51 0) (< ?v_31 0)) (< ?v_9 0))) (ite ?v_7 (ite ?v_6 (= (- x_78 x_60) 0) (= (- x_78 x_61) 0)) (= (- x_78 x_62) 0))) ?v_16) ?v_25) ?v_27) ?v_50) ?v_26) ?v_28) ?v_10) (and (and (= ?v_8 1) (or (or (and (and (and (and (and (= ?v_29 1) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_30 ?v_12) ?v_13) ?v_14) x_67) ?v_23) ?v_15) (<= (- x_76 x_64) 2)) ?v_10) (and (and (and (and (and (and ?v_32 ?v_12) ?v_13) ?v_35) ?v_15) ?v_10) ?v_16)) (and (and (and (and (and (and (and ?v_37 x_53) ?v_17) ?v_13) ?v_22) x_68) ?v_254) (<= ?v_18 (- 4)))) (and (and (and (and (and (and (and ?v_40 ?v_20) ?v_13) ?v_21) x_67) x_68) ?v_15) ?v_10)) (and (and (and (and (and (and ?v_42 ?v_20) ?v_13) ?v_257) ?v_24) ?v_15) ?v_10)) (and (and (and (and (and (and ?v_47 x_53) x_54) ?v_13) ?v_24) ?v_49) ?v_15))) ?v_25) ?v_26) ?v_27) ?v_28) (and (and (and (and (and (= ?v_29 2) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_30 ?v_33) ?v_34) ?v_14) x_72) ?v_46) ?v_36) (<= (- x_75 x_64) 2)) ?v_10) (and (and (and (and (and (and ?v_32 ?v_33) ?v_34) ?v_35) ?v_36) ?v_10) ?v_25)) (and (and (and (and (and (and (and ?v_37 x_58) ?v_38) ?v_34) ?v_45) x_73) ?v_255) (<= ?v_39 (- 4)))) (and (and (and (and (and (and (and ?v_40 ?v_43) ?v_34) ?v_44) x_72) x_73) ?v_36) ?v_10)) (and (and (and (and (and (and ?v_42 ?v_43) ?v_34) ?v_258) ?v_48) ?v_36) ?v_10)) (and (and (and (and (and (and ?v_47 x_58) x_59) ?v_34) ?v_48) ?v_49) ?v_36))) ?v_16) ?v_50) ?v_27) ?v_28)) (and (and (and (and (and (= ?v_29 3) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_30 ?v_52) ?v_53) ?v_14) x_70) ?v_61) ?v_54) (<= (- x_74 x_64) 2)) ?v_10) (and (and (and (and (and (and ?v_32 ?v_52) ?v_53) ?v_35) ?v_54) ?v_10) ?v_27)) (and (and (and (and (and (and (and ?v_37 x_56) ?v_55) ?v_53) ?v_60) x_71) ?v_256) (<= ?v_56 (- 4)))) (and (and (and (and (and (and (and ?v_40 ?v_58) ?v_53) ?v_59) x_70) x_71) ?v_54) ?v_10)) (and (and (and (and (and (and ?v_42 ?v_58) ?v_53) ?v_259) ?v_62) ?v_54) ?v_10)) (and (and (and (and (and (and ?v_47 x_56) x_57) ?v_53) ?v_62) ?v_49) ?v_54))) ?v_16) ?v_50) ?v_25) ?v_26))) (= (- x_78 x_64) 0)))) (or (and (and (and (and (and (and (and (and (and (= ?v_65 0) (ite ?v_64 (ite ?v_63 (< ?v_101 0) (< ?v_85 0)) (< ?v_66 0))) (ite ?v_64 (ite ?v_63 (= (- x_64 x_46) 0) (= (- x_64 x_47) 0)) (= (- x_64 x_48) 0))) ?v_73) ?v_79) ?v_81) ?v_100) ?v_80) ?v_82) ?v_67) (and (and (= ?v_65 1) (or (or (and (and (and (and (and (= ?v_83 1) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_84 ?v_69) ?v_70) ?v_71) x_53) ?v_17) ?v_72) (<= (- x_62 x_50) 2)) ?v_67) (and (and (and (and (and (and ?v_86 ?v_69) ?v_70) ?v_89) ?v_72) ?v_67) ?v_73)) (and (and (and (and (and (and (and ?v_91 x_39) ?v_74) ?v_70) ?v_19) x_54) ?v_21) (<= ?v_75 (- 4)))) (and (and (and (and (and (and (and ?v_94 ?v_77) ?v_70) ?v_78) x_53) x_54) ?v_72) ?v_67)) (and (and (and (and (and (and ?v_96 ?v_77) ?v_70) ?v_260) ?v_12) ?v_72) ?v_67)) (and (and (and (and (and (and ?v_99 x_39) x_40) ?v_70) ?v_12) ?v_14) ?v_72))) ?v_79) ?v_80) ?v_81) ?v_82) (and (and (and (and (and (= ?v_83 2) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_84 ?v_87) ?v_88) ?v_71) x_58) ?v_38) ?v_90) (<= (- x_61 x_50) 2)) ?v_67) (and (and (and (and (and (and ?v_86 ?v_87) ?v_88) ?v_89) ?v_90) ?v_67) ?v_79)) (and (and (and (and (and (and (and ?v_91 x_44) ?v_92) ?v_88) ?v_41) x_59) ?v_44) (<= ?v_93 (- 4)))) (and (and (and (and (and (and (and ?v_94 ?v_97) ?v_88) ?v_98) x_58) x_59) ?v_90) ?v_67)) (and (and (and (and (and (and ?v_96 ?v_97) ?v_88) ?v_261) ?v_33) ?v_90) ?v_67)) (and (and (and (and (and (and ?v_99 x_44) x_45) ?v_88) ?v_33) ?v_14) ?v_90))) ?v_73) ?v_100) ?v_81) ?v_82)) (and (and (and (and (and (= ?v_83 3) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_84 ?v_102) ?v_103) ?v_71) x_56) ?v_55) ?v_104) (<= (- x_60 x_50) 2)) ?v_67) (and (and (and (and (and (and ?v_86 ?v_102) ?v_103) ?v_89) ?v_104) ?v_67) ?v_81)) (and (and (and (and (and (and (and ?v_91 x_42) ?v_105) ?v_103) ?v_57) x_57) ?v_59) (<= ?v_106 (- 4)))) (and (and (and (and (and (and (and ?v_94 ?v_108) ?v_103) ?v_109) x_56) x_57) ?v_104) ?v_67)) (and (and (and (and (and (and ?v_96 ?v_108) ?v_103) ?v_262) ?v_52) ?v_104) ?v_67)) (and (and (and (and (and (and ?v_99 x_42) x_43) ?v_103) ?v_52) ?v_14) ?v_104))) ?v_73) ?v_100) ?v_79) ?v_80))) (= (- x_64 x_50) 0)))) (or (and (and (and (and (and (and (and (and (and (= ?v_112 0) (ite ?v_111 (ite ?v_110 (< ?v_148 0) (< ?v_132 0)) (< ?v_113 0))) (ite ?v_111 (ite ?v_110 (= (- x_50 x_32) 0) (= (- x_50 x_33) 0)) (= (- x_50 x_34) 0))) ?v_120) ?v_126) ?v_128) ?v_147) ?v_127) ?v_129) ?v_114) (and (and (= ?v_112 1) (or (or (and (and (and (and (and (= ?v_130 1) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_131 ?v_116) ?v_117) ?v_118) x_39) ?v_74) ?v_119) (<= (- x_48 x_36) 2)) ?v_114) (and (and (and (and (and (and ?v_133 ?v_116) ?v_117) ?v_136) ?v_119) ?v_114) ?v_120)) (and (and (and (and (and (and (and ?v_138 x_25) ?v_121) ?v_117) ?v_76) x_40) ?v_78) (<= ?v_122 (- 4)))) (and (and (and (and (and (and (and ?v_141 ?v_124) ?v_117) ?v_125) x_39) x_40) ?v_119) ?v_114)) (and (and (and (and (and (and ?v_143 ?v_124) ?v_117) ?v_263) ?v_69) ?v_119) ?v_114)) (and (and (and (and (and (and ?v_146 x_25) x_26) ?v_117) ?v_69) ?v_71) ?v_119))) ?v_126) ?v_127) ?v_128) ?v_129) (and (and (and (and (and (= ?v_130 2) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_131 ?v_134) ?v_135) ?v_118) x_44) ?v_92) ?v_137) (<= (- x_47 x_36) 2)) ?v_114) (and (and (and (and (and (and ?v_133 ?v_134) ?v_135) ?v_136) ?v_137) ?v_114) ?v_126)) (and (and (and (and (and (and (and ?v_138 x_30) ?v_139) ?v_135) ?v_95) x_45) ?v_98) (<= ?v_140 (- 4)))) (and (and (and (and (and (and (and ?v_141 ?v_144) ?v_135) ?v_145) x_44) x_45) ?v_137) ?v_114)) (and (and (and (and (and (and ?v_143 ?v_144) ?v_135) ?v_264) ?v_87) ?v_137) ?v_114)) (and (and (and (and (and (and ?v_146 x_30) x_31) ?v_135) ?v_87) ?v_71) ?v_137))) ?v_120) ?v_147) ?v_128) ?v_129)) (and (and (and (and (and (= ?v_130 3) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_131 ?v_149) ?v_150) ?v_118) x_42) ?v_105) ?v_151) (<= (- x_46 x_36) 2)) ?v_114) (and (and (and (and (and (and ?v_133 ?v_149) ?v_150) ?v_136) ?v_151) ?v_114) ?v_128)) (and (and (and (and (and (and (and ?v_138 x_28) ?v_152) ?v_150) ?v_107) x_43) ?v_109) (<= ?v_153 (- 4)))) (and (and (and (and (and (and (and ?v_141 ?v_155) ?v_150) ?v_156) x_42) x_43) ?v_151) ?v_114)) (and (and (and (and (and (and ?v_143 ?v_155) ?v_150) ?v_265) ?v_102) ?v_151) ?v_114)) (and (and (and (and (and (and ?v_146 x_28) x_29) ?v_150) ?v_102) ?v_71) ?v_151))) ?v_120) ?v_147) ?v_126) ?v_127))) (= (- x_50 x_36) 0)))) (or (and (and (and (and (and (and (and (and (and (= ?v_159 0) (ite ?v_158 (ite ?v_157 (< ?v_195 0) (< ?v_179 0)) (< ?v_160 0))) (ite ?v_158 (ite ?v_157 (= (- x_36 x_18) 0) (= (- x_36 x_19) 0)) (= (- x_36 x_20) 0))) ?v_167) ?v_173) ?v_175) ?v_194) ?v_174) ?v_176) ?v_161) (and (and (= ?v_159 1) (or (or (and (and (and (and (and (= ?v_177 1) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_178 ?v_163) ?v_164) ?v_165) x_25) ?v_121) ?v_166) (<= (- x_34 x_22) 2)) ?v_161) (and (and (and (and (and (and ?v_180 ?v_163) ?v_164) ?v_183) ?v_166) ?v_161) ?v_167)) (and (and (and (and (and (and (and ?v_185 x_11) ?v_168) ?v_164) ?v_123) x_26) ?v_125) (<= ?v_169 (- 4)))) (and (and (and (and (and (and (and ?v_188 ?v_171) ?v_164) ?v_172) x_25) x_26) ?v_166) ?v_161)) (and (and (and (and (and (and ?v_190 ?v_171) ?v_164) ?v_266) ?v_116) ?v_166) ?v_161)) (and (and (and (and (and (and ?v_193 x_11) x_12) ?v_164) ?v_116) ?v_118) ?v_166))) ?v_173) ?v_174) ?v_175) ?v_176) (and (and (and (and (and (= ?v_177 2) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_178 ?v_181) ?v_182) ?v_165) x_30) ?v_139) ?v_184) (<= (- x_33 x_22) 2)) ?v_161) (and (and (and (and (and (and ?v_180 ?v_181) ?v_182) ?v_183) ?v_184) ?v_161) ?v_173)) (and (and (and (and (and (and (and ?v_185 x_16) ?v_186) ?v_182) ?v_142) x_31) ?v_145) (<= ?v_187 (- 4)))) (and (and (and (and (and (and (and ?v_188 ?v_191) ?v_182) ?v_192) x_30) x_31) ?v_184) ?v_161)) (and (and (and (and (and (and ?v_190 ?v_191) ?v_182) ?v_267) ?v_134) ?v_184) ?v_161)) (and (and (and (and (and (and ?v_193 x_16) x_17) ?v_182) ?v_134) ?v_118) ?v_184))) ?v_167) ?v_194) ?v_175) ?v_176)) (and (and (and (and (and (= ?v_177 3) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_178 ?v_196) ?v_197) ?v_165) x_28) ?v_152) ?v_198) (<= (- x_32 x_22) 2)) ?v_161) (and (and (and (and (and (and ?v_180 ?v_196) ?v_197) ?v_183) ?v_198) ?v_161) ?v_175)) (and (and (and (and (and (and (and ?v_185 x_14) ?v_199) ?v_197) ?v_154) x_29) ?v_156) (<= ?v_200 (- 4)))) (and (and (and (and (and (and (and ?v_188 ?v_202) ?v_197) ?v_203) x_28) x_29) ?v_198) ?v_161)) (and (and (and (and (and (and ?v_190 ?v_202) ?v_197) ?v_268) ?v_149) ?v_198) ?v_161)) (and (and (and (and (and (and ?v_193 x_14) x_15) ?v_197) ?v_149) ?v_118) ?v_198))) ?v_167) ?v_194) ?v_173) ?v_174))) (= (- x_36 x_22) 0)))) (or (and (and (and (and (and (and (and (and (and (= ?v_209 0) (ite ?v_208 (ite ?v_204 ?v_205 ?v_206) ?v_207)) (ite ?v_208 (ite ?v_204 (= (- x_22 x_8) 0) (= (- x_22 x_7) 0)) (= (- x_22 x_6) 0))) ?v_217) ?v_223) ?v_225) ?v_244) ?v_224) ?v_226) ?v_213) (and (and (= ?v_209 1) (or (or (and (and (and (and (and (= ?v_227 1) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_228 ?v_210) ?v_215) ?v_212) x_11) ?v_168) ?v_216) (<= (- x_20 cvclZero) 2)) ?v_213) (and (and (and (and (and (and ?v_231 ?v_210) ?v_215) ?v_233) ?v_216) ?v_213) ?v_217)) (and (and (and (and (and (and (and ?v_235 x_0) ?v_218) ?v_215) ?v_170) x_12) ?v_172) (<= ?v_219 (- 4)))) (and (and (and (and (and (and (and ?v_238 ?v_221) ?v_215) ?v_222) x_11) x_12) ?v_216) ?v_213)) (and (and (and (and (and (and ?v_240 ?v_221) ?v_215) ?v_269) ?v_163) ?v_216) ?v_213)) (and (and (and (and (and (and ?v_243 x_0) x_1) ?v_215) ?v_163) ?v_165) ?v_216))) ?v_223) ?v_224) ?v_225) ?v_226) (and (and (and (and (and (= ?v_227 2) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_228 ?v_229) ?v_232) ?v_212) x_16) ?v_186) ?v_234) (<= (- x_19 cvclZero) 2)) ?v_213) (and (and (and (and (and (and ?v_231 ?v_229) ?v_232) ?v_233) ?v_234) ?v_213) ?v_223)) (and (and (and (and (and (and (and ?v_235 x_2) ?v_236) ?v_232) ?v_189) x_17) ?v_192) (<= ?v_237 (- 4)))) (and (and (and (and (and (and (and ?v_238 ?v_241) ?v_232) ?v_242) x_16) x_17) ?v_234) ?v_213)) (and (and (and (and (and (and ?v_240 ?v_241) ?v_232) ?v_270) ?v_181) ?v_234) ?v_213)) (and (and (and (and (and (and ?v_243 x_2) x_3) ?v_232) ?v_181) ?v_165) ?v_234))) ?v_217) ?v_244) ?v_225) ?v_226)) (and (and (and (and (and (= ?v_227 3) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_228 ?v_245) ?v_247) ?v_212) x_14) ?v_199) ?v_248) (<= (- x_18 cvclZero) 2)) ?v_213) (and (and (and (and (and (and ?v_231 ?v_245) ?v_247) ?v_233) ?v_248) ?v_213) ?v_225)) (and (and (and (and (and (and (and ?v_235 x_4) ?v_249) ?v_247) ?v_201) x_15) ?v_203) (<= ?v_250 (- 4)))) (and (and (and (and (and (and (and ?v_238 ?v_252) ?v_247) ?v_253) x_14) x_15) ?v_248) ?v_213)) (and (and (and (and (and (and ?v_240 ?v_252) ?v_247) ?v_271) ?v_196) ?v_248) ?v_213)) (and (and (and (and (and (and ?v_243 x_4) x_5) ?v_247) ?v_196) ?v_165) ?v_248))) ?v_217) ?v_244) ?v_223) ?v_224))) (= (- x_22 cvclZero) 0)))) (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (and (and x_67 x_68) (not ?v_254)) (and (and x_72 x_73) (not ?v_255))) (and (and x_70 x_71) (not ?v_256))) (and (and x_53 x_54) ?v_257)) (and (and x_58 x_59) ?v_258)) (and (and x_56 x_57) ?v_259)) (and (and x_39 x_40) ?v_260)) (and (and x_44 x_45) ?v_261)) (and (and x_42 x_43) ?v_262)) (and (and x_25 x_26) ?v_263)) (and (and x_30 x_31) ?v_264)) (and (and x_28 x_29) ?v_265)) (and (and x_11 x_12) ?v_266)) (and (and x_16 x_17) ?v_267)) (and (and x_14 x_15) ?v_268)) (and (and x_0 x_1) ?v_269)) (and (and x_2 x_3) ?v_270)) (and (and x_4 x_5) ?v_271))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
(exit)

(set-info :smt-lib-version 2.6)
(set-logic QF_IDL)
(set-info :source |The Averest Framework (http://www.averest.org)|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun cvclZero () Int)
(declare-fun F0 () Int)
(declare-fun F2 () Int)
(declare-fun F4 () Int)
(declare-fun F6 () Int)
(declare-fun F8 () Int)
(declare-fun F14 () Int)
(declare-fun F16 () Int)
(declare-fun F18 () Int)
(declare-fun F20 () Int)
(declare-fun F22 () Int)
(declare-fun F134 () Int)
(declare-fun F135 () Int)
(declare-fun F136 () Int)
(declare-fun F137 () Int)
(declare-fun F138 () Int)
(declare-fun F141 () Int)
(declare-fun F142 () Int)
(declare-fun F143 () Int)
(declare-fun F144 () Int)
(declare-fun F145 () Int)
(declare-fun F152 () Int)
(declare-fun F153 () Int)
(declare-fun F154 () Int)
(declare-fun F155 () Int)
(declare-fun F156 () Int)
(declare-fun F159 () Int)
(declare-fun F160 () Int)
(declare-fun F161 () Int)
(declare-fun F162 () Int)
(declare-fun F163 () Int)
(declare-fun F190 () Int)
(declare-fun F191 () Int)
(declare-fun F192 () Int)
(declare-fun F193 () Int)
(declare-fun F194 () Int)
(declare-fun F201 () Int)
(declare-fun F202 () Int)
(declare-fun F203 () Int)
(declare-fun F204 () Int)
(declare-fun F205 () Int)
(declare-fun F208 () Int)
(declare-fun F209 () Int)
(declare-fun F210 () Int)
(declare-fun F211 () Int)
(declare-fun F212 () Int)
(declare-fun F219 () Int)
(declare-fun F220 () Int)
(declare-fun F221 () Int)
(declare-fun F222 () Int)
(declare-fun F223 () Int)
(declare-fun F226 () Int)
(declare-fun F227 () Int)
(declare-fun F228 () Int)
(declare-fun F229 () Int)
(declare-fun F230 () Int)
(declare-fun F239 () Int)
(declare-fun F240 () Int)
(declare-fun F241 () Int)
(declare-fun F242 () Int)
(declare-fun F243 () Int)
(declare-fun F250 () Int)
(declare-fun F251 () Int)
(declare-fun F252 () Int)
(declare-fun F253 () Int)
(declare-fun F254 () Int)
(declare-fun F257 () Int)
(declare-fun F258 () Int)
(declare-fun F259 () Int)
(declare-fun F260 () Int)
(declare-fun F261 () Int)
(declare-fun P10 () Bool)
(declare-fun P12 () Bool)
(declare-fun P24 () Bool)
(declare-fun P26 () Bool)
(declare-fun P28 () Bool)
(declare-fun P30 () Bool)
(declare-fun P32 () Bool)
(declare-fun P34 () Bool)
(declare-fun P139 () Bool)
(declare-fun P140 () Bool)
(declare-fun P146 () Bool)
(declare-fun P147 () Bool)
(declare-fun P148 () Bool)
(declare-fun P149 () Bool)
(declare-fun P150 () Bool)
(declare-fun P151 () Bool)
(declare-fun P157 () Bool)
(declare-fun P158 () Bool)
(declare-fun P164 () Bool)
(declare-fun P165 () Bool)
(declare-fun P166 () Bool)
(declare-fun P167 () Bool)
(declare-fun P168 () Bool)
(declare-fun P169 () Bool)
(declare-fun P188 () Bool)
(declare-fun P189 () Bool)
(declare-fun P195 () Bool)
(declare-fun P196 () Bool)
(declare-fun P197 () Bool)
(declare-fun P198 () Bool)
(declare-fun P199 () Bool)
(declare-fun P200 () Bool)
(declare-fun P206 () Bool)
(declare-fun P207 () Bool)
(declare-fun P213 () Bool)
(declare-fun P214 () Bool)
(declare-fun P215 () Bool)
(declare-fun P216 () Bool)
(declare-fun P217 () Bool)
(declare-fun P218 () Bool)
(declare-fun P224 () Bool)
(declare-fun P225 () Bool)
(declare-fun P231 () Bool)
(declare-fun P232 () Bool)
(declare-fun P233 () Bool)
(declare-fun P234 () Bool)
(declare-fun P235 () Bool)
(declare-fun P236 () Bool)
(declare-fun P237 () Bool)
(declare-fun P238 () Bool)
(declare-fun P244 () Bool)
(declare-fun P245 () Bool)
(declare-fun P246 () Bool)
(declare-fun P247 () Bool)
(declare-fun P248 () Bool)
(declare-fun P249 () Bool)
(declare-fun P255 () Bool)
(declare-fun P256 () Bool)
(declare-fun P262 () Bool)
(declare-fun P263 () Bool)
(declare-fun P264 () Bool)
(declare-fun P265 () Bool)
(declare-fun P266 () Bool)
(declare-fun P267 () Bool)
(assert (let ((?v_0 (not P10))) (let ((?v_2 (or ?v_0 (and P10 P30))) (?v_4 (and P10 P26))) (let ((?v_3 (= ?v_2 ?v_4)) (?v_1 (or ?v_0 (and P10 P28))) (?v_5 (and P10 P24)) (?v_7 (not ?v_4))) (let ((?v_8 (not ?v_5))) (let ((?v_10 (and P10 ?v_8))) (let ((?v_6 (and ?v_7 ?v_10)) (?v_12 (and ?v_0 ?v_8))) (let ((?v_19 (and ?v_7 ?v_12)) (?v_15 (and ?v_0 ?v_5))) (let ((?v_9 (and ?v_7 ?v_15)) (?v_11 (and ?v_4 ?v_10)) (?v_13 (and ?v_4 ?v_12)) (?v_17 (and P10 ?v_5))) (let ((?v_14 (and ?v_4 ?v_17)) (?v_16 (and ?v_4 ?v_15)) (?v_18 (and ?v_7 ?v_17)) (?v_28 (not P139)) (?v_35 (and P139 P146))) (let ((?v_34 (or ?v_28 (and P139 P148)))) (let ((?v_37 (and ?v_35 ?v_34)) (?v_29 (and P139 P147)) (?v_30 (or ?v_28 (and P139 P149)))) (let ((?v_33 (= ?v_29 ?v_30))) (let ((?v_32 (not ?v_33))) (let ((?v_31 (or (and ?v_37 ?v_32) (and ?v_29 ?v_30))) (?v_38 (not (= ?v_35 ?v_34)))) (let ((?v_36 (and P140 (or (and ?v_30 ?v_32) (and ?v_33 (and ?v_34 ?v_38)))))) (let ((?v_42 (not ?v_36))) (let ((?v_43 (or (and ?v_28 ?v_31) (and P139 (or (and ?v_31 ?v_36) (and P151 ?v_42))))) (?v_39 (not ?v_31)) (?v_40 (not (= ?v_37 ?v_32)))) (let ((?v_41 (or (and (not (= ?v_39 ?v_40)) (or (and ?v_31 (not (= ?v_31 ?v_38))) (and ?v_31 ?v_38))) (and ?v_39 ?v_40)))) (let ((?v_44 (or (and ?v_28 ?v_41) (and P139 (or (and ?v_36 ?v_41) (and P150 ?v_42)))))) (let ((?v_49 (and P139 ?v_44))) (let ((?v_55 (and ?v_43 ?v_49)) (?v_50 (and ?v_28 ?v_44))) (let ((?v_56 (and ?v_43 ?v_50)) (?v_46 (not ?v_43)) (?v_47 (not ?v_44))) (let ((?v_52 (and P139 ?v_47))) (let ((?v_65 (and ?v_46 ?v_52)) (?v_53 (and ?v_28 ?v_47))) (let ((?v_64 (and ?v_46 ?v_53)) (?v_62 (and ?v_46 ?v_49)) (?v_61 (and ?v_46 ?v_50)) (?v_59 (and ?v_43 ?v_52)) (?v_58 (and ?v_43 ?v_53)) (?v_72 (not (= ?v_43 ?v_44))) (?v_78 (not P255))) (let ((?v_80 (or (and P255 P265) ?v_78)) (?v_85 (and P255 P263))) (let ((?v_81 (= ?v_80 ?v_85)) (?v_79 (or (and P264 P255) ?v_78)) (?v_83 (and P255 P262))) (let ((?v_87 (not (= ?v_79 ?v_83))) (?v_84 (not ?v_81))) (let ((?v_82 (and (or (and ?v_81 (and ?v_87 ?v_79)) (and ?v_80 ?v_84)) P256))) (let ((?v_92 (not ?v_82)) (?v_86 (and ?v_79 ?v_83))) (let ((?v_89 (not (= ?v_86 ?v_84))) (?v_88 (or (and ?v_80 ?v_85) (and ?v_86 ?v_84)))) (let ((?v_90 (not ?v_88))) (let ((?v_91 (or (and ?v_89 ?v_90) (and (or (and ?v_87 ?v_88) (and ?v_88 (not (= ?v_87 ?v_88)))) (not (= ?v_89 ?v_90)))))) (let ((?v_95 (or (and P255 (or (and ?v_92 P266) (and ?v_82 ?v_91))) (and ?v_78 ?v_91)))) (let ((?v_94 (not ?v_95))) (let ((?v_96 (and P255 ?v_94)) (?v_97 (or (and P255 (or (and ?v_92 P267) (and ?v_82 ?v_88))) (and ?v_78 ?v_88)))) (let ((?v_93 (not ?v_97))) (let ((?v_106 (and ?v_96 ?v_93)) (?v_98 (and ?v_78 ?v_94))) (let ((?v_105 (and ?v_93 ?v_98)) (?v_100 (and P255 ?v_95))) (let ((?v_104 (and ?v_93 ?v_100)) (?v_99 (and ?v_78 ?v_95))) (let ((?v_103 (and ?v_93 ?v_99)) (?v_102 (and ?v_96 ?v_97)) (?v_101 (and ?v_97 ?v_98)) (?v_107 (and ?v_97 ?v_99)) (?v_108 (and ?v_97 ?v_100)) (?v_287 (or ?v_78 ?v_82)) (?v_117 (not (= ?v_95 ?v_97))) (?v_129 (and P237 P244))) (let ((?v_138 (not ?v_129)) (?v_130 (not P237))) (let ((?v_136 (and ?v_138 ?v_130)) (?v_132 (and P237 P245))) (let ((?v_128 (not ?v_132))) (let ((?v_142 (and ?v_136 ?v_128)) (?v_134 (and P237 ?v_129))) (let ((?v_131 (and ?v_128 ?v_134)) (?v_140 (and ?v_129 ?v_130))) (let ((?v_133 (and ?v_132 ?v_140)) (?v_135 (and ?v_132 ?v_134)) (?v_137 (and ?v_136 ?v_132)) (?v_143 (and P237 ?v_138))) (let ((?v_139 (and ?v_132 ?v_143)) (?v_141 (and ?v_128 ?v_140)) (?v_144 (and ?v_128 ?v_143)) (?v_145 (or ?v_130 (and P237 P247)))) (let ((?v_146 (= ?v_132 ?v_145)) (?v_147 (or ?v_130 (and P246 P237))) (?v_148 (not P224)) (?v_149 (and P224 P232))) (let ((?v_150 (or ?v_148 (and P224 P234)))) (let ((?v_159 (= ?v_149 ?v_150))) (let ((?v_151 (not ?v_159)) (?v_153 (or ?v_148 (and P224 P233))) (?v_154 (and P224 P231))) (let ((?v_152 (and ?v_153 ?v_154))) (let ((?v_155 (or (and ?v_151 ?v_152) (and ?v_149 ?v_150)))) (let ((?v_157 (not ?v_155)) (?v_158 (not (= ?v_151 ?v_152))) (?v_156 (not (= ?v_153 ?v_154)))) (let ((?v_161 (or (and (not (= ?v_157 ?v_158)) (or (and (not (= ?v_156 ?v_155)) ?v_155) (and ?v_156 ?v_155))) (and ?v_157 ?v_158))) (?v_160 (and (or (and ?v_159 (and ?v_153 ?v_156)) (and ?v_151 ?v_150)) P225))) (let ((?v_162 (not ?v_160))) (let ((?v_163 (or (and ?v_148 ?v_161) (and P224 (or (and ?v_162 P235) (and ?v_160 ?v_161)))))) (let ((?v_172 (and P224 ?v_163)) (?v_164 (or (and P224 (or (and ?v_162 P236) (and ?v_160 ?v_155))) (and ?v_148 ?v_155)))) (let ((?v_166 (not ?v_164))) (let ((?v_168 (and ?v_172 ?v_166)) (?v_167 (not ?v_163))) (let ((?v_165 (and P224 ?v_167))) (let ((?v_170 (and ?v_165 ?v_164)) (?v_169 (and ?v_148 ?v_163))) (let ((?v_171 (and ?v_169 ?v_164)) (?v_178 (and ?v_165 ?v_166)) (?v_173 (and ?v_148 ?v_167))) (let ((?v_177 (and ?v_173 ?v_166)) (?v_176 (and ?v_169 ?v_166)) (?v_174 (and ?v_172 ?v_164)) (?v_175 (and ?v_173 ?v_164)) (?v_185 (not (= ?v_163 ?v_164))) (?v_190 (not P206))) (let ((?v_191 (or ?v_190 (and P206 P216))) (?v_192 (and P206 P214))) (let ((?v_195 (= ?v_191 ?v_192))) (let ((?v_196 (not ?v_195)) (?v_193 (or (and P206 P215) ?v_190)) (?v_194 (and P206 P213))) (let ((?v_200 (and ?v_193 ?v_194))) (let ((?v_198 (or (and ?v_196 ?v_200) (and ?v_191 ?v_192))) (?v_199 (not (= ?v_193 ?v_194)))) (let ((?v_197 (and (or (and (and ?v_193 ?v_199) ?v_195) (and ?v_196 ?v_191)) P207))) (let ((?v_203 (not ?v_197))) (let ((?v_207 (or (and P206 (or (and ?v_198 ?v_197) (and ?v_203 P218))) (and ?v_190 ?v_198))) (?v_201 (not (= ?v_196 ?v_200))) (?v_202 (not ?v_198))) (let ((?v_204 (or (and (or (and ?v_199 ?v_198) (and ?v_198 (not (= ?v_199 ?v_198)))) (not (= ?v_201 ?v_202))) (and ?v_201 ?v_202)))) (let ((?v_205 (or (and P206 (or (and ?v_204 ?v_197) (and P217 ?v_203))) (and ?v_190 ?v_204)))) (let ((?v_209 (not ?v_205))) (let ((?v_212 (and P206 ?v_209)) (?v_208 (not ?v_207))) (let ((?v_227 (and ?v_212 ?v_208)) (?v_213 (and ?v_190 ?v_209))) (let ((?v_226 (and ?v_208 ?v_213)) (?v_214 (and P206 ?v_205))) (let ((?v_224 (and ?v_208 ?v_214)) (?v_219 (and ?v_190 ?v_205))) (let ((?v_223 (and ?v_208 ?v_219)) (?v_216 (and ?v_212 ?v_207)) (?v_221 (and ?v_213 ?v_207)) (?v_217 (and ?v_214 ?v_207)) (?v_228 (and ?v_219 ?v_207)) (?v_237 (not (= ?v_205 ?v_207))) (?v_241 (not P157))) (let ((?v_242 (or ?v_241 (and P167 P157))) (?v_247 (and P157 P165))) (let ((?v_243 (= ?v_247 ?v_242))) (let ((?v_246 (not ?v_243)) (?v_244 (or (and P166 P157) ?v_241)) (?v_245 (and P157 P164))) (let ((?v_251 (not (= ?v_245 ?v_244)))) (let ((?v_249 (and (or (and ?v_242 ?v_246) (and ?v_243 (and ?v_244 ?v_251))) P158)) (?v_250 (and ?v_245 ?v_244))) (let ((?v_248 (or (and ?v_250 ?v_246) (and ?v_247 ?v_242))) (?v_255 (not ?v_249))) (let ((?v_256 (or (and ?v_241 ?v_248) (and (or (and ?v_248 ?v_249) (and P169 ?v_255)) P157))) (?v_252 (not ?v_248)) (?v_253 (not (= ?v_250 ?v_246)))) (let ((?v_254 (or (and (not (= ?v_252 ?v_253)) (or (and ?v_248 (not (= ?v_248 ?v_251))) (and ?v_248 ?v_251))) (and ?v_252 ?v_253)))) (let ((?v_257 (or (and ?v_241 ?v_254) (and P157 (or (and ?v_249 ?v_254) (and P168 ?v_255)))))) (let ((?v_258 (not ?v_257))) (let ((?v_262 (and ?v_241 ?v_258))) (let ((?v_266 (and ?v_256 ?v_262)) (?v_261 (and P157 ?v_257))) (let ((?v_265 (and ?v_256 ?v_261)) (?v_259 (and ?v_241 ?v_257))) (let ((?v_264 (and ?v_256 ?v_259)) (?v_263 (and P157 ?v_258))) (let ((?v_267 (and ?v_256 ?v_263)) (?v_260 (not ?v_256))) (let ((?v_268 (and ?v_260 ?v_259)) (?v_269 (and ?v_260 ?v_261)) (?v_270 (and ?v_260 ?v_262)) (?v_271 (and ?v_260 ?v_263)) (?v_275 (not (= ?v_256 ?v_257))) (?v_27 (= (- F22 F20) 0)) (?v_26 (= (- F8 F0) 0)) (?v_25 (= (- F6 F0) 0)) (?v_22 (= (- F22 F16) 0)) (?v_23 (= (- F4 F0) 0)) (?v_20 (= (- F22 F14) 0)) (?v_21 (= (- F2 F0) 0)) (?v_24 (= (- F22 F18) 0)) (?v_45 (- F145 F141)) (?v_48 (- F138 F134)) (?v_51 (- F137 F134)) (?v_54 (- F136 F134)) (?v_57 (- F135 F134)) (?v_60 (- F145 F142)) (?v_63 (- F145 F143)) (?v_66 (- F145 F144))) (let ((?v_67 (or (or (or (or (or (or (or (and (and P139 ?v_55) (> ?v_45 0)) (or (and (and P139 ?v_56) (> (- F145 F135) 0)) (or (and (and ?v_28 ?v_65) (< (- F144 F134) 0)) (or (and (and ?v_28 ?v_64) (< ?v_48 0)) (or (and (and ?v_28 ?v_62) (< (- F143 F134) 0)) (or (and (and ?v_28 ?v_61) (< ?v_51 0)) (or (and (and ?v_28 ?v_59) (< (- F142 F134) 0)) (or (and (and ?v_28 ?v_58) (< ?v_54 0)) (or (and (and ?v_28 ?v_55) (< (- F141 F134) 0)) (and (and ?v_28 ?v_56) (< ?v_57 0))))))))))) (and (and P139 ?v_58) (> (- F145 F136) 0))) (and (and P139 ?v_59) (> ?v_60 0))) (and (and P139 ?v_61) (> (- F145 F137) 0))) (and (and P139 ?v_62) (> ?v_63 0))) (and (and P139 ?v_64) (> (- F145 F138) 0))) (and (and P139 ?v_65) (> ?v_66 0))))) (let ((?v_69 (and ?v_67 ?v_28)) (?v_68 (and ?v_67 ?v_36))) (let ((?v_71 (not ?v_68)) (?v_70 (not ?v_69)) (?v_73 (not ?v_67))) (let ((?v_75 (and ?v_28 ?v_73)) (?v_74 (and ?v_36 ?v_73))) (let ((?v_77 (not ?v_74)) (?v_76 (not ?v_75)) (?v_127 (- F261 F260)) (?v_124 (- F261 F259)) (?v_122 (- F261 F258)) (?v_121 (- F251 F250)) (?v_123 (- F252 F250)) (?v_125 (- F253 F250)) (?v_126 (- F254 F250)) (?v_120 (- F261 F257))) (let ((?v_109 (or (and (> ?v_127 0) (and P255 ?v_106)) (or (and (> (- F261 F254) 0) (and P255 ?v_105)) (or (and (> ?v_124 0) (and P255 ?v_104)) (or (and (> (- F261 F253) 0) (and P255 ?v_103)) (or (and (> ?v_122 0) (and P255 ?v_102)) (or (and (> (- F261 F252) 0) (and P255 ?v_101)) (or (or (or (or (or (or (or (or (or (and (< ?v_121 0) (and ?v_78 ?v_107)) (and (< (- F257 F250) 0) (and ?v_78 ?v_108))) (and (< ?v_123 0) (and ?v_78 ?v_101))) (and (< (- F258 F250) 0) (and ?v_78 ?v_102))) (and (< ?v_125 0) (and ?v_78 ?v_103))) (and (< (- F259 F250) 0) (and ?v_78 ?v_104))) (and (< ?v_126 0) (and ?v_78 ?v_105))) (and (< (- F260 F250) 0) (and ?v_78 ?v_106))) (and (> (- F261 F251) 0) (and P255 ?v_107))) (and (> ?v_120 0) (and P255 ?v_108))))))))))) (let ((?v_111 (and ?v_78 ?v_109))) (let ((?v_118 (not ?v_111)) (?v_110 (and ?v_82 ?v_109))) (let ((?v_119 (not ?v_110))) (let ((?v_288 (or (and ?v_118 (or (and ?v_79 ?v_119) (and ?v_95 ?v_110))) (and ?v_111 ?v_95))) (?v_113 (not ?v_109))) (let ((?v_112 (and ?v_82 ?v_113))) (let ((?v_116 (not ?v_112)) (?v_114 (and ?v_78 ?v_113))) (let ((?v_115 (not ?v_114))) (let ((?v_286 (or (and (or (and ?v_94 ?v_112) (and ?v_83 ?v_116)) ?v_115) (and ?v_94 ?v_114))) (?v_285 (or (and ?v_115 (or (and ?v_85 ?v_116) (and ?v_112 ?v_117))) (and ?v_114 ?v_117))) (?v_284 (or (and ?v_118 (or (and ?v_97 ?v_110) (and ?v_80 ?v_119))) (and ?v_111 ?v_97))) (?v_283 (and (and (and (and (and (and (and (and (= (- cvclZero F261) 0) (and (= (- cvclZero F260) 0) (and (= (- cvclZero F259) 0) (and (and (= (- cvclZero F257) 0) (and ?v_78 (not P256))) (= (- cvclZero F258) 0))))) (not P262)) (not P263)) (not P264)) (not P265)) (not P266)) (not P267)) (and (or (or (or (or (and P255 (= ?v_120 0)) (and ?v_78 (= ?v_121 0))) (or (and P255 (= ?v_122 0)) (and ?v_78 (= ?v_123 0)))) (or (and P255 (= ?v_124 0)) (and ?v_78 (= ?v_125 0)))) (or (and ?v_78 (= ?v_126 0)) (and P255 (= ?v_127 0)))) (and (and (or (and ?v_78 (<= (- F253 F252) 0)) (and P255 (<= (- F259 F258) 0))) (or (and ?v_78 (<= (- F252 F251) 0)) (and P255 (<= (- F258 F257) 0)))) (or (and ?v_78 (<= (- F254 F253) 0)) (and P255 (<= (- F260 F259) 0))))))) (?v_240 (or (or (or (or (and (and P237 ?v_142) (= (- F243 F8) 0)) (or (or (and (and P237 ?v_131) (= (- F243 F241) 0)) (or (and (and ?v_130 ?v_131) (= (- F241 F0) 0)) (or (or (or (or (or (or (or (or (or (and (and P237 ?v_133) (= (- F243 F2) 0)) (and ?v_21 (and ?v_130 ?v_133))) (and (and ?v_130 ?v_135) (= (- F239 F0) 0))) (and (and P237 ?v_135) (= (- F243 F239) 0))) (and ?v_23 (and ?v_130 ?v_137))) (and (and P237 ?v_137) (= (- F243 F4) 0))) (and (and ?v_130 ?v_139) (= (- F240 F0) 0))) (and (and P237 ?v_139) (= (- F243 F240) 0))) (and ?v_25 (and ?v_130 ?v_141))) (and (and P237 ?v_141) (= (- F243 F6) 0))))) (and ?v_26 (and ?v_130 ?v_142)))) (and (and ?v_130 ?v_144) (= (- F242 F0) 0))) (and (and P237 ?v_144) (= (- F243 F242) 0))) (not (and P238 (not (or (and ?v_145 (not ?v_146)) (and ?v_146 (and ?v_147 (not (= ?v_129 ?v_147)))))))))) (?v_179 (or (or (or (and (> (- F230 F228) 0) (and P224 ?v_168)) (or (or (and (and ?v_170 P224) (> (- F230 F227) 0)) (or (or (or (and (and ?v_171 P224) (> (- F230 F220) 0)) (or (and (and ?v_148 ?v_178) (< (- F229 F219) 0)) (or (and (< (- F223 F219) 0) (and ?v_148 ?v_177)) (or (and (< (- F228 F219) 0) (and ?v_148 ?v_168)) (or (and (< (- F222 F219) 0) (and ?v_176 ?v_148)) (or (and (< (- F227 F219) 0) (and ?v_170 ?v_148)) (or (or (and (< (- F220 F219) 0) (and ?v_148 ?v_171)) (and (< (- F226 F219) 0) (and ?v_148 ?v_174))) (and (and ?v_175 ?v_148) (< (- F221 F219) 0))))))))) (and (> (- F230 F226) 0) (and P224 ?v_174))) (and (> (- F230 F221) 0) (and ?v_175 P224)))) (and (and ?v_176 P224) (> (- F230 F222) 0)))) (and (> (- F230 F223) 0) (and P224 ?v_177))) (and (> (- F230 F229) 0) (and P224 ?v_178))))) (let ((?v_181 (and ?v_148 ?v_179))) (let ((?v_188 (not ?v_181)) (?v_180 (and ?v_179 ?v_160))) (let ((?v_189 (not ?v_180)) (?v_182 (not ?v_179))) (let ((?v_184 (and ?v_148 ?v_182))) (let ((?v_186 (not ?v_184)) (?v_183 (and ?v_182 ?v_160))) (let ((?v_187 (not ?v_183)) (?v_206 (- F212 F211)) (?v_210 (- F212 F210)) (?v_211 (- F212 F209)) (?v_215 (- F212 F208)) (?v_218 (- F202 F201)) (?v_220 (- F203 F201)) (?v_222 (- F204 F201)) (?v_225 (- F205 F201))) (let ((?v_229 (or (and (> ?v_206 0) (and P206 ?v_227)) (or (and (> (- F212 F205) 0) (and P206 ?v_226)) (or (and (and P206 ?v_224) (> ?v_210 0)) (or (and (and P206 ?v_223) (> (- F212 F204) 0)) (or (and (> ?v_211 0) (and P206 ?v_216)) (or (and (> (- F212 F203) 0) (and P206 ?v_221)) (or (and (and P206 ?v_217) (> ?v_215 0)) (or (or (or (or (or (or (and (and ?v_190 ?v_216) (< (- F209 F201) 0)) (or (or (and (and ?v_190 ?v_217) (< (- F208 F201) 0)) (and (< ?v_218 0) (and ?v_190 ?v_228))) (and (< ?v_220 0) (and ?v_190 ?v_221)))) (and (< ?v_222 0) (and ?v_190 ?v_223))) (and (< (- F210 F201) 0) (and ?v_190 ?v_224))) (and (< ?v_225 0) (and ?v_190 ?v_226))) (and (< (- F211 F201) 0) (and ?v_190 ?v_227))) (and (> (- F212 F202) 0) (and P206 ?v_228)))))))))))) (let ((?v_231 (and ?v_190 ?v_229)) (?v_230 (and ?v_197 ?v_229))) (let ((?v_238 (not ?v_230)) (?v_239 (not ?v_231)) (?v_233 (not ?v_229))) (let ((?v_232 (and ?v_197 ?v_233))) (let ((?v_235 (not ?v_232)) (?v_234 (and ?v_190 ?v_233))) (let ((?v_236 (not ?v_234)) (?v_278 (or (or (or (or (or (or (or (or (or (or (or (or (or (or (and (< (- F154 F152) 0) (and ?v_241 ?v_266)) (or (and (and ?v_241 ?v_265) (< (- F159 F152) 0)) (and (and ?v_241 ?v_264) (< (- F153 F152) 0)))) (and (and ?v_241 ?v_267) (< (- F160 F152) 0))) (and (and ?v_241 ?v_268) (< (- F155 F152) 0))) (and (and ?v_241 ?v_269) (< (- F161 F152) 0))) (and (and ?v_241 ?v_270) (< (- F156 F152) 0))) (and (and ?v_241 ?v_271) (< (- F162 F152) 0))) (and (and P157 ?v_264) (> (- F163 F153) 0))) (and (and P157 ?v_265) (> (- F163 F159) 0))) (and (and P157 ?v_266) (> (- F163 F154) 0))) (and (and P157 ?v_267) (> (- F163 F160) 0))) (and (and P157 ?v_268) (> (- F163 F155) 0))) (and (and P157 ?v_269) (> (- F163 F161) 0))) (and (and P157 ?v_270) (> (- F163 F156) 0))) (and (and P157 ?v_271) (> (- F163 F162) 0))))) (let ((?v_273 (not ?v_278))) (let ((?v_272 (and ?v_241 ?v_273))) (let ((?v_277 (not ?v_272)) (?v_274 (and ?v_249 ?v_273))) (let ((?v_276 (not ?v_274)) (?v_279 (and ?v_241 ?v_278))) (let ((?v_282 (not ?v_279)) (?v_280 (and ?v_249 ?v_278))) (let ((?v_281 (not ?v_280))) (or (not (or (or (not (and P12 (not (or (and ?v_3 (and ?v_1 (not (= ?v_1 ?v_5)))) (and ?v_2 (not ?v_3)))))) (or (and ?v_27 (and P10 ?v_6)) (or (and (= (- F20 F0) 0) (and ?v_0 ?v_6)) (or (or (and ?v_26 (and ?v_0 ?v_19)) (or (or (or (and (= (- F22 F6) 0) (and P10 ?v_9)) (or (and ?v_25 (and ?v_0 ?v_9)) (or (and ?v_22 (and P10 ?v_11)) (or (and (= (- F16 F0) 0) (and ?v_0 ?v_11)) (or (and (= (- F22 F4) 0) (and P10 ?v_13)) (or (and ?v_23 (and ?v_0 ?v_13)) (or (and ?v_20 (and P10 ?v_14)) (or (and (= (- F14 F0) 0) (and ?v_0 ?v_14)) (or (and ?v_21 (and ?v_0 ?v_16)) (and (= (- F22 F2) 0) (and P10 ?v_16))))))))))) (and (= (- F18 F0) 0) (and ?v_0 ?v_18))) (and ?v_24 (and P10 ?v_18)))) (and (= (- F22 F8) 0) (and P10 ?v_19)))))) (not (and (and (and (and (and (and (and (and (= (- cvclZero F22) 0) (and (= (- cvclZero F20) 0) (and (= (- cvclZero F18) 0) (and (and (= (- cvclZero F14) 0) (and ?v_0 (not P12))) (= (- cvclZero F16) 0))))) (not P24)) (not P26)) (not P28)) (not P30)) (not P32)) (not P34)) (and (or (or (or (or (and P10 ?v_20) (and ?v_0 ?v_21)) (or (and P10 ?v_22) (and ?v_0 ?v_23))) (or (and P10 ?v_24) (and ?v_0 ?v_25))) (or (and ?v_0 ?v_26) (and P10 ?v_27))) (and (and (or (and ?v_0 (<= (- F6 F4) 0)) (and P10 (<= (- F18 F16) 0))) (or (and ?v_0 (<= (- F4 F2) 0)) (and P10 (<= (- F16 F14) 0)))) (or (and ?v_0 (<= (- F8 F6) 0)) (and P10 (<= (- F20 F18) 0))))))))) (and (and (and (and (and (or (and (<= (- F144 F143) 0) P139) (and (<= (- F138 F137) 0) ?v_28)) (and (or (and P139 (<= (- F142 F141) 0)) (and ?v_28 (<= (- F136 F135) 0))) (or (and P139 (<= (- F143 F142) 0)) (and ?v_28 (<= (- F137 F136) 0))))) (or (or (and P139 (= ?v_66 0)) (and ?v_28 (= ?v_48 0))) (or (or (and ?v_28 (= ?v_51 0)) (and P139 (= ?v_63 0))) (or (or (and ?v_28 (= ?v_54 0)) (and P139 (= ?v_60 0))) (or (and ?v_28 (= ?v_57 0)) (and P139 (= ?v_45 0))))))) (and (not P151) (and (not P150) (and (not P149) (and (not P148) (and (not P147) (and (not P146) (and (and (and (and (= (- cvclZero F142) 0) (and (and ?v_28 (not P140)) (= (- cvclZero F141) 0))) (= (- cvclZero F143) 0)) (= (- cvclZero F144) 0)) (= (- cvclZero F145) 0))))))))) (and (= P34 ?v_43) (and (= P32 ?v_44) (and (= P30 (or (and ?v_69 ?v_43) (and (or (and ?v_71 ?v_30) (and ?v_68 ?v_43)) ?v_70))) (and (= P28 (or (and ?v_69 ?v_44) (and ?v_70 (or (and ?v_71 ?v_34) (and ?v_68 ?v_44))))) (and (= P26 (or (and ?v_72 ?v_75) (and (or (and ?v_72 ?v_74) (and ?v_29 ?v_77)) ?v_76))) (and (= P24 (or (and ?v_47 ?v_75) (and ?v_76 (or (and ?v_35 ?v_77) (and ?v_47 ?v_74))))) (and (or (and ?v_28 (= (- F134 F22) 0)) (and P139 (= (- F145 F22) 0))) (and (or (and P139 (= (- F144 F20) 0)) (and ?v_28 (= (- F138 F20) 0))) (and (or (and P139 (= (- F143 F18) 0)) (and ?v_28 (= (- F137 F18) 0))) (and (or (and P139 (= (- F142 F16) 0)) (and ?v_28 (= (- F136 F16) 0))) (and (or (and P139 (= (- F141 F14) 0)) (and ?v_28 (= (- F135 F14) 0))) (and P10 (= P12 (or ?v_28 ?v_36))))))))))))))) (or (not (or (not (and (and (and (and (and (= ?v_288 P246) (and (and (and (and (or (and (= (- F260 F242) 0) P255) (and ?v_78 (= (- F254 F242) 0))) (and (and (or (and P255 (= (- F258 F240) 0)) (and ?v_78 (= (- F252 F240) 0))) (and (and (= ?v_287 P238) P237) (or (and ?v_78 (= (- F251 F239) 0)) (and P255 (= (- F257 F239) 0))))) (or (and ?v_78 (= (- F253 F241) 0)) (and P255 (= (- F259 F241) 0))))) (or (and (= (- F261 F243) 0) P255) (and (= (- F250 F243) 0) ?v_78))) (= ?v_286 P244)) (= ?v_285 P245))) (= ?v_284 P247)) (= ?v_95 P248)) (= ?v_97 P249)) ?v_283)) ?v_240)) (and (and (and (and (and (= P198 (or (and ?v_188 (or (and ?v_189 ?v_150) (and ?v_180 ?v_164))) (and ?v_181 ?v_164))) (and (and (= (or (and ?v_186 (or (and ?v_187 ?v_149) (and ?v_183 ?v_185))) (and ?v_184 ?v_185)) P196) (and (= (or (and ?v_186 (or (and ?v_183 ?v_167) (and ?v_187 ?v_154))) (and ?v_184 ?v_167)) P195) (and (and (and (or (and ?v_148 (= (- F222 F192) 0)) (and (= (- F228 F192) 0) P224)) (and (or (and (= (- F227 F191) 0) P224) (and ?v_148 (= (- F221 F191) 0))) (and (and (= P189 (or ?v_148 ?v_160)) P188) (or (and ?v_148 (= (- F220 F190) 0)) (and (= (- F226 F190) 0) P224))))) (or (and (= (- F229 F193) 0) P224) (and ?v_148 (= (- F223 F193) 0)))) (or (and (= (- F230 F194) 0) P224) (and ?v_148 (= (- F219 F194) 0)))))) (= (or (and ?v_188 (or (and ?v_180 ?v_163) (and ?v_189 ?v_153))) (and ?v_181 ?v_163)) P197))) (= P199 ?v_163)) (= P200 ?v_164)) (and (and (and (and (or (and P206 (<= (- F211 F210) 0)) (and ?v_190 (<= (- F205 F204) 0))) (and (or (and P206 (<= (- F209 F208) 0)) (and ?v_190 (<= (- F203 F202) 0))) (or (and ?v_190 (<= (- F204 F203) 0)) (and P206 (<= (- F210 F209) 0))))) (or (or (or (and ?v_190 (= ?v_222 0)) (and P206 (= ?v_210 0))) (or (or (and ?v_190 (= ?v_220 0)) (and P206 (= ?v_211 0))) (or (and P206 (= ?v_215 0)) (and ?v_190 (= ?v_218 0))))) (or (and P206 (= ?v_206 0)) (and ?v_190 (= ?v_225 0))))) (and (and (and (and (not P215) (and (and (and (= (- cvclZero F212) 0) (and (and (and (and (= (- cvclZero F208) 0) (and ?v_190 (not P207))) (= (- cvclZero F209) 0)) (= (- cvclZero F210) 0)) (= (- cvclZero F211) 0))) (not P213)) (not P214))) (not P216)) (not P217)) (not P218))) (and (= ?v_207 P236) (and (= ?v_205 P235) (and (and (= (or (and ?v_205 ?v_231) (and (or (and ?v_205 ?v_230) (and ?v_193 ?v_238)) ?v_239)) P233) (and (and (and (and (or (and ?v_190 (= (- F229 F205) 0)) (and P206 (= (- F229 F211) 0))) (and (and (and (or (and P206 (= (- F226 F208) 0)) (and ?v_190 (= (- F226 F202) 0))) (and (= (or ?v_190 ?v_197) P225) P224)) (or (and ?v_190 (= (- F227 F203) 0)) (and P206 (= (- F227 F209) 0)))) (or (and P206 (= (- F228 F210) 0)) (and ?v_190 (= (- F228 F204) 0))))) (or (and ?v_190 (= (- F230 F201) 0)) (and P206 (= (- F230 F212) 0)))) (= (or (and (or (and ?v_209 ?v_232) (and ?v_194 ?v_235)) ?v_236) (and ?v_209 ?v_234)) P231)) (= (or (and (or (and ?v_192 ?v_235) (and ?v_237 ?v_232)) ?v_236) (and ?v_237 ?v_234)) P232))) (= (or (and (or (and ?v_191 ?v_238) (and ?v_207 ?v_230)) ?v_239) (and ?v_207 ?v_231)) P234)))))) (not (or ?v_240 (not (and (and (and (and (and (and (and (and (and (and (and (and (and P237 (= P238 (or ?v_241 ?v_249))) (or (and ?v_241 (= (- F239 F153) 0)) (and P157 (= (- F239 F159) 0)))) (or (and ?v_241 (= (- F240 F154) 0)) (and P157 (= (- F240 F160) 0)))) (or (and ?v_241 (= (- F241 F155) 0)) (and P157 (= (- F241 F161) 0)))) (or (and ?v_241 (= (- F242 F156) 0)) (and P157 (= (- F242 F162) 0)))) (or (and P157 (= (- F243 F163) 0)) (and ?v_241 (= (- F243 F152) 0)))) (= (or (and ?v_272 ?v_258) (and ?v_277 (or (and ?v_245 ?v_276) (and ?v_274 ?v_258)))) P244)) (= (or (and ?v_275 ?v_272) (and (or (and ?v_275 ?v_274) (and ?v_247 ?v_276)) ?v_277)) P245)) (= P246 (or (and ?v_279 ?v_257) (and ?v_282 (or (and ?v_244 ?v_281) (and ?v_280 ?v_257)))))) (= (or (and ?v_256 ?v_279) (and (or (and ?v_242 ?v_281) (and ?v_256 ?v_280)) ?v_282)) P247)) (= ?v_257 P248)) (= ?v_256 P249)) (and ?v_283 (and (= ?v_97 P169) (and (= ?v_95 P168) (and (= P167 ?v_284) (and (and (= P165 ?v_285) (and (= P164 ?v_286) (and (or (and (= (- F250 F163) 0) ?v_78) (and (= (- F261 F163) 0) P255)) (and (or (and P255 (= (- F260 F162) 0)) (and ?v_78 (= (- F254 F162) 0))) (and (or (and P255 (= (- F259 F161) 0)) (and ?v_78 (= (- F253 F161) 0))) (and (or (and P255 (= (- F258 F160) 0)) (and ?v_78 (= (- F252 F160) 0))) (and (or (and P255 (= (- F257 F159) 0)) (and ?v_78 (= (- F251 F159) 0))) (and P157 (= ?v_287 P158))))))))) (= ?v_288 P166))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
(exit)

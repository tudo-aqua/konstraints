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
(declare-fun x_80 () Real)
(declare-fun x_81 () Bool)
(declare-fun x_82 () Bool)
(declare-fun x_83 () Real)
(declare-fun x_84 () Bool)
(declare-fun x_85 () Bool)
(declare-fun x_86 () Bool)
(declare-fun x_87 () Bool)
(declare-fun x_88 () Real)
(declare-fun x_89 () Real)
(declare-fun x_90 () Real)
(declare-fun x_91 () Real)
(declare-fun x_92 () Real)
(declare-fun x_93 () Real)
(declare-fun x_94 () Real)
(declare-fun x_95 () Bool)
(declare-fun x_96 () Bool)
(declare-fun x_97 () Real)
(declare-fun x_98 () Bool)
(declare-fun x_99 () Bool)
(declare-fun x_100 () Bool)
(declare-fun x_101 () Bool)
(declare-fun x_102 () Real)
(declare-fun x_103 () Real)
(declare-fun x_104 () Real)
(declare-fun x_105 () Real)
(declare-fun x_106 () Real)
(declare-fun x_107 () Real)
(assert (let ((?v_24 (not x_95)) (?v_25 (not x_96))) (let ((?v_26 (and ?v_24 ?v_25)) (?v_62 (not x_98)) (?v_63 (not x_99))) (let ((?v_64 (and ?v_62 ?v_63)) (?v_47 (not x_100)) (?v_48 (not x_101))) (let ((?v_50 (and ?v_47 ?v_48)) (?v_29 (and (= x_98 x_84) (= x_99 x_85))) (?v_59 (not x_84)) (?v_57 (not x_85))) (let ((?v_54 (and ?v_59 ?v_57)) (?v_18 (and (= x_95 x_81) (= x_96 x_82))) (?v_43 (not x_86)) (?v_40 (not x_87))) (let ((?v_35 (and ?v_43 ?v_40)) (?v_60 (and ?v_59 x_85)) (?v_27 (and (= x_100 x_86) (= x_101 x_87))) (?v_45 (and ?v_43 x_87)) (?v_21 (not x_81)) (?v_19 (not x_82))) (let ((?v_14 (and ?v_21 ?v_19)) (?v_22 (and ?v_21 x_82)) (?v_83 (and (= x_84 x_70) (= x_85 x_71))) (?v_109 (not x_70)) (?v_107 (not x_71))) (let ((?v_104 (and ?v_109 ?v_107)) (?v_75 (and (= x_81 x_67) (= x_82 x_68))) (?v_97 (not x_72)) (?v_94 (not x_73))) (let ((?v_89 (and ?v_97 ?v_94)) (?v_110 (and ?v_109 x_71)) (?v_81 (and (= x_86 x_72) (= x_87 x_73))) (?v_99 (and ?v_97 x_73)) (?v_78 (not x_67)) (?v_76 (not x_68))) (let ((?v_71 (and ?v_78 ?v_76)) (?v_79 (and ?v_78 x_68)) (?v_130 (and (= x_70 x_56) (= x_71 x_57))) (?v_156 (not x_56)) (?v_154 (not x_57))) (let ((?v_151 (and ?v_156 ?v_154)) (?v_122 (and (= x_67 x_53) (= x_68 x_54))) (?v_144 (not x_58)) (?v_141 (not x_59))) (let ((?v_136 (and ?v_144 ?v_141)) (?v_157 (and ?v_156 x_57)) (?v_128 (and (= x_72 x_58) (= x_73 x_59))) (?v_146 (and ?v_144 x_59)) (?v_125 (not x_53)) (?v_123 (not x_54))) (let ((?v_118 (and ?v_125 ?v_123)) (?v_126 (and ?v_125 x_54)) (?v_177 (and (= x_56 x_42) (= x_57 x_43))) (?v_203 (not x_42)) (?v_201 (not x_43))) (let ((?v_198 (and ?v_203 ?v_201)) (?v_169 (and (= x_53 x_39) (= x_54 x_40))) (?v_191 (not x_44)) (?v_188 (not x_45))) (let ((?v_183 (and ?v_191 ?v_188)) (?v_204 (and ?v_203 x_43)) (?v_175 (and (= x_58 x_44) (= x_59 x_45))) (?v_193 (and ?v_191 x_45)) (?v_172 (not x_39)) (?v_170 (not x_40))) (let ((?v_165 (and ?v_172 ?v_170)) (?v_173 (and ?v_172 x_40)) (?v_224 (and (= x_42 x_28) (= x_43 x_29))) (?v_250 (not x_28)) (?v_248 (not x_29))) (let ((?v_245 (and ?v_250 ?v_248)) (?v_216 (and (= x_39 x_25) (= x_40 x_26))) (?v_238 (not x_30)) (?v_235 (not x_31))) (let ((?v_230 (and ?v_238 ?v_235)) (?v_251 (and ?v_250 x_29)) (?v_222 (and (= x_44 x_30) (= x_45 x_31))) (?v_240 (and ?v_238 x_31)) (?v_219 (not x_25)) (?v_217 (not x_26))) (let ((?v_212 (and ?v_219 ?v_217)) (?v_220 (and ?v_219 x_26)) (?v_271 (and (= x_28 x_14) (= x_29 x_15))) (?v_297 (not x_14)) (?v_295 (not x_15))) (let ((?v_292 (and ?v_297 ?v_295)) (?v_263 (and (= x_25 x_11) (= x_26 x_12))) (?v_285 (not x_16)) (?v_282 (not x_17))) (let ((?v_277 (and ?v_285 ?v_282)) (?v_298 (and ?v_297 x_15)) (?v_269 (and (= x_30 x_16) (= x_31 x_17))) (?v_287 (and ?v_285 x_17)) (?v_266 (not x_11)) (?v_264 (not x_12))) (let ((?v_259 (and ?v_266 ?v_264)) (?v_267 (and ?v_266 x_12)) (?v_321 (and (= x_14 x_4) (= x_15 x_5))) (?v_347 (not x_4)) (?v_345 (not x_5))) (let ((?v_341 (and ?v_347 ?v_345)) (?v_313 (and (= x_11 x_0) (= x_12 x_1))) (?v_335 (not x_2)) (?v_332 (not x_3))) (let ((?v_325 (and ?v_335 ?v_332)) (?v_348 (and ?v_347 x_5)) (?v_319 (and (= x_16 x_2) (= x_17 x_3))) (?v_337 (and ?v_335 x_3)) (?v_316 (not x_0)) (?v_314 (not x_1))) (let ((?v_306 (and ?v_316 ?v_314)) (?v_317 (and ?v_316 x_1)) (?v_307 (- cvclZero x_6))) (let ((?v_303 (< ?v_307 0)) (?v_326 (- cvclZero x_7))) (let ((?v_302 (< ?v_326 0)) (?v_342 (- cvclZero x_8))) (let ((?v_301 (< ?v_342 0)) (?v_0 (- x_9 cvclZero))) (let ((?v_308 (= ?v_0 0)) (?v_8 (< (- x_88 x_89) 0))) (let ((?v_9 (ite ?v_8 (< (- x_88 x_90) 0) (< (- x_89 x_90) 0))) (?v_52 (= (- x_104 x_90) 0)) (?v_28 (= (- x_103 x_89) 0)) (?v_30 (= (- x_102 x_88) 0)) (?v_12 (= (- x_97 x_83) 0)) (?v_13 (- x_94 cvclZero))) (let ((?v_32 (= ?v_13 0)) (?v_11 (- x_92 x_90))) (let ((?v_15 (= ?v_11 0)) (?v_6 (- x_83 cvclZero))) (let ((?v_16 (= ?v_6 0)) (?v_20 (- x_92 x_104))) (let ((?v_17 (< ?v_20 0)) (?v_34 (= ?v_13 1)) (?v_37 (not ?v_16)) (?v_39 (= ?v_13 2)) (?v_7 (- x_97 cvclZero))) (let ((?v_350 (= ?v_7 1)) (?v_42 (= ?v_13 3)) (?v_23 (= ?v_6 1)) (?v_44 (= ?v_13 4))) (let ((?v_353 (not ?v_23)) (?v_49 (= ?v_13 5)) (?v_51 (= ?v_7 0)) (?v_33 (- x_92 x_89))) (let ((?v_36 (= ?v_33 0)) (?v_41 (- x_92 x_103))) (let ((?v_38 (< ?v_41 0)) (?v_351 (= ?v_7 2)) (?v_46 (= ?v_6 2))) (let ((?v_354 (not ?v_46)) (?v_53 (- x_92 x_88))) (let ((?v_55 (= ?v_53 0)) (?v_58 (- x_92 x_102))) (let ((?v_56 (< ?v_58 0)) (?v_352 (= ?v_7 3)) (?v_61 (= ?v_6 3))) (let ((?v_355 (not ?v_61)) (?v_65 (< (- x_74 x_75) 0))) (let ((?v_66 (ite ?v_65 (< (- x_74 x_76) 0) (< (- x_75 x_76) 0))) (?v_102 (= (- x_90 x_76) 0)) (?v_82 (= (- x_89 x_75) 0)) (?v_84 (= (- x_88 x_74) 0)) (?v_69 (= (- x_83 x_69) 0)) (?v_70 (- x_80 cvclZero))) (let ((?v_86 (= ?v_70 0)) (?v_68 (- x_78 x_76))) (let ((?v_72 (= ?v_68 0)) (?v_5 (- x_69 cvclZero))) (let ((?v_73 (= ?v_5 0)) (?v_77 (- x_78 x_90))) (let ((?v_74 (< ?v_77 0)) (?v_88 (= ?v_70 1)) (?v_91 (not ?v_73)) (?v_93 (= ?v_70 2)) (?v_96 (= ?v_70 3)) (?v_80 (= ?v_5 1)) (?v_98 (= ?v_70 4))) (let ((?v_356 (not ?v_80)) (?v_101 (= ?v_70 5)) (?v_87 (- x_78 x_75))) (let ((?v_90 (= ?v_87 0)) (?v_95 (- x_78 x_89))) (let ((?v_92 (< ?v_95 0)) (?v_100 (= ?v_5 2))) (let ((?v_357 (not ?v_100)) (?v_103 (- x_78 x_74))) (let ((?v_105 (= ?v_103 0)) (?v_108 (- x_78 x_88))) (let ((?v_106 (< ?v_108 0)) (?v_111 (= ?v_5 3))) (let ((?v_358 (not ?v_111)) (?v_112 (< (- x_60 x_61) 0))) (let ((?v_113 (ite ?v_112 (< (- x_60 x_62) 0) (< (- x_61 x_62) 0))) (?v_149 (= (- x_76 x_62) 0)) (?v_129 (= (- x_75 x_61) 0)) (?v_131 (= (- x_74 x_60) 0)) (?v_116 (= (- x_69 x_55) 0)) (?v_117 (- x_66 cvclZero))) (let ((?v_133 (= ?v_117 0)) (?v_115 (- x_64 x_62))) (let ((?v_119 (= ?v_115 0)) (?v_4 (- x_55 cvclZero))) (let ((?v_120 (= ?v_4 0)) (?v_124 (- x_64 x_76))) (let ((?v_121 (< ?v_124 0)) (?v_135 (= ?v_117 1)) (?v_138 (not ?v_120)) (?v_140 (= ?v_117 2)) (?v_143 (= ?v_117 3)) (?v_127 (= ?v_4 1)) (?v_145 (= ?v_117 4))) (let ((?v_359 (not ?v_127)) (?v_148 (= ?v_117 5)) (?v_134 (- x_64 x_61))) (let ((?v_137 (= ?v_134 0)) (?v_142 (- x_64 x_75))) (let ((?v_139 (< ?v_142 0)) (?v_147 (= ?v_4 2))) (let ((?v_360 (not ?v_147)) (?v_150 (- x_64 x_60))) (let ((?v_152 (= ?v_150 0)) (?v_155 (- x_64 x_74))) (let ((?v_153 (< ?v_155 0)) (?v_158 (= ?v_4 3))) (let ((?v_361 (not ?v_158)) (?v_159 (< (- x_46 x_47) 0))) (let ((?v_160 (ite ?v_159 (< (- x_46 x_48) 0) (< (- x_47 x_48) 0))) (?v_196 (= (- x_62 x_48) 0)) (?v_176 (= (- x_61 x_47) 0)) (?v_178 (= (- x_60 x_46) 0)) (?v_163 (= (- x_55 x_41) 0)) (?v_164 (- x_52 cvclZero))) (let ((?v_180 (= ?v_164 0)) (?v_162 (- x_50 x_48))) (let ((?v_166 (= ?v_162 0)) (?v_3 (- x_41 cvclZero))) (let ((?v_167 (= ?v_3 0)) (?v_171 (- x_50 x_62))) (let ((?v_168 (< ?v_171 0)) (?v_182 (= ?v_164 1)) (?v_185 (not ?v_167)) (?v_187 (= ?v_164 2)) (?v_190 (= ?v_164 3)) (?v_174 (= ?v_3 1)) (?v_192 (= ?v_164 4))) (let ((?v_362 (not ?v_174)) (?v_195 (= ?v_164 5)) (?v_181 (- x_50 x_47))) (let ((?v_184 (= ?v_181 0)) (?v_189 (- x_50 x_61))) (let ((?v_186 (< ?v_189 0)) (?v_194 (= ?v_3 2))) (let ((?v_363 (not ?v_194)) (?v_197 (- x_50 x_46))) (let ((?v_199 (= ?v_197 0)) (?v_202 (- x_50 x_60))) (let ((?v_200 (< ?v_202 0)) (?v_205 (= ?v_3 3))) (let ((?v_364 (not ?v_205)) (?v_206 (< (- x_32 x_33) 0))) (let ((?v_207 (ite ?v_206 (< (- x_32 x_34) 0) (< (- x_33 x_34) 0))) (?v_243 (= (- x_48 x_34) 0)) (?v_223 (= (- x_47 x_33) 0)) (?v_225 (= (- x_46 x_32) 0)) (?v_210 (= (- x_41 x_27) 0)) (?v_211 (- x_38 cvclZero))) (let ((?v_227 (= ?v_211 0)) (?v_209 (- x_36 x_34))) (let ((?v_213 (= ?v_209 0)) (?v_2 (- x_27 cvclZero))) (let ((?v_214 (= ?v_2 0)) (?v_218 (- x_36 x_48))) (let ((?v_215 (< ?v_218 0)) (?v_229 (= ?v_211 1)) (?v_232 (not ?v_214)) (?v_234 (= ?v_211 2)) (?v_237 (= ?v_211 3)) (?v_221 (= ?v_2 1)) (?v_239 (= ?v_211 4))) (let ((?v_365 (not ?v_221)) (?v_242 (= ?v_211 5)) (?v_228 (- x_36 x_33))) (let ((?v_231 (= ?v_228 0)) (?v_236 (- x_36 x_47))) (let ((?v_233 (< ?v_236 0)) (?v_241 (= ?v_2 2))) (let ((?v_366 (not ?v_241)) (?v_244 (- x_36 x_32))) (let ((?v_246 (= ?v_244 0)) (?v_249 (- x_36 x_46))) (let ((?v_247 (< ?v_249 0)) (?v_252 (= ?v_2 3))) (let ((?v_367 (not ?v_252)) (?v_253 (< (- x_18 x_19) 0))) (let ((?v_254 (ite ?v_253 (< (- x_18 x_20) 0) (< (- x_19 x_20) 0))) (?v_290 (= (- x_34 x_20) 0)) (?v_270 (= (- x_33 x_19) 0)) (?v_272 (= (- x_32 x_18) 0)) (?v_257 (= (- x_27 x_13) 0)) (?v_258 (- x_24 cvclZero))) (let ((?v_274 (= ?v_258 0)) (?v_256 (- x_22 x_20))) (let ((?v_260 (= ?v_256 0)) (?v_1 (- x_13 cvclZero))) (let ((?v_261 (= ?v_1 0)) (?v_265 (- x_22 x_34))) (let ((?v_262 (< ?v_265 0)) (?v_276 (= ?v_258 1)) (?v_279 (not ?v_261)) (?v_281 (= ?v_258 2)) (?v_284 (= ?v_258 3)) (?v_268 (= ?v_1 1)) (?v_286 (= ?v_258 4))) (let ((?v_368 (not ?v_268)) (?v_289 (= ?v_258 5)) (?v_275 (- x_22 x_19))) (let ((?v_278 (= ?v_275 0)) (?v_283 (- x_22 x_33))) (let ((?v_280 (< ?v_283 0)) (?v_288 (= ?v_1 2))) (let ((?v_369 (not ?v_288)) (?v_291 (- x_22 x_18))) (let ((?v_293 (= ?v_291 0)) (?v_296 (- x_22 x_32))) (let ((?v_294 (< ?v_296 0)) (?v_299 (= ?v_1 3))) (let ((?v_370 (not ?v_299)) (?v_300 (< (- x_8 x_7) 0))) (let ((?v_304 (ite ?v_300 (< (- x_8 x_6) 0) (< (- x_7 x_6) 0))) (?v_340 (= (- x_20 x_6) 0)) (?v_320 (= (- x_19 x_7) 0)) (?v_322 (= (- x_18 x_8) 0)) (?v_309 (= (- x_13 x_9) 0)) (?v_310 (- x_10 cvclZero))) (let ((?v_324 (= ?v_310 0)) (?v_311 (= ?v_307 0)) (?v_315 (- cvclZero x_20))) (let ((?v_312 (< ?v_315 0)) (?v_327 (= ?v_310 1)) (?v_329 (not ?v_308)) (?v_331 (= ?v_310 2)) (?v_334 (= ?v_310 3)) (?v_318 (= ?v_0 1)) (?v_336 (= ?v_310 4))) (let ((?v_371 (not ?v_318)) (?v_339 (= ?v_310 5)) (?v_328 (= ?v_326 0)) (?v_333 (- cvclZero x_19))) (let ((?v_330 (< ?v_333 0)) (?v_338 (= ?v_0 2))) (let ((?v_372 (not ?v_338)) (?v_343 (= ?v_342 0)) (?v_346 (- cvclZero x_18))) (let ((?v_344 (< ?v_346 0)) (?v_349 (= ?v_0 3))) (let ((?v_373 (not ?v_349)) (?v_10 (- x_105 cvclZero)) (?v_31 (- x_107 cvclZero)) (?v_67 (- x_91 cvclZero)) (?v_85 (- x_93 cvclZero)) (?v_114 (- x_77 cvclZero)) (?v_132 (- x_79 cvclZero)) (?v_161 (- x_63 cvclZero)) (?v_179 (- x_65 cvclZero)) (?v_208 (- x_49 cvclZero)) (?v_226 (- x_51 cvclZero)) (?v_255 (- x_35 cvclZero)) (?v_273 (- x_37 cvclZero)) (?v_305 (- x_21 cvclZero)) (?v_323 (- x_23 cvclZero))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (not (< ?v_0 0)) (<= ?v_0 3)) (not (< ?v_1 0))) (<= ?v_1 3)) (not (< ?v_2 0))) (<= ?v_2 3)) (not (< ?v_3 0))) (<= ?v_3 3)) (not (< ?v_4 0))) (<= ?v_4 3)) (not (< ?v_5 0))) (<= ?v_5 3)) (not (< ?v_6 0))) (<= ?v_6 3)) (not (< ?v_7 0))) (<= ?v_7 3)) ?v_306) ?v_325) ?v_341) ?v_303) ?v_302) ?v_301) ?v_308) (or (and (and (and (and (and (and (and (and (and (= ?v_10 0) (ite ?v_9 (ite ?v_8 (< ?v_53 0) (< ?v_33 0)) (< ?v_11 0))) (ite ?v_9 (ite ?v_8 (= (- x_106 x_88) 0) (= (- x_106 x_89) 0)) (= (- x_106 x_90) 0))) ?v_18) ?v_27) ?v_29) ?v_52) ?v_28) ?v_30) ?v_12) (and (and (= ?v_10 1) (or (or (and (and (and (and (and (= ?v_31 1) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_32 ?v_14) ?v_15) ?v_16) x_95) ?v_25) ?v_17) (<= (- x_104 x_92) 2)) ?v_12) (and (and (and (and (and (and ?v_34 ?v_14) ?v_15) ?v_37) ?v_17) ?v_12) ?v_18)) (and (and (and (and (and (and (and ?v_39 x_81) ?v_19) ?v_15) ?v_24) x_96) ?v_350) (<= ?v_20 (- 4)))) (and (and (and (and (and (and (and ?v_42 ?v_22) ?v_15) ?v_23) x_95) x_96) ?v_17) ?v_12)) (and (and (and (and (and (and ?v_44 ?v_22) ?v_15) ?v_353) ?v_26) ?v_17) ?v_12)) (and (and (and (and (and (and ?v_49 x_81) x_82) ?v_15) ?v_26) ?v_51) ?v_17))) ?v_27) ?v_28) ?v_29) ?v_30) (and (and (and (and (and (= ?v_31 2) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_32 ?v_35) ?v_36) ?v_16) x_100) ?v_48) ?v_38) (<= (- x_103 x_92) 2)) ?v_12) (and (and (and (and (and (and ?v_34 ?v_35) ?v_36) ?v_37) ?v_38) ?v_12) ?v_27)) (and (and (and (and (and (and (and ?v_39 x_86) ?v_40) ?v_36) ?v_47) x_101) ?v_351) (<= ?v_41 (- 4)))) (and (and (and (and (and (and (and ?v_42 ?v_45) ?v_36) ?v_46) x_100) x_101) ?v_38) ?v_12)) (and (and (and (and (and (and ?v_44 ?v_45) ?v_36) ?v_354) ?v_50) ?v_38) ?v_12)) (and (and (and (and (and (and ?v_49 x_86) x_87) ?v_36) ?v_50) ?v_51) ?v_38))) ?v_18) ?v_52) ?v_29) ?v_30)) (and (and (and (and (and (= ?v_31 3) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_32 ?v_54) ?v_55) ?v_16) x_98) ?v_63) ?v_56) (<= (- x_102 x_92) 2)) ?v_12) (and (and (and (and (and (and ?v_34 ?v_54) ?v_55) ?v_37) ?v_56) ?v_12) ?v_29)) (and (and (and (and (and (and (and ?v_39 x_84) ?v_57) ?v_55) ?v_62) x_99) ?v_352) (<= ?v_58 (- 4)))) (and (and (and (and (and (and (and ?v_42 ?v_60) ?v_55) ?v_61) x_98) x_99) ?v_56) ?v_12)) (and (and (and (and (and (and ?v_44 ?v_60) ?v_55) ?v_355) ?v_64) ?v_56) ?v_12)) (and (and (and (and (and (and ?v_49 x_84) x_85) ?v_55) ?v_64) ?v_51) ?v_56))) ?v_18) ?v_52) ?v_27) ?v_28))) (= (- x_106 x_92) 0)))) (or (and (and (and (and (and (and (and (and (and (= ?v_67 0) (ite ?v_66 (ite ?v_65 (< ?v_103 0) (< ?v_87 0)) (< ?v_68 0))) (ite ?v_66 (ite ?v_65 (= (- x_92 x_74) 0) (= (- x_92 x_75) 0)) (= (- x_92 x_76) 0))) ?v_75) ?v_81) ?v_83) ?v_102) ?v_82) ?v_84) ?v_69) (and (and (= ?v_67 1) (or (or (and (and (and (and (and (= ?v_85 1) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_86 ?v_71) ?v_72) ?v_73) x_81) ?v_19) ?v_74) (<= (- x_90 x_78) 2)) ?v_69) (and (and (and (and (and (and ?v_88 ?v_71) ?v_72) ?v_91) ?v_74) ?v_69) ?v_75)) (and (and (and (and (and (and (and ?v_93 x_67) ?v_76) ?v_72) ?v_21) x_82) ?v_23) (<= ?v_77 (- 4)))) (and (and (and (and (and (and (and ?v_96 ?v_79) ?v_72) ?v_80) x_81) x_82) ?v_74) ?v_69)) (and (and (and (and (and (and ?v_98 ?v_79) ?v_72) ?v_356) ?v_14) ?v_74) ?v_69)) (and (and (and (and (and (and ?v_101 x_67) x_68) ?v_72) ?v_14) ?v_16) ?v_74))) ?v_81) ?v_82) ?v_83) ?v_84) (and (and (and (and (and (= ?v_85 2) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_86 ?v_89) ?v_90) ?v_73) x_86) ?v_40) ?v_92) (<= (- x_89 x_78) 2)) ?v_69) (and (and (and (and (and (and ?v_88 ?v_89) ?v_90) ?v_91) ?v_92) ?v_69) ?v_81)) (and (and (and (and (and (and (and ?v_93 x_72) ?v_94) ?v_90) ?v_43) x_87) ?v_46) (<= ?v_95 (- 4)))) (and (and (and (and (and (and (and ?v_96 ?v_99) ?v_90) ?v_100) x_86) x_87) ?v_92) ?v_69)) (and (and (and (and (and (and ?v_98 ?v_99) ?v_90) ?v_357) ?v_35) ?v_92) ?v_69)) (and (and (and (and (and (and ?v_101 x_72) x_73) ?v_90) ?v_35) ?v_16) ?v_92))) ?v_75) ?v_102) ?v_83) ?v_84)) (and (and (and (and (and (= ?v_85 3) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_86 ?v_104) ?v_105) ?v_73) x_84) ?v_57) ?v_106) (<= (- x_88 x_78) 2)) ?v_69) (and (and (and (and (and (and ?v_88 ?v_104) ?v_105) ?v_91) ?v_106) ?v_69) ?v_83)) (and (and (and (and (and (and (and ?v_93 x_70) ?v_107) ?v_105) ?v_59) x_85) ?v_61) (<= ?v_108 (- 4)))) (and (and (and (and (and (and (and ?v_96 ?v_110) ?v_105) ?v_111) x_84) x_85) ?v_106) ?v_69)) (and (and (and (and (and (and ?v_98 ?v_110) ?v_105) ?v_358) ?v_54) ?v_106) ?v_69)) (and (and (and (and (and (and ?v_101 x_70) x_71) ?v_105) ?v_54) ?v_16) ?v_106))) ?v_75) ?v_102) ?v_81) ?v_82))) (= (- x_92 x_78) 0)))) (or (and (and (and (and (and (and (and (and (and (= ?v_114 0) (ite ?v_113 (ite ?v_112 (< ?v_150 0) (< ?v_134 0)) (< ?v_115 0))) (ite ?v_113 (ite ?v_112 (= (- x_78 x_60) 0) (= (- x_78 x_61) 0)) (= (- x_78 x_62) 0))) ?v_122) ?v_128) ?v_130) ?v_149) ?v_129) ?v_131) ?v_116) (and (and (= ?v_114 1) (or (or (and (and (and (and (and (= ?v_132 1) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_133 ?v_118) ?v_119) ?v_120) x_67) ?v_76) ?v_121) (<= (- x_76 x_64) 2)) ?v_116) (and (and (and (and (and (and ?v_135 ?v_118) ?v_119) ?v_138) ?v_121) ?v_116) ?v_122)) (and (and (and (and (and (and (and ?v_140 x_53) ?v_123) ?v_119) ?v_78) x_68) ?v_80) (<= ?v_124 (- 4)))) (and (and (and (and (and (and (and ?v_143 ?v_126) ?v_119) ?v_127) x_67) x_68) ?v_121) ?v_116)) (and (and (and (and (and (and ?v_145 ?v_126) ?v_119) ?v_359) ?v_71) ?v_121) ?v_116)) (and (and (and (and (and (and ?v_148 x_53) x_54) ?v_119) ?v_71) ?v_73) ?v_121))) ?v_128) ?v_129) ?v_130) ?v_131) (and (and (and (and (and (= ?v_132 2) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_133 ?v_136) ?v_137) ?v_120) x_72) ?v_94) ?v_139) (<= (- x_75 x_64) 2)) ?v_116) (and (and (and (and (and (and ?v_135 ?v_136) ?v_137) ?v_138) ?v_139) ?v_116) ?v_128)) (and (and (and (and (and (and (and ?v_140 x_58) ?v_141) ?v_137) ?v_97) x_73) ?v_100) (<= ?v_142 (- 4)))) (and (and (and (and (and (and (and ?v_143 ?v_146) ?v_137) ?v_147) x_72) x_73) ?v_139) ?v_116)) (and (and (and (and (and (and ?v_145 ?v_146) ?v_137) ?v_360) ?v_89) ?v_139) ?v_116)) (and (and (and (and (and (and ?v_148 x_58) x_59) ?v_137) ?v_89) ?v_73) ?v_139))) ?v_122) ?v_149) ?v_130) ?v_131)) (and (and (and (and (and (= ?v_132 3) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_133 ?v_151) ?v_152) ?v_120) x_70) ?v_107) ?v_153) (<= (- x_74 x_64) 2)) ?v_116) (and (and (and (and (and (and ?v_135 ?v_151) ?v_152) ?v_138) ?v_153) ?v_116) ?v_130)) (and (and (and (and (and (and (and ?v_140 x_56) ?v_154) ?v_152) ?v_109) x_71) ?v_111) (<= ?v_155 (- 4)))) (and (and (and (and (and (and (and ?v_143 ?v_157) ?v_152) ?v_158) x_70) x_71) ?v_153) ?v_116)) (and (and (and (and (and (and ?v_145 ?v_157) ?v_152) ?v_361) ?v_104) ?v_153) ?v_116)) (and (and (and (and (and (and ?v_148 x_56) x_57) ?v_152) ?v_104) ?v_73) ?v_153))) ?v_122) ?v_149) ?v_128) ?v_129))) (= (- x_78 x_64) 0)))) (or (and (and (and (and (and (and (and (and (and (= ?v_161 0) (ite ?v_160 (ite ?v_159 (< ?v_197 0) (< ?v_181 0)) (< ?v_162 0))) (ite ?v_160 (ite ?v_159 (= (- x_64 x_46) 0) (= (- x_64 x_47) 0)) (= (- x_64 x_48) 0))) ?v_169) ?v_175) ?v_177) ?v_196) ?v_176) ?v_178) ?v_163) (and (and (= ?v_161 1) (or (or (and (and (and (and (and (= ?v_179 1) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_180 ?v_165) ?v_166) ?v_167) x_53) ?v_123) ?v_168) (<= (- x_62 x_50) 2)) ?v_163) (and (and (and (and (and (and ?v_182 ?v_165) ?v_166) ?v_185) ?v_168) ?v_163) ?v_169)) (and (and (and (and (and (and (and ?v_187 x_39) ?v_170) ?v_166) ?v_125) x_54) ?v_127) (<= ?v_171 (- 4)))) (and (and (and (and (and (and (and ?v_190 ?v_173) ?v_166) ?v_174) x_53) x_54) ?v_168) ?v_163)) (and (and (and (and (and (and ?v_192 ?v_173) ?v_166) ?v_362) ?v_118) ?v_168) ?v_163)) (and (and (and (and (and (and ?v_195 x_39) x_40) ?v_166) ?v_118) ?v_120) ?v_168))) ?v_175) ?v_176) ?v_177) ?v_178) (and (and (and (and (and (= ?v_179 2) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_180 ?v_183) ?v_184) ?v_167) x_58) ?v_141) ?v_186) (<= (- x_61 x_50) 2)) ?v_163) (and (and (and (and (and (and ?v_182 ?v_183) ?v_184) ?v_185) ?v_186) ?v_163) ?v_175)) (and (and (and (and (and (and (and ?v_187 x_44) ?v_188) ?v_184) ?v_144) x_59) ?v_147) (<= ?v_189 (- 4)))) (and (and (and (and (and (and (and ?v_190 ?v_193) ?v_184) ?v_194) x_58) x_59) ?v_186) ?v_163)) (and (and (and (and (and (and ?v_192 ?v_193) ?v_184) ?v_363) ?v_136) ?v_186) ?v_163)) (and (and (and (and (and (and ?v_195 x_44) x_45) ?v_184) ?v_136) ?v_120) ?v_186))) ?v_169) ?v_196) ?v_177) ?v_178)) (and (and (and (and (and (= ?v_179 3) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_180 ?v_198) ?v_199) ?v_167) x_56) ?v_154) ?v_200) (<= (- x_60 x_50) 2)) ?v_163) (and (and (and (and (and (and ?v_182 ?v_198) ?v_199) ?v_185) ?v_200) ?v_163) ?v_177)) (and (and (and (and (and (and (and ?v_187 x_42) ?v_201) ?v_199) ?v_156) x_57) ?v_158) (<= ?v_202 (- 4)))) (and (and (and (and (and (and (and ?v_190 ?v_204) ?v_199) ?v_205) x_56) x_57) ?v_200) ?v_163)) (and (and (and (and (and (and ?v_192 ?v_204) ?v_199) ?v_364) ?v_151) ?v_200) ?v_163)) (and (and (and (and (and (and ?v_195 x_42) x_43) ?v_199) ?v_151) ?v_120) ?v_200))) ?v_169) ?v_196) ?v_175) ?v_176))) (= (- x_64 x_50) 0)))) (or (and (and (and (and (and (and (and (and (and (= ?v_208 0) (ite ?v_207 (ite ?v_206 (< ?v_244 0) (< ?v_228 0)) (< ?v_209 0))) (ite ?v_207 (ite ?v_206 (= (- x_50 x_32) 0) (= (- x_50 x_33) 0)) (= (- x_50 x_34) 0))) ?v_216) ?v_222) ?v_224) ?v_243) ?v_223) ?v_225) ?v_210) (and (and (= ?v_208 1) (or (or (and (and (and (and (and (= ?v_226 1) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_227 ?v_212) ?v_213) ?v_214) x_39) ?v_170) ?v_215) (<= (- x_48 x_36) 2)) ?v_210) (and (and (and (and (and (and ?v_229 ?v_212) ?v_213) ?v_232) ?v_215) ?v_210) ?v_216)) (and (and (and (and (and (and (and ?v_234 x_25) ?v_217) ?v_213) ?v_172) x_40) ?v_174) (<= ?v_218 (- 4)))) (and (and (and (and (and (and (and ?v_237 ?v_220) ?v_213) ?v_221) x_39) x_40) ?v_215) ?v_210)) (and (and (and (and (and (and ?v_239 ?v_220) ?v_213) ?v_365) ?v_165) ?v_215) ?v_210)) (and (and (and (and (and (and ?v_242 x_25) x_26) ?v_213) ?v_165) ?v_167) ?v_215))) ?v_222) ?v_223) ?v_224) ?v_225) (and (and (and (and (and (= ?v_226 2) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_227 ?v_230) ?v_231) ?v_214) x_44) ?v_188) ?v_233) (<= (- x_47 x_36) 2)) ?v_210) (and (and (and (and (and (and ?v_229 ?v_230) ?v_231) ?v_232) ?v_233) ?v_210) ?v_222)) (and (and (and (and (and (and (and ?v_234 x_30) ?v_235) ?v_231) ?v_191) x_45) ?v_194) (<= ?v_236 (- 4)))) (and (and (and (and (and (and (and ?v_237 ?v_240) ?v_231) ?v_241) x_44) x_45) ?v_233) ?v_210)) (and (and (and (and (and (and ?v_239 ?v_240) ?v_231) ?v_366) ?v_183) ?v_233) ?v_210)) (and (and (and (and (and (and ?v_242 x_30) x_31) ?v_231) ?v_183) ?v_167) ?v_233))) ?v_216) ?v_243) ?v_224) ?v_225)) (and (and (and (and (and (= ?v_226 3) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_227 ?v_245) ?v_246) ?v_214) x_42) ?v_201) ?v_247) (<= (- x_46 x_36) 2)) ?v_210) (and (and (and (and (and (and ?v_229 ?v_245) ?v_246) ?v_232) ?v_247) ?v_210) ?v_224)) (and (and (and (and (and (and (and ?v_234 x_28) ?v_248) ?v_246) ?v_203) x_43) ?v_205) (<= ?v_249 (- 4)))) (and (and (and (and (and (and (and ?v_237 ?v_251) ?v_246) ?v_252) x_42) x_43) ?v_247) ?v_210)) (and (and (and (and (and (and ?v_239 ?v_251) ?v_246) ?v_367) ?v_198) ?v_247) ?v_210)) (and (and (and (and (and (and ?v_242 x_28) x_29) ?v_246) ?v_198) ?v_167) ?v_247))) ?v_216) ?v_243) ?v_222) ?v_223))) (= (- x_50 x_36) 0)))) (or (and (and (and (and (and (and (and (and (and (= ?v_255 0) (ite ?v_254 (ite ?v_253 (< ?v_291 0) (< ?v_275 0)) (< ?v_256 0))) (ite ?v_254 (ite ?v_253 (= (- x_36 x_18) 0) (= (- x_36 x_19) 0)) (= (- x_36 x_20) 0))) ?v_263) ?v_269) ?v_271) ?v_290) ?v_270) ?v_272) ?v_257) (and (and (= ?v_255 1) (or (or (and (and (and (and (and (= ?v_273 1) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_274 ?v_259) ?v_260) ?v_261) x_25) ?v_217) ?v_262) (<= (- x_34 x_22) 2)) ?v_257) (and (and (and (and (and (and ?v_276 ?v_259) ?v_260) ?v_279) ?v_262) ?v_257) ?v_263)) (and (and (and (and (and (and (and ?v_281 x_11) ?v_264) ?v_260) ?v_219) x_26) ?v_221) (<= ?v_265 (- 4)))) (and (and (and (and (and (and (and ?v_284 ?v_267) ?v_260) ?v_268) x_25) x_26) ?v_262) ?v_257)) (and (and (and (and (and (and ?v_286 ?v_267) ?v_260) ?v_368) ?v_212) ?v_262) ?v_257)) (and (and (and (and (and (and ?v_289 x_11) x_12) ?v_260) ?v_212) ?v_214) ?v_262))) ?v_269) ?v_270) ?v_271) ?v_272) (and (and (and (and (and (= ?v_273 2) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_274 ?v_277) ?v_278) ?v_261) x_30) ?v_235) ?v_280) (<= (- x_33 x_22) 2)) ?v_257) (and (and (and (and (and (and ?v_276 ?v_277) ?v_278) ?v_279) ?v_280) ?v_257) ?v_269)) (and (and (and (and (and (and (and ?v_281 x_16) ?v_282) ?v_278) ?v_238) x_31) ?v_241) (<= ?v_283 (- 4)))) (and (and (and (and (and (and (and ?v_284 ?v_287) ?v_278) ?v_288) x_30) x_31) ?v_280) ?v_257)) (and (and (and (and (and (and ?v_286 ?v_287) ?v_278) ?v_369) ?v_230) ?v_280) ?v_257)) (and (and (and (and (and (and ?v_289 x_16) x_17) ?v_278) ?v_230) ?v_214) ?v_280))) ?v_263) ?v_290) ?v_271) ?v_272)) (and (and (and (and (and (= ?v_273 3) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_274 ?v_292) ?v_293) ?v_261) x_28) ?v_248) ?v_294) (<= (- x_32 x_22) 2)) ?v_257) (and (and (and (and (and (and ?v_276 ?v_292) ?v_293) ?v_279) ?v_294) ?v_257) ?v_271)) (and (and (and (and (and (and (and ?v_281 x_14) ?v_295) ?v_293) ?v_250) x_29) ?v_252) (<= ?v_296 (- 4)))) (and (and (and (and (and (and (and ?v_284 ?v_298) ?v_293) ?v_299) x_28) x_29) ?v_294) ?v_257)) (and (and (and (and (and (and ?v_286 ?v_298) ?v_293) ?v_370) ?v_245) ?v_294) ?v_257)) (and (and (and (and (and (and ?v_289 x_14) x_15) ?v_293) ?v_245) ?v_214) ?v_294))) ?v_263) ?v_290) ?v_269) ?v_270))) (= (- x_36 x_22) 0)))) (or (and (and (and (and (and (and (and (and (and (= ?v_305 0) (ite ?v_304 (ite ?v_300 ?v_301 ?v_302) ?v_303)) (ite ?v_304 (ite ?v_300 (= (- x_22 x_8) 0) (= (- x_22 x_7) 0)) (= (- x_22 x_6) 0))) ?v_313) ?v_319) ?v_321) ?v_340) ?v_320) ?v_322) ?v_309) (and (and (= ?v_305 1) (or (or (and (and (and (and (and (= ?v_323 1) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_324 ?v_306) ?v_311) ?v_308) x_11) ?v_264) ?v_312) (<= (- x_20 cvclZero) 2)) ?v_309) (and (and (and (and (and (and ?v_327 ?v_306) ?v_311) ?v_329) ?v_312) ?v_309) ?v_313)) (and (and (and (and (and (and (and ?v_331 x_0) ?v_314) ?v_311) ?v_266) x_12) ?v_268) (<= ?v_315 (- 4)))) (and (and (and (and (and (and (and ?v_334 ?v_317) ?v_311) ?v_318) x_11) x_12) ?v_312) ?v_309)) (and (and (and (and (and (and ?v_336 ?v_317) ?v_311) ?v_371) ?v_259) ?v_312) ?v_309)) (and (and (and (and (and (and ?v_339 x_0) x_1) ?v_311) ?v_259) ?v_261) ?v_312))) ?v_319) ?v_320) ?v_321) ?v_322) (and (and (and (and (and (= ?v_323 2) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_324 ?v_325) ?v_328) ?v_308) x_16) ?v_282) ?v_330) (<= (- x_19 cvclZero) 2)) ?v_309) (and (and (and (and (and (and ?v_327 ?v_325) ?v_328) ?v_329) ?v_330) ?v_309) ?v_319)) (and (and (and (and (and (and (and ?v_331 x_2) ?v_332) ?v_328) ?v_285) x_17) ?v_288) (<= ?v_333 (- 4)))) (and (and (and (and (and (and (and ?v_334 ?v_337) ?v_328) ?v_338) x_16) x_17) ?v_330) ?v_309)) (and (and (and (and (and (and ?v_336 ?v_337) ?v_328) ?v_372) ?v_277) ?v_330) ?v_309)) (and (and (and (and (and (and ?v_339 x_2) x_3) ?v_328) ?v_277) ?v_261) ?v_330))) ?v_313) ?v_340) ?v_321) ?v_322)) (and (and (and (and (and (= ?v_323 3) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_324 ?v_341) ?v_343) ?v_308) x_14) ?v_295) ?v_344) (<= (- x_18 cvclZero) 2)) ?v_309) (and (and (and (and (and (and ?v_327 ?v_341) ?v_343) ?v_329) ?v_344) ?v_309) ?v_321)) (and (and (and (and (and (and (and ?v_331 x_4) ?v_345) ?v_343) ?v_297) x_15) ?v_299) (<= ?v_346 (- 4)))) (and (and (and (and (and (and (and ?v_334 ?v_348) ?v_343) ?v_349) x_14) x_15) ?v_344) ?v_309)) (and (and (and (and (and (and ?v_336 ?v_348) ?v_343) ?v_373) ?v_292) ?v_344) ?v_309)) (and (and (and (and (and (and ?v_339 x_4) x_5) ?v_343) ?v_292) ?v_261) ?v_344))) ?v_313) ?v_340) ?v_319) ?v_320))) (= (- x_22 cvclZero) 0)))) (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (and (and x_95 x_96) (not ?v_350)) (and (and x_100 x_101) (not ?v_351))) (and (and x_98 x_99) (not ?v_352))) (and (and x_81 x_82) ?v_353)) (and (and x_86 x_87) ?v_354)) (and (and x_84 x_85) ?v_355)) (and (and x_67 x_68) ?v_356)) (and (and x_72 x_73) ?v_357)) (and (and x_70 x_71) ?v_358)) (and (and x_53 x_54) ?v_359)) (and (and x_58 x_59) ?v_360)) (and (and x_56 x_57) ?v_361)) (and (and x_39 x_40) ?v_362)) (and (and x_44 x_45) ?v_363)) (and (and x_42 x_43) ?v_364)) (and (and x_25 x_26) ?v_365)) (and (and x_30 x_31) ?v_366)) (and (and x_28 x_29) ?v_367)) (and (and x_11 x_12) ?v_368)) (and (and x_16 x_17) ?v_369)) (and (and x_14 x_15) ?v_370)) (and (and x_0 x_1) ?v_371)) (and (and x_2 x_3) ?v_372)) (and (and x_4 x_5) ?v_373))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
(exit)
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
(declare-fun x_108 () Real)
(declare-fun x_109 () Bool)
(declare-fun x_110 () Bool)
(declare-fun x_111 () Real)
(declare-fun x_112 () Bool)
(declare-fun x_113 () Bool)
(declare-fun x_114 () Bool)
(declare-fun x_115 () Bool)
(declare-fun x_116 () Real)
(declare-fun x_117 () Real)
(declare-fun x_118 () Real)
(declare-fun x_119 () Real)
(declare-fun x_120 () Real)
(declare-fun x_121 () Real)
(assert (let ((?v_25 (not x_109)) (?v_26 (not x_110))) (let ((?v_27 (and ?v_25 ?v_26)) (?v_63 (not x_112)) (?v_64 (not x_113))) (let ((?v_65 (and ?v_63 ?v_64)) (?v_48 (not x_114)) (?v_49 (not x_115))) (let ((?v_51 (and ?v_48 ?v_49)) (?v_30 (and (= x_112 x_98) (= x_113 x_99))) (?v_60 (not x_98)) (?v_58 (not x_99))) (let ((?v_55 (and ?v_60 ?v_58)) (?v_19 (and (= x_109 x_95) (= x_110 x_96))) (?v_44 (not x_100)) (?v_41 (not x_101))) (let ((?v_36 (and ?v_44 ?v_41)) (?v_61 (and ?v_60 x_99)) (?v_28 (and (= x_114 x_100) (= x_115 x_101))) (?v_46 (and ?v_44 x_101)) (?v_22 (not x_95)) (?v_20 (not x_96))) (let ((?v_15 (and ?v_22 ?v_20)) (?v_23 (and ?v_22 x_96)) (?v_84 (and (= x_98 x_84) (= x_99 x_85))) (?v_110 (not x_84)) (?v_108 (not x_85))) (let ((?v_105 (and ?v_110 ?v_108)) (?v_76 (and (= x_95 x_81) (= x_96 x_82))) (?v_98 (not x_86)) (?v_95 (not x_87))) (let ((?v_90 (and ?v_98 ?v_95)) (?v_111 (and ?v_110 x_85)) (?v_82 (and (= x_100 x_86) (= x_101 x_87))) (?v_100 (and ?v_98 x_87)) (?v_79 (not x_81)) (?v_77 (not x_82))) (let ((?v_72 (and ?v_79 ?v_77)) (?v_80 (and ?v_79 x_82)) (?v_131 (and (= x_84 x_70) (= x_85 x_71))) (?v_157 (not x_70)) (?v_155 (not x_71))) (let ((?v_152 (and ?v_157 ?v_155)) (?v_123 (and (= x_81 x_67) (= x_82 x_68))) (?v_145 (not x_72)) (?v_142 (not x_73))) (let ((?v_137 (and ?v_145 ?v_142)) (?v_158 (and ?v_157 x_71)) (?v_129 (and (= x_86 x_72) (= x_87 x_73))) (?v_147 (and ?v_145 x_73)) (?v_126 (not x_67)) (?v_124 (not x_68))) (let ((?v_119 (and ?v_126 ?v_124)) (?v_127 (and ?v_126 x_68)) (?v_178 (and (= x_70 x_56) (= x_71 x_57))) (?v_204 (not x_56)) (?v_202 (not x_57))) (let ((?v_199 (and ?v_204 ?v_202)) (?v_170 (and (= x_67 x_53) (= x_68 x_54))) (?v_192 (not x_58)) (?v_189 (not x_59))) (let ((?v_184 (and ?v_192 ?v_189)) (?v_205 (and ?v_204 x_57)) (?v_176 (and (= x_72 x_58) (= x_73 x_59))) (?v_194 (and ?v_192 x_59)) (?v_173 (not x_53)) (?v_171 (not x_54))) (let ((?v_166 (and ?v_173 ?v_171)) (?v_174 (and ?v_173 x_54)) (?v_225 (and (= x_56 x_42) (= x_57 x_43))) (?v_251 (not x_42)) (?v_249 (not x_43))) (let ((?v_246 (and ?v_251 ?v_249)) (?v_217 (and (= x_53 x_39) (= x_54 x_40))) (?v_239 (not x_44)) (?v_236 (not x_45))) (let ((?v_231 (and ?v_239 ?v_236)) (?v_252 (and ?v_251 x_43)) (?v_223 (and (= x_58 x_44) (= x_59 x_45))) (?v_241 (and ?v_239 x_45)) (?v_220 (not x_39)) (?v_218 (not x_40))) (let ((?v_213 (and ?v_220 ?v_218)) (?v_221 (and ?v_220 x_40)) (?v_272 (and (= x_42 x_28) (= x_43 x_29))) (?v_298 (not x_28)) (?v_296 (not x_29))) (let ((?v_293 (and ?v_298 ?v_296)) (?v_264 (and (= x_39 x_25) (= x_40 x_26))) (?v_286 (not x_30)) (?v_283 (not x_31))) (let ((?v_278 (and ?v_286 ?v_283)) (?v_299 (and ?v_298 x_29)) (?v_270 (and (= x_44 x_30) (= x_45 x_31))) (?v_288 (and ?v_286 x_31)) (?v_267 (not x_25)) (?v_265 (not x_26))) (let ((?v_260 (and ?v_267 ?v_265)) (?v_268 (and ?v_267 x_26)) (?v_319 (and (= x_28 x_14) (= x_29 x_15))) (?v_345 (not x_14)) (?v_343 (not x_15))) (let ((?v_340 (and ?v_345 ?v_343)) (?v_311 (and (= x_25 x_11) (= x_26 x_12))) (?v_333 (not x_16)) (?v_330 (not x_17))) (let ((?v_325 (and ?v_333 ?v_330)) (?v_346 (and ?v_345 x_15)) (?v_317 (and (= x_30 x_16) (= x_31 x_17))) (?v_335 (and ?v_333 x_17)) (?v_314 (not x_11)) (?v_312 (not x_12))) (let ((?v_307 (and ?v_314 ?v_312)) (?v_315 (and ?v_314 x_12)) (?v_369 (and (= x_14 x_4) (= x_15 x_5))) (?v_395 (not x_4)) (?v_393 (not x_5))) (let ((?v_389 (and ?v_395 ?v_393)) (?v_361 (and (= x_11 x_0) (= x_12 x_1))) (?v_383 (not x_2)) (?v_380 (not x_3))) (let ((?v_373 (and ?v_383 ?v_380)) (?v_396 (and ?v_395 x_5)) (?v_367 (and (= x_16 x_2) (= x_17 x_3))) (?v_385 (and ?v_383 x_3)) (?v_364 (not x_0)) (?v_362 (not x_1))) (let ((?v_354 (and ?v_364 ?v_362)) (?v_365 (and ?v_364 x_1)) (?v_355 (- cvclZero x_6))) (let ((?v_351 (< ?v_355 0)) (?v_374 (- cvclZero x_7))) (let ((?v_350 (< ?v_374 0)) (?v_390 (- cvclZero x_8))) (let ((?v_349 (< ?v_390 0)) (?v_0 (- x_9 cvclZero))) (let ((?v_356 (= ?v_0 0)) (?v_9 (< (- x_102 x_103) 0))) (let ((?v_10 (ite ?v_9 (< (- x_102 x_104) 0) (< (- x_103 x_104) 0))) (?v_53 (= (- x_118 x_104) 0)) (?v_29 (= (- x_117 x_103) 0)) (?v_31 (= (- x_116 x_102) 0)) (?v_13 (= (- x_111 x_97) 0)) (?v_14 (- x_108 cvclZero))) (let ((?v_33 (= ?v_14 0)) (?v_12 (- x_106 x_104))) (let ((?v_16 (= ?v_12 0)) (?v_7 (- x_97 cvclZero))) (let ((?v_17 (= ?v_7 0)) (?v_21 (- x_106 x_118))) (let ((?v_18 (< ?v_21 0)) (?v_35 (= ?v_14 1)) (?v_38 (not ?v_17)) (?v_40 (= ?v_14 2)) (?v_8 (- x_111 cvclZero))) (let ((?v_398 (= ?v_8 1)) (?v_43 (= ?v_14 3)) (?v_24 (= ?v_7 1)) (?v_45 (= ?v_14 4))) (let ((?v_401 (not ?v_24)) (?v_50 (= ?v_14 5)) (?v_52 (= ?v_8 0)) (?v_34 (- x_106 x_103))) (let ((?v_37 (= ?v_34 0)) (?v_42 (- x_106 x_117))) (let ((?v_39 (< ?v_42 0)) (?v_399 (= ?v_8 2)) (?v_47 (= ?v_7 2))) (let ((?v_402 (not ?v_47)) (?v_54 (- x_106 x_102))) (let ((?v_56 (= ?v_54 0)) (?v_59 (- x_106 x_116))) (let ((?v_57 (< ?v_59 0)) (?v_400 (= ?v_8 3)) (?v_62 (= ?v_7 3))) (let ((?v_403 (not ?v_62)) (?v_66 (< (- x_88 x_89) 0))) (let ((?v_67 (ite ?v_66 (< (- x_88 x_90) 0) (< (- x_89 x_90) 0))) (?v_103 (= (- x_104 x_90) 0)) (?v_83 (= (- x_103 x_89) 0)) (?v_85 (= (- x_102 x_88) 0)) (?v_70 (= (- x_97 x_83) 0)) (?v_71 (- x_94 cvclZero))) (let ((?v_87 (= ?v_71 0)) (?v_69 (- x_92 x_90))) (let ((?v_73 (= ?v_69 0)) (?v_6 (- x_83 cvclZero))) (let ((?v_74 (= ?v_6 0)) (?v_78 (- x_92 x_104))) (let ((?v_75 (< ?v_78 0)) (?v_89 (= ?v_71 1)) (?v_92 (not ?v_74)) (?v_94 (= ?v_71 2)) (?v_97 (= ?v_71 3)) (?v_81 (= ?v_6 1)) (?v_99 (= ?v_71 4))) (let ((?v_404 (not ?v_81)) (?v_102 (= ?v_71 5)) (?v_88 (- x_92 x_89))) (let ((?v_91 (= ?v_88 0)) (?v_96 (- x_92 x_103))) (let ((?v_93 (< ?v_96 0)) (?v_101 (= ?v_6 2))) (let ((?v_405 (not ?v_101)) (?v_104 (- x_92 x_88))) (let ((?v_106 (= ?v_104 0)) (?v_109 (- x_92 x_102))) (let ((?v_107 (< ?v_109 0)) (?v_112 (= ?v_6 3))) (let ((?v_406 (not ?v_112)) (?v_113 (< (- x_74 x_75) 0))) (let ((?v_114 (ite ?v_113 (< (- x_74 x_76) 0) (< (- x_75 x_76) 0))) (?v_150 (= (- x_90 x_76) 0)) (?v_130 (= (- x_89 x_75) 0)) (?v_132 (= (- x_88 x_74) 0)) (?v_117 (= (- x_83 x_69) 0)) (?v_118 (- x_80 cvclZero))) (let ((?v_134 (= ?v_118 0)) (?v_116 (- x_78 x_76))) (let ((?v_120 (= ?v_116 0)) (?v_5 (- x_69 cvclZero))) (let ((?v_121 (= ?v_5 0)) (?v_125 (- x_78 x_90))) (let ((?v_122 (< ?v_125 0)) (?v_136 (= ?v_118 1)) (?v_139 (not ?v_121)) (?v_141 (= ?v_118 2)) (?v_144 (= ?v_118 3)) (?v_128 (= ?v_5 1)) (?v_146 (= ?v_118 4))) (let ((?v_407 (not ?v_128)) (?v_149 (= ?v_118 5)) (?v_135 (- x_78 x_75))) (let ((?v_138 (= ?v_135 0)) (?v_143 (- x_78 x_89))) (let ((?v_140 (< ?v_143 0)) (?v_148 (= ?v_5 2))) (let ((?v_408 (not ?v_148)) (?v_151 (- x_78 x_74))) (let ((?v_153 (= ?v_151 0)) (?v_156 (- x_78 x_88))) (let ((?v_154 (< ?v_156 0)) (?v_159 (= ?v_5 3))) (let ((?v_409 (not ?v_159)) (?v_160 (< (- x_60 x_61) 0))) (let ((?v_161 (ite ?v_160 (< (- x_60 x_62) 0) (< (- x_61 x_62) 0))) (?v_197 (= (- x_76 x_62) 0)) (?v_177 (= (- x_75 x_61) 0)) (?v_179 (= (- x_74 x_60) 0)) (?v_164 (= (- x_69 x_55) 0)) (?v_165 (- x_66 cvclZero))) (let ((?v_181 (= ?v_165 0)) (?v_163 (- x_64 x_62))) (let ((?v_167 (= ?v_163 0)) (?v_4 (- x_55 cvclZero))) (let ((?v_168 (= ?v_4 0)) (?v_172 (- x_64 x_76))) (let ((?v_169 (< ?v_172 0)) (?v_183 (= ?v_165 1)) (?v_186 (not ?v_168)) (?v_188 (= ?v_165 2)) (?v_191 (= ?v_165 3)) (?v_175 (= ?v_4 1)) (?v_193 (= ?v_165 4))) (let ((?v_410 (not ?v_175)) (?v_196 (= ?v_165 5)) (?v_182 (- x_64 x_61))) (let ((?v_185 (= ?v_182 0)) (?v_190 (- x_64 x_75))) (let ((?v_187 (< ?v_190 0)) (?v_195 (= ?v_4 2))) (let ((?v_411 (not ?v_195)) (?v_198 (- x_64 x_60))) (let ((?v_200 (= ?v_198 0)) (?v_203 (- x_64 x_74))) (let ((?v_201 (< ?v_203 0)) (?v_206 (= ?v_4 3))) (let ((?v_412 (not ?v_206)) (?v_207 (< (- x_46 x_47) 0))) (let ((?v_208 (ite ?v_207 (< (- x_46 x_48) 0) (< (- x_47 x_48) 0))) (?v_244 (= (- x_62 x_48) 0)) (?v_224 (= (- x_61 x_47) 0)) (?v_226 (= (- x_60 x_46) 0)) (?v_211 (= (- x_55 x_41) 0)) (?v_212 (- x_52 cvclZero))) (let ((?v_228 (= ?v_212 0)) (?v_210 (- x_50 x_48))) (let ((?v_214 (= ?v_210 0)) (?v_3 (- x_41 cvclZero))) (let ((?v_215 (= ?v_3 0)) (?v_219 (- x_50 x_62))) (let ((?v_216 (< ?v_219 0)) (?v_230 (= ?v_212 1)) (?v_233 (not ?v_215)) (?v_235 (= ?v_212 2)) (?v_238 (= ?v_212 3)) (?v_222 (= ?v_3 1)) (?v_240 (= ?v_212 4))) (let ((?v_413 (not ?v_222)) (?v_243 (= ?v_212 5)) (?v_229 (- x_50 x_47))) (let ((?v_232 (= ?v_229 0)) (?v_237 (- x_50 x_61))) (let ((?v_234 (< ?v_237 0)) (?v_242 (= ?v_3 2))) (let ((?v_414 (not ?v_242)) (?v_245 (- x_50 x_46))) (let ((?v_247 (= ?v_245 0)) (?v_250 (- x_50 x_60))) (let ((?v_248 (< ?v_250 0)) (?v_253 (= ?v_3 3))) (let ((?v_415 (not ?v_253)) (?v_254 (< (- x_32 x_33) 0))) (let ((?v_255 (ite ?v_254 (< (- x_32 x_34) 0) (< (- x_33 x_34) 0))) (?v_291 (= (- x_48 x_34) 0)) (?v_271 (= (- x_47 x_33) 0)) (?v_273 (= (- x_46 x_32) 0)) (?v_258 (= (- x_41 x_27) 0)) (?v_259 (- x_38 cvclZero))) (let ((?v_275 (= ?v_259 0)) (?v_257 (- x_36 x_34))) (let ((?v_261 (= ?v_257 0)) (?v_2 (- x_27 cvclZero))) (let ((?v_262 (= ?v_2 0)) (?v_266 (- x_36 x_48))) (let ((?v_263 (< ?v_266 0)) (?v_277 (= ?v_259 1)) (?v_280 (not ?v_262)) (?v_282 (= ?v_259 2)) (?v_285 (= ?v_259 3)) (?v_269 (= ?v_2 1)) (?v_287 (= ?v_259 4))) (let ((?v_416 (not ?v_269)) (?v_290 (= ?v_259 5)) (?v_276 (- x_36 x_33))) (let ((?v_279 (= ?v_276 0)) (?v_284 (- x_36 x_47))) (let ((?v_281 (< ?v_284 0)) (?v_289 (= ?v_2 2))) (let ((?v_417 (not ?v_289)) (?v_292 (- x_36 x_32))) (let ((?v_294 (= ?v_292 0)) (?v_297 (- x_36 x_46))) (let ((?v_295 (< ?v_297 0)) (?v_300 (= ?v_2 3))) (let ((?v_418 (not ?v_300)) (?v_301 (< (- x_18 x_19) 0))) (let ((?v_302 (ite ?v_301 (< (- x_18 x_20) 0) (< (- x_19 x_20) 0))) (?v_338 (= (- x_34 x_20) 0)) (?v_318 (= (- x_33 x_19) 0)) (?v_320 (= (- x_32 x_18) 0)) (?v_305 (= (- x_27 x_13) 0)) (?v_306 (- x_24 cvclZero))) (let ((?v_322 (= ?v_306 0)) (?v_304 (- x_22 x_20))) (let ((?v_308 (= ?v_304 0)) (?v_1 (- x_13 cvclZero))) (let ((?v_309 (= ?v_1 0)) (?v_313 (- x_22 x_34))) (let ((?v_310 (< ?v_313 0)) (?v_324 (= ?v_306 1)) (?v_327 (not ?v_309)) (?v_329 (= ?v_306 2)) (?v_332 (= ?v_306 3)) (?v_316 (= ?v_1 1)) (?v_334 (= ?v_306 4))) (let ((?v_419 (not ?v_316)) (?v_337 (= ?v_306 5)) (?v_323 (- x_22 x_19))) (let ((?v_326 (= ?v_323 0)) (?v_331 (- x_22 x_33))) (let ((?v_328 (< ?v_331 0)) (?v_336 (= ?v_1 2))) (let ((?v_420 (not ?v_336)) (?v_339 (- x_22 x_18))) (let ((?v_341 (= ?v_339 0)) (?v_344 (- x_22 x_32))) (let ((?v_342 (< ?v_344 0)) (?v_347 (= ?v_1 3))) (let ((?v_421 (not ?v_347)) (?v_348 (< (- x_8 x_7) 0))) (let ((?v_352 (ite ?v_348 (< (- x_8 x_6) 0) (< (- x_7 x_6) 0))) (?v_388 (= (- x_20 x_6) 0)) (?v_368 (= (- x_19 x_7) 0)) (?v_370 (= (- x_18 x_8) 0)) (?v_357 (= (- x_13 x_9) 0)) (?v_358 (- x_10 cvclZero))) (let ((?v_372 (= ?v_358 0)) (?v_359 (= ?v_355 0)) (?v_363 (- cvclZero x_20))) (let ((?v_360 (< ?v_363 0)) (?v_375 (= ?v_358 1)) (?v_377 (not ?v_356)) (?v_379 (= ?v_358 2)) (?v_382 (= ?v_358 3)) (?v_366 (= ?v_0 1)) (?v_384 (= ?v_358 4))) (let ((?v_422 (not ?v_366)) (?v_387 (= ?v_358 5)) (?v_376 (= ?v_374 0)) (?v_381 (- cvclZero x_19))) (let ((?v_378 (< ?v_381 0)) (?v_386 (= ?v_0 2))) (let ((?v_423 (not ?v_386)) (?v_391 (= ?v_390 0)) (?v_394 (- cvclZero x_18))) (let ((?v_392 (< ?v_394 0)) (?v_397 (= ?v_0 3))) (let ((?v_424 (not ?v_397)) (?v_11 (- x_119 cvclZero)) (?v_32 (- x_121 cvclZero)) (?v_68 (- x_105 cvclZero)) (?v_86 (- x_107 cvclZero)) (?v_115 (- x_91 cvclZero)) (?v_133 (- x_93 cvclZero)) (?v_162 (- x_77 cvclZero)) (?v_180 (- x_79 cvclZero)) (?v_209 (- x_63 cvclZero)) (?v_227 (- x_65 cvclZero)) (?v_256 (- x_49 cvclZero)) (?v_274 (- x_51 cvclZero)) (?v_303 (- x_35 cvclZero)) (?v_321 (- x_37 cvclZero)) (?v_353 (- x_21 cvclZero)) (?v_371 (- x_23 cvclZero))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (not (< ?v_0 0)) (<= ?v_0 3)) (not (< ?v_1 0))) (<= ?v_1 3)) (not (< ?v_2 0))) (<= ?v_2 3)) (not (< ?v_3 0))) (<= ?v_3 3)) (not (< ?v_4 0))) (<= ?v_4 3)) (not (< ?v_5 0))) (<= ?v_5 3)) (not (< ?v_6 0))) (<= ?v_6 3)) (not (< ?v_7 0))) (<= ?v_7 3)) (not (< ?v_8 0))) (<= ?v_8 3)) ?v_354) ?v_373) ?v_389) ?v_351) ?v_350) ?v_349) ?v_356) (or (and (and (and (and (and (and (and (and (and (= ?v_11 0) (ite ?v_10 (ite ?v_9 (< ?v_54 0) (< ?v_34 0)) (< ?v_12 0))) (ite ?v_10 (ite ?v_9 (= (- x_120 x_102) 0) (= (- x_120 x_103) 0)) (= (- x_120 x_104) 0))) ?v_19) ?v_28) ?v_30) ?v_53) ?v_29) ?v_31) ?v_13) (and (and (= ?v_11 1) (or (or (and (and (and (and (and (= ?v_32 1) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_33 ?v_15) ?v_16) ?v_17) x_109) ?v_26) ?v_18) (<= (- x_118 x_106) 2)) ?v_13) (and (and (and (and (and (and ?v_35 ?v_15) ?v_16) ?v_38) ?v_18) ?v_13) ?v_19)) (and (and (and (and (and (and (and ?v_40 x_95) ?v_20) ?v_16) ?v_25) x_110) ?v_398) (<= ?v_21 (- 4)))) (and (and (and (and (and (and (and ?v_43 ?v_23) ?v_16) ?v_24) x_109) x_110) ?v_18) ?v_13)) (and (and (and (and (and (and ?v_45 ?v_23) ?v_16) ?v_401) ?v_27) ?v_18) ?v_13)) (and (and (and (and (and (and ?v_50 x_95) x_96) ?v_16) ?v_27) ?v_52) ?v_18))) ?v_28) ?v_29) ?v_30) ?v_31) (and (and (and (and (and (= ?v_32 2) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_33 ?v_36) ?v_37) ?v_17) x_114) ?v_49) ?v_39) (<= (- x_117 x_106) 2)) ?v_13) (and (and (and (and (and (and ?v_35 ?v_36) ?v_37) ?v_38) ?v_39) ?v_13) ?v_28)) (and (and (and (and (and (and (and ?v_40 x_100) ?v_41) ?v_37) ?v_48) x_115) ?v_399) (<= ?v_42 (- 4)))) (and (and (and (and (and (and (and ?v_43 ?v_46) ?v_37) ?v_47) x_114) x_115) ?v_39) ?v_13)) (and (and (and (and (and (and ?v_45 ?v_46) ?v_37) ?v_402) ?v_51) ?v_39) ?v_13)) (and (and (and (and (and (and ?v_50 x_100) x_101) ?v_37) ?v_51) ?v_52) ?v_39))) ?v_19) ?v_53) ?v_30) ?v_31)) (and (and (and (and (and (= ?v_32 3) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_33 ?v_55) ?v_56) ?v_17) x_112) ?v_64) ?v_57) (<= (- x_116 x_106) 2)) ?v_13) (and (and (and (and (and (and ?v_35 ?v_55) ?v_56) ?v_38) ?v_57) ?v_13) ?v_30)) (and (and (and (and (and (and (and ?v_40 x_98) ?v_58) ?v_56) ?v_63) x_113) ?v_400) (<= ?v_59 (- 4)))) (and (and (and (and (and (and (and ?v_43 ?v_61) ?v_56) ?v_62) x_112) x_113) ?v_57) ?v_13)) (and (and (and (and (and (and ?v_45 ?v_61) ?v_56) ?v_403) ?v_65) ?v_57) ?v_13)) (and (and (and (and (and (and ?v_50 x_98) x_99) ?v_56) ?v_65) ?v_52) ?v_57))) ?v_19) ?v_53) ?v_28) ?v_29))) (= (- x_120 x_106) 0)))) (or (and (and (and (and (and (and (and (and (and (= ?v_68 0) (ite ?v_67 (ite ?v_66 (< ?v_104 0) (< ?v_88 0)) (< ?v_69 0))) (ite ?v_67 (ite ?v_66 (= (- x_106 x_88) 0) (= (- x_106 x_89) 0)) (= (- x_106 x_90) 0))) ?v_76) ?v_82) ?v_84) ?v_103) ?v_83) ?v_85) ?v_70) (and (and (= ?v_68 1) (or (or (and (and (and (and (and (= ?v_86 1) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_87 ?v_72) ?v_73) ?v_74) x_95) ?v_20) ?v_75) (<= (- x_104 x_92) 2)) ?v_70) (and (and (and (and (and (and ?v_89 ?v_72) ?v_73) ?v_92) ?v_75) ?v_70) ?v_76)) (and (and (and (and (and (and (and ?v_94 x_81) ?v_77) ?v_73) ?v_22) x_96) ?v_24) (<= ?v_78 (- 4)))) (and (and (and (and (and (and (and ?v_97 ?v_80) ?v_73) ?v_81) x_95) x_96) ?v_75) ?v_70)) (and (and (and (and (and (and ?v_99 ?v_80) ?v_73) ?v_404) ?v_15) ?v_75) ?v_70)) (and (and (and (and (and (and ?v_102 x_81) x_82) ?v_73) ?v_15) ?v_17) ?v_75))) ?v_82) ?v_83) ?v_84) ?v_85) (and (and (and (and (and (= ?v_86 2) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_87 ?v_90) ?v_91) ?v_74) x_100) ?v_41) ?v_93) (<= (- x_103 x_92) 2)) ?v_70) (and (and (and (and (and (and ?v_89 ?v_90) ?v_91) ?v_92) ?v_93) ?v_70) ?v_82)) (and (and (and (and (and (and (and ?v_94 x_86) ?v_95) ?v_91) ?v_44) x_101) ?v_47) (<= ?v_96 (- 4)))) (and (and (and (and (and (and (and ?v_97 ?v_100) ?v_91) ?v_101) x_100) x_101) ?v_93) ?v_70)) (and (and (and (and (and (and ?v_99 ?v_100) ?v_91) ?v_405) ?v_36) ?v_93) ?v_70)) (and (and (and (and (and (and ?v_102 x_86) x_87) ?v_91) ?v_36) ?v_17) ?v_93))) ?v_76) ?v_103) ?v_84) ?v_85)) (and (and (and (and (and (= ?v_86 3) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_87 ?v_105) ?v_106) ?v_74) x_98) ?v_58) ?v_107) (<= (- x_102 x_92) 2)) ?v_70) (and (and (and (and (and (and ?v_89 ?v_105) ?v_106) ?v_92) ?v_107) ?v_70) ?v_84)) (and (and (and (and (and (and (and ?v_94 x_84) ?v_108) ?v_106) ?v_60) x_99) ?v_62) (<= ?v_109 (- 4)))) (and (and (and (and (and (and (and ?v_97 ?v_111) ?v_106) ?v_112) x_98) x_99) ?v_107) ?v_70)) (and (and (and (and (and (and ?v_99 ?v_111) ?v_106) ?v_406) ?v_55) ?v_107) ?v_70)) (and (and (and (and (and (and ?v_102 x_84) x_85) ?v_106) ?v_55) ?v_17) ?v_107))) ?v_76) ?v_103) ?v_82) ?v_83))) (= (- x_106 x_92) 0)))) (or (and (and (and (and (and (and (and (and (and (= ?v_115 0) (ite ?v_114 (ite ?v_113 (< ?v_151 0) (< ?v_135 0)) (< ?v_116 0))) (ite ?v_114 (ite ?v_113 (= (- x_92 x_74) 0) (= (- x_92 x_75) 0)) (= (- x_92 x_76) 0))) ?v_123) ?v_129) ?v_131) ?v_150) ?v_130) ?v_132) ?v_117) (and (and (= ?v_115 1) (or (or (and (and (and (and (and (= ?v_133 1) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_134 ?v_119) ?v_120) ?v_121) x_81) ?v_77) ?v_122) (<= (- x_90 x_78) 2)) ?v_117) (and (and (and (and (and (and ?v_136 ?v_119) ?v_120) ?v_139) ?v_122) ?v_117) ?v_123)) (and (and (and (and (and (and (and ?v_141 x_67) ?v_124) ?v_120) ?v_79) x_82) ?v_81) (<= ?v_125 (- 4)))) (and (and (and (and (and (and (and ?v_144 ?v_127) ?v_120) ?v_128) x_81) x_82) ?v_122) ?v_117)) (and (and (and (and (and (and ?v_146 ?v_127) ?v_120) ?v_407) ?v_72) ?v_122) ?v_117)) (and (and (and (and (and (and ?v_149 x_67) x_68) ?v_120) ?v_72) ?v_74) ?v_122))) ?v_129) ?v_130) ?v_131) ?v_132) (and (and (and (and (and (= ?v_133 2) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_134 ?v_137) ?v_138) ?v_121) x_86) ?v_95) ?v_140) (<= (- x_89 x_78) 2)) ?v_117) (and (and (and (and (and (and ?v_136 ?v_137) ?v_138) ?v_139) ?v_140) ?v_117) ?v_129)) (and (and (and (and (and (and (and ?v_141 x_72) ?v_142) ?v_138) ?v_98) x_87) ?v_101) (<= ?v_143 (- 4)))) (and (and (and (and (and (and (and ?v_144 ?v_147) ?v_138) ?v_148) x_86) x_87) ?v_140) ?v_117)) (and (and (and (and (and (and ?v_146 ?v_147) ?v_138) ?v_408) ?v_90) ?v_140) ?v_117)) (and (and (and (and (and (and ?v_149 x_72) x_73) ?v_138) ?v_90) ?v_74) ?v_140))) ?v_123) ?v_150) ?v_131) ?v_132)) (and (and (and (and (and (= ?v_133 3) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_134 ?v_152) ?v_153) ?v_121) x_84) ?v_108) ?v_154) (<= (- x_88 x_78) 2)) ?v_117) (and (and (and (and (and (and ?v_136 ?v_152) ?v_153) ?v_139) ?v_154) ?v_117) ?v_131)) (and (and (and (and (and (and (and ?v_141 x_70) ?v_155) ?v_153) ?v_110) x_85) ?v_112) (<= ?v_156 (- 4)))) (and (and (and (and (and (and (and ?v_144 ?v_158) ?v_153) ?v_159) x_84) x_85) ?v_154) ?v_117)) (and (and (and (and (and (and ?v_146 ?v_158) ?v_153) ?v_409) ?v_105) ?v_154) ?v_117)) (and (and (and (and (and (and ?v_149 x_70) x_71) ?v_153) ?v_105) ?v_74) ?v_154))) ?v_123) ?v_150) ?v_129) ?v_130))) (= (- x_92 x_78) 0)))) (or (and (and (and (and (and (and (and (and (and (= ?v_162 0) (ite ?v_161 (ite ?v_160 (< ?v_198 0) (< ?v_182 0)) (< ?v_163 0))) (ite ?v_161 (ite ?v_160 (= (- x_78 x_60) 0) (= (- x_78 x_61) 0)) (= (- x_78 x_62) 0))) ?v_170) ?v_176) ?v_178) ?v_197) ?v_177) ?v_179) ?v_164) (and (and (= ?v_162 1) (or (or (and (and (and (and (and (= ?v_180 1) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_181 ?v_166) ?v_167) ?v_168) x_67) ?v_124) ?v_169) (<= (- x_76 x_64) 2)) ?v_164) (and (and (and (and (and (and ?v_183 ?v_166) ?v_167) ?v_186) ?v_169) ?v_164) ?v_170)) (and (and (and (and (and (and (and ?v_188 x_53) ?v_171) ?v_167) ?v_126) x_68) ?v_128) (<= ?v_172 (- 4)))) (and (and (and (and (and (and (and ?v_191 ?v_174) ?v_167) ?v_175) x_67) x_68) ?v_169) ?v_164)) (and (and (and (and (and (and ?v_193 ?v_174) ?v_167) ?v_410) ?v_119) ?v_169) ?v_164)) (and (and (and (and (and (and ?v_196 x_53) x_54) ?v_167) ?v_119) ?v_121) ?v_169))) ?v_176) ?v_177) ?v_178) ?v_179) (and (and (and (and (and (= ?v_180 2) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_181 ?v_184) ?v_185) ?v_168) x_72) ?v_142) ?v_187) (<= (- x_75 x_64) 2)) ?v_164) (and (and (and (and (and (and ?v_183 ?v_184) ?v_185) ?v_186) ?v_187) ?v_164) ?v_176)) (and (and (and (and (and (and (and ?v_188 x_58) ?v_189) ?v_185) ?v_145) x_73) ?v_148) (<= ?v_190 (- 4)))) (and (and (and (and (and (and (and ?v_191 ?v_194) ?v_185) ?v_195) x_72) x_73) ?v_187) ?v_164)) (and (and (and (and (and (and ?v_193 ?v_194) ?v_185) ?v_411) ?v_137) ?v_187) ?v_164)) (and (and (and (and (and (and ?v_196 x_58) x_59) ?v_185) ?v_137) ?v_121) ?v_187))) ?v_170) ?v_197) ?v_178) ?v_179)) (and (and (and (and (and (= ?v_180 3) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_181 ?v_199) ?v_200) ?v_168) x_70) ?v_155) ?v_201) (<= (- x_74 x_64) 2)) ?v_164) (and (and (and (and (and (and ?v_183 ?v_199) ?v_200) ?v_186) ?v_201) ?v_164) ?v_178)) (and (and (and (and (and (and (and ?v_188 x_56) ?v_202) ?v_200) ?v_157) x_71) ?v_159) (<= ?v_203 (- 4)))) (and (and (and (and (and (and (and ?v_191 ?v_205) ?v_200) ?v_206) x_70) x_71) ?v_201) ?v_164)) (and (and (and (and (and (and ?v_193 ?v_205) ?v_200) ?v_412) ?v_152) ?v_201) ?v_164)) (and (and (and (and (and (and ?v_196 x_56) x_57) ?v_200) ?v_152) ?v_121) ?v_201))) ?v_170) ?v_197) ?v_176) ?v_177))) (= (- x_78 x_64) 0)))) (or (and (and (and (and (and (and (and (and (and (= ?v_209 0) (ite ?v_208 (ite ?v_207 (< ?v_245 0) (< ?v_229 0)) (< ?v_210 0))) (ite ?v_208 (ite ?v_207 (= (- x_64 x_46) 0) (= (- x_64 x_47) 0)) (= (- x_64 x_48) 0))) ?v_217) ?v_223) ?v_225) ?v_244) ?v_224) ?v_226) ?v_211) (and (and (= ?v_209 1) (or (or (and (and (and (and (and (= ?v_227 1) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_228 ?v_213) ?v_214) ?v_215) x_53) ?v_171) ?v_216) (<= (- x_62 x_50) 2)) ?v_211) (and (and (and (and (and (and ?v_230 ?v_213) ?v_214) ?v_233) ?v_216) ?v_211) ?v_217)) (and (and (and (and (and (and (and ?v_235 x_39) ?v_218) ?v_214) ?v_173) x_54) ?v_175) (<= ?v_219 (- 4)))) (and (and (and (and (and (and (and ?v_238 ?v_221) ?v_214) ?v_222) x_53) x_54) ?v_216) ?v_211)) (and (and (and (and (and (and ?v_240 ?v_221) ?v_214) ?v_413) ?v_166) ?v_216) ?v_211)) (and (and (and (and (and (and ?v_243 x_39) x_40) ?v_214) ?v_166) ?v_168) ?v_216))) ?v_223) ?v_224) ?v_225) ?v_226) (and (and (and (and (and (= ?v_227 2) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_228 ?v_231) ?v_232) ?v_215) x_58) ?v_189) ?v_234) (<= (- x_61 x_50) 2)) ?v_211) (and (and (and (and (and (and ?v_230 ?v_231) ?v_232) ?v_233) ?v_234) ?v_211) ?v_223)) (and (and (and (and (and (and (and ?v_235 x_44) ?v_236) ?v_232) ?v_192) x_59) ?v_195) (<= ?v_237 (- 4)))) (and (and (and (and (and (and (and ?v_238 ?v_241) ?v_232) ?v_242) x_58) x_59) ?v_234) ?v_211)) (and (and (and (and (and (and ?v_240 ?v_241) ?v_232) ?v_414) ?v_184) ?v_234) ?v_211)) (and (and (and (and (and (and ?v_243 x_44) x_45) ?v_232) ?v_184) ?v_168) ?v_234))) ?v_217) ?v_244) ?v_225) ?v_226)) (and (and (and (and (and (= ?v_227 3) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_228 ?v_246) ?v_247) ?v_215) x_56) ?v_202) ?v_248) (<= (- x_60 x_50) 2)) ?v_211) (and (and (and (and (and (and ?v_230 ?v_246) ?v_247) ?v_233) ?v_248) ?v_211) ?v_225)) (and (and (and (and (and (and (and ?v_235 x_42) ?v_249) ?v_247) ?v_204) x_57) ?v_206) (<= ?v_250 (- 4)))) (and (and (and (and (and (and (and ?v_238 ?v_252) ?v_247) ?v_253) x_56) x_57) ?v_248) ?v_211)) (and (and (and (and (and (and ?v_240 ?v_252) ?v_247) ?v_415) ?v_199) ?v_248) ?v_211)) (and (and (and (and (and (and ?v_243 x_42) x_43) ?v_247) ?v_199) ?v_168) ?v_248))) ?v_217) ?v_244) ?v_223) ?v_224))) (= (- x_64 x_50) 0)))) (or (and (and (and (and (and (and (and (and (and (= ?v_256 0) (ite ?v_255 (ite ?v_254 (< ?v_292 0) (< ?v_276 0)) (< ?v_257 0))) (ite ?v_255 (ite ?v_254 (= (- x_50 x_32) 0) (= (- x_50 x_33) 0)) (= (- x_50 x_34) 0))) ?v_264) ?v_270) ?v_272) ?v_291) ?v_271) ?v_273) ?v_258) (and (and (= ?v_256 1) (or (or (and (and (and (and (and (= ?v_274 1) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_275 ?v_260) ?v_261) ?v_262) x_39) ?v_218) ?v_263) (<= (- x_48 x_36) 2)) ?v_258) (and (and (and (and (and (and ?v_277 ?v_260) ?v_261) ?v_280) ?v_263) ?v_258) ?v_264)) (and (and (and (and (and (and (and ?v_282 x_25) ?v_265) ?v_261) ?v_220) x_40) ?v_222) (<= ?v_266 (- 4)))) (and (and (and (and (and (and (and ?v_285 ?v_268) ?v_261) ?v_269) x_39) x_40) ?v_263) ?v_258)) (and (and (and (and (and (and ?v_287 ?v_268) ?v_261) ?v_416) ?v_213) ?v_263) ?v_258)) (and (and (and (and (and (and ?v_290 x_25) x_26) ?v_261) ?v_213) ?v_215) ?v_263))) ?v_270) ?v_271) ?v_272) ?v_273) (and (and (and (and (and (= ?v_274 2) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_275 ?v_278) ?v_279) ?v_262) x_44) ?v_236) ?v_281) (<= (- x_47 x_36) 2)) ?v_258) (and (and (and (and (and (and ?v_277 ?v_278) ?v_279) ?v_280) ?v_281) ?v_258) ?v_270)) (and (and (and (and (and (and (and ?v_282 x_30) ?v_283) ?v_279) ?v_239) x_45) ?v_242) (<= ?v_284 (- 4)))) (and (and (and (and (and (and (and ?v_285 ?v_288) ?v_279) ?v_289) x_44) x_45) ?v_281) ?v_258)) (and (and (and (and (and (and ?v_287 ?v_288) ?v_279) ?v_417) ?v_231) ?v_281) ?v_258)) (and (and (and (and (and (and ?v_290 x_30) x_31) ?v_279) ?v_231) ?v_215) ?v_281))) ?v_264) ?v_291) ?v_272) ?v_273)) (and (and (and (and (and (= ?v_274 3) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_275 ?v_293) ?v_294) ?v_262) x_42) ?v_249) ?v_295) (<= (- x_46 x_36) 2)) ?v_258) (and (and (and (and (and (and ?v_277 ?v_293) ?v_294) ?v_280) ?v_295) ?v_258) ?v_272)) (and (and (and (and (and (and (and ?v_282 x_28) ?v_296) ?v_294) ?v_251) x_43) ?v_253) (<= ?v_297 (- 4)))) (and (and (and (and (and (and (and ?v_285 ?v_299) ?v_294) ?v_300) x_42) x_43) ?v_295) ?v_258)) (and (and (and (and (and (and ?v_287 ?v_299) ?v_294) ?v_418) ?v_246) ?v_295) ?v_258)) (and (and (and (and (and (and ?v_290 x_28) x_29) ?v_294) ?v_246) ?v_215) ?v_295))) ?v_264) ?v_291) ?v_270) ?v_271))) (= (- x_50 x_36) 0)))) (or (and (and (and (and (and (and (and (and (and (= ?v_303 0) (ite ?v_302 (ite ?v_301 (< ?v_339 0) (< ?v_323 0)) (< ?v_304 0))) (ite ?v_302 (ite ?v_301 (= (- x_36 x_18) 0) (= (- x_36 x_19) 0)) (= (- x_36 x_20) 0))) ?v_311) ?v_317) ?v_319) ?v_338) ?v_318) ?v_320) ?v_305) (and (and (= ?v_303 1) (or (or (and (and (and (and (and (= ?v_321 1) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_322 ?v_307) ?v_308) ?v_309) x_25) ?v_265) ?v_310) (<= (- x_34 x_22) 2)) ?v_305) (and (and (and (and (and (and ?v_324 ?v_307) ?v_308) ?v_327) ?v_310) ?v_305) ?v_311)) (and (and (and (and (and (and (and ?v_329 x_11) ?v_312) ?v_308) ?v_267) x_26) ?v_269) (<= ?v_313 (- 4)))) (and (and (and (and (and (and (and ?v_332 ?v_315) ?v_308) ?v_316) x_25) x_26) ?v_310) ?v_305)) (and (and (and (and (and (and ?v_334 ?v_315) ?v_308) ?v_419) ?v_260) ?v_310) ?v_305)) (and (and (and (and (and (and ?v_337 x_11) x_12) ?v_308) ?v_260) ?v_262) ?v_310))) ?v_317) ?v_318) ?v_319) ?v_320) (and (and (and (and (and (= ?v_321 2) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_322 ?v_325) ?v_326) ?v_309) x_30) ?v_283) ?v_328) (<= (- x_33 x_22) 2)) ?v_305) (and (and (and (and (and (and ?v_324 ?v_325) ?v_326) ?v_327) ?v_328) ?v_305) ?v_317)) (and (and (and (and (and (and (and ?v_329 x_16) ?v_330) ?v_326) ?v_286) x_31) ?v_289) (<= ?v_331 (- 4)))) (and (and (and (and (and (and (and ?v_332 ?v_335) ?v_326) ?v_336) x_30) x_31) ?v_328) ?v_305)) (and (and (and (and (and (and ?v_334 ?v_335) ?v_326) ?v_420) ?v_278) ?v_328) ?v_305)) (and (and (and (and (and (and ?v_337 x_16) x_17) ?v_326) ?v_278) ?v_262) ?v_328))) ?v_311) ?v_338) ?v_319) ?v_320)) (and (and (and (and (and (= ?v_321 3) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_322 ?v_340) ?v_341) ?v_309) x_28) ?v_296) ?v_342) (<= (- x_32 x_22) 2)) ?v_305) (and (and (and (and (and (and ?v_324 ?v_340) ?v_341) ?v_327) ?v_342) ?v_305) ?v_319)) (and (and (and (and (and (and (and ?v_329 x_14) ?v_343) ?v_341) ?v_298) x_29) ?v_300) (<= ?v_344 (- 4)))) (and (and (and (and (and (and (and ?v_332 ?v_346) ?v_341) ?v_347) x_28) x_29) ?v_342) ?v_305)) (and (and (and (and (and (and ?v_334 ?v_346) ?v_341) ?v_421) ?v_293) ?v_342) ?v_305)) (and (and (and (and (and (and ?v_337 x_14) x_15) ?v_341) ?v_293) ?v_262) ?v_342))) ?v_311) ?v_338) ?v_317) ?v_318))) (= (- x_36 x_22) 0)))) (or (and (and (and (and (and (and (and (and (and (= ?v_353 0) (ite ?v_352 (ite ?v_348 ?v_349 ?v_350) ?v_351)) (ite ?v_352 (ite ?v_348 (= (- x_22 x_8) 0) (= (- x_22 x_7) 0)) (= (- x_22 x_6) 0))) ?v_361) ?v_367) ?v_369) ?v_388) ?v_368) ?v_370) ?v_357) (and (and (= ?v_353 1) (or (or (and (and (and (and (and (= ?v_371 1) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_372 ?v_354) ?v_359) ?v_356) x_11) ?v_312) ?v_360) (<= (- x_20 cvclZero) 2)) ?v_357) (and (and (and (and (and (and ?v_375 ?v_354) ?v_359) ?v_377) ?v_360) ?v_357) ?v_361)) (and (and (and (and (and (and (and ?v_379 x_0) ?v_362) ?v_359) ?v_314) x_12) ?v_316) (<= ?v_363 (- 4)))) (and (and (and (and (and (and (and ?v_382 ?v_365) ?v_359) ?v_366) x_11) x_12) ?v_360) ?v_357)) (and (and (and (and (and (and ?v_384 ?v_365) ?v_359) ?v_422) ?v_307) ?v_360) ?v_357)) (and (and (and (and (and (and ?v_387 x_0) x_1) ?v_359) ?v_307) ?v_309) ?v_360))) ?v_367) ?v_368) ?v_369) ?v_370) (and (and (and (and (and (= ?v_371 2) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_372 ?v_373) ?v_376) ?v_356) x_16) ?v_330) ?v_378) (<= (- x_19 cvclZero) 2)) ?v_357) (and (and (and (and (and (and ?v_375 ?v_373) ?v_376) ?v_377) ?v_378) ?v_357) ?v_367)) (and (and (and (and (and (and (and ?v_379 x_2) ?v_380) ?v_376) ?v_333) x_17) ?v_336) (<= ?v_381 (- 4)))) (and (and (and (and (and (and (and ?v_382 ?v_385) ?v_376) ?v_386) x_16) x_17) ?v_378) ?v_357)) (and (and (and (and (and (and ?v_384 ?v_385) ?v_376) ?v_423) ?v_325) ?v_378) ?v_357)) (and (and (and (and (and (and ?v_387 x_2) x_3) ?v_376) ?v_325) ?v_309) ?v_378))) ?v_361) ?v_388) ?v_369) ?v_370)) (and (and (and (and (and (= ?v_371 3) (or (or (or (or (or (and (and (and (and (and (and (and (and ?v_372 ?v_389) ?v_391) ?v_356) x_14) ?v_343) ?v_392) (<= (- x_18 cvclZero) 2)) ?v_357) (and (and (and (and (and (and ?v_375 ?v_389) ?v_391) ?v_377) ?v_392) ?v_357) ?v_369)) (and (and (and (and (and (and (and ?v_379 x_4) ?v_393) ?v_391) ?v_345) x_15) ?v_347) (<= ?v_394 (- 4)))) (and (and (and (and (and (and (and ?v_382 ?v_396) ?v_391) ?v_397) x_14) x_15) ?v_392) ?v_357)) (and (and (and (and (and (and ?v_384 ?v_396) ?v_391) ?v_424) ?v_340) ?v_392) ?v_357)) (and (and (and (and (and (and ?v_387 x_4) x_5) ?v_391) ?v_340) ?v_309) ?v_392))) ?v_361) ?v_388) ?v_367) ?v_368))) (= (- x_22 cvclZero) 0)))) (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (and (and x_109 x_110) (not ?v_398)) (and (and x_114 x_115) (not ?v_399))) (and (and x_112 x_113) (not ?v_400))) (and (and x_95 x_96) ?v_401)) (and (and x_100 x_101) ?v_402)) (and (and x_98 x_99) ?v_403)) (and (and x_81 x_82) ?v_404)) (and (and x_86 x_87) ?v_405)) (and (and x_84 x_85) ?v_406)) (and (and x_67 x_68) ?v_407)) (and (and x_72 x_73) ?v_408)) (and (and x_70 x_71) ?v_409)) (and (and x_53 x_54) ?v_410)) (and (and x_58 x_59) ?v_411)) (and (and x_56 x_57) ?v_412)) (and (and x_39 x_40) ?v_413)) (and (and x_44 x_45) ?v_414)) (and (and x_42 x_43) ?v_415)) (and (and x_25 x_26) ?v_416)) (and (and x_30 x_31) ?v_417)) (and (and x_28 x_29) ?v_418)) (and (and x_11 x_12) ?v_419)) (and (and x_16 x_17) ?v_420)) (and (and x_14 x_15) ?v_421)) (and (and x_0 x_1) ?v_422)) (and (and x_2 x_3) ?v_423)) (and (and x_4 x_5) ?v_424)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
(exit)

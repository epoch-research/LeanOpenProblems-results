import Submission.Bounds

set_option maxHeartbeats 20000000

lemma no_sol_chunk_0 (k m : ℕ) (hk1 : 0 ≤ k) (hk2 : k < 50) (hm : m ≥ 1) :
  k = 16 ∧ m = 1119 ∨ my_pi (k*(k+1)) + my_pi (m*(m+1)/2) ≠ 51156 := by
  interval_cases k
  · right; exact no_sol_k_0 m hm
  · right; exact no_sol_k_1 m hm
  · right; exact no_sol_k_2 m hm
  · right; exact no_sol_k_3 m hm
  · right; exact no_sol_k_4 m hm
  · right; exact no_sol_k_5 m hm
  · right; exact no_sol_k_6 m hm
  · right; exact no_sol_k_7 m hm
  · right; exact no_sol_k_8 m hm
  · right; exact no_sol_k_9 m hm
  · right; exact no_sol_k_10 m hm
  · right; exact no_sol_k_11 m hm
  · right; exact no_sol_k_12 m hm
  · right; exact no_sol_k_13 m hm
  · right; exact no_sol_k_14 m hm
  · right; exact no_sol_k_15 m hm
  · by_cases h_m : m = 1119
    · left; exact ⟨rfl, h_m⟩
    · right; exact no_sol_k_16 m h_m hm
  · right; exact no_sol_k_17 m hm
  · right; exact no_sol_k_18 m hm
  · right; exact no_sol_k_19 m hm
  · right; exact no_sol_k_20 m hm
  · right; exact no_sol_k_21 m hm
  · right; exact no_sol_k_22 m hm
  · right; exact no_sol_k_23 m hm
  · right; exact no_sol_k_24 m hm
  · right; exact no_sol_k_25 m hm
  · right; exact no_sol_k_26 m hm
  · right; exact no_sol_k_27 m hm
  · right; exact no_sol_k_28 m hm
  · right; exact no_sol_k_29 m hm
  · right; exact no_sol_k_30 m hm
  · right; exact no_sol_k_31 m hm
  · right; exact no_sol_k_32 m hm
  · right; exact no_sol_k_33 m hm
  · right; exact no_sol_k_34 m hm
  · right; exact no_sol_k_35 m hm
  · right; exact no_sol_k_36 m hm
  · right; exact no_sol_k_37 m hm
  · right; exact no_sol_k_38 m hm
  · right; exact no_sol_k_39 m hm
  · right; exact no_sol_k_40 m hm
  · right; exact no_sol_k_41 m hm
  · right; exact no_sol_k_42 m hm
  · right; exact no_sol_k_43 m hm
  · right; exact no_sol_k_44 m hm
  · right; exact no_sol_k_45 m hm
  · right; exact no_sol_k_46 m hm
  · right; exact no_sol_k_47 m hm
  · right; exact no_sol_k_48 m hm
  · right; exact no_sol_k_49 m hm

lemma no_sol_chunk_50 (k m : ℕ) (hk1 : 50 ≤ k) (hk2 : k < 100) (hm : m ≥ 1) :
  k = 16 ∧ m = 1119 ∨ my_pi (k*(k+1)) + my_pi (m*(m+1)/2) ≠ 51156 := by
  interval_cases k
  · right; exact no_sol_k_50 m hm
  · right; exact no_sol_k_51 m hm
  · right; exact no_sol_k_52 m hm
  · right; exact no_sol_k_53 m hm
  · right; exact no_sol_k_54 m hm
  · right; exact no_sol_k_55 m hm
  · right; exact no_sol_k_56 m hm
  · right; exact no_sol_k_57 m hm
  · right; exact no_sol_k_58 m hm
  · right; exact no_sol_k_59 m hm
  · right; exact no_sol_k_60 m hm
  · right; exact no_sol_k_61 m hm
  · right; exact no_sol_k_62 m hm
  · right; exact no_sol_k_63 m hm
  · right; exact no_sol_k_64 m hm
  · right; exact no_sol_k_65 m hm
  · right; exact no_sol_k_66 m hm
  · right; exact no_sol_k_67 m hm
  · right; exact no_sol_k_68 m hm
  · right; exact no_sol_k_69 m hm
  · right; exact no_sol_k_70 m hm
  · right; exact no_sol_k_71 m hm
  · right; exact no_sol_k_72 m hm
  · right; exact no_sol_k_73 m hm
  · right; exact no_sol_k_74 m hm
  · right; exact no_sol_k_75 m hm
  · right; exact no_sol_k_76 m hm
  · right; exact no_sol_k_77 m hm
  · right; exact no_sol_k_78 m hm
  · right; exact no_sol_k_79 m hm
  · right; exact no_sol_k_80 m hm
  · right; exact no_sol_k_81 m hm
  · right; exact no_sol_k_82 m hm
  · right; exact no_sol_k_83 m hm
  · right; exact no_sol_k_84 m hm
  · right; exact no_sol_k_85 m hm
  · right; exact no_sol_k_86 m hm
  · right; exact no_sol_k_87 m hm
  · right; exact no_sol_k_88 m hm
  · right; exact no_sol_k_89 m hm
  · right; exact no_sol_k_90 m hm
  · right; exact no_sol_k_91 m hm
  · right; exact no_sol_k_92 m hm
  · right; exact no_sol_k_93 m hm
  · right; exact no_sol_k_94 m hm
  · right; exact no_sol_k_95 m hm
  · right; exact no_sol_k_96 m hm
  · right; exact no_sol_k_97 m hm
  · right; exact no_sol_k_98 m hm
  · right; exact no_sol_k_99 m hm

lemma no_sol_chunk_100 (k m : ℕ) (hk1 : 100 ≤ k) (hk2 : k < 150) (hm : m ≥ 1) :
  k = 16 ∧ m = 1119 ∨ my_pi (k*(k+1)) + my_pi (m*(m+1)/2) ≠ 51156 := by
  interval_cases k
  · right; exact no_sol_k_100 m hm
  · right; exact no_sol_k_101 m hm
  · right; exact no_sol_k_102 m hm
  · right; exact no_sol_k_103 m hm
  · right; exact no_sol_k_104 m hm
  · right; exact no_sol_k_105 m hm
  · right; exact no_sol_k_106 m hm
  · right; exact no_sol_k_107 m hm
  · right; exact no_sol_k_108 m hm
  · right; exact no_sol_k_109 m hm
  · right; exact no_sol_k_110 m hm
  · right; exact no_sol_k_111 m hm
  · right; exact no_sol_k_112 m hm
  · right; exact no_sol_k_113 m hm
  · right; exact no_sol_k_114 m hm
  · right; exact no_sol_k_115 m hm
  · right; exact no_sol_k_116 m hm
  · right; exact no_sol_k_117 m hm
  · right; exact no_sol_k_118 m hm
  · right; exact no_sol_k_119 m hm
  · right; exact no_sol_k_120 m hm
  · right; exact no_sol_k_121 m hm
  · right; exact no_sol_k_122 m hm
  · right; exact no_sol_k_123 m hm
  · right; exact no_sol_k_124 m hm
  · right; exact no_sol_k_125 m hm
  · right; exact no_sol_k_126 m hm
  · right; exact no_sol_k_127 m hm
  · right; exact no_sol_k_128 m hm
  · right; exact no_sol_k_129 m hm
  · right; exact no_sol_k_130 m hm
  · right; exact no_sol_k_131 m hm
  · right; exact no_sol_k_132 m hm
  · right; exact no_sol_k_133 m hm
  · right; exact no_sol_k_134 m hm
  · right; exact no_sol_k_135 m hm
  · right; exact no_sol_k_136 m hm
  · right; exact no_sol_k_137 m hm
  · right; exact no_sol_k_138 m hm
  · right; exact no_sol_k_139 m hm
  · right; exact no_sol_k_140 m hm
  · right; exact no_sol_k_141 m hm
  · right; exact no_sol_k_142 m hm
  · right; exact no_sol_k_143 m hm
  · right; exact no_sol_k_144 m hm
  · right; exact no_sol_k_145 m hm
  · right; exact no_sol_k_146 m hm
  · right; exact no_sol_k_147 m hm
  · right; exact no_sol_k_148 m hm
  · right; exact no_sol_k_149 m hm

lemma no_sol_chunk_150 (k m : ℕ) (hk1 : 150 ≤ k) (hk2 : k < 200) (hm : m ≥ 1) :
  k = 16 ∧ m = 1119 ∨ my_pi (k*(k+1)) + my_pi (m*(m+1)/2) ≠ 51156 := by
  interval_cases k
  · right; exact no_sol_k_150 m hm
  · right; exact no_sol_k_151 m hm
  · right; exact no_sol_k_152 m hm
  · right; exact no_sol_k_153 m hm
  · right; exact no_sol_k_154 m hm
  · right; exact no_sol_k_155 m hm
  · right; exact no_sol_k_156 m hm
  · right; exact no_sol_k_157 m hm
  · right; exact no_sol_k_158 m hm
  · right; exact no_sol_k_159 m hm
  · right; exact no_sol_k_160 m hm
  · right; exact no_sol_k_161 m hm
  · right; exact no_sol_k_162 m hm
  · right; exact no_sol_k_163 m hm
  · right; exact no_sol_k_164 m hm
  · right; exact no_sol_k_165 m hm
  · right; exact no_sol_k_166 m hm
  · right; exact no_sol_k_167 m hm
  · right; exact no_sol_k_168 m hm
  · right; exact no_sol_k_169 m hm
  · right; exact no_sol_k_170 m hm
  · right; exact no_sol_k_171 m hm
  · right; exact no_sol_k_172 m hm
  · right; exact no_sol_k_173 m hm
  · right; exact no_sol_k_174 m hm
  · right; exact no_sol_k_175 m hm
  · right; exact no_sol_k_176 m hm
  · right; exact no_sol_k_177 m hm
  · right; exact no_sol_k_178 m hm
  · right; exact no_sol_k_179 m hm
  · right; exact no_sol_k_180 m hm
  · right; exact no_sol_k_181 m hm
  · right; exact no_sol_k_182 m hm
  · right; exact no_sol_k_183 m hm
  · right; exact no_sol_k_184 m hm
  · right; exact no_sol_k_185 m hm
  · right; exact no_sol_k_186 m hm
  · right; exact no_sol_k_187 m hm
  · right; exact no_sol_k_188 m hm
  · right; exact no_sol_k_189 m hm
  · right; exact no_sol_k_190 m hm
  · right; exact no_sol_k_191 m hm
  · right; exact no_sol_k_192 m hm
  · right; exact no_sol_k_193 m hm
  · right; exact no_sol_k_194 m hm
  · right; exact no_sol_k_195 m hm
  · right; exact no_sol_k_196 m hm
  · right; exact no_sol_k_197 m hm
  · right; exact no_sol_k_198 m hm
  · right; exact no_sol_k_199 m hm

lemma no_sol_chunk_200 (k m : ℕ) (hk1 : 200 ≤ k) (hk2 : k < 250) (hm : m ≥ 1) :
  k = 16 ∧ m = 1119 ∨ my_pi (k*(k+1)) + my_pi (m*(m+1)/2) ≠ 51156 := by
  interval_cases k
  · right; exact no_sol_k_200 m hm
  · right; exact no_sol_k_201 m hm
  · right; exact no_sol_k_202 m hm
  · right; exact no_sol_k_203 m hm
  · right; exact no_sol_k_204 m hm
  · right; exact no_sol_k_205 m hm
  · right; exact no_sol_k_206 m hm
  · right; exact no_sol_k_207 m hm
  · right; exact no_sol_k_208 m hm
  · right; exact no_sol_k_209 m hm
  · right; exact no_sol_k_210 m hm
  · right; exact no_sol_k_211 m hm
  · right; exact no_sol_k_212 m hm
  · right; exact no_sol_k_213 m hm
  · right; exact no_sol_k_214 m hm
  · right; exact no_sol_k_215 m hm
  · right; exact no_sol_k_216 m hm
  · right; exact no_sol_k_217 m hm
  · right; exact no_sol_k_218 m hm
  · right; exact no_sol_k_219 m hm
  · right; exact no_sol_k_220 m hm
  · right; exact no_sol_k_221 m hm
  · right; exact no_sol_k_222 m hm
  · right; exact no_sol_k_223 m hm
  · right; exact no_sol_k_224 m hm
  · right; exact no_sol_k_225 m hm
  · right; exact no_sol_k_226 m hm
  · right; exact no_sol_k_227 m hm
  · right; exact no_sol_k_228 m hm
  · right; exact no_sol_k_229 m hm
  · right; exact no_sol_k_230 m hm
  · right; exact no_sol_k_231 m hm
  · right; exact no_sol_k_232 m hm
  · right; exact no_sol_k_233 m hm
  · right; exact no_sol_k_234 m hm
  · right; exact no_sol_k_235 m hm
  · right; exact no_sol_k_236 m hm
  · right; exact no_sol_k_237 m hm
  · right; exact no_sol_k_238 m hm
  · right; exact no_sol_k_239 m hm
  · right; exact no_sol_k_240 m hm
  · right; exact no_sol_k_241 m hm
  · right; exact no_sol_k_242 m hm
  · right; exact no_sol_k_243 m hm
  · right; exact no_sol_k_244 m hm
  · right; exact no_sol_k_245 m hm
  · right; exact no_sol_k_246 m hm
  · right; exact no_sol_k_247 m hm
  · right; exact no_sol_k_248 m hm
  · right; exact no_sol_k_249 m hm

lemma no_sol_chunk_250 (k m : ℕ) (hk1 : 250 ≤ k) (hk2 : k < 300) (hm : m ≥ 1) :
  k = 16 ∧ m = 1119 ∨ my_pi (k*(k+1)) + my_pi (m*(m+1)/2) ≠ 51156 := by
  interval_cases k
  · right; exact no_sol_k_250 m hm
  · right; exact no_sol_k_251 m hm
  · right; exact no_sol_k_252 m hm
  · right; exact no_sol_k_253 m hm
  · right; exact no_sol_k_254 m hm
  · right; exact no_sol_k_255 m hm
  · right; exact no_sol_k_256 m hm
  · right; exact no_sol_k_257 m hm
  · right; exact no_sol_k_258 m hm
  · right; exact no_sol_k_259 m hm
  · right; exact no_sol_k_260 m hm
  · right; exact no_sol_k_261 m hm
  · right; exact no_sol_k_262 m hm
  · right; exact no_sol_k_263 m hm
  · right; exact no_sol_k_264 m hm
  · right; exact no_sol_k_265 m hm
  · right; exact no_sol_k_266 m hm
  · right; exact no_sol_k_267 m hm
  · right; exact no_sol_k_268 m hm
  · right; exact no_sol_k_269 m hm
  · right; exact no_sol_k_270 m hm
  · right; exact no_sol_k_271 m hm
  · right; exact no_sol_k_272 m hm
  · right; exact no_sol_k_273 m hm
  · right; exact no_sol_k_274 m hm
  · right; exact no_sol_k_275 m hm
  · right; exact no_sol_k_276 m hm
  · right; exact no_sol_k_277 m hm
  · right; exact no_sol_k_278 m hm
  · right; exact no_sol_k_279 m hm
  · right; exact no_sol_k_280 m hm
  · right; exact no_sol_k_281 m hm
  · right; exact no_sol_k_282 m hm
  · right; exact no_sol_k_283 m hm
  · right; exact no_sol_k_284 m hm
  · right; exact no_sol_k_285 m hm
  · right; exact no_sol_k_286 m hm
  · right; exact no_sol_k_287 m hm
  · right; exact no_sol_k_288 m hm
  · right; exact no_sol_k_289 m hm
  · right; exact no_sol_k_290 m hm
  · right; exact no_sol_k_291 m hm
  · right; exact no_sol_k_292 m hm
  · right; exact no_sol_k_293 m hm
  · right; exact no_sol_k_294 m hm
  · right; exact no_sol_k_295 m hm
  · right; exact no_sol_k_296 m hm
  · right; exact no_sol_k_297 m hm
  · right; exact no_sol_k_298 m hm
  · right; exact no_sol_k_299 m hm

lemma no_sol_chunk_300 (k m : ℕ) (hk1 : 300 ≤ k) (hk2 : k < 350) (hm : m ≥ 1) :
  k = 16 ∧ m = 1119 ∨ my_pi (k*(k+1)) + my_pi (m*(m+1)/2) ≠ 51156 := by
  interval_cases k
  · right; exact no_sol_k_300 m hm
  · right; exact no_sol_k_301 m hm
  · right; exact no_sol_k_302 m hm
  · right; exact no_sol_k_303 m hm
  · right; exact no_sol_k_304 m hm
  · right; exact no_sol_k_305 m hm
  · right; exact no_sol_k_306 m hm
  · right; exact no_sol_k_307 m hm
  · right; exact no_sol_k_308 m hm
  · right; exact no_sol_k_309 m hm
  · right; exact no_sol_k_310 m hm
  · right; exact no_sol_k_311 m hm
  · right; exact no_sol_k_312 m hm
  · right; exact no_sol_k_313 m hm
  · right; exact no_sol_k_314 m hm
  · right; exact no_sol_k_315 m hm
  · right; exact no_sol_k_316 m hm
  · right; exact no_sol_k_317 m hm
  · right; exact no_sol_k_318 m hm
  · right; exact no_sol_k_319 m hm
  · right; exact no_sol_k_320 m hm
  · right; exact no_sol_k_321 m hm
  · right; exact no_sol_k_322 m hm
  · right; exact no_sol_k_323 m hm
  · right; exact no_sol_k_324 m hm
  · right; exact no_sol_k_325 m hm
  · right; exact no_sol_k_326 m hm
  · right; exact no_sol_k_327 m hm
  · right; exact no_sol_k_328 m hm
  · right; exact no_sol_k_329 m hm
  · right; exact no_sol_k_330 m hm
  · right; exact no_sol_k_331 m hm
  · right; exact no_sol_k_332 m hm
  · right; exact no_sol_k_333 m hm
  · right; exact no_sol_k_334 m hm
  · right; exact no_sol_k_335 m hm
  · right; exact no_sol_k_336 m hm
  · right; exact no_sol_k_337 m hm
  · right; exact no_sol_k_338 m hm
  · right; exact no_sol_k_339 m hm
  · right; exact no_sol_k_340 m hm
  · right; exact no_sol_k_341 m hm
  · right; exact no_sol_k_342 m hm
  · right; exact no_sol_k_343 m hm
  · right; exact no_sol_k_344 m hm
  · right; exact no_sol_k_345 m hm
  · right; exact no_sol_k_346 m hm
  · right; exact no_sol_k_347 m hm
  · right; exact no_sol_k_348 m hm
  · right; exact no_sol_k_349 m hm

lemma no_sol_chunk_350 (k m : ℕ) (hk1 : 350 ≤ k) (hk2 : k < 400) (hm : m ≥ 1) :
  k = 16 ∧ m = 1119 ∨ my_pi (k*(k+1)) + my_pi (m*(m+1)/2) ≠ 51156 := by
  interval_cases k
  · right; exact no_sol_k_350 m hm
  · right; exact no_sol_k_351 m hm
  · right; exact no_sol_k_352 m hm
  · right; exact no_sol_k_353 m hm
  · right; exact no_sol_k_354 m hm
  · right; exact no_sol_k_355 m hm
  · right; exact no_sol_k_356 m hm
  · right; exact no_sol_k_357 m hm
  · right; exact no_sol_k_358 m hm
  · right; exact no_sol_k_359 m hm
  · right; exact no_sol_k_360 m hm
  · right; exact no_sol_k_361 m hm
  · right; exact no_sol_k_362 m hm
  · right; exact no_sol_k_363 m hm
  · right; exact no_sol_k_364 m hm
  · right; exact no_sol_k_365 m hm
  · right; exact no_sol_k_366 m hm
  · right; exact no_sol_k_367 m hm
  · right; exact no_sol_k_368 m hm
  · right; exact no_sol_k_369 m hm
  · right; exact no_sol_k_370 m hm
  · right; exact no_sol_k_371 m hm
  · right; exact no_sol_k_372 m hm
  · right; exact no_sol_k_373 m hm
  · right; exact no_sol_k_374 m hm
  · right; exact no_sol_k_375 m hm
  · right; exact no_sol_k_376 m hm
  · right; exact no_sol_k_377 m hm
  · right; exact no_sol_k_378 m hm
  · right; exact no_sol_k_379 m hm
  · right; exact no_sol_k_380 m hm
  · right; exact no_sol_k_381 m hm
  · right; exact no_sol_k_382 m hm
  · right; exact no_sol_k_383 m hm
  · right; exact no_sol_k_384 m hm
  · right; exact no_sol_k_385 m hm
  · right; exact no_sol_k_386 m hm
  · right; exact no_sol_k_387 m hm
  · right; exact no_sol_k_388 m hm
  · right; exact no_sol_k_389 m hm
  · right; exact no_sol_k_390 m hm
  · right; exact no_sol_k_391 m hm
  · right; exact no_sol_k_392 m hm
  · right; exact no_sol_k_393 m hm
  · right; exact no_sol_k_394 m hm
  · right; exact no_sol_k_395 m hm
  · right; exact no_sol_k_396 m hm
  · right; exact no_sol_k_397 m hm
  · right; exact no_sol_k_398 m hm
  · right; exact no_sol_k_399 m hm

lemma no_sol_chunk_400 (k m : ℕ) (hk1 : 400 ≤ k) (hk2 : k < 450) (hm : m ≥ 1) :
  k = 16 ∧ m = 1119 ∨ my_pi (k*(k+1)) + my_pi (m*(m+1)/2) ≠ 51156 := by
  interval_cases k
  · right; exact no_sol_k_400 m hm
  · right; exact no_sol_k_401 m hm
  · right; exact no_sol_k_402 m hm
  · right; exact no_sol_k_403 m hm
  · right; exact no_sol_k_404 m hm
  · right; exact no_sol_k_405 m hm
  · right; exact no_sol_k_406 m hm
  · right; exact no_sol_k_407 m hm
  · right; exact no_sol_k_408 m hm
  · right; exact no_sol_k_409 m hm
  · right; exact no_sol_k_410 m hm
  · right; exact no_sol_k_411 m hm
  · right; exact no_sol_k_412 m hm
  · right; exact no_sol_k_413 m hm
  · right; exact no_sol_k_414 m hm
  · right; exact no_sol_k_415 m hm
  · right; exact no_sol_k_416 m hm
  · right; exact no_sol_k_417 m hm
  · right; exact no_sol_k_418 m hm
  · right; exact no_sol_k_419 m hm
  · right; exact no_sol_k_420 m hm
  · right; exact no_sol_k_421 m hm
  · right; exact no_sol_k_422 m hm
  · right; exact no_sol_k_423 m hm
  · right; exact no_sol_k_424 m hm
  · right; exact no_sol_k_425 m hm
  · right; exact no_sol_k_426 m hm
  · right; exact no_sol_k_427 m hm
  · right; exact no_sol_k_428 m hm
  · right; exact no_sol_k_429 m hm
  · right; exact no_sol_k_430 m hm
  · right; exact no_sol_k_431 m hm
  · right; exact no_sol_k_432 m hm
  · right; exact no_sol_k_433 m hm
  · right; exact no_sol_k_434 m hm
  · right; exact no_sol_k_435 m hm
  · right; exact no_sol_k_436 m hm
  · right; exact no_sol_k_437 m hm
  · right; exact no_sol_k_438 m hm
  · right; exact no_sol_k_439 m hm
  · right; exact no_sol_k_440 m hm
  · right; exact no_sol_k_441 m hm
  · right; exact no_sol_k_442 m hm
  · right; exact no_sol_k_443 m hm
  · right; exact no_sol_k_444 m hm
  · right; exact no_sol_k_445 m hm
  · right; exact no_sol_k_446 m hm
  · right; exact no_sol_k_447 m hm
  · right; exact no_sol_k_448 m hm
  · right; exact no_sol_k_449 m hm

lemma no_sol_chunk_450 (k m : ℕ) (hk1 : 450 ≤ k) (hk2 : k < 500) (hm : m ≥ 1) :
  k = 16 ∧ m = 1119 ∨ my_pi (k*(k+1)) + my_pi (m*(m+1)/2) ≠ 51156 := by
  interval_cases k
  · right; exact no_sol_k_450 m hm
  · right; exact no_sol_k_451 m hm
  · right; exact no_sol_k_452 m hm
  · right; exact no_sol_k_453 m hm
  · right; exact no_sol_k_454 m hm
  · right; exact no_sol_k_455 m hm
  · right; exact no_sol_k_456 m hm
  · right; exact no_sol_k_457 m hm
  · right; exact no_sol_k_458 m hm
  · right; exact no_sol_k_459 m hm
  · right; exact no_sol_k_460 m hm
  · right; exact no_sol_k_461 m hm
  · right; exact no_sol_k_462 m hm
  · right; exact no_sol_k_463 m hm
  · right; exact no_sol_k_464 m hm
  · right; exact no_sol_k_465 m hm
  · right; exact no_sol_k_466 m hm
  · right; exact no_sol_k_467 m hm
  · right; exact no_sol_k_468 m hm
  · right; exact no_sol_k_469 m hm
  · right; exact no_sol_k_470 m hm
  · right; exact no_sol_k_471 m hm
  · right; exact no_sol_k_472 m hm
  · right; exact no_sol_k_473 m hm
  · right; exact no_sol_k_474 m hm
  · right; exact no_sol_k_475 m hm
  · right; exact no_sol_k_476 m hm
  · right; exact no_sol_k_477 m hm
  · right; exact no_sol_k_478 m hm
  · right; exact no_sol_k_479 m hm
  · right; exact no_sol_k_480 m hm
  · right; exact no_sol_k_481 m hm
  · right; exact no_sol_k_482 m hm
  · right; exact no_sol_k_483 m hm
  · right; exact no_sol_k_484 m hm
  · right; exact no_sol_k_485 m hm
  · right; exact no_sol_k_486 m hm
  · right; exact no_sol_k_487 m hm
  · right; exact no_sol_k_488 m hm
  · right; exact no_sol_k_489 m hm
  · right; exact no_sol_k_490 m hm
  · right; exact no_sol_k_491 m hm
  · right; exact no_sol_k_492 m hm
  · right; exact no_sol_k_493 m hm
  · right; exact no_sol_k_494 m hm
  · right; exact no_sol_k_495 m hm
  · right; exact no_sol_k_496 m hm
  · right; exact no_sol_k_497 m hm
  · right; exact no_sol_k_498 m hm
  · right; exact no_sol_k_499 m hm

lemma no_sol_chunk_500 (k m : ℕ) (hk1 : 500 ≤ k) (hk2 : k < 550) (hm : m ≥ 1) :
  k = 16 ∧ m = 1119 ∨ my_pi (k*(k+1)) + my_pi (m*(m+1)/2) ≠ 51156 := by
  interval_cases k
  · right; exact no_sol_k_500 m hm
  · right; exact no_sol_k_501 m hm
  · right; exact no_sol_k_502 m hm
  · right; exact no_sol_k_503 m hm
  · right; exact no_sol_k_504 m hm
  · right; exact no_sol_k_505 m hm
  · right; exact no_sol_k_506 m hm
  · right; exact no_sol_k_507 m hm
  · right; exact no_sol_k_508 m hm
  · right; exact no_sol_k_509 m hm
  · right; exact no_sol_k_510 m hm
  · right; exact no_sol_k_511 m hm
  · right; exact no_sol_k_512 m hm
  · right; exact no_sol_k_513 m hm
  · right; exact no_sol_k_514 m hm
  · right; exact no_sol_k_515 m hm
  · right; exact no_sol_k_516 m hm
  · right; exact no_sol_k_517 m hm
  · right; exact no_sol_k_518 m hm
  · right; exact no_sol_k_519 m hm
  · right; exact no_sol_k_520 m hm
  · right; exact no_sol_k_521 m hm
  · right; exact no_sol_k_522 m hm
  · right; exact no_sol_k_523 m hm
  · right; exact no_sol_k_524 m hm
  · right; exact no_sol_k_525 m hm
  · right; exact no_sol_k_526 m hm
  · right; exact no_sol_k_527 m hm
  · right; exact no_sol_k_528 m hm
  · right; exact no_sol_k_529 m hm
  · right; exact no_sol_k_530 m hm
  · right; exact no_sol_k_531 m hm
  · right; exact no_sol_k_532 m hm
  · right; exact no_sol_k_533 m hm
  · right; exact no_sol_k_534 m hm
  · right; exact no_sol_k_535 m hm
  · right; exact no_sol_k_536 m hm
  · right; exact no_sol_k_537 m hm
  · right; exact no_sol_k_538 m hm
  · right; exact no_sol_k_539 m hm
  · right; exact no_sol_k_540 m hm
  · right; exact no_sol_k_541 m hm
  · right; exact no_sol_k_542 m hm
  · right; exact no_sol_k_543 m hm
  · right; exact no_sol_k_544 m hm
  · right; exact no_sol_k_545 m hm
  · right; exact no_sol_k_546 m hm
  · right; exact no_sol_k_547 m hm
  · right; exact no_sol_k_548 m hm
  · right; exact no_sol_k_549 m hm

lemma no_sol_chunk_550 (k m : ℕ) (hk1 : 550 ≤ k) (hk2 : k < 600) (hm : m ≥ 1) :
  k = 16 ∧ m = 1119 ∨ my_pi (k*(k+1)) + my_pi (m*(m+1)/2) ≠ 51156 := by
  interval_cases k
  · right; exact no_sol_k_550 m hm
  · right; exact no_sol_k_551 m hm
  · right; exact no_sol_k_552 m hm
  · right; exact no_sol_k_553 m hm
  · right; exact no_sol_k_554 m hm
  · right; exact no_sol_k_555 m hm
  · right; exact no_sol_k_556 m hm
  · right; exact no_sol_k_557 m hm
  · right; exact no_sol_k_558 m hm
  · right; exact no_sol_k_559 m hm
  · right; exact no_sol_k_560 m hm
  · right; exact no_sol_k_561 m hm
  · right; exact no_sol_k_562 m hm
  · right; exact no_sol_k_563 m hm
  · right; exact no_sol_k_564 m hm
  · right; exact no_sol_k_565 m hm
  · right; exact no_sol_k_566 m hm
  · right; exact no_sol_k_567 m hm
  · right; exact no_sol_k_568 m hm
  · right; exact no_sol_k_569 m hm
  · right; exact no_sol_k_570 m hm
  · right; exact no_sol_k_571 m hm
  · right; exact no_sol_k_572 m hm
  · right; exact no_sol_k_573 m hm
  · right; exact no_sol_k_574 m hm
  · right; exact no_sol_k_575 m hm
  · right; exact no_sol_k_576 m hm
  · right; exact no_sol_k_577 m hm
  · right; exact no_sol_k_578 m hm
  · right; exact no_sol_k_579 m hm
  · right; exact no_sol_k_580 m hm
  · right; exact no_sol_k_581 m hm
  · right; exact no_sol_k_582 m hm
  · right; exact no_sol_k_583 m hm
  · right; exact no_sol_k_584 m hm
  · right; exact no_sol_k_585 m hm
  · right; exact no_sol_k_586 m hm
  · right; exact no_sol_k_587 m hm
  · right; exact no_sol_k_588 m hm
  · right; exact no_sol_k_589 m hm
  · right; exact no_sol_k_590 m hm
  · right; exact no_sol_k_591 m hm
  · right; exact no_sol_k_592 m hm
  · right; exact no_sol_k_593 m hm
  · right; exact no_sol_k_594 m hm
  · right; exact no_sol_k_595 m hm
  · right; exact no_sol_k_596 m hm
  · right; exact no_sol_k_597 m hm
  · right; exact no_sol_k_598 m hm
  · right; exact no_sol_k_599 m hm

lemma no_sol_chunk_600 (k m : ℕ) (hk1 : 600 ≤ k) (hk2 : k < 650) (hm : m ≥ 1) :
  k = 16 ∧ m = 1119 ∨ my_pi (k*(k+1)) + my_pi (m*(m+1)/2) ≠ 51156 := by
  interval_cases k
  · right; exact no_sol_k_600 m hm
  · right; exact no_sol_k_601 m hm
  · right; exact no_sol_k_602 m hm
  · right; exact no_sol_k_603 m hm
  · right; exact no_sol_k_604 m hm
  · right; exact no_sol_k_605 m hm
  · right; exact no_sol_k_606 m hm
  · right; exact no_sol_k_607 m hm
  · right; exact no_sol_k_608 m hm
  · right; exact no_sol_k_609 m hm
  · right; exact no_sol_k_610 m hm
  · right; exact no_sol_k_611 m hm
  · right; exact no_sol_k_612 m hm
  · right; exact no_sol_k_613 m hm
  · right; exact no_sol_k_614 m hm
  · right; exact no_sol_k_615 m hm
  · right; exact no_sol_k_616 m hm
  · right; exact no_sol_k_617 m hm
  · right; exact no_sol_k_618 m hm
  · right; exact no_sol_k_619 m hm
  · right; exact no_sol_k_620 m hm
  · right; exact no_sol_k_621 m hm
  · right; exact no_sol_k_622 m hm
  · right; exact no_sol_k_623 m hm
  · right; exact no_sol_k_624 m hm
  · right; exact no_sol_k_625 m hm
  · right; exact no_sol_k_626 m hm
  · right; exact no_sol_k_627 m hm
  · right; exact no_sol_k_628 m hm
  · right; exact no_sol_k_629 m hm
  · right; exact no_sol_k_630 m hm
  · right; exact no_sol_k_631 m hm
  · right; exact no_sol_k_632 m hm
  · right; exact no_sol_k_633 m hm
  · right; exact no_sol_k_634 m hm
  · right; exact no_sol_k_635 m hm
  · right; exact no_sol_k_636 m hm
  · right; exact no_sol_k_637 m hm
  · right; exact no_sol_k_638 m hm
  · right; exact no_sol_k_639 m hm
  · right; exact no_sol_k_640 m hm
  · right; exact no_sol_k_641 m hm
  · right; exact no_sol_k_642 m hm
  · right; exact no_sol_k_643 m hm
  · right; exact no_sol_k_644 m hm
  · right; exact no_sol_k_645 m hm
  · right; exact no_sol_k_646 m hm
  · right; exact no_sol_k_647 m hm
  · right; exact no_sol_k_648 m hm
  · right; exact no_sol_k_649 m hm

lemma no_sol_chunk_650 (k m : ℕ) (hk1 : 650 ≤ k) (hk2 : k < 700) (hm : m ≥ 1) :
  k = 16 ∧ m = 1119 ∨ my_pi (k*(k+1)) + my_pi (m*(m+1)/2) ≠ 51156 := by
  interval_cases k
  · right; exact no_sol_k_650 m hm
  · right; exact no_sol_k_651 m hm
  · right; exact no_sol_k_652 m hm
  · right; exact no_sol_k_653 m hm
  · right; exact no_sol_k_654 m hm
  · right; exact no_sol_k_655 m hm
  · right; exact no_sol_k_656 m hm
  · right; exact no_sol_k_657 m hm
  · right; exact no_sol_k_658 m hm
  · right; exact no_sol_k_659 m hm
  · right; exact no_sol_k_660 m hm
  · right; exact no_sol_k_661 m hm
  · right; exact no_sol_k_662 m hm
  · right; exact no_sol_k_663 m hm
  · right; exact no_sol_k_664 m hm
  · right; exact no_sol_k_665 m hm
  · right; exact no_sol_k_666 m hm
  · right; exact no_sol_k_667 m hm
  · right; exact no_sol_k_668 m hm
  · right; exact no_sol_k_669 m hm
  · right; exact no_sol_k_670 m hm
  · right; exact no_sol_k_671 m hm
  · right; exact no_sol_k_672 m hm
  · right; exact no_sol_k_673 m hm
  · right; exact no_sol_k_674 m hm
  · right; exact no_sol_k_675 m hm
  · right; exact no_sol_k_676 m hm
  · right; exact no_sol_k_677 m hm
  · right; exact no_sol_k_678 m hm
  · right; exact no_sol_k_679 m hm
  · right; exact no_sol_k_680 m hm
  · right; exact no_sol_k_681 m hm
  · right; exact no_sol_k_682 m hm
  · right; exact no_sol_k_683 m hm
  · right; exact no_sol_k_684 m hm
  · right; exact no_sol_k_685 m hm
  · right; exact no_sol_k_686 m hm
  · right; exact no_sol_k_687 m hm
  · right; exact no_sol_k_688 m hm
  · right; exact no_sol_k_689 m hm
  · right; exact no_sol_k_690 m hm
  · right; exact no_sol_k_691 m hm
  · right; exact no_sol_k_692 m hm
  · right; exact no_sol_k_693 m hm
  · right; exact no_sol_k_694 m hm
  · right; exact no_sol_k_695 m hm
  · right; exact no_sol_k_696 m hm
  · right; exact no_sol_k_697 m hm
  · right; exact no_sol_k_698 m hm
  · right; exact no_sol_k_699 m hm

lemma no_sol_chunk_700 (k m : ℕ) (hk1 : 700 ≤ k) (hk2 : k < 750) (hm : m ≥ 1) :
  k = 16 ∧ m = 1119 ∨ my_pi (k*(k+1)) + my_pi (m*(m+1)/2) ≠ 51156 := by
  interval_cases k
  · right; exact no_sol_k_700 m hm
  · right; exact no_sol_k_701 m hm
  · right; exact no_sol_k_702 m hm
  · right; exact no_sol_k_703 m hm
  · right; exact no_sol_k_704 m hm
  · right; exact no_sol_k_705 m hm
  · right; exact no_sol_k_706 m hm
  · right; exact no_sol_k_707 m hm
  · right; exact no_sol_k_708 m hm
  · right; exact no_sol_k_709 m hm
  · right; exact no_sol_k_710 m hm
  · right; exact no_sol_k_711 m hm
  · right; exact no_sol_k_712 m hm
  · right; exact no_sol_k_713 m hm
  · right; exact no_sol_k_714 m hm
  · right; exact no_sol_k_715 m hm
  · right; exact no_sol_k_716 m hm
  · right; exact no_sol_k_717 m hm
  · right; exact no_sol_k_718 m hm
  · right; exact no_sol_k_719 m hm
  · right; exact no_sol_k_720 m hm
  · right; exact no_sol_k_721 m hm
  · right; exact no_sol_k_722 m hm
  · right; exact no_sol_k_723 m hm
  · right; exact no_sol_k_724 m hm
  · right; exact no_sol_k_725 m hm
  · right; exact no_sol_k_726 m hm
  · right; exact no_sol_k_727 m hm
  · right; exact no_sol_k_728 m hm
  · right; exact no_sol_k_729 m hm
  · right; exact no_sol_k_730 m hm
  · right; exact no_sol_k_731 m hm
  · right; exact no_sol_k_732 m hm
  · right; exact no_sol_k_733 m hm
  · right; exact no_sol_k_734 m hm
  · right; exact no_sol_k_735 m hm
  · right; exact no_sol_k_736 m hm
  · right; exact no_sol_k_737 m hm
  · right; exact no_sol_k_738 m hm
  · right; exact no_sol_k_739 m hm
  · right; exact no_sol_k_740 m hm
  · right; exact no_sol_k_741 m hm
  · right; exact no_sol_k_742 m hm
  · right; exact no_sol_k_743 m hm
  · right; exact no_sol_k_744 m hm
  · right; exact no_sol_k_745 m hm
  · right; exact no_sol_k_746 m hm
  · right; exact no_sol_k_747 m hm
  · right; exact no_sol_k_748 m hm
  · right; exact no_sol_k_749 m hm

lemma no_sol_chunk_750 (k m : ℕ) (hk1 : 750 ≤ k) (hk2 : k < 792) (hm : m ≥ 1) :
  k = 16 ∧ m = 1119 ∨ my_pi (k*(k+1)) + my_pi (m*(m+1)/2) ≠ 51156 := by
  interval_cases k
  · right; exact no_sol_k_750 m hm
  · right; exact no_sol_k_751 m hm
  · right; exact no_sol_k_752 m hm
  · right; exact no_sol_k_753 m hm
  · right; exact no_sol_k_754 m hm
  · right; exact no_sol_k_755 m hm
  · right; exact no_sol_k_756 m hm
  · right; exact no_sol_k_757 m hm
  · right; exact no_sol_k_758 m hm
  · right; exact no_sol_k_759 m hm
  · right; exact no_sol_k_760 m hm
  · right; exact no_sol_k_761 m hm
  · right; exact no_sol_k_762 m hm
  · right; exact no_sol_k_763 m hm
  · right; exact no_sol_k_764 m hm
  · right; exact no_sol_k_765 m hm
  · right; exact no_sol_k_766 m hm
  · right; exact no_sol_k_767 m hm
  · right; exact no_sol_k_768 m hm
  · right; exact no_sol_k_769 m hm
  · right; exact no_sol_k_770 m hm
  · right; exact no_sol_k_771 m hm
  · right; exact no_sol_k_772 m hm
  · right; exact no_sol_k_773 m hm
  · right; exact no_sol_k_774 m hm
  · right; exact no_sol_k_775 m hm
  · right; exact no_sol_k_776 m hm
  · right; exact no_sol_k_777 m hm
  · right; exact no_sol_k_778 m hm
  · right; exact no_sol_k_779 m hm
  · right; exact no_sol_k_780 m hm
  · right; exact no_sol_k_781 m hm
  · right; exact no_sol_k_782 m hm
  · right; exact no_sol_k_783 m hm
  · right; exact no_sol_k_784 m hm
  · right; exact no_sol_k_785 m hm
  · right; exact no_sol_k_786 m hm
  · right; exact no_sol_k_787 m hm
  · right; exact no_sol_k_788 m hm
  · right; exact no_sol_k_789 m hm
  · right; exact no_sol_k_790 m hm
  · right; exact no_sol_k_791 m hm

lemma no_sol_general (k m : ℕ) (hm : m ≥ 1) : k = 16 ∧ m = 1119 ∨ my_pi (k*(k+1)) + my_pi (m*(m+1)/2) ≠ 51156 := by
  rcases le_or_gt k 791 with hk | hk
  · if h_0 : k < 50 then
      have hk1 : 0 ≤ k := by omega
      exact no_sol_chunk_0 k m hk1 h_0 hm
    else if h_50 : k < 100 then
      have hk1 : 50 ≤ k := by omega
      exact no_sol_chunk_50 k m hk1 h_50 hm
    else if h_100 : k < 150 then
      have hk1 : 100 ≤ k := by omega
      exact no_sol_chunk_100 k m hk1 h_100 hm
    else if h_150 : k < 200 then
      have hk1 : 150 ≤ k := by omega
      exact no_sol_chunk_150 k m hk1 h_150 hm
    else if h_200 : k < 250 then
      have hk1 : 200 ≤ k := by omega
      exact no_sol_chunk_200 k m hk1 h_200 hm
    else if h_250 : k < 300 then
      have hk1 : 250 ≤ k := by omega
      exact no_sol_chunk_250 k m hk1 h_250 hm
    else if h_300 : k < 350 then
      have hk1 : 300 ≤ k := by omega
      exact no_sol_chunk_300 k m hk1 h_300 hm
    else if h_350 : k < 400 then
      have hk1 : 350 ≤ k := by omega
      exact no_sol_chunk_350 k m hk1 h_350 hm
    else if h_400 : k < 450 then
      have hk1 : 400 ≤ k := by omega
      exact no_sol_chunk_400 k m hk1 h_400 hm
    else if h_450 : k < 500 then
      have hk1 : 450 ≤ k := by omega
      exact no_sol_chunk_450 k m hk1 h_450 hm
    else if h_500 : k < 550 then
      have hk1 : 500 ≤ k := by omega
      exact no_sol_chunk_500 k m hk1 h_500 hm
    else if h_550 : k < 600 then
      have hk1 : 550 ≤ k := by omega
      exact no_sol_chunk_550 k m hk1 h_550 hm
    else if h_600 : k < 650 then
      have hk1 : 600 ≤ k := by omega
      exact no_sol_chunk_600 k m hk1 h_600 hm
    else if h_650 : k < 700 then
      have hk1 : 650 ≤ k := by omega
      exact no_sol_chunk_650 k m hk1 h_650 hm
    else if h_700 : k < 750 then
      have hk1 : 700 ≤ k := by omega
      exact no_sol_chunk_700 k m hk1 h_700 hm
    else 
      have hk1 : 750 ≤ k := by omega
      have h_750 : k < 792 := by omega
      exact no_sol_chunk_750 k m hk1 h_750 hm
  · right
    have hk_large : 628056 ≤ k*(k+1) := by nlinarith
    have h_pi : my_pi 628056 ≤ my_pi (k*(k+1)) := my_pi_mono hk_large
    have h_val : my_pi 628056 = 51200 := pi_628056
    omega

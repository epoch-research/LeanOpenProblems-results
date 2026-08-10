import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option linter.all false



def noDivFrom (n d : Nat) : Nat → Bool
| 0 => true
| k+1 => (n % d != 0) && noDivFrom n (d+1) k

def isPrimeOver (n : Nat) : Bool := (2 <= n) && noDivFrom n 2 100

def countSmall (s : Nat) : Nat → Nat
| 0 => 0
| k+1 => countSmall s k + if isPrimeOver (s+k) then 1 else 0

lemma countSmall_add (s a b : Nat) :
    countSmall s (a + b) = countSmall s a + countSmall (s + a) b := by
  induction b with
  | zero => simp [countSmall]
  | succ b ih =>
      rw [show a + (b + 1) = (a + b) + 1 by omega]
      simp only [countSmall]
      rw [ih]
      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma noDivFrom_of_prime_ge_aux {n : Nat} (hp : Nat.Prime n) :
    ∀ k d : Nat, 2 ≤ d → d + k < n → noDivFrom n d k = true
| 0, d, hd2, hlt => by simp [noDivFrom]
| k+1, d, hd2, hlt => by
    simp only [noDivFrom]
    have hdn : d < n := by omega
    have hnotdvd : ¬ d ∣ n := by
      intro hdvd
      rcases hp.eq_one_or_self_of_dvd d hdvd with h | h
      · omega
      · omega
    have hmod : n % d ≠ 0 := by
      intro hzero
      exact hnotdvd (Nat.dvd_of_mod_eq_zero hzero)
    have hrec : noDivFrom n (d + 1) k = true := by
      exact noDivFrom_of_prime_ge_aux hp k (d+1) (by omega) (by omega)
    simp [hmod, hrec]

lemma isPrimeOver_of_prime_ge {n : Nat} (hp : Nat.Prime n) (hge : 227 ≤ n) :
    isPrimeOver n = true := by
  have hn2 : 2 ≤ n := by omega
  have hno : noDivFrom n 2 100 = true := by
    exact noDivFrom_of_prime_ge_aux hp 100 2 (by omega) (by omega)
  simp [isPrimeOver, hn2, hno]

lemma countSmall_eq_count (s len : Nat) :
    countSmall s len = Nat.count (fun k => isPrimeOver (s + k) = true) len := by
  induction len with
  | zero => simp [countSmall]
  | succ len ih =>
      rw [Nat.count_succ]
      simp [countSmall, ih]

lemma card_primes_Ico_eq_count (s len : Nat) :
    ((Finset.Ico s (s + len)).filter Nat.Prime).card =
      Nat.count (fun k => Nat.Prime (s + k)) len := by
  induction len with
  | zero => simp
  | succ len ih =>
      rw [Nat.count_succ]
      have hle : s ≤ s + len := by omega
      have hnot : s + len ∉ Finset.Ico s (s + len) := by simp
      rw [show s + (len + 1) = (s + len).succ by omega]
      rw [Nat.Ico_succ_right_eq_insert_Ico hle]
      rw [Finset.filter_insert]

      by_cases hp : Nat.Prime (s + len)
      · simp [hp, hnot, ih]
      · simp [hp, ih]

lemma card_primes_Ico_le_countSmall (s len : Nat) (hs : 227 ≤ s) :
    ((Finset.Ico s (s + len)).filter Nat.Prime).card ≤ countSmall s len := by
  rw [card_primes_Ico_eq_count, countSmall_eq_count]
  apply Nat.count_mono_left
  intro k hk hp
  exact isPrimeOver_of_prime_ge hp (by omega)

lemma chunk_0 : countSmall 0 100 = 0 := by decide
lemma chunk_1 : countSmall 100 100 = 20 := by decide
lemma chunk_2 : countSmall 200 100 = 16 := by decide
lemma chunk_3 : countSmall 300 100 = 16 := by decide
lemma chunk_4 : countSmall 400 100 = 17 := by decide
lemma chunk_5 : countSmall 500 100 = 14 := by decide
lemma chunk_6 : countSmall 600 100 = 16 := by decide
lemma chunk_7 : countSmall 700 100 = 14 := by decide
lemma chunk_8 : countSmall 800 100 = 15 := by decide
lemma chunk_9 : countSmall 900 100 = 14 := by decide
lemma chunk_10 : countSmall 1000 100 = 16 := by decide
lemma chunk_11 : countSmall 1100 100 = 12 := by decide
lemma chunk_12 : countSmall 1200 100 = 15 := by decide
lemma chunk_13 : countSmall 1300 100 = 11 := by decide
lemma chunk_14 : countSmall 1400 100 = 17 := by decide
lemma chunk_15 : countSmall 1500 100 = 12 := by decide
lemma chunk_16 : countSmall 1600 100 = 15 := by decide
lemma chunk_17 : countSmall 1700 100 = 12 := by decide
lemma chunk_18 : countSmall 1800 100 = 12 := by decide
lemma chunk_19 : countSmall 1900 100 = 13 := by decide
lemma chunk_20 : countSmall 2000 100 = 14 := by decide
lemma chunk_21 : countSmall 2100 100 = 10 := by decide
lemma chunk_22 : countSmall 2200 100 = 15 := by decide
lemma chunk_23 : countSmall 2300 100 = 15 := by decide
lemma chunk_24 : countSmall 2400 100 = 10 := by decide
lemma chunk_25 : countSmall 2500 100 = 11 := by decide
lemma chunk_26 : countSmall 2600 100 = 15 := by decide
lemma chunk_27 : countSmall 2700 100 = 14 := by decide
lemma chunk_28 : countSmall 2800 100 = 12 := by decide
lemma chunk_29 : countSmall 2900 100 = 11 := by decide
lemma chunk_30 : countSmall 3000 100 = 12 := by decide
lemma chunk_31 : countSmall 3100 100 = 10 := by decide
lemma chunk_32 : countSmall 3200 100 = 11 := by decide
lemma chunk_33 : countSmall 3300 100 = 15 := by decide
lemma chunk_34 : countSmall 3400 100 = 11 := by decide
lemma chunk_35 : countSmall 3500 100 = 14 := by decide
lemma chunk_36 : countSmall 3600 100 = 13 := by decide
lemma chunk_37 : countSmall 3700 100 = 12 := by decide
lemma chunk_38 : countSmall 3800 100 = 11 := by decide
lemma chunk_39 : countSmall 3900 100 = 11 := by decide
lemma chunk_40 : countSmall 4000 100 = 15 := by decide
lemma chunk_41 : countSmall 4100 100 = 9 := by decide
lemma chunk_42 : countSmall 4200 100 = 16 := by decide
lemma chunk_43 : countSmall 4300 100 = 9 := by decide
lemma chunk_44 : countSmall 4400 100 = 11 := by decide
lemma chunk_45 : countSmall 4500 100 = 12 := by decide
lemma chunk_46 : countSmall 4600 100 = 12 := by decide
lemma chunk_47 : countSmall 4700 100 = 12 := by decide
lemma chunk_48 : countSmall 4800 100 = 8 := by decide
lemma chunk_49 : countSmall 4900 100 = 15 := by decide
lemma chunk_50 : countSmall 5000 100 = 12 := by decide
lemma chunk_51 : countSmall 5100 100 = 11 := by decide
lemma chunk_52 : countSmall 5200 100 = 10 := by decide
lemma chunk_53 : countSmall 5300 100 = 10 := by decide
lemma chunk_54 : countSmall 5400 100 = 13 := by decide
lemma chunk_55 : countSmall 5500 100 = 13 := by decide
lemma chunk_56 : countSmall 5600 100 = 12 := by decide
lemma chunk_57 : countSmall 5700 100 = 10 := by decide
lemma chunk_58 : countSmall 5800 100 = 16 := by decide
lemma chunk_59 : countSmall 5900 100 = 7 := by decide
lemma chunk_60 : countSmall 6000 100 = 12 := by decide
lemma chunk_61 : countSmall 6100 100 = 11 := by decide
lemma chunk_62 : countSmall 6200 100 = 13 := by decide
lemma chunk_63 : countSmall 6300 100 = 15 := by decide
lemma chunk_64 : countSmall 6400 100 = 8 := by decide
lemma chunk_65 : countSmall 6500 100 = 11 := by decide
lemma chunk_66 : countSmall 6600 100 = 10 := by decide
lemma chunk_67 : countSmall 6700 100 = 12 := by decide
lemma chunk_68 : countSmall 6800 100 = 12 := by decide
lemma chunk_69 : countSmall 6900 100 = 13 := by decide
lemma chunk_70 : countSmall 7000 100 = 9 := by decide
lemma chunk_71 : countSmall 7100 100 = 10 := by decide
lemma chunk_72 : countSmall 7200 100 = 11 := by decide
lemma chunk_73 : countSmall 7300 100 = 9 := by decide
lemma chunk_74 : countSmall 7400 100 = 11 := by decide
lemma chunk_75 : countSmall 7500 100 = 15 := by decide
lemma chunk_76 : countSmall 7600 100 = 12 := by decide
lemma chunk_77 : countSmall 7700 100 = 10 := by decide
lemma chunk_78 : countSmall 7800 100 = 10 := by decide
lemma chunk_79 : countSmall 7900 100 = 10 := by decide
lemma chunk_80 : countSmall 8000 100 = 11 := by decide
lemma chunk_81 : countSmall 8100 100 = 10 := by decide
lemma chunk_82 : countSmall 8200 100 = 14 := by decide
lemma chunk_83 : countSmall 8300 100 = 9 := by decide
lemma chunk_84 : countSmall 8400 100 = 8 := by decide
lemma chunk_85 : countSmall 8500 100 = 12 := by decide
lemma chunk_86 : countSmall 8600 100 = 13 := by decide
lemma chunk_87 : countSmall 8700 100 = 11 := by decide
lemma chunk_88 : countSmall 8800 100 = 13 := by decide
lemma chunk_89 : countSmall 8900 100 = 9 := by decide
lemma chunk_90 : countSmall 9000 100 = 11 := by decide
lemma chunk_91 : countSmall 9100 100 = 12 := by decide
lemma chunk_92 : countSmall 9200 100 = 11 := by decide
lemma chunk_93 : countSmall 9300 100 = 11 := by decide
lemma chunk_94 : countSmall 9400 100 = 15 := by decide
lemma chunk_95 : countSmall 9500 100 = 7 := by decide
lemma chunk_96 : countSmall 9600 100 = 13 := by decide
lemma chunk_97 : countSmall 9700 100 = 11 := by decide
lemma chunk_98 : countSmall 9800 100 = 12 := by decide
lemma chunk_99 : countSmall 9900 100 = 9 := by decide
lemma chunk_100 : countSmall 10000 100 = 11 := by decide
lemma chunk_101 : countSmall 10100 100 = 12 := by decide
lemma chunk_102 : countSmall 10200 100 = 10 := by decide
lemma chunk_103 : countSmall 10300 100 = 12 := by decide
lemma chunk_104 : countSmall 10400 100 = 10 := by decide
lemma chunk_105 : countSmall 10500 100 = 8 := by decide
lemma chunk_106 : countSmall 10600 100 = 13 := by decide
lemma chunk_107 : countSmall 10700 100 = 11 := by decide
lemma chunk_108 : countSmall 10800 100 = 10 := by decide
lemma chunk_109 : countSmall 10900 100 = 10 := by decide
lemma chunk_110 : countSmall 11000 100 = 11 := by decide
lemma chunk_111 : countSmall 11100 100 = 11 := by decide
lemma chunk_112 : countSmall 11200 100 = 11 := by decide
lemma chunk_113 : countSmall 11300 100 = 10 := by decide
lemma chunk_114 : countSmall 11400 100 = 12 := by decide
lemma chunk_115 : countSmall 11500 100 = 9 := by decide
lemma chunk_116 : countSmall 11600 100 = 10 := by decide
lemma chunk_117 : countSmall 11700 100 = 9 := by decide
lemma chunk_118 : countSmall 11800 100 = 13 := by decide
lemma chunk_119 : countSmall 11900 100 = 13 := by decide
lemma chunk_120 : countSmall 12000 100 = 10 := by decide
lemma chunk_121 : countSmall 12100 100 = 11 := by decide
lemma chunk_122 : countSmall 12200 100 = 12 := by decide
lemma chunk_123 : countSmall 12300 100 = 10 := by decide
lemma chunk_124 : countSmall 12400 100 = 13 := by decide
lemma chunk_125 : countSmall 12500 100 = 12 := by decide
lemma chunk_126 : countSmall 12600 100 = 12 := by decide
lemma chunk_127 : countSmall 12700 100 = 11 := by decide
lemma chunk_128 : countSmall 12800 100 = 9 := by decide
lemma chunk_129 : countSmall 12900 100 = 12 := by decide
lemma chunk_130 : countSmall 13000 100 = 12 := by decide
lemma chunk_131 : countSmall 13100 100 = 12 := by decide
lemma chunk_132 : countSmall 13200 100 = 9 := by decide
lemma chunk_133 : countSmall 13300 100 = 10 := by decide
lemma chunk_134 : countSmall 13400 100 = 12 := by decide
lemma chunk_135 : countSmall 13500 100 = 9 := by decide
lemma chunk_136 : countSmall 13600 100 = 12 := by decide
lemma chunk_137 : countSmall 13700 100 = 12 := by decide
lemma chunk_138 : countSmall 13800 100 = 10 := by decide
lemma chunk_139 : countSmall 13900 100 = 11 := by decide
lemma chunk_140 : countSmall 14000 100 = 11 := by decide
lemma chunk_141 : countSmall 14100 100 = 9 := by decide
lemma chunk_142 : countSmall 14200 100 = 8 := by decide
lemma chunk_143 : countSmall 14300 100 = 11 := by decide
lemma chunk_144 : countSmall 14400 100 = 12 := by decide
lemma chunk_145 : countSmall 14500 100 = 12 := by decide
lemma chunk_146 : countSmall 14600 100 = 11 := by decide
lemma chunk_147 : countSmall 14700 100 = 14 := by decide
lemma chunk_148 : countSmall 14800 100 = 14 := by decide
lemma chunk_149 : countSmall 14900 100 = 9 := by decide
lemma chunk_150 : countSmall 15000 100 = 9 := by decide
lemma chunk_151 : countSmall 15100 100 = 13 := by decide
lemma chunk_152 : countSmall 15200 100 = 12 := by decide
lemma chunk_153 : countSmall 15300 100 = 13 := by decide
lemma chunk_154 : countSmall 15400 100 = 12 := by decide
lemma chunk_155 : countSmall 15500 100 = 9 := by decide
lemma chunk_156 : countSmall 15600 100 = 13 := by decide
lemma chunk_157 : countSmall 15700 100 = 13 := by decide
lemma chunk_158 : countSmall 15800 100 = 9 := by decide
lemma chunk_159 : countSmall 15900 100 = 11 := by decide
lemma chunk_160 : countSmall 16000 100 = 12 := by decide
lemma chunk_161 : countSmall 16100 100 = 12 := by decide
lemma chunk_162 : countSmall 16200 100 = 9 := by decide
lemma chunk_163 : countSmall 16300 100 = 9 := by decide
lemma chunk_164 : countSmall 16400 100 = 13 := by decide
lemma chunk_165 : countSmall 16500 100 = 7 := by decide
lemma chunk_166 : countSmall 16600 100 = 14 := by decide
lemma chunk_167 : countSmall 16700 100 = 9 := by decide
lemma chunk_168 : countSmall 16800 100 = 10 := by decide
lemma chunk_169 : countSmall 16900 100 = 12 := by decide
lemma chunk_170 : countSmall 17000 100 = 12 := by decide
lemma chunk_171 : countSmall 17100 100 = 11 := by decide
lemma chunk_172 : countSmall 17200 100 = 10 := by decide
lemma chunk_173 : countSmall 17300 100 = 13 := by decide
lemma chunk_174 : countSmall 17400 100 = 14 := by decide
lemma chunk_175 : countSmall 17500 100 = 10 := by decide
lemma chunk_176 : countSmall 17600 100 = 9 := by decide
lemma chunk_177 : countSmall 17700 100 = 12 := by decide
lemma chunk_178 : countSmall 17800 100 = 10 := by decide
lemma chunk_179 : countSmall 17900 100 = 15 := by decide
lemma chunk_180 : countSmall 18000 100 = 10 := by decide
lemma chunk_181 : countSmall 18100 100 = 11 := by decide
lemma chunk_182 : countSmall 18200 100 = 13 := by decide
lemma chunk_183 : countSmall 18300 100 = 11 := by decide
lemma chunk_184 : countSmall 18400 100 = 13 := by decide
lemma chunk_185 : countSmall 18500 100 = 11 := by decide
lemma chunk_186 : countSmall 18600 100 = 7 := by decide
lemma chunk_187 : countSmall 18700 100 = 12 := by decide
lemma chunk_188 : countSmall 18800 100 = 7 := by decide
lemma chunk_189 : countSmall 18900 100 = 9 := by decide
lemma chunk_190 : countSmall 19000 100 = 12 := by decide
lemma chunk_191 : countSmall 19100 100 = 9 := by decide
lemma chunk_192 : countSmall 19200 100 = 11 := by decide
lemma chunk_193 : countSmall 19300 100 = 11 := by decide
lemma chunk_194 : countSmall 19400 100 = 16 := by decide
lemma chunk_195 : countSmall 19500 100 = 14 := by decide
lemma chunk_196 : countSmall 19600 100 = 8 := by decide
lemma chunk_197 : countSmall 19700 100 = 12 := by decide
lemma chunk_198 : countSmall 19800 100 = 11 := by decide
lemma chunk_199 : countSmall 19900 100 = 13 := by decide
lemma chunk_200 : countSmall 20000 100 = 9 := by decide
lemma chunk_201 : countSmall 20100 100 = 13 := by decide
lemma chunk_202 : countSmall 20200 100 = 11 := by decide
lemma chunk_203 : countSmall 20300 100 = 12 := by decide
lemma chunk_204 : countSmall 20400 100 = 12 := by decide
lemma chunk_205 : countSmall 20500 100 = 11 := by decide
lemma chunk_206 : countSmall 20600 100 = 9 := by decide
lemma chunk_207 : countSmall 20700 100 = 14 := by decide
lemma chunk_208 : countSmall 20800 100 = 10 := by decide
lemma chunk_209 : countSmall 20900 100 = 10 := by decide
lemma chunk_210 : countSmall 21000 100 = 13 := by decide
lemma chunk_211 : countSmall 21100 100 = 13 := by decide
lemma chunk_212 : countSmall 21200 100 = 9 := by decide
lemma chunk_213 : countSmall 21300 100 = 12 := by decide
lemma chunk_214 : countSmall 21400 100 = 11 := by decide
lemma chunk_215 : countSmall 21500 100 = 15 := by decide
lemma chunk_216 : countSmall 21600 100 = 10 := by decide
lemma chunk_217 : countSmall 21700 100 = 12 := by decide
lemma chunk_218 : countSmall 21800 100 = 14 := by decide
lemma chunk_219 : countSmall 21900 100 = 9 := by decide
lemma chunk_220 : countSmall 22000 100 = 13 := by decide
lemma chunk_221 : countSmall 22100 100 = 12 := by decide
lemma chunk_222 : countSmall 22200 100 = 11 := by decide
lemma chunk_223 : countSmall 22300 100 = 10 := by decide
lemma chunk_224 : countSmall 22400 100 = 10 := by decide
lemma chunk_225 : countSmall 22500 100 = 10 := by decide
lemma chunk_226 : countSmall 22600 100 = 14 := by decide
lemma chunk_227 : countSmall 22700 100 = 12 := by decide
lemma chunk_228 : countSmall 22800 100 = 10 := by decide
lemma chunk_229 : countSmall 22900 100 = 12 := by decide
lemma chunk_230 : countSmall 23000 100 = 16 := by decide
lemma chunk_231 : countSmall 23100 100 = 8 := by decide
lemma chunk_232 : countSmall 23200 100 = 11 := by decide
lemma chunk_233 : countSmall 23300 100 = 11 := by decide
lemma chunk_234 : countSmall 23400 100 = 7 := by decide
lemma chunk_235 : countSmall 23500 100 = 13 := by decide
lemma chunk_236 : countSmall 23600 100 = 12 := by decide
lemma chunk_237 : countSmall 23700 100 = 12 := by decide
lemma chunk_238 : countSmall 23800 100 = 15 := by decide
lemma chunk_239 : countSmall 23900 100 = 10 := by decide
lemma chunk_240 : countSmall 24000 100 = 14 := by decide
lemma chunk_241 : countSmall 24100 100 = 12 := by decide
lemma chunk_242 : countSmall 24200 100 = 10 := by decide
lemma chunk_243 : countSmall 24300 100 = 9 := by decide
lemma chunk_244 : countSmall 24400 100 = 10 := by decide
lemma chunk_245 : countSmall 24500 100 = 11 := by decide
lemma chunk_246 : countSmall 24600 100 = 12 := by decide
lemma chunk_247 : countSmall 24700 100 = 10 := by decide
lemma chunk_248 : countSmall 24800 100 = 11 := by decide
lemma chunk_249 : countSmall 24900 100 = 13 := by decide
lemma chunk_250 : countSmall 25000 100 = 10 := by decide
lemma chunk_251 : countSmall 25100 100 = 13 := by decide
lemma chunk_252 : countSmall 25200 100 = 10 := by decide
lemma chunk_253 : countSmall 25300 100 = 13 := by decide
lemma chunk_254 : countSmall 25400 100 = 10 := by decide
lemma chunk_255 : countSmall 25500 100 = 10 := by decide
lemma chunk_256 : countSmall 25600 100 = 13 := by decide
lemma chunk_257 : countSmall 25700 100 = 12 := by decide
lemma chunk_258 : countSmall 25800 100 = 11 := by decide
lemma chunk_259 : countSmall 25900 100 = 12 := by decide
lemma chunk_260 : countSmall 26000 100 = 10 := by decide
lemma chunk_261 : countSmall 26100 100 = 13 := by decide
lemma chunk_262 : countSmall 26200 100 = 13 := by decide
lemma chunk_263 : countSmall 26300 100 = 11 := by decide
lemma chunk_264 : countSmall 26400 100 = 12 := by decide
lemma chunk_265 : countSmall 26500 100 = 10 := by decide
lemma chunk_266 : countSmall 26600 100 = 11 := by decide
lemma chunk_267 : countSmall 26700 100 = 12 := by decide
lemma chunk_268 : countSmall 26800 100 = 14 := by decide
lemma chunk_269 : countSmall 26900 100 = 12 := by decide
lemma chunk_270 : countSmall 27000 100 = 13 := by decide
lemma chunk_271 : countSmall 27100 100 = 9 := by decide
lemma chunk_272 : countSmall 27200 100 = 13 := by decide
lemma chunk_273 : countSmall 27300 100 = 8 := by decide
lemma chunk_274 : countSmall 27400 100 = 11 := by decide
lemma chunk_275 : countSmall 27500 100 = 8 := by decide
lemma chunk_276 : countSmall 27600 100 = 11 := by decide
lemma chunk_277 : countSmall 27700 100 = 15 := by decide
lemma chunk_278 : countSmall 27800 100 = 10 := by decide
lemma chunk_279 : countSmall 27900 100 = 12 := by decide
lemma chunk_280 : countSmall 28000 100 = 12 := by decide
lemma chunk_281 : countSmall 28100 100 = 10 := by decide
lemma chunk_282 : countSmall 28200 100 = 9 := by decide
lemma chunk_283 : countSmall 28300 100 = 9 := by decide
lemma chunk_284 : countSmall 28400 100 = 13 := by decide
lemma chunk_285 : countSmall 28500 100 = 13 := by decide
lemma chunk_286 : countSmall 28600 100 = 15 := by decide
lemma chunk_287 : countSmall 28700 100 = 12 := by decide
lemma chunk_288 : countSmall 28800 100 = 12 := by decide
lemma chunk_289 : countSmall 28900 100 = 11 := by decide
lemma chunk_290 : countSmall 29000 100 = 11 := by decide
lemma chunk_291 : countSmall 29100 100 = 14 := by decide
lemma chunk_292 : countSmall 29200 100 = 11 := by decide
lemma chunk_293 : countSmall 29300 100 = 14 := by decide
lemma chunk_294 : countSmall 29400 100 = 9 := by decide
lemma chunk_295 : countSmall 29500 100 = 13 := by decide
lemma chunk_296 : countSmall 29600 100 = 10 := by decide
lemma chunk_297 : countSmall 29700 100 = 10 := by decide
lemma chunk_298 : countSmall 29800 100 = 11 := by decide
lemma chunk_299 : countSmall 29900 100 = 10 := by decide
lemma chunk_300 : countSmall 30000 100 = 11 := by decide
lemma chunk_301 : countSmall 30100 100 = 14 := by decide
lemma chunk_302 : countSmall 30200 100 = 11 := by decide
lemma chunk_303 : countSmall 30300 100 = 12 := by decide
lemma chunk_304 : countSmall 30400 100 = 9 := by decide
lemma chunk_305 : countSmall 30500 100 = 11 := by decide
lemma chunk_306 : countSmall 30600 100 = 12 := by decide
lemma chunk_307 : countSmall 30700 100 = 8 := by decide
lemma chunk_308 : countSmall 30800 100 = 14 := by decide
lemma chunk_309 : countSmall 30900 100 = 11 := by decide
lemma chunk_310 : countSmall 31000 100 = 11 := by decide
lemma chunk_311 : countSmall 31100 100 = 13 := by decide
lemma chunk_312 : countSmall 31200 100 = 12 := by decide
lemma chunk_313 : countSmall 31300 100 = 17 := by decide
lemma chunk_314 : countSmall 31400 100 = 6 := by decide
lemma chunk_315 : countSmall 31500 100 = 12 := by decide
lemma chunk_316 : countSmall 31600 100 = 11 := by decide
lemma chunk_317 : countSmall 31700 100 = 11 := by decide
lemma chunk_318 : countSmall 31800 100 = 11 := by decide
lemma chunk_319 : countSmall 31900 100 = 9 := by decide
lemma chunk_320 : countSmall 32000 100 = 15 := by decide
lemma chunk_321 : countSmall 32100 100 = 10 := by decide
lemma chunk_322 : countSmall 32200 100 = 11 := by decide
lemma chunk_323 : countSmall 32300 100 = 15 := by decide
lemma chunk_324 : countSmall 32400 100 = 12 := by decide
lemma chunk_325 : countSmall 32500 100 = 11 := by decide
lemma chunk_326 : countSmall 32600 100 = 11 := by decide
lemma chunk_327 : countSmall 32700 100 = 12 := by decide
lemma chunk_328 : countSmall 32800 100 = 11 := by decide
lemma chunk_329 : countSmall 32900 100 = 13 := by decide
lemma chunk_330 : countSmall 33000 100 = 12 := by decide
lemma chunk_331 : countSmall 33100 100 = 12 := by decide
lemma chunk_332 : countSmall 33200 100 = 10 := by decide
lemma chunk_333 : countSmall 33300 100 = 13 := by decide
lemma chunk_334 : countSmall 33400 100 = 14 := by decide
lemma chunk_335 : countSmall 33500 100 = 12 := by decide
lemma chunk_336 : countSmall 33600 100 = 12 := by decide
lemma chunk_337 : countSmall 33700 100 = 12 := by decide
lemma chunk_338 : countSmall 33800 100 = 12 := by decide
lemma chunk_339 : countSmall 33900 100 = 9 := by decide
lemma chunk_340 : countSmall 34000 100 = 8 := by decide
lemma chunk_341 : countSmall 34100 100 = 13 := by decide
lemma chunk_342 : countSmall 34200 100 = 12 := by decide
lemma chunk_343 : countSmall 34300 100 = 13 := by decide
lemma chunk_344 : countSmall 34400 100 = 13 := by decide
lemma chunk_345 : countSmall 34500 100 = 14 := by decide
lemma chunk_346 : countSmall 34600 100 = 12 := by decide
lemma chunk_347 : countSmall 34700 100 = 11 := by decide
lemma chunk_348 : countSmall 34800 100 = 11 := by decide
lemma chunk_349 : countSmall 34900 100 = 8 := by decide
lemma chunk_350 : countSmall 35000 100 = 11 := by decide
lemma chunk_351 : countSmall 35100 100 = 12 := by decide
lemma chunk_352 : countSmall 35200 100 = 13 := by decide
lemma chunk_353 : countSmall 35300 100 = 10 := by decide
lemma chunk_354 : countSmall 35400 100 = 10 := by decide
lemma chunk_355 : countSmall 35500 100 = 14 := by decide
lemma chunk_356 : countSmall 35600 100 = 9 := by decide
lemma chunk_357 : countSmall 35700 100 = 9 := by decide
lemma chunk_358 : countSmall 35800 100 = 13 := by decide
lemma chunk_359 : countSmall 35900 100 = 14 := by decide
lemma chunk_360 : countSmall 36000 100 = 15 := by decide
lemma chunk_361 : countSmall 36100 100 = 8 := by decide
lemma chunk_362 : countSmall 36200 100 = 11 := by decide
lemma chunk_363 : countSmall 36300 100 = 12 := by decide
lemma chunk_364 : countSmall 36400 100 = 10 := by decide
lemma chunk_365 : countSmall 36500 100 = 14 := by decide
lemma chunk_366 : countSmall 36600 100 = 10 := by decide
lemma chunk_367 : countSmall 36700 100 = 13 := by decide
lemma chunk_368 : countSmall 36800 100 = 12 := by decide
lemma chunk_369 : countSmall 36900 100 = 12 := by decide
lemma chunk_370 : countSmall 37000 100 = 12 := by decide
lemma chunk_371 : countSmall 37100 100 = 10 := by decide
lemma chunk_372 : countSmall 37200 100 = 10 := by decide
lemma chunk_373 : countSmall 37300 100 = 16 := by decide
lemma chunk_374 : countSmall 37400 100 = 9 := by decide
lemma chunk_375 : countSmall 37500 100 = 16 := by decide
lemma chunk_376 : countSmall 37600 100 = 12 := by decide
lemma chunk_377 : countSmall 37700 45 = 1 := by decide
lemma countUp_0 : countSmall 0 0 = 0 := by simp [countSmall]
lemma countUp_100 : countSmall 0 100 = 0 := by
  simpa using chunk_0
lemma countUp_200 : countSmall 0 200 = 20 := by
  have h := countSmall_add 0 100 100
  rw [countUp_100, chunk_1] at h
  simpa using h
lemma countUp_300 : countSmall 0 300 = 36 := by
  have h := countSmall_add 0 200 100
  rw [countUp_200, chunk_2] at h
  simpa using h
lemma countUp_400 : countSmall 0 400 = 52 := by
  have h := countSmall_add 0 300 100
  rw [countUp_300, chunk_3] at h
  simpa using h
lemma countUp_500 : countSmall 0 500 = 69 := by
  have h := countSmall_add 0 400 100
  rw [countUp_400, chunk_4] at h
  simpa using h
lemma countUp_600 : countSmall 0 600 = 83 := by
  have h := countSmall_add 0 500 100
  rw [countUp_500, chunk_5] at h
  simpa using h
lemma countUp_700 : countSmall 0 700 = 99 := by
  have h := countSmall_add 0 600 100
  rw [countUp_600, chunk_6] at h
  simpa using h
lemma countUp_800 : countSmall 0 800 = 113 := by
  have h := countSmall_add 0 700 100
  rw [countUp_700, chunk_7] at h
  simpa using h
lemma countUp_900 : countSmall 0 900 = 128 := by
  have h := countSmall_add 0 800 100
  rw [countUp_800, chunk_8] at h
  simpa using h
lemma countUp_1000 : countSmall 0 1000 = 142 := by
  have h := countSmall_add 0 900 100
  rw [countUp_900, chunk_9] at h
  simpa using h
lemma countUp_1100 : countSmall 0 1100 = 158 := by
  have h := countSmall_add 0 1000 100
  rw [countUp_1000, chunk_10] at h
  simpa using h
lemma countUp_1200 : countSmall 0 1200 = 170 := by
  have h := countSmall_add 0 1100 100
  rw [countUp_1100, chunk_11] at h
  simpa using h
lemma countUp_1300 : countSmall 0 1300 = 185 := by
  have h := countSmall_add 0 1200 100
  rw [countUp_1200, chunk_12] at h
  simpa using h
lemma countUp_1400 : countSmall 0 1400 = 196 := by
  have h := countSmall_add 0 1300 100
  rw [countUp_1300, chunk_13] at h
  simpa using h
lemma countUp_1500 : countSmall 0 1500 = 213 := by
  have h := countSmall_add 0 1400 100
  rw [countUp_1400, chunk_14] at h
  simpa using h
lemma countUp_1600 : countSmall 0 1600 = 225 := by
  have h := countSmall_add 0 1500 100
  rw [countUp_1500, chunk_15] at h
  simpa using h
lemma countUp_1700 : countSmall 0 1700 = 240 := by
  have h := countSmall_add 0 1600 100
  rw [countUp_1600, chunk_16] at h
  simpa using h
lemma countUp_1800 : countSmall 0 1800 = 252 := by
  have h := countSmall_add 0 1700 100
  rw [countUp_1700, chunk_17] at h
  simpa using h
lemma countUp_1900 : countSmall 0 1900 = 264 := by
  have h := countSmall_add 0 1800 100
  rw [countUp_1800, chunk_18] at h
  simpa using h
lemma countUp_2000 : countSmall 0 2000 = 277 := by
  have h := countSmall_add 0 1900 100
  rw [countUp_1900, chunk_19] at h
  simpa using h
lemma countUp_2100 : countSmall 0 2100 = 291 := by
  have h := countSmall_add 0 2000 100
  rw [countUp_2000, chunk_20] at h
  simpa using h
lemma countUp_2200 : countSmall 0 2200 = 301 := by
  have h := countSmall_add 0 2100 100
  rw [countUp_2100, chunk_21] at h
  simpa using h
lemma countUp_2300 : countSmall 0 2300 = 316 := by
  have h := countSmall_add 0 2200 100
  rw [countUp_2200, chunk_22] at h
  simpa using h
lemma countUp_2400 : countSmall 0 2400 = 331 := by
  have h := countSmall_add 0 2300 100
  rw [countUp_2300, chunk_23] at h
  simpa using h
lemma countUp_2500 : countSmall 0 2500 = 341 := by
  have h := countSmall_add 0 2400 100
  rw [countUp_2400, chunk_24] at h
  simpa using h
lemma countUp_2600 : countSmall 0 2600 = 352 := by
  have h := countSmall_add 0 2500 100
  rw [countUp_2500, chunk_25] at h
  simpa using h
lemma countUp_2700 : countSmall 0 2700 = 367 := by
  have h := countSmall_add 0 2600 100
  rw [countUp_2600, chunk_26] at h
  simpa using h
lemma countUp_2800 : countSmall 0 2800 = 381 := by
  have h := countSmall_add 0 2700 100
  rw [countUp_2700, chunk_27] at h
  simpa using h
lemma countUp_2900 : countSmall 0 2900 = 393 := by
  have h := countSmall_add 0 2800 100
  rw [countUp_2800, chunk_28] at h
  simpa using h
lemma countUp_3000 : countSmall 0 3000 = 404 := by
  have h := countSmall_add 0 2900 100
  rw [countUp_2900, chunk_29] at h
  simpa using h
lemma countUp_3100 : countSmall 0 3100 = 416 := by
  have h := countSmall_add 0 3000 100
  rw [countUp_3000, chunk_30] at h
  simpa using h
lemma countUp_3200 : countSmall 0 3200 = 426 := by
  have h := countSmall_add 0 3100 100
  rw [countUp_3100, chunk_31] at h
  simpa using h
lemma countUp_3300 : countSmall 0 3300 = 437 := by
  have h := countSmall_add 0 3200 100
  rw [countUp_3200, chunk_32] at h
  simpa using h
lemma countUp_3400 : countSmall 0 3400 = 452 := by
  have h := countSmall_add 0 3300 100
  rw [countUp_3300, chunk_33] at h
  simpa using h
lemma countUp_3500 : countSmall 0 3500 = 463 := by
  have h := countSmall_add 0 3400 100
  rw [countUp_3400, chunk_34] at h
  simpa using h
lemma countUp_3600 : countSmall 0 3600 = 477 := by
  have h := countSmall_add 0 3500 100
  rw [countUp_3500, chunk_35] at h
  simpa using h
lemma countUp_3700 : countSmall 0 3700 = 490 := by
  have h := countSmall_add 0 3600 100
  rw [countUp_3600, chunk_36] at h
  simpa using h
lemma countUp_3800 : countSmall 0 3800 = 502 := by
  have h := countSmall_add 0 3700 100
  rw [countUp_3700, chunk_37] at h
  simpa using h
lemma countUp_3900 : countSmall 0 3900 = 513 := by
  have h := countSmall_add 0 3800 100
  rw [countUp_3800, chunk_38] at h
  simpa using h
lemma countUp_4000 : countSmall 0 4000 = 524 := by
  have h := countSmall_add 0 3900 100
  rw [countUp_3900, chunk_39] at h
  simpa using h
lemma countUp_4100 : countSmall 0 4100 = 539 := by
  have h := countSmall_add 0 4000 100
  rw [countUp_4000, chunk_40] at h
  simpa using h
lemma countUp_4200 : countSmall 0 4200 = 548 := by
  have h := countSmall_add 0 4100 100
  rw [countUp_4100, chunk_41] at h
  simpa using h
lemma countUp_4300 : countSmall 0 4300 = 564 := by
  have h := countSmall_add 0 4200 100
  rw [countUp_4200, chunk_42] at h
  simpa using h
lemma countUp_4400 : countSmall 0 4400 = 573 := by
  have h := countSmall_add 0 4300 100
  rw [countUp_4300, chunk_43] at h
  simpa using h
lemma countUp_4500 : countSmall 0 4500 = 584 := by
  have h := countSmall_add 0 4400 100
  rw [countUp_4400, chunk_44] at h
  simpa using h
lemma countUp_4600 : countSmall 0 4600 = 596 := by
  have h := countSmall_add 0 4500 100
  rw [countUp_4500, chunk_45] at h
  simpa using h
lemma countUp_4700 : countSmall 0 4700 = 608 := by
  have h := countSmall_add 0 4600 100
  rw [countUp_4600, chunk_46] at h
  simpa using h
lemma countUp_4800 : countSmall 0 4800 = 620 := by
  have h := countSmall_add 0 4700 100
  rw [countUp_4700, chunk_47] at h
  simpa using h
lemma countUp_4900 : countSmall 0 4900 = 628 := by
  have h := countSmall_add 0 4800 100
  rw [countUp_4800, chunk_48] at h
  simpa using h
lemma countUp_5000 : countSmall 0 5000 = 643 := by
  have h := countSmall_add 0 4900 100
  rw [countUp_4900, chunk_49] at h
  simpa using h
lemma countUp_5100 : countSmall 0 5100 = 655 := by
  have h := countSmall_add 0 5000 100
  rw [countUp_5000, chunk_50] at h
  simpa using h
lemma countUp_5200 : countSmall 0 5200 = 666 := by
  have h := countSmall_add 0 5100 100
  rw [countUp_5100, chunk_51] at h
  simpa using h
lemma countUp_5300 : countSmall 0 5300 = 676 := by
  have h := countSmall_add 0 5200 100
  rw [countUp_5200, chunk_52] at h
  simpa using h
lemma countUp_5400 : countSmall 0 5400 = 686 := by
  have h := countSmall_add 0 5300 100
  rw [countUp_5300, chunk_53] at h
  simpa using h
lemma countUp_5500 : countSmall 0 5500 = 699 := by
  have h := countSmall_add 0 5400 100
  rw [countUp_5400, chunk_54] at h
  simpa using h
lemma countUp_5600 : countSmall 0 5600 = 712 := by
  have h := countSmall_add 0 5500 100
  rw [countUp_5500, chunk_55] at h
  simpa using h
lemma countUp_5700 : countSmall 0 5700 = 724 := by
  have h := countSmall_add 0 5600 100
  rw [countUp_5600, chunk_56] at h
  simpa using h
lemma countUp_5800 : countSmall 0 5800 = 734 := by
  have h := countSmall_add 0 5700 100
  rw [countUp_5700, chunk_57] at h
  simpa using h
lemma countUp_5900 : countSmall 0 5900 = 750 := by
  have h := countSmall_add 0 5800 100
  rw [countUp_5800, chunk_58] at h
  simpa using h
lemma countUp_6000 : countSmall 0 6000 = 757 := by
  have h := countSmall_add 0 5900 100
  rw [countUp_5900, chunk_59] at h
  simpa using h
lemma countUp_6100 : countSmall 0 6100 = 769 := by
  have h := countSmall_add 0 6000 100
  rw [countUp_6000, chunk_60] at h
  simpa using h
lemma countUp_6200 : countSmall 0 6200 = 780 := by
  have h := countSmall_add 0 6100 100
  rw [countUp_6100, chunk_61] at h
  simpa using h
lemma countUp_6300 : countSmall 0 6300 = 793 := by
  have h := countSmall_add 0 6200 100
  rw [countUp_6200, chunk_62] at h
  simpa using h
lemma countUp_6400 : countSmall 0 6400 = 808 := by
  have h := countSmall_add 0 6300 100
  rw [countUp_6300, chunk_63] at h
  simpa using h
lemma countUp_6500 : countSmall 0 6500 = 816 := by
  have h := countSmall_add 0 6400 100
  rw [countUp_6400, chunk_64] at h
  simpa using h
lemma countUp_6600 : countSmall 0 6600 = 827 := by
  have h := countSmall_add 0 6500 100
  rw [countUp_6500, chunk_65] at h
  simpa using h
lemma countUp_6700 : countSmall 0 6700 = 837 := by
  have h := countSmall_add 0 6600 100
  rw [countUp_6600, chunk_66] at h
  simpa using h
lemma countUp_6800 : countSmall 0 6800 = 849 := by
  have h := countSmall_add 0 6700 100
  rw [countUp_6700, chunk_67] at h
  simpa using h
lemma countUp_6900 : countSmall 0 6900 = 861 := by
  have h := countSmall_add 0 6800 100
  rw [countUp_6800, chunk_68] at h
  simpa using h
lemma countUp_7000 : countSmall 0 7000 = 874 := by
  have h := countSmall_add 0 6900 100
  rw [countUp_6900, chunk_69] at h
  simpa using h
lemma countUp_7100 : countSmall 0 7100 = 883 := by
  have h := countSmall_add 0 7000 100
  rw [countUp_7000, chunk_70] at h
  simpa using h
lemma countUp_7200 : countSmall 0 7200 = 893 := by
  have h := countSmall_add 0 7100 100
  rw [countUp_7100, chunk_71] at h
  simpa using h
lemma countUp_7300 : countSmall 0 7300 = 904 := by
  have h := countSmall_add 0 7200 100
  rw [countUp_7200, chunk_72] at h
  simpa using h
lemma countUp_7400 : countSmall 0 7400 = 913 := by
  have h := countSmall_add 0 7300 100
  rw [countUp_7300, chunk_73] at h
  simpa using h
lemma countUp_7500 : countSmall 0 7500 = 924 := by
  have h := countSmall_add 0 7400 100
  rw [countUp_7400, chunk_74] at h
  simpa using h
lemma countUp_7600 : countSmall 0 7600 = 939 := by
  have h := countSmall_add 0 7500 100
  rw [countUp_7500, chunk_75] at h
  simpa using h
lemma countUp_7700 : countSmall 0 7700 = 951 := by
  have h := countSmall_add 0 7600 100
  rw [countUp_7600, chunk_76] at h
  simpa using h
lemma countUp_7800 : countSmall 0 7800 = 961 := by
  have h := countSmall_add 0 7700 100
  rw [countUp_7700, chunk_77] at h
  simpa using h
lemma countUp_7900 : countSmall 0 7900 = 971 := by
  have h := countSmall_add 0 7800 100
  rw [countUp_7800, chunk_78] at h
  simpa using h
lemma countUp_8000 : countSmall 0 8000 = 981 := by
  have h := countSmall_add 0 7900 100
  rw [countUp_7900, chunk_79] at h
  simpa using h
lemma countUp_8100 : countSmall 0 8100 = 992 := by
  have h := countSmall_add 0 8000 100
  rw [countUp_8000, chunk_80] at h
  simpa using h
lemma countUp_8200 : countSmall 0 8200 = 1002 := by
  have h := countSmall_add 0 8100 100
  rw [countUp_8100, chunk_81] at h
  simpa using h
lemma countUp_8300 : countSmall 0 8300 = 1016 := by
  have h := countSmall_add 0 8200 100
  rw [countUp_8200, chunk_82] at h
  simpa using h
lemma countUp_8400 : countSmall 0 8400 = 1025 := by
  have h := countSmall_add 0 8300 100
  rw [countUp_8300, chunk_83] at h
  simpa using h
lemma countUp_8500 : countSmall 0 8500 = 1033 := by
  have h := countSmall_add 0 8400 100
  rw [countUp_8400, chunk_84] at h
  simpa using h
lemma countUp_8600 : countSmall 0 8600 = 1045 := by
  have h := countSmall_add 0 8500 100
  rw [countUp_8500, chunk_85] at h
  simpa using h
lemma countUp_8700 : countSmall 0 8700 = 1058 := by
  have h := countSmall_add 0 8600 100
  rw [countUp_8600, chunk_86] at h
  simpa using h
lemma countUp_8800 : countSmall 0 8800 = 1069 := by
  have h := countSmall_add 0 8700 100
  rw [countUp_8700, chunk_87] at h
  simpa using h
lemma countUp_8900 : countSmall 0 8900 = 1082 := by
  have h := countSmall_add 0 8800 100
  rw [countUp_8800, chunk_88] at h
  simpa using h
lemma countUp_9000 : countSmall 0 9000 = 1091 := by
  have h := countSmall_add 0 8900 100
  rw [countUp_8900, chunk_89] at h
  simpa using h
lemma countUp_9100 : countSmall 0 9100 = 1102 := by
  have h := countSmall_add 0 9000 100
  rw [countUp_9000, chunk_90] at h
  simpa using h
lemma countUp_9200 : countSmall 0 9200 = 1114 := by
  have h := countSmall_add 0 9100 100
  rw [countUp_9100, chunk_91] at h
  simpa using h
lemma countUp_9300 : countSmall 0 9300 = 1125 := by
  have h := countSmall_add 0 9200 100
  rw [countUp_9200, chunk_92] at h
  simpa using h
lemma countUp_9400 : countSmall 0 9400 = 1136 := by
  have h := countSmall_add 0 9300 100
  rw [countUp_9300, chunk_93] at h
  simpa using h
lemma countUp_9500 : countSmall 0 9500 = 1151 := by
  have h := countSmall_add 0 9400 100
  rw [countUp_9400, chunk_94] at h
  simpa using h
lemma countUp_9600 : countSmall 0 9600 = 1158 := by
  have h := countSmall_add 0 9500 100
  rw [countUp_9500, chunk_95] at h
  simpa using h
lemma countUp_9700 : countSmall 0 9700 = 1171 := by
  have h := countSmall_add 0 9600 100
  rw [countUp_9600, chunk_96] at h
  simpa using h
lemma countUp_9800 : countSmall 0 9800 = 1182 := by
  have h := countSmall_add 0 9700 100
  rw [countUp_9700, chunk_97] at h
  simpa using h
lemma countUp_9900 : countSmall 0 9900 = 1194 := by
  have h := countSmall_add 0 9800 100
  rw [countUp_9800, chunk_98] at h
  simpa using h
lemma countUp_10000 : countSmall 0 10000 = 1203 := by
  have h := countSmall_add 0 9900 100
  rw [countUp_9900, chunk_99] at h
  simpa using h
lemma countUp_10100 : countSmall 0 10100 = 1214 := by
  have h := countSmall_add 0 10000 100
  rw [countUp_10000, chunk_100] at h
  simpa using h
lemma countUp_10200 : countSmall 0 10200 = 1226 := by
  have h := countSmall_add 0 10100 100
  rw [countUp_10100, chunk_101] at h
  simpa using h
lemma countUp_10300 : countSmall 0 10300 = 1236 := by
  have h := countSmall_add 0 10200 100
  rw [countUp_10200, chunk_102] at h
  simpa using h
lemma countUp_10400 : countSmall 0 10400 = 1248 := by
  have h := countSmall_add 0 10300 100
  rw [countUp_10300, chunk_103] at h
  simpa using h
lemma countUp_10500 : countSmall 0 10500 = 1258 := by
  have h := countSmall_add 0 10400 100
  rw [countUp_10400, chunk_104] at h
  simpa using h
lemma countUp_10600 : countSmall 0 10600 = 1266 := by
  have h := countSmall_add 0 10500 100
  rw [countUp_10500, chunk_105] at h
  simpa using h
lemma countUp_10700 : countSmall 0 10700 = 1279 := by
  have h := countSmall_add 0 10600 100
  rw [countUp_10600, chunk_106] at h
  simpa using h
lemma countUp_10800 : countSmall 0 10800 = 1290 := by
  have h := countSmall_add 0 10700 100
  rw [countUp_10700, chunk_107] at h
  simpa using h
lemma countUp_10900 : countSmall 0 10900 = 1300 := by
  have h := countSmall_add 0 10800 100
  rw [countUp_10800, chunk_108] at h
  simpa using h
lemma countUp_11000 : countSmall 0 11000 = 1310 := by
  have h := countSmall_add 0 10900 100
  rw [countUp_10900, chunk_109] at h
  simpa using h
lemma countUp_11100 : countSmall 0 11100 = 1321 := by
  have h := countSmall_add 0 11000 100
  rw [countUp_11000, chunk_110] at h
  simpa using h
lemma countUp_11200 : countSmall 0 11200 = 1332 := by
  have h := countSmall_add 0 11100 100
  rw [countUp_11100, chunk_111] at h
  simpa using h
lemma countUp_11300 : countSmall 0 11300 = 1343 := by
  have h := countSmall_add 0 11200 100
  rw [countUp_11200, chunk_112] at h
  simpa using h
lemma countUp_11400 : countSmall 0 11400 = 1353 := by
  have h := countSmall_add 0 11300 100
  rw [countUp_11300, chunk_113] at h
  simpa using h
lemma countUp_11500 : countSmall 0 11500 = 1365 := by
  have h := countSmall_add 0 11400 100
  rw [countUp_11400, chunk_114] at h
  simpa using h
lemma countUp_11600 : countSmall 0 11600 = 1374 := by
  have h := countSmall_add 0 11500 100
  rw [countUp_11500, chunk_115] at h
  simpa using h
lemma countUp_11700 : countSmall 0 11700 = 1384 := by
  have h := countSmall_add 0 11600 100
  rw [countUp_11600, chunk_116] at h
  simpa using h
lemma countUp_11800 : countSmall 0 11800 = 1393 := by
  have h := countSmall_add 0 11700 100
  rw [countUp_11700, chunk_117] at h
  simpa using h
lemma countUp_11900 : countSmall 0 11900 = 1406 := by
  have h := countSmall_add 0 11800 100
  rw [countUp_11800, chunk_118] at h
  simpa using h
lemma countUp_12000 : countSmall 0 12000 = 1419 := by
  have h := countSmall_add 0 11900 100
  rw [countUp_11900, chunk_119] at h
  simpa using h
lemma countUp_12100 : countSmall 0 12100 = 1429 := by
  have h := countSmall_add 0 12000 100
  rw [countUp_12000, chunk_120] at h
  simpa using h
lemma countUp_12200 : countSmall 0 12200 = 1440 := by
  have h := countSmall_add 0 12100 100
  rw [countUp_12100, chunk_121] at h
  simpa using h
lemma countUp_12300 : countSmall 0 12300 = 1452 := by
  have h := countSmall_add 0 12200 100
  rw [countUp_12200, chunk_122] at h
  simpa using h
lemma countUp_12400 : countSmall 0 12400 = 1462 := by
  have h := countSmall_add 0 12300 100
  rw [countUp_12300, chunk_123] at h
  simpa using h
lemma countUp_12500 : countSmall 0 12500 = 1475 := by
  have h := countSmall_add 0 12400 100
  rw [countUp_12400, chunk_124] at h
  simpa using h
lemma countUp_12600 : countSmall 0 12600 = 1487 := by
  have h := countSmall_add 0 12500 100
  rw [countUp_12500, chunk_125] at h
  simpa using h
lemma countUp_12700 : countSmall 0 12700 = 1499 := by
  have h := countSmall_add 0 12600 100
  rw [countUp_12600, chunk_126] at h
  simpa using h
lemma countUp_12800 : countSmall 0 12800 = 1510 := by
  have h := countSmall_add 0 12700 100
  rw [countUp_12700, chunk_127] at h
  simpa using h
lemma countUp_12900 : countSmall 0 12900 = 1519 := by
  have h := countSmall_add 0 12800 100
  rw [countUp_12800, chunk_128] at h
  simpa using h
lemma countUp_13000 : countSmall 0 13000 = 1531 := by
  have h := countSmall_add 0 12900 100
  rw [countUp_12900, chunk_129] at h
  simpa using h
lemma countUp_13100 : countSmall 0 13100 = 1543 := by
  have h := countSmall_add 0 13000 100
  rw [countUp_13000, chunk_130] at h
  simpa using h
lemma countUp_13200 : countSmall 0 13200 = 1555 := by
  have h := countSmall_add 0 13100 100
  rw [countUp_13100, chunk_131] at h
  simpa using h
lemma countUp_13300 : countSmall 0 13300 = 1564 := by
  have h := countSmall_add 0 13200 100
  rw [countUp_13200, chunk_132] at h
  simpa using h
lemma countUp_13400 : countSmall 0 13400 = 1574 := by
  have h := countSmall_add 0 13300 100
  rw [countUp_13300, chunk_133] at h
  simpa using h
lemma countUp_13500 : countSmall 0 13500 = 1586 := by
  have h := countSmall_add 0 13400 100
  rw [countUp_13400, chunk_134] at h
  simpa using h
lemma countUp_13600 : countSmall 0 13600 = 1595 := by
  have h := countSmall_add 0 13500 100
  rw [countUp_13500, chunk_135] at h
  simpa using h
lemma countUp_13700 : countSmall 0 13700 = 1607 := by
  have h := countSmall_add 0 13600 100
  rw [countUp_13600, chunk_136] at h
  simpa using h
lemma countUp_13800 : countSmall 0 13800 = 1619 := by
  have h := countSmall_add 0 13700 100
  rw [countUp_13700, chunk_137] at h
  simpa using h
lemma countUp_13900 : countSmall 0 13900 = 1629 := by
  have h := countSmall_add 0 13800 100
  rw [countUp_13800, chunk_138] at h
  simpa using h
lemma countUp_14000 : countSmall 0 14000 = 1640 := by
  have h := countSmall_add 0 13900 100
  rw [countUp_13900, chunk_139] at h
  simpa using h
lemma countUp_14100 : countSmall 0 14100 = 1651 := by
  have h := countSmall_add 0 14000 100
  rw [countUp_14000, chunk_140] at h
  simpa using h
lemma countUp_14200 : countSmall 0 14200 = 1660 := by
  have h := countSmall_add 0 14100 100
  rw [countUp_14100, chunk_141] at h
  simpa using h
lemma countUp_14300 : countSmall 0 14300 = 1668 := by
  have h := countSmall_add 0 14200 100
  rw [countUp_14200, chunk_142] at h
  simpa using h
lemma countUp_14400 : countSmall 0 14400 = 1679 := by
  have h := countSmall_add 0 14300 100
  rw [countUp_14300, chunk_143] at h
  simpa using h
lemma countUp_14500 : countSmall 0 14500 = 1691 := by
  have h := countSmall_add 0 14400 100
  rw [countUp_14400, chunk_144] at h
  simpa using h
lemma countUp_14600 : countSmall 0 14600 = 1703 := by
  have h := countSmall_add 0 14500 100
  rw [countUp_14500, chunk_145] at h
  simpa using h
lemma countUp_14700 : countSmall 0 14700 = 1714 := by
  have h := countSmall_add 0 14600 100
  rw [countUp_14600, chunk_146] at h
  simpa using h
lemma countUp_14800 : countSmall 0 14800 = 1728 := by
  have h := countSmall_add 0 14700 100
  rw [countUp_14700, chunk_147] at h
  simpa using h
lemma countUp_14900 : countSmall 0 14900 = 1742 := by
  have h := countSmall_add 0 14800 100
  rw [countUp_14800, chunk_148] at h
  simpa using h
lemma countUp_15000 : countSmall 0 15000 = 1751 := by
  have h := countSmall_add 0 14900 100
  rw [countUp_14900, chunk_149] at h
  simpa using h
lemma countUp_15100 : countSmall 0 15100 = 1760 := by
  have h := countSmall_add 0 15000 100
  rw [countUp_15000, chunk_150] at h
  simpa using h
lemma countUp_15200 : countSmall 0 15200 = 1773 := by
  have h := countSmall_add 0 15100 100
  rw [countUp_15100, chunk_151] at h
  simpa using h
lemma countUp_15300 : countSmall 0 15300 = 1785 := by
  have h := countSmall_add 0 15200 100
  rw [countUp_15200, chunk_152] at h
  simpa using h
lemma countUp_15400 : countSmall 0 15400 = 1798 := by
  have h := countSmall_add 0 15300 100
  rw [countUp_15300, chunk_153] at h
  simpa using h
lemma countUp_15500 : countSmall 0 15500 = 1810 := by
  have h := countSmall_add 0 15400 100
  rw [countUp_15400, chunk_154] at h
  simpa using h
lemma countUp_15600 : countSmall 0 15600 = 1819 := by
  have h := countSmall_add 0 15500 100
  rw [countUp_15500, chunk_155] at h
  simpa using h
lemma countUp_15700 : countSmall 0 15700 = 1832 := by
  have h := countSmall_add 0 15600 100
  rw [countUp_15600, chunk_156] at h
  simpa using h
lemma countUp_15800 : countSmall 0 15800 = 1845 := by
  have h := countSmall_add 0 15700 100
  rw [countUp_15700, chunk_157] at h
  simpa using h
lemma countUp_15900 : countSmall 0 15900 = 1854 := by
  have h := countSmall_add 0 15800 100
  rw [countUp_15800, chunk_158] at h
  simpa using h
lemma countUp_16000 : countSmall 0 16000 = 1865 := by
  have h := countSmall_add 0 15900 100
  rw [countUp_15900, chunk_159] at h
  simpa using h
lemma countUp_16100 : countSmall 0 16100 = 1877 := by
  have h := countSmall_add 0 16000 100
  rw [countUp_16000, chunk_160] at h
  simpa using h
lemma countUp_16200 : countSmall 0 16200 = 1889 := by
  have h := countSmall_add 0 16100 100
  rw [countUp_16100, chunk_161] at h
  simpa using h
lemma countUp_16300 : countSmall 0 16300 = 1898 := by
  have h := countSmall_add 0 16200 100
  rw [countUp_16200, chunk_162] at h
  simpa using h
lemma countUp_16400 : countSmall 0 16400 = 1907 := by
  have h := countSmall_add 0 16300 100
  rw [countUp_16300, chunk_163] at h
  simpa using h
lemma countUp_16500 : countSmall 0 16500 = 1920 := by
  have h := countSmall_add 0 16400 100
  rw [countUp_16400, chunk_164] at h
  simpa using h
lemma countUp_16600 : countSmall 0 16600 = 1927 := by
  have h := countSmall_add 0 16500 100
  rw [countUp_16500, chunk_165] at h
  simpa using h
lemma countUp_16700 : countSmall 0 16700 = 1941 := by
  have h := countSmall_add 0 16600 100
  rw [countUp_16600, chunk_166] at h
  simpa using h
lemma countUp_16800 : countSmall 0 16800 = 1950 := by
  have h := countSmall_add 0 16700 100
  rw [countUp_16700, chunk_167] at h
  simpa using h
lemma countUp_16900 : countSmall 0 16900 = 1960 := by
  have h := countSmall_add 0 16800 100
  rw [countUp_16800, chunk_168] at h
  simpa using h
lemma countUp_17000 : countSmall 0 17000 = 1972 := by
  have h := countSmall_add 0 16900 100
  rw [countUp_16900, chunk_169] at h
  simpa using h
lemma countUp_17100 : countSmall 0 17100 = 1984 := by
  have h := countSmall_add 0 17000 100
  rw [countUp_17000, chunk_170] at h
  simpa using h
lemma countUp_17200 : countSmall 0 17200 = 1995 := by
  have h := countSmall_add 0 17100 100
  rw [countUp_17100, chunk_171] at h
  simpa using h
lemma countUp_17300 : countSmall 0 17300 = 2005 := by
  have h := countSmall_add 0 17200 100
  rw [countUp_17200, chunk_172] at h
  simpa using h
lemma countUp_17400 : countSmall 0 17400 = 2018 := by
  have h := countSmall_add 0 17300 100
  rw [countUp_17300, chunk_173] at h
  simpa using h
lemma countUp_17500 : countSmall 0 17500 = 2032 := by
  have h := countSmall_add 0 17400 100
  rw [countUp_17400, chunk_174] at h
  simpa using h
lemma countUp_17600 : countSmall 0 17600 = 2042 := by
  have h := countSmall_add 0 17500 100
  rw [countUp_17500, chunk_175] at h
  simpa using h
lemma countUp_17700 : countSmall 0 17700 = 2051 := by
  have h := countSmall_add 0 17600 100
  rw [countUp_17600, chunk_176] at h
  simpa using h
lemma countUp_17800 : countSmall 0 17800 = 2063 := by
  have h := countSmall_add 0 17700 100
  rw [countUp_17700, chunk_177] at h
  simpa using h
lemma countUp_17900 : countSmall 0 17900 = 2073 := by
  have h := countSmall_add 0 17800 100
  rw [countUp_17800, chunk_178] at h
  simpa using h
lemma countUp_18000 : countSmall 0 18000 = 2088 := by
  have h := countSmall_add 0 17900 100
  rw [countUp_17900, chunk_179] at h
  simpa using h
lemma countUp_18100 : countSmall 0 18100 = 2098 := by
  have h := countSmall_add 0 18000 100
  rw [countUp_18000, chunk_180] at h
  simpa using h
lemma countUp_18200 : countSmall 0 18200 = 2109 := by
  have h := countSmall_add 0 18100 100
  rw [countUp_18100, chunk_181] at h
  simpa using h
lemma countUp_18300 : countSmall 0 18300 = 2122 := by
  have h := countSmall_add 0 18200 100
  rw [countUp_18200, chunk_182] at h
  simpa using h
lemma countUp_18400 : countSmall 0 18400 = 2133 := by
  have h := countSmall_add 0 18300 100
  rw [countUp_18300, chunk_183] at h
  simpa using h
lemma countUp_18500 : countSmall 0 18500 = 2146 := by
  have h := countSmall_add 0 18400 100
  rw [countUp_18400, chunk_184] at h
  simpa using h
lemma countUp_18600 : countSmall 0 18600 = 2157 := by
  have h := countSmall_add 0 18500 100
  rw [countUp_18500, chunk_185] at h
  simpa using h
lemma countUp_18700 : countSmall 0 18700 = 2164 := by
  have h := countSmall_add 0 18600 100
  rw [countUp_18600, chunk_186] at h
  simpa using h
lemma countUp_18800 : countSmall 0 18800 = 2176 := by
  have h := countSmall_add 0 18700 100
  rw [countUp_18700, chunk_187] at h
  simpa using h
lemma countUp_18900 : countSmall 0 18900 = 2183 := by
  have h := countSmall_add 0 18800 100
  rw [countUp_18800, chunk_188] at h
  simpa using h
lemma countUp_19000 : countSmall 0 19000 = 2192 := by
  have h := countSmall_add 0 18900 100
  rw [countUp_18900, chunk_189] at h
  simpa using h
lemma countUp_19100 : countSmall 0 19100 = 2204 := by
  have h := countSmall_add 0 19000 100
  rw [countUp_19000, chunk_190] at h
  simpa using h
lemma countUp_19200 : countSmall 0 19200 = 2213 := by
  have h := countSmall_add 0 19100 100
  rw [countUp_19100, chunk_191] at h
  simpa using h
lemma countUp_19300 : countSmall 0 19300 = 2224 := by
  have h := countSmall_add 0 19200 100
  rw [countUp_19200, chunk_192] at h
  simpa using h
lemma countUp_19400 : countSmall 0 19400 = 2235 := by
  have h := countSmall_add 0 19300 100
  rw [countUp_19300, chunk_193] at h
  simpa using h
lemma countUp_19500 : countSmall 0 19500 = 2251 := by
  have h := countSmall_add 0 19400 100
  rw [countUp_19400, chunk_194] at h
  simpa using h
lemma countUp_19600 : countSmall 0 19600 = 2265 := by
  have h := countSmall_add 0 19500 100
  rw [countUp_19500, chunk_195] at h
  simpa using h
lemma countUp_19700 : countSmall 0 19700 = 2273 := by
  have h := countSmall_add 0 19600 100
  rw [countUp_19600, chunk_196] at h
  simpa using h
lemma countUp_19800 : countSmall 0 19800 = 2285 := by
  have h := countSmall_add 0 19700 100
  rw [countUp_19700, chunk_197] at h
  simpa using h
lemma countUp_19900 : countSmall 0 19900 = 2296 := by
  have h := countSmall_add 0 19800 100
  rw [countUp_19800, chunk_198] at h
  simpa using h
lemma countUp_20000 : countSmall 0 20000 = 2309 := by
  have h := countSmall_add 0 19900 100
  rw [countUp_19900, chunk_199] at h
  simpa using h
lemma countUp_20100 : countSmall 0 20100 = 2318 := by
  have h := countSmall_add 0 20000 100
  rw [countUp_20000, chunk_200] at h
  simpa using h
lemma countUp_20200 : countSmall 0 20200 = 2331 := by
  have h := countSmall_add 0 20100 100
  rw [countUp_20100, chunk_201] at h
  simpa using h
lemma countUp_20300 : countSmall 0 20300 = 2342 := by
  have h := countSmall_add 0 20200 100
  rw [countUp_20200, chunk_202] at h
  simpa using h
lemma countUp_20400 : countSmall 0 20400 = 2354 := by
  have h := countSmall_add 0 20300 100
  rw [countUp_20300, chunk_203] at h
  simpa using h
lemma countUp_20500 : countSmall 0 20500 = 2366 := by
  have h := countSmall_add 0 20400 100
  rw [countUp_20400, chunk_204] at h
  simpa using h
lemma countUp_20600 : countSmall 0 20600 = 2377 := by
  have h := countSmall_add 0 20500 100
  rw [countUp_20500, chunk_205] at h
  simpa using h
lemma countUp_20700 : countSmall 0 20700 = 2386 := by
  have h := countSmall_add 0 20600 100
  rw [countUp_20600, chunk_206] at h
  simpa using h
lemma countUp_20800 : countSmall 0 20800 = 2400 := by
  have h := countSmall_add 0 20700 100
  rw [countUp_20700, chunk_207] at h
  simpa using h
lemma countUp_20900 : countSmall 0 20900 = 2410 := by
  have h := countSmall_add 0 20800 100
  rw [countUp_20800, chunk_208] at h
  simpa using h
lemma countUp_21000 : countSmall 0 21000 = 2420 := by
  have h := countSmall_add 0 20900 100
  rw [countUp_20900, chunk_209] at h
  simpa using h
lemma countUp_21100 : countSmall 0 21100 = 2433 := by
  have h := countSmall_add 0 21000 100
  rw [countUp_21000, chunk_210] at h
  simpa using h
lemma countUp_21200 : countSmall 0 21200 = 2446 := by
  have h := countSmall_add 0 21100 100
  rw [countUp_21100, chunk_211] at h
  simpa using h
lemma countUp_21300 : countSmall 0 21300 = 2455 := by
  have h := countSmall_add 0 21200 100
  rw [countUp_21200, chunk_212] at h
  simpa using h
lemma countUp_21400 : countSmall 0 21400 = 2467 := by
  have h := countSmall_add 0 21300 100
  rw [countUp_21300, chunk_213] at h
  simpa using h
lemma countUp_21500 : countSmall 0 21500 = 2478 := by
  have h := countSmall_add 0 21400 100
  rw [countUp_21400, chunk_214] at h
  simpa using h
lemma countUp_21600 : countSmall 0 21600 = 2493 := by
  have h := countSmall_add 0 21500 100
  rw [countUp_21500, chunk_215] at h
  simpa using h
lemma countUp_21700 : countSmall 0 21700 = 2503 := by
  have h := countSmall_add 0 21600 100
  rw [countUp_21600, chunk_216] at h
  simpa using h
lemma countUp_21800 : countSmall 0 21800 = 2515 := by
  have h := countSmall_add 0 21700 100
  rw [countUp_21700, chunk_217] at h
  simpa using h
lemma countUp_21900 : countSmall 0 21900 = 2529 := by
  have h := countSmall_add 0 21800 100
  rw [countUp_21800, chunk_218] at h
  simpa using h
lemma countUp_22000 : countSmall 0 22000 = 2538 := by
  have h := countSmall_add 0 21900 100
  rw [countUp_21900, chunk_219] at h
  simpa using h
lemma countUp_22100 : countSmall 0 22100 = 2551 := by
  have h := countSmall_add 0 22000 100
  rw [countUp_22000, chunk_220] at h
  simpa using h
lemma countUp_22200 : countSmall 0 22200 = 2563 := by
  have h := countSmall_add 0 22100 100
  rw [countUp_22100, chunk_221] at h
  simpa using h
lemma countUp_22300 : countSmall 0 22300 = 2574 := by
  have h := countSmall_add 0 22200 100
  rw [countUp_22200, chunk_222] at h
  simpa using h
lemma countUp_22400 : countSmall 0 22400 = 2584 := by
  have h := countSmall_add 0 22300 100
  rw [countUp_22300, chunk_223] at h
  simpa using h
lemma countUp_22500 : countSmall 0 22500 = 2594 := by
  have h := countSmall_add 0 22400 100
  rw [countUp_22400, chunk_224] at h
  simpa using h
lemma countUp_22600 : countSmall 0 22600 = 2604 := by
  have h := countSmall_add 0 22500 100
  rw [countUp_22500, chunk_225] at h
  simpa using h
lemma countUp_22700 : countSmall 0 22700 = 2618 := by
  have h := countSmall_add 0 22600 100
  rw [countUp_22600, chunk_226] at h
  simpa using h
lemma countUp_22800 : countSmall 0 22800 = 2630 := by
  have h := countSmall_add 0 22700 100
  rw [countUp_22700, chunk_227] at h
  simpa using h
lemma countUp_22900 : countSmall 0 22900 = 2640 := by
  have h := countSmall_add 0 22800 100
  rw [countUp_22800, chunk_228] at h
  simpa using h
lemma countUp_23000 : countSmall 0 23000 = 2652 := by
  have h := countSmall_add 0 22900 100
  rw [countUp_22900, chunk_229] at h
  simpa using h
lemma countUp_23100 : countSmall 0 23100 = 2668 := by
  have h := countSmall_add 0 23000 100
  rw [countUp_23000, chunk_230] at h
  simpa using h
lemma countUp_23200 : countSmall 0 23200 = 2676 := by
  have h := countSmall_add 0 23100 100
  rw [countUp_23100, chunk_231] at h
  simpa using h
lemma countUp_23300 : countSmall 0 23300 = 2687 := by
  have h := countSmall_add 0 23200 100
  rw [countUp_23200, chunk_232] at h
  simpa using h
lemma countUp_23400 : countSmall 0 23400 = 2698 := by
  have h := countSmall_add 0 23300 100
  rw [countUp_23300, chunk_233] at h
  simpa using h
lemma countUp_23500 : countSmall 0 23500 = 2705 := by
  have h := countSmall_add 0 23400 100
  rw [countUp_23400, chunk_234] at h
  simpa using h
lemma countUp_23600 : countSmall 0 23600 = 2718 := by
  have h := countSmall_add 0 23500 100
  rw [countUp_23500, chunk_235] at h
  simpa using h
lemma countUp_23700 : countSmall 0 23700 = 2730 := by
  have h := countSmall_add 0 23600 100
  rw [countUp_23600, chunk_236] at h
  simpa using h
lemma countUp_23800 : countSmall 0 23800 = 2742 := by
  have h := countSmall_add 0 23700 100
  rw [countUp_23700, chunk_237] at h
  simpa using h
lemma countUp_23900 : countSmall 0 23900 = 2757 := by
  have h := countSmall_add 0 23800 100
  rw [countUp_23800, chunk_238] at h
  simpa using h
lemma countUp_24000 : countSmall 0 24000 = 2767 := by
  have h := countSmall_add 0 23900 100
  rw [countUp_23900, chunk_239] at h
  simpa using h
lemma countUp_24100 : countSmall 0 24100 = 2781 := by
  have h := countSmall_add 0 24000 100
  rw [countUp_24000, chunk_240] at h
  simpa using h
lemma countUp_24200 : countSmall 0 24200 = 2793 := by
  have h := countSmall_add 0 24100 100
  rw [countUp_24100, chunk_241] at h
  simpa using h
lemma countUp_24300 : countSmall 0 24300 = 2803 := by
  have h := countSmall_add 0 24200 100
  rw [countUp_24200, chunk_242] at h
  simpa using h
lemma countUp_24400 : countSmall 0 24400 = 2812 := by
  have h := countSmall_add 0 24300 100
  rw [countUp_24300, chunk_243] at h
  simpa using h
lemma countUp_24500 : countSmall 0 24500 = 2822 := by
  have h := countSmall_add 0 24400 100
  rw [countUp_24400, chunk_244] at h
  simpa using h
lemma countUp_24600 : countSmall 0 24600 = 2833 := by
  have h := countSmall_add 0 24500 100
  rw [countUp_24500, chunk_245] at h
  simpa using h
lemma countUp_24700 : countSmall 0 24700 = 2845 := by
  have h := countSmall_add 0 24600 100
  rw [countUp_24600, chunk_246] at h
  simpa using h
lemma countUp_24800 : countSmall 0 24800 = 2855 := by
  have h := countSmall_add 0 24700 100
  rw [countUp_24700, chunk_247] at h
  simpa using h
lemma countUp_24900 : countSmall 0 24900 = 2866 := by
  have h := countSmall_add 0 24800 100
  rw [countUp_24800, chunk_248] at h
  simpa using h
lemma countUp_25000 : countSmall 0 25000 = 2879 := by
  have h := countSmall_add 0 24900 100
  rw [countUp_24900, chunk_249] at h
  simpa using h
lemma countUp_25100 : countSmall 0 25100 = 2889 := by
  have h := countSmall_add 0 25000 100
  rw [countUp_25000, chunk_250] at h
  simpa using h
lemma countUp_25200 : countSmall 0 25200 = 2902 := by
  have h := countSmall_add 0 25100 100
  rw [countUp_25100, chunk_251] at h
  simpa using h
lemma countUp_25300 : countSmall 0 25300 = 2912 := by
  have h := countSmall_add 0 25200 100
  rw [countUp_25200, chunk_252] at h
  simpa using h
lemma countUp_25400 : countSmall 0 25400 = 2925 := by
  have h := countSmall_add 0 25300 100
  rw [countUp_25300, chunk_253] at h
  simpa using h
lemma countUp_25500 : countSmall 0 25500 = 2935 := by
  have h := countSmall_add 0 25400 100
  rw [countUp_25400, chunk_254] at h
  simpa using h
lemma countUp_25600 : countSmall 0 25600 = 2945 := by
  have h := countSmall_add 0 25500 100
  rw [countUp_25500, chunk_255] at h
  simpa using h
lemma countUp_25700 : countSmall 0 25700 = 2958 := by
  have h := countSmall_add 0 25600 100
  rw [countUp_25600, chunk_256] at h
  simpa using h
lemma countUp_25800 : countSmall 0 25800 = 2970 := by
  have h := countSmall_add 0 25700 100
  rw [countUp_25700, chunk_257] at h
  simpa using h
lemma countUp_25900 : countSmall 0 25900 = 2981 := by
  have h := countSmall_add 0 25800 100
  rw [countUp_25800, chunk_258] at h
  simpa using h
lemma countUp_26000 : countSmall 0 26000 = 2993 := by
  have h := countSmall_add 0 25900 100
  rw [countUp_25900, chunk_259] at h
  simpa using h
lemma countUp_26100 : countSmall 0 26100 = 3003 := by
  have h := countSmall_add 0 26000 100
  rw [countUp_26000, chunk_260] at h
  simpa using h
lemma countUp_26200 : countSmall 0 26200 = 3016 := by
  have h := countSmall_add 0 26100 100
  rw [countUp_26100, chunk_261] at h
  simpa using h
lemma countUp_26300 : countSmall 0 26300 = 3029 := by
  have h := countSmall_add 0 26200 100
  rw [countUp_26200, chunk_262] at h
  simpa using h
lemma countUp_26400 : countSmall 0 26400 = 3040 := by
  have h := countSmall_add 0 26300 100
  rw [countUp_26300, chunk_263] at h
  simpa using h
lemma countUp_26500 : countSmall 0 26500 = 3052 := by
  have h := countSmall_add 0 26400 100
  rw [countUp_26400, chunk_264] at h
  simpa using h
lemma countUp_26600 : countSmall 0 26600 = 3062 := by
  have h := countSmall_add 0 26500 100
  rw [countUp_26500, chunk_265] at h
  simpa using h
lemma countUp_26700 : countSmall 0 26700 = 3073 := by
  have h := countSmall_add 0 26600 100
  rw [countUp_26600, chunk_266] at h
  simpa using h
lemma countUp_26800 : countSmall 0 26800 = 3085 := by
  have h := countSmall_add 0 26700 100
  rw [countUp_26700, chunk_267] at h
  simpa using h
lemma countUp_26900 : countSmall 0 26900 = 3099 := by
  have h := countSmall_add 0 26800 100
  rw [countUp_26800, chunk_268] at h
  simpa using h
lemma countUp_27000 : countSmall 0 27000 = 3111 := by
  have h := countSmall_add 0 26900 100
  rw [countUp_26900, chunk_269] at h
  simpa using h
lemma countUp_27100 : countSmall 0 27100 = 3124 := by
  have h := countSmall_add 0 27000 100
  rw [countUp_27000, chunk_270] at h
  simpa using h
lemma countUp_27200 : countSmall 0 27200 = 3133 := by
  have h := countSmall_add 0 27100 100
  rw [countUp_27100, chunk_271] at h
  simpa using h
lemma countUp_27300 : countSmall 0 27300 = 3146 := by
  have h := countSmall_add 0 27200 100
  rw [countUp_27200, chunk_272] at h
  simpa using h
lemma countUp_27400 : countSmall 0 27400 = 3154 := by
  have h := countSmall_add 0 27300 100
  rw [countUp_27300, chunk_273] at h
  simpa using h
lemma countUp_27500 : countSmall 0 27500 = 3165 := by
  have h := countSmall_add 0 27400 100
  rw [countUp_27400, chunk_274] at h
  simpa using h
lemma countUp_27600 : countSmall 0 27600 = 3173 := by
  have h := countSmall_add 0 27500 100
  rw [countUp_27500, chunk_275] at h
  simpa using h
lemma countUp_27700 : countSmall 0 27700 = 3184 := by
  have h := countSmall_add 0 27600 100
  rw [countUp_27600, chunk_276] at h
  simpa using h
lemma countUp_27800 : countSmall 0 27800 = 3199 := by
  have h := countSmall_add 0 27700 100
  rw [countUp_27700, chunk_277] at h
  simpa using h
lemma countUp_27900 : countSmall 0 27900 = 3209 := by
  have h := countSmall_add 0 27800 100
  rw [countUp_27800, chunk_278] at h
  simpa using h
lemma countUp_28000 : countSmall 0 28000 = 3221 := by
  have h := countSmall_add 0 27900 100
  rw [countUp_27900, chunk_279] at h
  simpa using h
lemma countUp_28100 : countSmall 0 28100 = 3233 := by
  have h := countSmall_add 0 28000 100
  rw [countUp_28000, chunk_280] at h
  simpa using h
lemma countUp_28200 : countSmall 0 28200 = 3243 := by
  have h := countSmall_add 0 28100 100
  rw [countUp_28100, chunk_281] at h
  simpa using h
lemma countUp_28300 : countSmall 0 28300 = 3252 := by
  have h := countSmall_add 0 28200 100
  rw [countUp_28200, chunk_282] at h
  simpa using h
lemma countUp_28400 : countSmall 0 28400 = 3261 := by
  have h := countSmall_add 0 28300 100
  rw [countUp_28300, chunk_283] at h
  simpa using h
lemma countUp_28500 : countSmall 0 28500 = 3274 := by
  have h := countSmall_add 0 28400 100
  rw [countUp_28400, chunk_284] at h
  simpa using h
lemma countUp_28600 : countSmall 0 28600 = 3287 := by
  have h := countSmall_add 0 28500 100
  rw [countUp_28500, chunk_285] at h
  simpa using h
lemma countUp_28700 : countSmall 0 28700 = 3302 := by
  have h := countSmall_add 0 28600 100
  rw [countUp_28600, chunk_286] at h
  simpa using h
lemma countUp_28800 : countSmall 0 28800 = 3314 := by
  have h := countSmall_add 0 28700 100
  rw [countUp_28700, chunk_287] at h
  simpa using h
lemma countUp_28900 : countSmall 0 28900 = 3326 := by
  have h := countSmall_add 0 28800 100
  rw [countUp_28800, chunk_288] at h
  simpa using h
lemma countUp_29000 : countSmall 0 29000 = 3337 := by
  have h := countSmall_add 0 28900 100
  rw [countUp_28900, chunk_289] at h
  simpa using h
lemma countUp_29100 : countSmall 0 29100 = 3348 := by
  have h := countSmall_add 0 29000 100
  rw [countUp_29000, chunk_290] at h
  simpa using h
lemma countUp_29200 : countSmall 0 29200 = 3362 := by
  have h := countSmall_add 0 29100 100
  rw [countUp_29100, chunk_291] at h
  simpa using h
lemma countUp_29300 : countSmall 0 29300 = 3373 := by
  have h := countSmall_add 0 29200 100
  rw [countUp_29200, chunk_292] at h
  simpa using h
lemma countUp_29400 : countSmall 0 29400 = 3387 := by
  have h := countSmall_add 0 29300 100
  rw [countUp_29300, chunk_293] at h
  simpa using h
lemma countUp_29500 : countSmall 0 29500 = 3396 := by
  have h := countSmall_add 0 29400 100
  rw [countUp_29400, chunk_294] at h
  simpa using h
lemma countUp_29600 : countSmall 0 29600 = 3409 := by
  have h := countSmall_add 0 29500 100
  rw [countUp_29500, chunk_295] at h
  simpa using h
lemma countUp_29700 : countSmall 0 29700 = 3419 := by
  have h := countSmall_add 0 29600 100
  rw [countUp_29600, chunk_296] at h
  simpa using h
lemma countUp_29800 : countSmall 0 29800 = 3429 := by
  have h := countSmall_add 0 29700 100
  rw [countUp_29700, chunk_297] at h
  simpa using h
lemma countUp_29900 : countSmall 0 29900 = 3440 := by
  have h := countSmall_add 0 29800 100
  rw [countUp_29800, chunk_298] at h
  simpa using h
lemma countUp_30000 : countSmall 0 30000 = 3450 := by
  have h := countSmall_add 0 29900 100
  rw [countUp_29900, chunk_299] at h
  simpa using h
lemma countUp_30100 : countSmall 0 30100 = 3461 := by
  have h := countSmall_add 0 30000 100
  rw [countUp_30000, chunk_300] at h
  simpa using h
lemma countUp_30200 : countSmall 0 30200 = 3475 := by
  have h := countSmall_add 0 30100 100
  rw [countUp_30100, chunk_301] at h
  simpa using h
lemma countUp_30300 : countSmall 0 30300 = 3486 := by
  have h := countSmall_add 0 30200 100
  rw [countUp_30200, chunk_302] at h
  simpa using h
lemma countUp_30400 : countSmall 0 30400 = 3498 := by
  have h := countSmall_add 0 30300 100
  rw [countUp_30300, chunk_303] at h
  simpa using h
lemma countUp_30500 : countSmall 0 30500 = 3507 := by
  have h := countSmall_add 0 30400 100
  rw [countUp_30400, chunk_304] at h
  simpa using h
lemma countUp_30600 : countSmall 0 30600 = 3518 := by
  have h := countSmall_add 0 30500 100
  rw [countUp_30500, chunk_305] at h
  simpa using h
lemma countUp_30700 : countSmall 0 30700 = 3530 := by
  have h := countSmall_add 0 30600 100
  rw [countUp_30600, chunk_306] at h
  simpa using h
lemma countUp_30800 : countSmall 0 30800 = 3538 := by
  have h := countSmall_add 0 30700 100
  rw [countUp_30700, chunk_307] at h
  simpa using h
lemma countUp_30900 : countSmall 0 30900 = 3552 := by
  have h := countSmall_add 0 30800 100
  rw [countUp_30800, chunk_308] at h
  simpa using h
lemma countUp_31000 : countSmall 0 31000 = 3563 := by
  have h := countSmall_add 0 30900 100
  rw [countUp_30900, chunk_309] at h
  simpa using h
lemma countUp_31100 : countSmall 0 31100 = 3574 := by
  have h := countSmall_add 0 31000 100
  rw [countUp_31000, chunk_310] at h
  simpa using h
lemma countUp_31200 : countSmall 0 31200 = 3587 := by
  have h := countSmall_add 0 31100 100
  rw [countUp_31100, chunk_311] at h
  simpa using h
lemma countUp_31300 : countSmall 0 31300 = 3599 := by
  have h := countSmall_add 0 31200 100
  rw [countUp_31200, chunk_312] at h
  simpa using h
lemma countUp_31400 : countSmall 0 31400 = 3616 := by
  have h := countSmall_add 0 31300 100
  rw [countUp_31300, chunk_313] at h
  simpa using h
lemma countUp_31500 : countSmall 0 31500 = 3622 := by
  have h := countSmall_add 0 31400 100
  rw [countUp_31400, chunk_314] at h
  simpa using h
lemma countUp_31600 : countSmall 0 31600 = 3634 := by
  have h := countSmall_add 0 31500 100
  rw [countUp_31500, chunk_315] at h
  simpa using h
lemma countUp_31700 : countSmall 0 31700 = 3645 := by
  have h := countSmall_add 0 31600 100
  rw [countUp_31600, chunk_316] at h
  simpa using h
lemma countUp_31800 : countSmall 0 31800 = 3656 := by
  have h := countSmall_add 0 31700 100
  rw [countUp_31700, chunk_317] at h
  simpa using h
lemma countUp_31900 : countSmall 0 31900 = 3667 := by
  have h := countSmall_add 0 31800 100
  rw [countUp_31800, chunk_318] at h
  simpa using h
lemma countUp_32000 : countSmall 0 32000 = 3676 := by
  have h := countSmall_add 0 31900 100
  rw [countUp_31900, chunk_319] at h
  simpa using h
lemma countUp_32100 : countSmall 0 32100 = 3691 := by
  have h := countSmall_add 0 32000 100
  rw [countUp_32000, chunk_320] at h
  simpa using h
lemma countUp_32200 : countSmall 0 32200 = 3701 := by
  have h := countSmall_add 0 32100 100
  rw [countUp_32100, chunk_321] at h
  simpa using h
lemma countUp_32300 : countSmall 0 32300 = 3712 := by
  have h := countSmall_add 0 32200 100
  rw [countUp_32200, chunk_322] at h
  simpa using h
lemma countUp_32400 : countSmall 0 32400 = 3727 := by
  have h := countSmall_add 0 32300 100
  rw [countUp_32300, chunk_323] at h
  simpa using h
lemma countUp_32500 : countSmall 0 32500 = 3739 := by
  have h := countSmall_add 0 32400 100
  rw [countUp_32400, chunk_324] at h
  simpa using h
lemma countUp_32600 : countSmall 0 32600 = 3750 := by
  have h := countSmall_add 0 32500 100
  rw [countUp_32500, chunk_325] at h
  simpa using h
lemma countUp_32700 : countSmall 0 32700 = 3761 := by
  have h := countSmall_add 0 32600 100
  rw [countUp_32600, chunk_326] at h
  simpa using h
lemma countUp_32800 : countSmall 0 32800 = 3773 := by
  have h := countSmall_add 0 32700 100
  rw [countUp_32700, chunk_327] at h
  simpa using h
lemma countUp_32900 : countSmall 0 32900 = 3784 := by
  have h := countSmall_add 0 32800 100
  rw [countUp_32800, chunk_328] at h
  simpa using h
lemma countUp_33000 : countSmall 0 33000 = 3797 := by
  have h := countSmall_add 0 32900 100
  rw [countUp_32900, chunk_329] at h
  simpa using h
lemma countUp_33100 : countSmall 0 33100 = 3809 := by
  have h := countSmall_add 0 33000 100
  rw [countUp_33000, chunk_330] at h
  simpa using h
lemma countUp_33200 : countSmall 0 33200 = 3821 := by
  have h := countSmall_add 0 33100 100
  rw [countUp_33100, chunk_331] at h
  simpa using h
lemma countUp_33300 : countSmall 0 33300 = 3831 := by
  have h := countSmall_add 0 33200 100
  rw [countUp_33200, chunk_332] at h
  simpa using h
lemma countUp_33400 : countSmall 0 33400 = 3844 := by
  have h := countSmall_add 0 33300 100
  rw [countUp_33300, chunk_333] at h
  simpa using h
lemma countUp_33500 : countSmall 0 33500 = 3858 := by
  have h := countSmall_add 0 33400 100
  rw [countUp_33400, chunk_334] at h
  simpa using h
lemma countUp_33600 : countSmall 0 33600 = 3870 := by
  have h := countSmall_add 0 33500 100
  rw [countUp_33500, chunk_335] at h
  simpa using h
lemma countUp_33700 : countSmall 0 33700 = 3882 := by
  have h := countSmall_add 0 33600 100
  rw [countUp_33600, chunk_336] at h
  simpa using h
lemma countUp_33800 : countSmall 0 33800 = 3894 := by
  have h := countSmall_add 0 33700 100
  rw [countUp_33700, chunk_337] at h
  simpa using h
lemma countUp_33900 : countSmall 0 33900 = 3906 := by
  have h := countSmall_add 0 33800 100
  rw [countUp_33800, chunk_338] at h
  simpa using h
lemma countUp_34000 : countSmall 0 34000 = 3915 := by
  have h := countSmall_add 0 33900 100
  rw [countUp_33900, chunk_339] at h
  simpa using h
lemma countUp_34100 : countSmall 0 34100 = 3923 := by
  have h := countSmall_add 0 34000 100
  rw [countUp_34000, chunk_340] at h
  simpa using h
lemma countUp_34200 : countSmall 0 34200 = 3936 := by
  have h := countSmall_add 0 34100 100
  rw [countUp_34100, chunk_341] at h
  simpa using h
lemma countUp_34300 : countSmall 0 34300 = 3948 := by
  have h := countSmall_add 0 34200 100
  rw [countUp_34200, chunk_342] at h
  simpa using h
lemma countUp_34400 : countSmall 0 34400 = 3961 := by
  have h := countSmall_add 0 34300 100
  rw [countUp_34300, chunk_343] at h
  simpa using h
lemma countUp_34500 : countSmall 0 34500 = 3974 := by
  have h := countSmall_add 0 34400 100
  rw [countUp_34400, chunk_344] at h
  simpa using h
lemma countUp_34600 : countSmall 0 34600 = 3988 := by
  have h := countSmall_add 0 34500 100
  rw [countUp_34500, chunk_345] at h
  simpa using h
lemma countUp_34700 : countSmall 0 34700 = 4000 := by
  have h := countSmall_add 0 34600 100
  rw [countUp_34600, chunk_346] at h
  simpa using h
lemma countUp_34800 : countSmall 0 34800 = 4011 := by
  have h := countSmall_add 0 34700 100
  rw [countUp_34700, chunk_347] at h
  simpa using h
lemma countUp_34900 : countSmall 0 34900 = 4022 := by
  have h := countSmall_add 0 34800 100
  rw [countUp_34800, chunk_348] at h
  simpa using h
lemma countUp_35000 : countSmall 0 35000 = 4030 := by
  have h := countSmall_add 0 34900 100
  rw [countUp_34900, chunk_349] at h
  simpa using h
lemma countUp_35100 : countSmall 0 35100 = 4041 := by
  have h := countSmall_add 0 35000 100
  rw [countUp_35000, chunk_350] at h
  simpa using h
lemma countUp_35200 : countSmall 0 35200 = 4053 := by
  have h := countSmall_add 0 35100 100
  rw [countUp_35100, chunk_351] at h
  simpa using h
lemma countUp_35300 : countSmall 0 35300 = 4066 := by
  have h := countSmall_add 0 35200 100
  rw [countUp_35200, chunk_352] at h
  simpa using h
lemma countUp_35400 : countSmall 0 35400 = 4076 := by
  have h := countSmall_add 0 35300 100
  rw [countUp_35300, chunk_353] at h
  simpa using h
lemma countUp_35500 : countSmall 0 35500 = 4086 := by
  have h := countSmall_add 0 35400 100
  rw [countUp_35400, chunk_354] at h
  simpa using h
lemma countUp_35600 : countSmall 0 35600 = 4100 := by
  have h := countSmall_add 0 35500 100
  rw [countUp_35500, chunk_355] at h
  simpa using h
lemma countUp_35700 : countSmall 0 35700 = 4109 := by
  have h := countSmall_add 0 35600 100
  rw [countUp_35600, chunk_356] at h
  simpa using h
lemma countUp_35800 : countSmall 0 35800 = 4118 := by
  have h := countSmall_add 0 35700 100
  rw [countUp_35700, chunk_357] at h
  simpa using h
lemma countUp_35900 : countSmall 0 35900 = 4131 := by
  have h := countSmall_add 0 35800 100
  rw [countUp_35800, chunk_358] at h
  simpa using h
lemma countUp_36000 : countSmall 0 36000 = 4145 := by
  have h := countSmall_add 0 35900 100
  rw [countUp_35900, chunk_359] at h
  simpa using h
lemma countUp_36100 : countSmall 0 36100 = 4160 := by
  have h := countSmall_add 0 36000 100
  rw [countUp_36000, chunk_360] at h
  simpa using h
lemma countUp_36200 : countSmall 0 36200 = 4168 := by
  have h := countSmall_add 0 36100 100
  rw [countUp_36100, chunk_361] at h
  simpa using h
lemma countUp_36300 : countSmall 0 36300 = 4179 := by
  have h := countSmall_add 0 36200 100
  rw [countUp_36200, chunk_362] at h
  simpa using h
lemma countUp_36400 : countSmall 0 36400 = 4191 := by
  have h := countSmall_add 0 36300 100
  rw [countUp_36300, chunk_363] at h
  simpa using h
lemma countUp_36500 : countSmall 0 36500 = 4201 := by
  have h := countSmall_add 0 36400 100
  rw [countUp_36400, chunk_364] at h
  simpa using h
lemma countUp_36600 : countSmall 0 36600 = 4215 := by
  have h := countSmall_add 0 36500 100
  rw [countUp_36500, chunk_365] at h
  simpa using h
lemma countUp_36700 : countSmall 0 36700 = 4225 := by
  have h := countSmall_add 0 36600 100
  rw [countUp_36600, chunk_366] at h
  simpa using h
lemma countUp_36800 : countSmall 0 36800 = 4238 := by
  have h := countSmall_add 0 36700 100
  rw [countUp_36700, chunk_367] at h
  simpa using h
lemma countUp_36900 : countSmall 0 36900 = 4250 := by
  have h := countSmall_add 0 36800 100
  rw [countUp_36800, chunk_368] at h
  simpa using h
lemma countUp_37000 : countSmall 0 37000 = 4262 := by
  have h := countSmall_add 0 36900 100
  rw [countUp_36900, chunk_369] at h
  simpa using h
lemma countUp_37100 : countSmall 0 37100 = 4274 := by
  have h := countSmall_add 0 37000 100
  rw [countUp_37000, chunk_370] at h
  simpa using h
lemma countUp_37200 : countSmall 0 37200 = 4284 := by
  have h := countSmall_add 0 37100 100
  rw [countUp_37100, chunk_371] at h
  simpa using h
lemma countUp_37300 : countSmall 0 37300 = 4294 := by
  have h := countSmall_add 0 37200 100
  rw [countUp_37200, chunk_372] at h
  simpa using h
lemma countUp_37400 : countSmall 0 37400 = 4310 := by
  have h := countSmall_add 0 37300 100
  rw [countUp_37300, chunk_373] at h
  simpa using h
lemma countUp_37500 : countSmall 0 37500 = 4319 := by
  have h := countSmall_add 0 37400 100
  rw [countUp_37400, chunk_374] at h
  simpa using h
lemma countUp_37600 : countSmall 0 37600 = 4335 := by
  have h := countSmall_add 0 37500 100
  rw [countUp_37500, chunk_375] at h
  simpa using h
lemma countUp_37700 : countSmall 0 37700 = 4347 := by
  have h := countSmall_add 0 37600 100
  rw [countUp_37600, chunk_376] at h
  simpa using h
lemma countUp_37745 : countSmall 0 37745 = 4348 := by
  have h := countSmall_add 0 37700 45
  rw [countUp_37700, chunk_377] at h
  simpa using h
lemma countUp_227 : countSmall 0 227 = 22 := by
  have h := countSmall_add 0 200 27
  have hc : countSmall 200 27 = 2 := by decide
  rw [countUp_200, hc] at h
  simpa using h
lemma countUp_277 : countSmall 0 277 = 32 := by
  have h := countSmall_add 0 200 77
  have hc : countSmall 200 77 = 12 := by decide
  rw [countUp_200, hc] at h
  simpa using h
lemma countUp_327 : countSmall 0 327 = 40 := by
  have h := countSmall_add 0 300 27
  have hc : countSmall 300 27 = 4 := by decide
  rw [countUp_300, hc] at h
  simpa using h
lemma countUp_377 : countSmall 0 377 = 48 := by
  have h := countSmall_add 0 300 77
  have hc : countSmall 300 77 = 12 := by decide
  rw [countUp_300, hc] at h
  simpa using h
lemma countUp_427 : countSmall 0 427 = 56 := by
  have h := countSmall_add 0 400 27
  have hc : countSmall 400 27 = 4 := by decide
  rw [countUp_400, hc] at h
  simpa using h
lemma countUp_477 : countSmall 0 477 = 65 := by
  have h := countSmall_add 0 400 77
  have hc : countSmall 400 77 = 13 := by decide
  rw [countUp_400, hc] at h
  simpa using h
lemma countUp_527 : countSmall 0 527 = 73 := by
  have h := countSmall_add 0 500 27
  have hc : countSmall 500 27 = 4 := by decide
  rw [countUp_500, hc] at h
  simpa using h
lemma countUp_577 : countSmall 0 577 = 79 := by
  have h := countSmall_add 0 500 77
  have hc : countSmall 500 77 = 10 := by decide
  rw [countUp_500, hc] at h
  simpa using h
lemma countUp_627 : countSmall 0 627 = 88 := by
  have h := countSmall_add 0 600 27
  have hc : countSmall 600 27 = 5 := by decide
  rw [countUp_600, hc] at h
  simpa using h
lemma countUp_677 : countSmall 0 677 = 96 := by
  have h := countSmall_add 0 600 77
  have hc : countSmall 600 77 = 13 := by decide
  rw [countUp_600, hc] at h
  simpa using h
lemma countUp_727 : countSmall 0 727 = 102 := by
  have h := countSmall_add 0 700 27
  have hc : countSmall 700 27 = 3 := by decide
  rw [countUp_700, hc] at h
  simpa using h
lemma countUp_777 : countSmall 0 777 = 111 := by
  have h := countSmall_add 0 700 77
  have hc : countSmall 700 77 = 12 := by decide
  rw [countUp_700, hc] at h
  simpa using h
lemma countUp_827 : countSmall 0 827 = 117 := by
  have h := countSmall_add 0 800 27
  have hc : countSmall 800 27 = 4 := by decide
  rw [countUp_800, hc] at h
  simpa using h
lemma countUp_877 : countSmall 0 877 = 124 := by
  have h := countSmall_add 0 800 77
  have hc : countSmall 800 77 = 11 := by decide
  rw [countUp_800, hc] at h
  simpa using h
lemma countUp_927 : countSmall 0 927 = 131 := by
  have h := countSmall_add 0 900 27
  have hc : countSmall 900 27 = 3 := by decide
  rw [countUp_900, hc] at h
  simpa using h
lemma countUp_977 : countSmall 0 977 = 138 := by
  have h := countSmall_add 0 900 77
  have hc : countSmall 900 77 = 10 := by decide
  rw [countUp_900, hc] at h
  simpa using h
lemma countUp_1027 : countSmall 0 1027 = 146 := by
  have h := countSmall_add 0 1000 27
  have hc : countSmall 1000 27 = 4 := by decide
  rw [countUp_1000, hc] at h
  simpa using h
lemma countUp_1077 : countSmall 0 1077 = 154 := by
  have h := countSmall_add 0 1000 77
  have hc : countSmall 1000 77 = 12 := by decide
  rw [countUp_1000, hc] at h
  simpa using h
lemma countUp_1127 : countSmall 0 1127 = 162 := by
  have h := countSmall_add 0 1100 27
  have hc : countSmall 1100 27 = 4 := by decide
  rw [countUp_1100, hc] at h
  simpa using h
lemma countUp_1177 : countSmall 0 1177 = 167 := by
  have h := countSmall_add 0 1100 77
  have hc : countSmall 1100 77 = 9 := by decide
  rw [countUp_1100, hc] at h
  simpa using h
lemma countUp_1227 : countSmall 0 1227 = 174 := by
  have h := countSmall_add 0 1200 27
  have hc : countSmall 1200 27 = 4 := by decide
  rw [countUp_1200, hc] at h
  simpa using h
lemma countUp_1277 : countSmall 0 1277 = 179 := by
  have h := countSmall_add 0 1200 77
  have hc : countSmall 1200 77 = 9 := by decide
  rw [countUp_1200, hc] at h
  simpa using h
lemma countUp_1327 : countSmall 0 1327 = 190 := by
  have h := countSmall_add 0 1300 27
  have hc : countSmall 1300 27 = 5 := by decide
  rw [countUp_1300, hc] at h
  simpa using h
lemma countUp_1377 : countSmall 0 1377 = 194 := by
  have h := countSmall_add 0 1300 77
  have hc : countSmall 1300 77 = 9 := by decide
  rw [countUp_1300, hc] at h
  simpa using h
lemma countUp_1427 : countSmall 0 1427 = 198 := by
  have h := countSmall_add 0 1400 27
  have hc : countSmall 1400 27 = 2 := by decide
  rw [countUp_1400, hc] at h
  simpa using h
lemma countUp_1477 : countSmall 0 1477 = 207 := by
  have h := countSmall_add 0 1400 77
  have hc : countSmall 1400 77 = 11 := by decide
  rw [countUp_1400, hc] at h
  simpa using h
lemma countUp_1527 : countSmall 0 1527 = 215 := by
  have h := countSmall_add 0 1500 27
  have hc : countSmall 1500 27 = 2 := by decide
  rw [countUp_1500, hc] at h
  simpa using h
lemma countUp_1577 : countSmall 0 1577 = 222 := by
  have h := countSmall_add 0 1500 77
  have hc : countSmall 1500 77 = 9 := by decide
  rw [countUp_1500, hc] at h
  simpa using h
lemma countUp_1627 : countSmall 0 1627 = 231 := by
  have h := countSmall_add 0 1600 27
  have hc : countSmall 1600 27 = 6 := by decide
  rw [countUp_1600, hc] at h
  simpa using h
lemma countUp_1677 : countSmall 0 1677 = 237 := by
  have h := countSmall_add 0 1600 77
  have hc : countSmall 1600 77 = 12 := by decide
  rw [countUp_1600, hc] at h
  simpa using h
lemma countUp_1727 : countSmall 0 1727 = 243 := by
  have h := countSmall_add 0 1700 27
  have hc : countSmall 1700 27 = 3 := by decide
  rw [countUp_1700, hc] at h
  simpa using h
lemma countUp_1777 : countSmall 0 1777 = 248 := by
  have h := countSmall_add 0 1700 77
  have hc : countSmall 1700 77 = 8 := by decide
  rw [countUp_1700, hc] at h
  simpa using h
lemma countUp_1827 : countSmall 0 1827 = 255 := by
  have h := countSmall_add 0 1800 27
  have hc : countSmall 1800 27 = 3 := by decide
  rw [countUp_1800, hc] at h
  simpa using h
lemma countUp_1877 : countSmall 0 1877 = 261 := by
  have h := countSmall_add 0 1800 77
  have hc : countSmall 1800 77 = 9 := by decide
  rw [countUp_1800, hc] at h
  simpa using h
lemma countUp_1927 : countSmall 0 1927 = 267 := by
  have h := countSmall_add 0 1900 27
  have hc : countSmall 1900 27 = 3 := by decide
  rw [countUp_1900, hc] at h
  simpa using h
lemma countUp_1977 : countSmall 0 1977 = 272 := by
  have h := countSmall_add 0 1900 77
  have hc : countSmall 1900 77 = 8 := by decide
  rw [countUp_1900, hc] at h
  simpa using h
lemma countUp_2027 : countSmall 0 2027 = 280 := by
  have h := countSmall_add 0 2000 27
  have hc : countSmall 2000 27 = 3 := by decide
  rw [countUp_2000, hc] at h
  simpa using h
lemma countUp_2077 : countSmall 0 2077 = 286 := by
  have h := countSmall_add 0 2000 77
  have hc : countSmall 2000 77 = 9 := by decide
  rw [countUp_2000, hc] at h
  simpa using h
lemma countUp_2127 : countSmall 0 2127 = 293 := by
  have h := countSmall_add 0 2100 27
  have hc : countSmall 2100 27 = 2 := by decide
  rw [countUp_2100, hc] at h
  simpa using h
lemma countUp_2177 : countSmall 0 2177 = 300 := by
  have h := countSmall_add 0 2100 77
  have hc : countSmall 2100 77 = 9 := by decide
  rw [countUp_2100, hc] at h
  simpa using h
lemma countUp_2227 : countSmall 0 2227 = 305 := by
  have h := countSmall_add 0 2200 27
  have hc : countSmall 2200 27 = 4 := by decide
  rw [countUp_2200, hc] at h
  simpa using h
lemma countUp_2277 : countSmall 0 2277 = 312 := by
  have h := countSmall_add 0 2200 77
  have hc : countSmall 2200 77 = 11 := by decide
  rw [countUp_2200, hc] at h
  simpa using h
lemma countUp_2327 : countSmall 0 2327 = 318 := by
  have h := countSmall_add 0 2300 27
  have hc : countSmall 2300 27 = 2 := by decide
  rw [countUp_2300, hc] at h
  simpa using h
lemma countUp_2377 : countSmall 0 2377 = 325 := by
  have h := countSmall_add 0 2300 77
  have hc : countSmall 2300 77 = 9 := by decide
  rw [countUp_2300, hc] at h
  simpa using h
lemma countUp_2427 : countSmall 0 2427 = 334 := by
  have h := countSmall_add 0 2400 27
  have hc : countSmall 2400 27 = 3 := by decide
  rw [countUp_2400, hc] at h
  simpa using h
lemma countUp_2477 : countSmall 0 2477 = 340 := by
  have h := countSmall_add 0 2400 77
  have hc : countSmall 2400 77 = 9 := by decide
  rw [countUp_2400, hc] at h
  simpa using h
lemma countUp_2527 : countSmall 0 2527 = 343 := by
  have h := countSmall_add 0 2500 27
  have hc : countSmall 2500 27 = 2 := by decide
  rw [countUp_2500, hc] at h
  simpa using h
lemma countUp_2577 : countSmall 0 2577 = 349 := by
  have h := countSmall_add 0 2500 77
  have hc : countSmall 2500 77 = 8 := by decide
  rw [countUp_2500, hc] at h
  simpa using h
lemma countUp_2627 : countSmall 0 2627 = 355 := by
  have h := countSmall_add 0 2600 27
  have hc : countSmall 2600 27 = 3 := by decide
  rw [countUp_2600, hc] at h
  simpa using h
lemma countUp_2677 : countSmall 0 2677 = 361 := by
  have h := countSmall_add 0 2600 77
  have hc : countSmall 2600 77 = 9 := by decide
  rw [countUp_2600, hc] at h
  simpa using h
lemma countUp_2727 : countSmall 0 2727 = 371 := by
  have h := countSmall_add 0 2700 27
  have hc : countSmall 2700 27 = 4 := by decide
  rw [countUp_2700, hc] at h
  simpa using h
lemma countUp_2777 : countSmall 0 2777 = 377 := by
  have h := countSmall_add 0 2700 77
  have hc : countSmall 2700 77 = 10 := by decide
  rw [countUp_2700, hc] at h
  simpa using h
lemma countUp_2827 : countSmall 0 2827 = 384 := by
  have h := countSmall_add 0 2800 27
  have hc : countSmall 2800 27 = 3 := by decide
  rw [countUp_2800, hc] at h
  simpa using h
lemma countUp_2877 : countSmall 0 2877 = 390 := by
  have h := countSmall_add 0 2800 77
  have hc : countSmall 2800 77 = 9 := by decide
  rw [countUp_2800, hc] at h
  simpa using h
lemma countUp_2927 : countSmall 0 2927 = 396 := by
  have h := countSmall_add 0 2900 27
  have hc : countSmall 2900 27 = 3 := by decide
  rw [countUp_2900, hc] at h
  simpa using h
lemma countUp_2928 : countSmall 0 2928 = 397 := by
  have h := countSmall_add 0 2900 28
  have hc : countSmall 2900 28 = 4 := by decide
  rw [countUp_2900, hc] at h
  simpa using h
lemma countUp_2979 : countSmall 0 2979 = 403 := by
  have h := countSmall_add 0 2900 79
  have hc : countSmall 2900 79 = 10 := by decide
  rw [countUp_2900, hc] at h
  simpa using h
lemma countUp_3031 : countSmall 0 3031 = 408 := by
  have h := countSmall_add 0 3000 31
  have hc : countSmall 3000 31 = 4 := by decide
  rw [countUp_3000, hc] at h
  simpa using h
lemma countUp_3086 : countSmall 0 3086 = 415 := by
  have h := countSmall_add 0 3000 86
  have hc : countSmall 3000 86 = 11 := by decide
  rw [countUp_3000, hc] at h
  simpa using h
lemma countUp_3142 : countSmall 0 3142 = 420 := by
  have h := countSmall_add 0 3100 42
  have hc : countSmall 3100 42 = 4 := by decide
  rw [countUp_3100, hc] at h
  simpa using h
lemma countUp_3201 : countSmall 0 3201 = 426 := by
  have h := countSmall_add 0 3200 1
  have hc : countSmall 3200 1 = 0 := by decide
  rw [countUp_3200, hc] at h
  simpa using h
lemma countUp_3262 : countSmall 0 3262 = 435 := by
  have h := countSmall_add 0 3200 62
  have hc : countSmall 3200 62 = 9 := by decide
  rw [countUp_3200, hc] at h
  simpa using h
lemma countUp_3325 : countSmall 0 3325 = 442 := by
  have h := countSmall_add 0 3300 25
  have hc : countSmall 3300 25 = 5 := by decide
  rw [countUp_3300, hc] at h
  simpa using h
lemma countUp_3391 : countSmall 0 3391 = 451 := by
  have h := countSmall_add 0 3300 91
  have hc : countSmall 3300 91 = 14 := by decide
  rw [countUp_3300, hc] at h
  simpa using h
lemma countUp_3460 : countSmall 0 3460 = 457 := by
  have h := countSmall_add 0 3400 60
  have hc : countSmall 3400 60 = 5 := by decide
  rw [countUp_3400, hc] at h
  simpa using h
lemma countUp_3531 : countSmall 0 3531 = 467 := by
  have h := countSmall_add 0 3500 31
  have hc : countSmall 3500 31 = 4 := by decide
  rw [countUp_3500, hc] at h
  simpa using h
lemma countUp_3605 : countSmall 0 3605 = 477 := by
  have h := countSmall_add 0 3600 5
  have hc : countSmall 3600 5 = 0 := by decide
  rw [countUp_3600, hc] at h
  simpa using h
lemma countUp_3682 : countSmall 0 3682 = 488 := by
  have h := countSmall_add 0 3600 82
  have hc : countSmall 3600 82 = 11 := by decide
  rw [countUp_3600, hc] at h
  simpa using h
lemma countUp_3763 : countSmall 0 3763 = 497 := by
  have h := countSmall_add 0 3700 63
  have hc : countSmall 3700 63 = 7 := by decide
  rw [countUp_3700, hc] at h
  simpa using h
lemma countUp_3848 : countSmall 0 3848 = 507 := by
  have h := countSmall_add 0 3800 48
  have hc : countSmall 3800 48 = 5 := by decide
  rw [countUp_3800, hc] at h
  simpa using h
lemma countUp_3936 : countSmall 0 3936 = 520 := by
  have h := countSmall_add 0 3900 36
  have hc : countSmall 3900 36 = 7 := by decide
  rw [countUp_3900, hc] at h
  simpa using h
lemma countUp_4029 : countSmall 0 4029 = 531 := by
  have h := countSmall_add 0 4000 29
  have hc : countSmall 4000 29 = 7 := by decide
  rw [countUp_4000, hc] at h
  simpa using h
lemma countUp_4126 : countSmall 0 4126 = 540 := by
  have h := countSmall_add 0 4100 26
  have hc : countSmall 4100 26 = 1 := by decide
  rw [countUp_4100, hc] at h
  simpa using h
lemma countUp_4227 : countSmall 0 4227 = 552 := by
  have h := countSmall_add 0 4200 27
  have hc : countSmall 4200 27 = 4 := by decide
  rw [countUp_4200, hc] at h
  simpa using h
lemma countUp_4334 : countSmall 0 4334 = 565 := by
  have h := countSmall_add 0 4300 34
  have hc : countSmall 4300 34 = 1 := by decide
  rw [countUp_4300, hc] at h
  simpa using h
lemma countUp_4447 : countSmall 0 4447 = 577 := by
  have h := countSmall_add 0 4400 47
  have hc : countSmall 4400 47 = 4 := by decide
  rw [countUp_4400, hc] at h
  simpa using h
lemma countUp_4565 : countSmall 0 4565 = 592 := by
  have h := countSmall_add 0 4500 65
  have hc : countSmall 4500 65 = 8 := by decide
  rw [countUp_4500, hc] at h
  simpa using h
lemma countUp_4690 : countSmall 0 4690 = 607 := by
  have h := countSmall_add 0 4600 90
  have hc : countSmall 4600 90 = 11 := by decide
  rw [countUp_4600, hc] at h
  simpa using h
lemma countUp_4822 : countSmall 0 4822 = 623 := by
  have h := countSmall_add 0 4800 22
  have hc : countSmall 4800 22 = 3 := by decide
  rw [countUp_4800, hc] at h
  simpa using h
lemma countUp_4962 : countSmall 0 4962 = 637 := by
  have h := countSmall_add 0 4900 62
  have hc : countSmall 4900 62 = 9 := by decide
  rw [countUp_4900, hc] at h
  simpa using h
lemma countUp_5110 : countSmall 0 5110 = 657 := by
  have h := countSmall_add 0 5100 10
  have hc : countSmall 5100 10 = 2 := by decide
  rw [countUp_5100, hc] at h
  simpa using h
lemma countUp_5267 : countSmall 0 5267 = 672 := by
  have h := countSmall_add 0 5200 67
  have hc : countSmall 5200 67 = 6 := by decide
  rw [countUp_5200, hc] at h
  simpa using h
lemma countUp_5434 : countSmall 0 5434 = 691 := by
  have h := countSmall_add 0 5400 34
  have hc : countSmall 5400 34 = 5 := by decide
  rw [countUp_5400, hc] at h
  simpa using h
lemma countUp_5611 : countSmall 0 5611 = 712 := by
  have h := countSmall_add 0 5600 11
  have hc : countSmall 5600 11 = 0 := by decide
  rw [countUp_5600, hc] at h
  simpa using h
lemma countUp_5801 : countSmall 0 5801 = 734 := by
  have h := countSmall_add 0 5800 1
  have hc : countSmall 5800 1 = 0 := by decide
  rw [countUp_5800, hc] at h
  simpa using h
lemma countUp_6005 : countSmall 0 6005 = 757 := by
  have h := countSmall_add 0 6000 5
  have hc : countSmall 6000 5 = 0 := by decide
  rw [countUp_6000, hc] at h
  simpa using h
lemma countUp_6223 : countSmall 0 6223 = 784 := by
  have h := countSmall_add 0 6200 23
  have hc : countSmall 6200 23 = 4 := by decide
  rw [countUp_6200, hc] at h
  simpa using h
lemma countUp_6457 : countSmall 0 6457 = 812 := by
  have h := countSmall_add 0 6400 57
  have hc : countSmall 6400 57 = 4 := by decide
  rw [countUp_6400, hc] at h
  simpa using h
lemma countUp_6710 : countSmall 0 6710 = 840 := by
  have h := countSmall_add 0 6700 10
  have hc : countSmall 6700 10 = 3 := by decide
  rw [countUp_6700, hc] at h
  simpa using h
lemma countUp_6983 : countSmall 0 6983 = 871 := by
  have h := countSmall_add 0 6900 83
  have hc : countSmall 6900 83 = 10 := by decide
  rw [countUp_6900, hc] at h
  simpa using h
lemma countUp_7280 : countSmall 0 7280 = 902 := by
  have h := countSmall_add 0 7200 80
  have hc : countSmall 7200 80 = 9 := by decide
  rw [countUp_7200, hc] at h
  simpa using h
lemma countUp_7603 : countSmall 0 7603 = 939 := by
  have h := countSmall_add 0 7600 3
  have hc : countSmall 7600 3 = 0 := by decide
  rw [countUp_7600, hc] at h
  simpa using h
lemma countUp_7956 : countSmall 0 7956 = 979 := by
  have h := countSmall_add 0 7900 56
  have hc : countSmall 7900 56 = 8 := by decide
  rw [countUp_7900, hc] at h
  simpa using h
lemma countUp_8343 : countSmall 0 8343 = 1019 := by
  have h := countSmall_add 0 8300 43
  have hc : countSmall 8300 43 = 3 := by decide
  rw [countUp_8300, hc] at h
  simpa using h
lemma countUp_8770 : countSmall 0 8770 = 1067 := by
  have h := countSmall_add 0 8700 70
  have hc : countSmall 8700 70 = 9 := by decide
  rw [countUp_8700, hc] at h
  simpa using h
lemma countUp_9243 : countSmall 0 9243 = 1120 := by
  have h := countSmall_add 0 9200 43
  have hc : countSmall 9200 43 = 6 := by decide
  rw [countUp_9200, hc] at h
  simpa using h
lemma countUp_9770 : countSmall 0 9770 = 1179 := by
  have h := countSmall_add 0 9700 70
  have hc : countSmall 9700 70 = 8 := by decide
  rw [countUp_9700, hc] at h
  simpa using h
lemma countUp_10361 : countSmall 0 10361 = 1245 := by
  have h := countSmall_add 0 10300 61
  have hc : countSmall 10300 61 = 9 := by decide
  rw [countUp_10300, hc] at h
  simpa using h
lemma countUp_11027 : countSmall 0 11027 = 1312 := by
  have h := countSmall_add 0 11000 27
  have hc : countSmall 11000 27 = 2 := by decide
  rw [countUp_11000, hc] at h
  simpa using h
lemma countUp_11786 : countSmall 0 11786 = 1392 := by
  have h := countSmall_add 0 11700 86
  have hc : countSmall 11700 86 = 8 := by decide
  rw [countUp_11700, hc] at h
  simpa using h
lemma countUp_12656 : countSmall 0 12656 = 1495 := by
  have h := countSmall_add 0 12600 56
  have hc : countSmall 12600 56 = 8 := by decide
  rw [countUp_12600, hc] at h
  simpa using h
lemma countUp_13666 : countSmall 0 13666 = 1600 := by
  have h := countSmall_add 0 13600 66
  have hc : countSmall 13600 66 = 5 := by decide
  rw [countUp_13600, hc] at h
  simpa using h
lemma countUp_14850 : countSmall 0 14850 = 1734 := by
  have h := countSmall_add 0 14800 50
  have hc : countSmall 14800 50 = 6 := by decide
  rw [countUp_14800, hc] at h
  simpa using h
lemma countUp_16258 : countSmall 0 16258 = 1896 := by
  have h := countSmall_add 0 16200 58
  have hc : countSmall 16200 58 = 7 := by decide
  rw [countUp_16200, hc] at h
  simpa using h
lemma countUp_17963 : countSmall 0 17963 = 2083 := by
  have h := countSmall_add 0 17900 63
  have hc : countSmall 17900 63 = 10 := by decide
  rw [countUp_17900, hc] at h
  simpa using h
lemma countUp_20066 : countSmall 0 20066 = 2316 := by
  have h := countSmall_add 0 20000 66
  have hc : countSmall 20000 66 = 7 := by decide
  rw [countUp_20000, hc] at h
  simpa using h
lemma countUp_22727 : countSmall 0 22727 = 2621 := by
  have h := countSmall_add 0 22700 27
  have hc : countSmall 22700 27 = 3 := by decide
  rw [countUp_22700, hc] at h
  simpa using h
lemma countUp_26202 : countSmall 0 26202 = 3016 := by
  have h := countSmall_add 0 26200 2
  have hc : countSmall 26200 2 = 0 := by decide
  rw [countUp_26200, hc] at h
  simpa using h
lemma countUp_30932 : countSmall 0 30932 = 3555 := by
  have h := countSmall_add 0 30900 32
  have hc : countSmall 30900 32 = 3 := by decide
  rw [countUp_30900, hc] at h
  simpa using h
lemma count_interval_p_0 : countSmall 227 50 = 10 := by
  have h := countSmall_add 0 227 50
  simp only [Nat.zero_add] at h
  rw [show 227 + 50 = 277 by norm_num] at h
  rw [countUp_277, countUp_227] at h
  omega
lemma count_interval_q_0 : countSmall 227 37518 = 4326 := by
  have h := countSmall_add 0 227 37518
  simp only [Nat.zero_add] at h
  rw [show 227 + 37518 = 37745 by norm_num] at h
  rw [countUp_37745, countUp_227] at h
  omega
lemma count_interval_p_1 : countSmall 277 50 = 8 := by
  have h := countSmall_add 0 277 50
  simp only [Nat.zero_add] at h
  rw [show 277 + 50 = 327 by norm_num] at h
  rw [countUp_327, countUp_277] at h
  omega
lemma count_interval_q_1 : countSmall 277 30655 = 3523 := by
  have h := countSmall_add 0 277 30655
  simp only [Nat.zero_add] at h
  rw [show 277 + 30655 = 30932 by norm_num] at h
  rw [countUp_30932, countUp_277] at h
  omega
lemma count_interval_p_2 : countSmall 327 50 = 8 := by
  have h := countSmall_add 0 327 50
  simp only [Nat.zero_add] at h
  rw [show 327 + 50 = 377 by norm_num] at h
  rw [countUp_377, countUp_327] at h
  omega
lemma count_interval_q_2 : countSmall 327 25875 = 2976 := by
  have h := countSmall_add 0 327 25875
  simp only [Nat.zero_add] at h
  rw [show 327 + 25875 = 26202 by norm_num] at h
  rw [countUp_26202, countUp_327] at h
  omega
lemma count_interval_p_3 : countSmall 377 50 = 8 := by
  have h := countSmall_add 0 377 50
  simp only [Nat.zero_add] at h
  rw [show 377 + 50 = 427 by norm_num] at h
  rw [countUp_427, countUp_377] at h
  omega
lemma count_interval_q_3 : countSmall 377 22350 = 2573 := by
  have h := countSmall_add 0 377 22350
  simp only [Nat.zero_add] at h
  rw [show 377 + 22350 = 22727 by norm_num] at h
  rw [countUp_22727, countUp_377] at h
  omega
lemma count_interval_p_4 : countSmall 427 50 = 9 := by
  have h := countSmall_add 0 427 50
  simp only [Nat.zero_add] at h
  rw [show 427 + 50 = 477 by norm_num] at h
  rw [countUp_477, countUp_427] at h
  omega
lemma count_interval_q_4 : countSmall 427 19639 = 2260 := by
  have h := countSmall_add 0 427 19639
  simp only [Nat.zero_add] at h
  rw [show 427 + 19639 = 20066 by norm_num] at h
  rw [countUp_20066, countUp_427] at h
  omega
lemma count_interval_p_5 : countSmall 477 50 = 8 := by
  have h := countSmall_add 0 477 50
  simp only [Nat.zero_add] at h
  rw [show 477 + 50 = 527 by norm_num] at h
  rw [countUp_527, countUp_477] at h
  omega
lemma count_interval_q_5 : countSmall 477 17486 = 2018 := by
  have h := countSmall_add 0 477 17486
  simp only [Nat.zero_add] at h
  rw [show 477 + 17486 = 17963 by norm_num] at h
  rw [countUp_17963, countUp_477] at h
  omega
lemma count_interval_p_6 : countSmall 527 50 = 6 := by
  have h := countSmall_add 0 527 50
  simp only [Nat.zero_add] at h
  rw [show 527 + 50 = 577 by norm_num] at h
  rw [countUp_577, countUp_527] at h
  omega
lemma count_interval_q_6 : countSmall 527 15731 = 1823 := by
  have h := countSmall_add 0 527 15731
  simp only [Nat.zero_add] at h
  rw [show 527 + 15731 = 16258 by norm_num] at h
  rw [countUp_16258, countUp_527] at h
  omega
lemma count_interval_p_7 : countSmall 577 50 = 9 := by
  have h := countSmall_add 0 577 50
  simp only [Nat.zero_add] at h
  rw [show 577 + 50 = 627 by norm_num] at h
  rw [countUp_627, countUp_577] at h
  omega
lemma count_interval_q_7 : countSmall 577 14273 = 1655 := by
  have h := countSmall_add 0 577 14273
  simp only [Nat.zero_add] at h
  rw [show 577 + 14273 = 14850 by norm_num] at h
  rw [countUp_14850, countUp_577] at h
  omega
lemma count_interval_p_8 : countSmall 627 50 = 8 := by
  have h := countSmall_add 0 627 50
  simp only [Nat.zero_add] at h
  rw [show 627 + 50 = 677 by norm_num] at h
  rw [countUp_677, countUp_627] at h
  omega
lemma count_interval_q_8 : countSmall 627 13039 = 1512 := by
  have h := countSmall_add 0 627 13039
  simp only [Nat.zero_add] at h
  rw [show 627 + 13039 = 13666 by norm_num] at h
  rw [countUp_13666, countUp_627] at h
  omega
lemma count_interval_p_9 : countSmall 677 50 = 6 := by
  have h := countSmall_add 0 677 50
  simp only [Nat.zero_add] at h
  rw [show 677 + 50 = 727 by norm_num] at h
  rw [countUp_727, countUp_677] at h
  omega
lemma count_interval_q_9 : countSmall 677 11979 = 1399 := by
  have h := countSmall_add 0 677 11979
  simp only [Nat.zero_add] at h
  rw [show 677 + 11979 = 12656 by norm_num] at h
  rw [countUp_12656, countUp_677] at h
  omega
lemma count_interval_p_10 : countSmall 727 50 = 9 := by
  have h := countSmall_add 0 727 50
  simp only [Nat.zero_add] at h
  rw [show 727 + 50 = 777 by norm_num] at h
  rw [countUp_777, countUp_727] at h
  omega
lemma count_interval_q_10 : countSmall 727 11059 = 1290 := by
  have h := countSmall_add 0 727 11059
  simp only [Nat.zero_add] at h
  rw [show 727 + 11059 = 11786 by norm_num] at h
  rw [countUp_11786, countUp_727] at h
  omega
lemma count_interval_p_11 : countSmall 777 50 = 6 := by
  have h := countSmall_add 0 777 50
  simp only [Nat.zero_add] at h
  rw [show 777 + 50 = 827 by norm_num] at h
  rw [countUp_827, countUp_777] at h
  omega
lemma count_interval_q_11 : countSmall 777 10250 = 1201 := by
  have h := countSmall_add 0 777 10250
  simp only [Nat.zero_add] at h
  rw [show 777 + 10250 = 11027 by norm_num] at h
  rw [countUp_11027, countUp_777] at h
  omega
lemma count_interval_p_12 : countSmall 827 50 = 7 := by
  have h := countSmall_add 0 827 50
  simp only [Nat.zero_add] at h
  rw [show 827 + 50 = 877 by norm_num] at h
  rw [countUp_877, countUp_827] at h
  omega
lemma count_interval_q_12 : countSmall 827 9534 = 1128 := by
  have h := countSmall_add 0 827 9534
  simp only [Nat.zero_add] at h
  rw [show 827 + 9534 = 10361 by norm_num] at h
  rw [countUp_10361, countUp_827] at h
  omega
lemma count_interval_p_13 : countSmall 877 50 = 7 := by
  have h := countSmall_add 0 877 50
  simp only [Nat.zero_add] at h
  rw [show 877 + 50 = 927 by norm_num] at h
  rw [countUp_927, countUp_877] at h
  omega
lemma count_interval_q_13 : countSmall 877 8893 = 1055 := by
  have h := countSmall_add 0 877 8893
  simp only [Nat.zero_add] at h
  rw [show 877 + 8893 = 9770 by norm_num] at h
  rw [countUp_9770, countUp_877] at h
  omega
lemma count_interval_p_14 : countSmall 927 50 = 7 := by
  have h := countSmall_add 0 927 50
  simp only [Nat.zero_add] at h
  rw [show 927 + 50 = 977 by norm_num] at h
  rw [countUp_977, countUp_927] at h
  omega
lemma count_interval_q_14 : countSmall 927 8316 = 989 := by
  have h := countSmall_add 0 927 8316
  simp only [Nat.zero_add] at h
  rw [show 927 + 8316 = 9243 by norm_num] at h
  rw [countUp_9243, countUp_927] at h
  omega
lemma count_interval_p_15 : countSmall 977 50 = 8 := by
  have h := countSmall_add 0 977 50
  simp only [Nat.zero_add] at h
  rw [show 977 + 50 = 1027 by norm_num] at h
  rw [countUp_1027, countUp_977] at h
  omega
lemma count_interval_q_15 : countSmall 977 7793 = 929 := by
  have h := countSmall_add 0 977 7793
  simp only [Nat.zero_add] at h
  rw [show 977 + 7793 = 8770 by norm_num] at h
  rw [countUp_8770, countUp_977] at h
  omega
lemma count_interval_p_16 : countSmall 1027 50 = 8 := by
  have h := countSmall_add 0 1027 50
  simp only [Nat.zero_add] at h
  rw [show 1027 + 50 = 1077 by norm_num] at h
  rw [countUp_1077, countUp_1027] at h
  omega
lemma count_interval_q_16 : countSmall 1027 7316 = 873 := by
  have h := countSmall_add 0 1027 7316
  simp only [Nat.zero_add] at h
  rw [show 1027 + 7316 = 8343 by norm_num] at h
  rw [countUp_8343, countUp_1027] at h
  omega
lemma count_interval_p_17 : countSmall 1077 50 = 8 := by
  have h := countSmall_add 0 1077 50
  simp only [Nat.zero_add] at h
  rw [show 1077 + 50 = 1127 by norm_num] at h
  rw [countUp_1127, countUp_1077] at h
  omega
lemma count_interval_q_17 : countSmall 1077 6879 = 825 := by
  have h := countSmall_add 0 1077 6879
  simp only [Nat.zero_add] at h
  rw [show 1077 + 6879 = 7956 by norm_num] at h
  rw [countUp_7956, countUp_1077] at h
  omega
lemma count_interval_p_18 : countSmall 1127 50 = 5 := by
  have h := countSmall_add 0 1127 50
  simp only [Nat.zero_add] at h
  rw [show 1127 + 50 = 1177 by norm_num] at h
  rw [countUp_1177, countUp_1127] at h
  omega
lemma count_interval_q_18 : countSmall 1127 6476 = 777 := by
  have h := countSmall_add 0 1127 6476
  simp only [Nat.zero_add] at h
  rw [show 1127 + 6476 = 7603 by norm_num] at h
  rw [countUp_7603, countUp_1127] at h
  omega
lemma count_interval_p_19 : countSmall 1177 50 = 7 := by
  have h := countSmall_add 0 1177 50
  simp only [Nat.zero_add] at h
  rw [show 1177 + 50 = 1227 by norm_num] at h
  rw [countUp_1227, countUp_1177] at h
  omega
lemma count_interval_q_19 : countSmall 1177 6103 = 735 := by
  have h := countSmall_add 0 1177 6103
  simp only [Nat.zero_add] at h
  rw [show 1177 + 6103 = 7280 by norm_num] at h
  rw [countUp_7280, countUp_1177] at h
  omega
lemma count_interval_p_20 : countSmall 1227 50 = 5 := by
  have h := countSmall_add 0 1227 50
  simp only [Nat.zero_add] at h
  rw [show 1227 + 50 = 1277 by norm_num] at h
  rw [countUp_1277, countUp_1227] at h
  omega
lemma count_interval_q_20 : countSmall 1227 5756 = 697 := by
  have h := countSmall_add 0 1227 5756
  simp only [Nat.zero_add] at h
  rw [show 1227 + 5756 = 6983 by norm_num] at h
  rw [countUp_6983, countUp_1227] at h
  omega
lemma count_interval_p_21 : countSmall 1277 50 = 11 := by
  have h := countSmall_add 0 1277 50
  simp only [Nat.zero_add] at h
  rw [show 1277 + 50 = 1327 by norm_num] at h
  rw [countUp_1327, countUp_1277] at h
  omega
lemma count_interval_q_21 : countSmall 1277 5433 = 661 := by
  have h := countSmall_add 0 1277 5433
  simp only [Nat.zero_add] at h
  rw [show 1277 + 5433 = 6710 by norm_num] at h
  rw [countUp_6710, countUp_1277] at h
  omega
lemma count_interval_p_22 : countSmall 1327 50 = 4 := by
  have h := countSmall_add 0 1327 50
  simp only [Nat.zero_add] at h
  rw [show 1327 + 50 = 1377 by norm_num] at h
  rw [countUp_1377, countUp_1327] at h
  omega
lemma count_interval_q_22 : countSmall 1327 5130 = 622 := by
  have h := countSmall_add 0 1327 5130
  simp only [Nat.zero_add] at h
  rw [show 1327 + 5130 = 6457 by norm_num] at h
  rw [countUp_6457, countUp_1327] at h
  omega
lemma count_interval_p_23 : countSmall 1377 50 = 4 := by
  have h := countSmall_add 0 1377 50
  simp only [Nat.zero_add] at h
  rw [show 1377 + 50 = 1427 by norm_num] at h
  rw [countUp_1427, countUp_1377] at h
  omega
lemma count_interval_q_23 : countSmall 1377 4846 = 590 := by
  have h := countSmall_add 0 1377 4846
  simp only [Nat.zero_add] at h
  rw [show 1377 + 4846 = 6223 by norm_num] at h
  rw [countUp_6223, countUp_1377] at h
  omega
lemma count_interval_p_24 : countSmall 1427 50 = 9 := by
  have h := countSmall_add 0 1427 50
  simp only [Nat.zero_add] at h
  rw [show 1427 + 50 = 1477 by norm_num] at h
  rw [countUp_1477, countUp_1427] at h
  omega
lemma count_interval_q_24 : countSmall 1427 4578 = 559 := by
  have h := countSmall_add 0 1427 4578
  simp only [Nat.zero_add] at h
  rw [show 1427 + 4578 = 6005 by norm_num] at h
  rw [countUp_6005, countUp_1427] at h
  omega
lemma count_interval_p_25 : countSmall 1477 50 = 8 := by
  have h := countSmall_add 0 1477 50
  simp only [Nat.zero_add] at h
  rw [show 1477 + 50 = 1527 by norm_num] at h
  rw [countUp_1527, countUp_1477] at h
  omega
lemma count_interval_q_25 : countSmall 1477 4324 = 527 := by
  have h := countSmall_add 0 1477 4324
  simp only [Nat.zero_add] at h
  rw [show 1477 + 4324 = 5801 by norm_num] at h
  rw [countUp_5801, countUp_1477] at h
  omega
lemma count_interval_p_26 : countSmall 1527 50 = 7 := by
  have h := countSmall_add 0 1527 50
  simp only [Nat.zero_add] at h
  rw [show 1527 + 50 = 1577 by norm_num] at h
  rw [countUp_1577, countUp_1527] at h
  omega
lemma count_interval_q_26 : countSmall 1527 4084 = 497 := by
  have h := countSmall_add 0 1527 4084
  simp only [Nat.zero_add] at h
  rw [show 1527 + 4084 = 5611 by norm_num] at h
  rw [countUp_5611, countUp_1527] at h
  omega
lemma count_interval_p_27 : countSmall 1577 50 = 9 := by
  have h := countSmall_add 0 1577 50
  simp only [Nat.zero_add] at h
  rw [show 1577 + 50 = 1627 by norm_num] at h
  rw [countUp_1627, countUp_1577] at h
  omega
lemma count_interval_q_27 : countSmall 1577 3857 = 469 := by
  have h := countSmall_add 0 1577 3857
  simp only [Nat.zero_add] at h
  rw [show 1577 + 3857 = 5434 by norm_num] at h
  rw [countUp_5434, countUp_1577] at h
  omega
lemma count_interval_p_28 : countSmall 1627 50 = 6 := by
  have h := countSmall_add 0 1627 50
  simp only [Nat.zero_add] at h
  rw [show 1627 + 50 = 1677 by norm_num] at h
  rw [countUp_1677, countUp_1627] at h
  omega
lemma count_interval_q_28 : countSmall 1627 3640 = 441 := by
  have h := countSmall_add 0 1627 3640
  simp only [Nat.zero_add] at h
  rw [show 1627 + 3640 = 5267 by norm_num] at h
  rw [countUp_5267, countUp_1627] at h
  omega
lemma count_interval_p_29 : countSmall 1677 50 = 6 := by
  have h := countSmall_add 0 1677 50
  simp only [Nat.zero_add] at h
  rw [show 1677 + 50 = 1727 by norm_num] at h
  rw [countUp_1727, countUp_1677] at h
  omega
lemma count_interval_q_29 : countSmall 1677 3433 = 420 := by
  have h := countSmall_add 0 1677 3433
  simp only [Nat.zero_add] at h
  rw [show 1677 + 3433 = 5110 by norm_num] at h
  rw [countUp_5110, countUp_1677] at h
  omega
lemma count_interval_p_30 : countSmall 1727 50 = 5 := by
  have h := countSmall_add 0 1727 50
  simp only [Nat.zero_add] at h
  rw [show 1727 + 50 = 1777 by norm_num] at h
  rw [countUp_1777, countUp_1727] at h
  omega
lemma count_interval_q_30 : countSmall 1727 3235 = 394 := by
  have h := countSmall_add 0 1727 3235
  simp only [Nat.zero_add] at h
  rw [show 1727 + 3235 = 4962 by norm_num] at h
  rw [countUp_4962, countUp_1727] at h
  omega
lemma count_interval_p_31 : countSmall 1777 50 = 7 := by
  have h := countSmall_add 0 1777 50
  simp only [Nat.zero_add] at h
  rw [show 1777 + 50 = 1827 by norm_num] at h
  rw [countUp_1827, countUp_1777] at h
  omega
lemma count_interval_q_31 : countSmall 1777 3045 = 375 := by
  have h := countSmall_add 0 1777 3045
  simp only [Nat.zero_add] at h
  rw [show 1777 + 3045 = 4822 by norm_num] at h
  rw [countUp_4822, countUp_1777] at h
  omega
lemma count_interval_p_32 : countSmall 1827 50 = 6 := by
  have h := countSmall_add 0 1827 50
  simp only [Nat.zero_add] at h
  rw [show 1827 + 50 = 1877 by norm_num] at h
  rw [countUp_1877, countUp_1827] at h
  omega
lemma count_interval_q_32 : countSmall 1827 2863 = 352 := by
  have h := countSmall_add 0 1827 2863
  simp only [Nat.zero_add] at h
  rw [show 1827 + 2863 = 4690 by norm_num] at h
  rw [countUp_4690, countUp_1827] at h
  omega
lemma count_interval_p_33 : countSmall 1877 50 = 6 := by
  have h := countSmall_add 0 1877 50
  simp only [Nat.zero_add] at h
  rw [show 1877 + 50 = 1927 by norm_num] at h
  rw [countUp_1927, countUp_1877] at h
  omega
lemma count_interval_q_33 : countSmall 1877 2688 = 331 := by
  have h := countSmall_add 0 1877 2688
  simp only [Nat.zero_add] at h
  rw [show 1877 + 2688 = 4565 by norm_num] at h
  rw [countUp_4565, countUp_1877] at h
  omega
lemma count_interval_p_34 : countSmall 1927 50 = 5 := by
  have h := countSmall_add 0 1927 50
  simp only [Nat.zero_add] at h
  rw [show 1927 + 50 = 1977 by norm_num] at h
  rw [countUp_1977, countUp_1927] at h
  omega
lemma count_interval_q_34 : countSmall 1927 2520 = 310 := by
  have h := countSmall_add 0 1927 2520
  simp only [Nat.zero_add] at h
  rw [show 1927 + 2520 = 4447 by norm_num] at h
  rw [countUp_4447, countUp_1927] at h
  omega
lemma count_interval_p_35 : countSmall 1977 50 = 8 := by
  have h := countSmall_add 0 1977 50
  simp only [Nat.zero_add] at h
  rw [show 1977 + 50 = 2027 by norm_num] at h
  rw [countUp_2027, countUp_1977] at h
  omega
lemma count_interval_q_35 : countSmall 1977 2357 = 293 := by
  have h := countSmall_add 0 1977 2357
  simp only [Nat.zero_add] at h
  rw [show 1977 + 2357 = 4334 by norm_num] at h
  rw [countUp_4334, countUp_1977] at h
  omega
lemma count_interval_p_36 : countSmall 2027 50 = 6 := by
  have h := countSmall_add 0 2027 50
  simp only [Nat.zero_add] at h
  rw [show 2027 + 50 = 2077 by norm_num] at h
  rw [countUp_2077, countUp_2027] at h
  omega
lemma count_interval_q_36 : countSmall 2027 2200 = 272 := by
  have h := countSmall_add 0 2027 2200
  simp only [Nat.zero_add] at h
  rw [show 2027 + 2200 = 4227 by norm_num] at h
  rw [countUp_4227, countUp_2027] at h
  omega
lemma count_interval_p_37 : countSmall 2077 50 = 7 := by
  have h := countSmall_add 0 2077 50
  simp only [Nat.zero_add] at h
  rw [show 2077 + 50 = 2127 by norm_num] at h
  rw [countUp_2127, countUp_2077] at h
  omega
lemma count_interval_q_37 : countSmall 2077 2049 = 254 := by
  have h := countSmall_add 0 2077 2049
  simp only [Nat.zero_add] at h
  rw [show 2077 + 2049 = 4126 by norm_num] at h
  rw [countUp_4126, countUp_2077] at h
  omega
lemma count_interval_p_38 : countSmall 2127 50 = 7 := by
  have h := countSmall_add 0 2127 50
  simp only [Nat.zero_add] at h
  rw [show 2127 + 50 = 2177 by norm_num] at h
  rw [countUp_2177, countUp_2127] at h
  omega
lemma count_interval_q_38 : countSmall 2127 1902 = 238 := by
  have h := countSmall_add 0 2127 1902
  simp only [Nat.zero_add] at h
  rw [show 2127 + 1902 = 4029 by norm_num] at h
  rw [countUp_4029, countUp_2127] at h
  omega
lemma count_interval_p_39 : countSmall 2177 50 = 5 := by
  have h := countSmall_add 0 2177 50
  simp only [Nat.zero_add] at h
  rw [show 2177 + 50 = 2227 by norm_num] at h
  rw [countUp_2227, countUp_2177] at h
  omega
lemma count_interval_q_39 : countSmall 2177 1759 = 220 := by
  have h := countSmall_add 0 2177 1759
  simp only [Nat.zero_add] at h
  rw [show 2177 + 1759 = 3936 by norm_num] at h
  rw [countUp_3936, countUp_2177] at h
  omega
lemma count_interval_p_40 : countSmall 2227 50 = 7 := by
  have h := countSmall_add 0 2227 50
  simp only [Nat.zero_add] at h
  rw [show 2227 + 50 = 2277 by norm_num] at h
  rw [countUp_2277, countUp_2227] at h
  omega
lemma count_interval_q_40 : countSmall 2227 1621 = 202 := by
  have h := countSmall_add 0 2227 1621
  simp only [Nat.zero_add] at h
  rw [show 2227 + 1621 = 3848 by norm_num] at h
  rw [countUp_3848, countUp_2227] at h
  omega
lemma count_interval_p_41 : countSmall 2277 50 = 6 := by
  have h := countSmall_add 0 2277 50
  simp only [Nat.zero_add] at h
  rw [show 2277 + 50 = 2327 by norm_num] at h
  rw [countUp_2327, countUp_2277] at h
  omega
lemma count_interval_q_41 : countSmall 2277 1486 = 185 := by
  have h := countSmall_add 0 2277 1486
  simp only [Nat.zero_add] at h
  rw [show 2277 + 1486 = 3763 by norm_num] at h
  rw [countUp_3763, countUp_2277] at h
  omega
lemma count_interval_p_42 : countSmall 2327 50 = 7 := by
  have h := countSmall_add 0 2327 50
  simp only [Nat.zero_add] at h
  rw [show 2327 + 50 = 2377 by norm_num] at h
  rw [countUp_2377, countUp_2327] at h
  omega
lemma count_interval_q_42 : countSmall 2327 1355 = 170 := by
  have h := countSmall_add 0 2327 1355
  simp only [Nat.zero_add] at h
  rw [show 2327 + 1355 = 3682 by norm_num] at h
  rw [countUp_3682, countUp_2327] at h
  omega
lemma count_interval_p_43 : countSmall 2377 50 = 9 := by
  have h := countSmall_add 0 2377 50
  simp only [Nat.zero_add] at h
  rw [show 2377 + 50 = 2427 by norm_num] at h
  rw [countUp_2427, countUp_2377] at h
  omega
lemma count_interval_q_43 : countSmall 2377 1228 = 152 := by
  have h := countSmall_add 0 2377 1228
  simp only [Nat.zero_add] at h
  rw [show 2377 + 1228 = 3605 by norm_num] at h
  rw [countUp_3605, countUp_2377] at h
  omega
lemma count_interval_p_44 : countSmall 2427 50 = 6 := by
  have h := countSmall_add 0 2427 50
  simp only [Nat.zero_add] at h
  rw [show 2427 + 50 = 2477 by norm_num] at h
  rw [countUp_2477, countUp_2427] at h
  omega
lemma count_interval_q_44 : countSmall 2427 1104 = 133 := by
  have h := countSmall_add 0 2427 1104
  simp only [Nat.zero_add] at h
  rw [show 2427 + 1104 = 3531 by norm_num] at h
  rw [countUp_3531, countUp_2427] at h
  omega
lemma count_interval_p_45 : countSmall 2477 50 = 3 := by
  have h := countSmall_add 0 2477 50
  simp only [Nat.zero_add] at h
  rw [show 2477 + 50 = 2527 by norm_num] at h
  rw [countUp_2527, countUp_2477] at h
  omega
lemma count_interval_q_45 : countSmall 2477 983 = 117 := by
  have h := countSmall_add 0 2477 983
  simp only [Nat.zero_add] at h
  rw [show 2477 + 983 = 3460 by norm_num] at h
  rw [countUp_3460, countUp_2477] at h
  omega
lemma count_interval_p_46 : countSmall 2527 50 = 6 := by
  have h := countSmall_add 0 2527 50
  simp only [Nat.zero_add] at h
  rw [show 2527 + 50 = 2577 by norm_num] at h
  rw [countUp_2577, countUp_2527] at h
  omega
lemma count_interval_q_46 : countSmall 2527 864 = 108 := by
  have h := countSmall_add 0 2527 864
  simp only [Nat.zero_add] at h
  rw [show 2527 + 864 = 3391 by norm_num] at h
  rw [countUp_3391, countUp_2527] at h
  omega
lemma count_interval_p_47 : countSmall 2577 50 = 6 := by
  have h := countSmall_add 0 2577 50
  simp only [Nat.zero_add] at h
  rw [show 2577 + 50 = 2627 by norm_num] at h
  rw [countUp_2627, countUp_2577] at h
  omega
lemma count_interval_q_47 : countSmall 2577 748 = 93 := by
  have h := countSmall_add 0 2577 748
  simp only [Nat.zero_add] at h
  rw [show 2577 + 748 = 3325 by norm_num] at h
  rw [countUp_3325, countUp_2577] at h
  omega
lemma count_interval_p_48 : countSmall 2627 50 = 6 := by
  have h := countSmall_add 0 2627 50
  simp only [Nat.zero_add] at h
  rw [show 2627 + 50 = 2677 by norm_num] at h
  rw [countUp_2677, countUp_2627] at h
  omega
lemma count_interval_q_48 : countSmall 2627 635 = 80 := by
  have h := countSmall_add 0 2627 635
  simp only [Nat.zero_add] at h
  rw [show 2627 + 635 = 3262 by norm_num] at h
  rw [countUp_3262, countUp_2627] at h
  omega
lemma count_interval_p_49 : countSmall 2677 50 = 10 := by
  have h := countSmall_add 0 2677 50
  simp only [Nat.zero_add] at h
  rw [show 2677 + 50 = 2727 by norm_num] at h
  rw [countUp_2727, countUp_2677] at h
  omega
lemma count_interval_q_49 : countSmall 2677 524 = 65 := by
  have h := countSmall_add 0 2677 524
  simp only [Nat.zero_add] at h
  rw [show 2677 + 524 = 3201 by norm_num] at h
  rw [countUp_3201, countUp_2677] at h
  omega
lemma count_interval_p_50 : countSmall 2727 50 = 6 := by
  have h := countSmall_add 0 2727 50
  simp only [Nat.zero_add] at h
  rw [show 2727 + 50 = 2777 by norm_num] at h
  rw [countUp_2777, countUp_2727] at h
  omega
lemma count_interval_q_50 : countSmall 2727 415 = 49 := by
  have h := countSmall_add 0 2727 415
  simp only [Nat.zero_add] at h
  rw [show 2727 + 415 = 3142 by norm_num] at h
  rw [countUp_3142, countUp_2727] at h
  omega
lemma count_interval_p_51 : countSmall 2777 50 = 7 := by
  have h := countSmall_add 0 2777 50
  simp only [Nat.zero_add] at h
  rw [show 2777 + 50 = 2827 by norm_num] at h
  rw [countUp_2827, countUp_2777] at h
  omega
lemma count_interval_q_51 : countSmall 2777 309 = 38 := by
  have h := countSmall_add 0 2777 309
  simp only [Nat.zero_add] at h
  rw [show 2777 + 309 = 3086 by norm_num] at h
  rw [countUp_3086, countUp_2777] at h
  omega
lemma count_interval_p_52 : countSmall 2827 50 = 6 := by
  have h := countSmall_add 0 2827 50
  simp only [Nat.zero_add] at h
  rw [show 2827 + 50 = 2877 by norm_num] at h
  rw [countUp_2877, countUp_2827] at h
  omega
lemma count_interval_q_52 : countSmall 2827 204 = 24 := by
  have h := countSmall_add 0 2827 204
  simp only [Nat.zero_add] at h
  rw [show 2827 + 204 = 3031 by norm_num] at h
  rw [countUp_3031, countUp_2827] at h
  omega
lemma count_interval_p_53 : countSmall 2877 50 = 6 := by
  have h := countSmall_add 0 2877 50
  simp only [Nat.zero_add] at h
  rw [show 2877 + 50 = 2927 by norm_num] at h
  rw [countUp_2927, countUp_2877] at h
  omega
lemma count_interval_q_53 : countSmall 2877 102 = 13 := by
  have h := countSmall_add 0 2877 102
  simp only [Nat.zero_add] at h
  rw [show 2877 + 102 = 2979 by norm_num] at h
  rw [countUp_2979, countUp_2877] at h
  omega
lemma count_interval_p_54 : countSmall 2927 1 = 1 := by
  have h := countSmall_add 0 2927 1
  simp only [Nat.zero_add] at h
  rw [show 2927 + 1 = 2928 by norm_num] at h
  rw [countUp_2928, countUp_2927] at h
  omega
lemma count_interval_q_54 : countSmall 2927 1 = 1 := by
  have h := countSmall_add 0 2927 1
  simp only [Nat.zero_add] at h
  rw [show 2927 + 1 = 2928 by norm_num] at h
  rw [countUp_2928, countUp_2927] at h
  omega
theorem block_count_total : (10 * 4326) + (8 * 3523) + (8 * 2976) + (8 * 2573) + (9 * 2260) + (8 * 2018) + (6 * 1823) + (9 * 1655) + (8 * 1512) + (6 * 1399) + (9 * 1290) + (6 * 1201) + (7 * 1128) + (7 * 1055) + (7 * 989) + (8 * 929) + (8 * 873) + (8 * 825) + (5 * 777) + (7 * 735) + (5 * 697) + (11 * 661) + (4 * 622) + (4 * 590) + (9 * 559) + (8 * 527) + (7 * 497) + (9 * 469) + (6 * 441) + (6 * 420) + (5 * 394) + (7 * 375) + (6 * 352) + (6 * 331) + (5 * 310) + (8 * 293) + (6 * 272) + (7 * 254) + (7 * 238) + (5 * 220) + (7 * 202) + (6 * 185) + (7 * 170) + (9 * 152) + (6 * 133) + (3 * 117) + (6 * 108) + (6 * 93) + (6 * 80) + (10 * 65) + (6 * 49) + (7 * 38) + (6 * 24) + (6 * 13) + (1 * 1) = 335539 := by norm_num

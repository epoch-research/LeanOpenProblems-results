import Submission.Primes
import FormalConjectures.Util.ProblemImports
import Submission.Primes

set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000


set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000


/--
A248802: Smallest prime factor of $2^{(2^n+2)} + 3$.
-/
def a (n : ℕ) : ℕ := (2 ^ (2 ^ n + 2) + 3).minFac

-- Helper definitions for the "covered" conditions based on the index k, where k = 58*n + 26.




/--
A248802 Conjecture 4: a(58n+26) = 1399 for n >= 0 and when it is not covered by Conjectures 1-3.
-/


lemma no_small_prime_0_50 (N n p : ℕ) (hEq : N = 2^(2^(58*n+26)+2) + 3)
  (hC1 : ¬ covered_by_C1 (58 * n + 26))
  (hC2 : ¬ covered_by_C2 (58 * n + 26))
  (hC3 : ¬ covered_by_C3 (58 * n + 26))
  (hp_ge : 2 ≤ p) (hp_lt : p < 50) (hp_prime : p.Prime) : ¬ p ∣ N := by
  interval_cases p
  · rw [hEq]; exact not_dvd_2 n hC1 hC2 hC3
  · rw [hEq]; exact not_dvd_3 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 4) hp_prime)
  · rw [hEq]; exact not_dvd_5 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 6) hp_prime)
  · rw [hEq]; exact not_dvd_7 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 8) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 9) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 10) hp_prime)
  · rw [hEq]; exact not_dvd_11 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 12) hp_prime)
  · rw [hEq]; exact not_dvd_13 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 14) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 15) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 16) hp_prime)
  · rw [hEq]; exact not_dvd_17 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 18) hp_prime)
  · rw [hEq]; exact not_dvd_19 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 20) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 21) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 22) hp_prime)
  · rw [hEq]; exact not_dvd_23 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 24) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 25) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 26) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 27) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 28) hp_prime)
  · rw [hEq]; exact not_dvd_29 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 30) hp_prime)
  · rw [hEq]; exact not_dvd_31 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 32) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 33) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 34) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 35) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 36) hp_prime)
  · rw [hEq]; exact not_dvd_37 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 38) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 39) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 40) hp_prime)
  · rw [hEq]; exact not_dvd_41 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 42) hp_prime)
  · rw [hEq]; exact not_dvd_43 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 44) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 45) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 46) hp_prime)
  · rw [hEq]; exact not_dvd_47 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 48) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 49) hp_prime)

lemma no_small_prime_50_100 (N n p : ℕ) (hEq : N = 2^(2^(58*n+26)+2) + 3)
  (hC1 : ¬ covered_by_C1 (58 * n + 26))
  (hC2 : ¬ covered_by_C2 (58 * n + 26))
  (hC3 : ¬ covered_by_C3 (58 * n + 26))
  (hp_ge : 50 ≤ p) (hp_lt : p < 100) (hp_prime : p.Prime) : ¬ p ∣ N := by
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 50) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 51) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 52) hp_prime)
  · rw [hEq]; exact not_dvd_53 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 54) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 55) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 56) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 57) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 58) hp_prime)
  · rw [hEq]; exact not_dvd_59 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 60) hp_prime)
  · rw [hEq]; exact not_dvd_61 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 62) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 63) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 64) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 65) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 66) hp_prime)
  · rw [hEq]; exact not_dvd_67 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 68) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 69) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 70) hp_prime)
  · rw [hEq]; exact not_dvd_71 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 72) hp_prime)
  · rw [hEq]; exact not_dvd_73 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 74) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 75) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 76) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 77) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 78) hp_prime)
  · rw [hEq]; exact not_dvd_79 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 80) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 81) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 82) hp_prime)
  · rw [hEq]; exact not_dvd_83 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 84) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 85) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 86) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 87) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 88) hp_prime)
  · rw [hEq]; exact not_dvd_89 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 90) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 91) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 92) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 93) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 94) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 95) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 96) hp_prime)
  · rw [hEq]; exact not_dvd_97 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 98) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 99) hp_prime)

lemma no_small_prime_100_150 (N n p : ℕ) (hEq : N = 2^(2^(58*n+26)+2) + 3)
  (hC1 : ¬ covered_by_C1 (58 * n + 26))
  (hC2 : ¬ covered_by_C2 (58 * n + 26))
  (hC3 : ¬ covered_by_C3 (58 * n + 26))
  (hp_ge : 100 ≤ p) (hp_lt : p < 150) (hp_prime : p.Prime) : ¬ p ∣ N := by
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 100) hp_prime)
  · rw [hEq]; exact not_dvd_101 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 102) hp_prime)
  · rw [hEq]; exact not_dvd_103 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 104) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 105) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 106) hp_prime)
  · rw [hEq]; exact not_dvd_107 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 108) hp_prime)
  · rw [hEq]; exact not_dvd_109 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 110) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 111) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 112) hp_prime)
  · rw [hEq]; exact not_dvd_113 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 114) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 115) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 116) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 117) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 118) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 119) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 120) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 121) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 122) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 123) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 124) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 125) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 126) hp_prime)
  · rw [hEq]; exact not_dvd_127 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 128) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 129) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 130) hp_prime)
  · rw [hEq]; exact not_dvd_131 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 132) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 133) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 134) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 135) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 136) hp_prime)
  · rw [hEq]; exact not_dvd_137 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 138) hp_prime)
  · rw [hEq]; exact not_dvd_139 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 140) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 141) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 142) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 143) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 144) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 145) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 146) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 147) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 148) hp_prime)
  · rw [hEq]; exact not_dvd_149 n hC1 hC2 hC3

lemma no_small_prime_150_200 (N n p : ℕ) (hEq : N = 2^(2^(58*n+26)+2) + 3)
  (hC1 : ¬ covered_by_C1 (58 * n + 26))
  (hC2 : ¬ covered_by_C2 (58 * n + 26))
  (hC3 : ¬ covered_by_C3 (58 * n + 26))
  (hp_ge : 150 ≤ p) (hp_lt : p < 200) (hp_prime : p.Prime) : ¬ p ∣ N := by
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 150) hp_prime)
  · rw [hEq]; exact not_dvd_151 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 152) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 153) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 154) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 155) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 156) hp_prime)
  · rw [hEq]; exact not_dvd_157 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 158) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 159) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 160) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 161) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 162) hp_prime)
  · rw [hEq]; exact not_dvd_163 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 164) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 165) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 166) hp_prime)
  · rw [hEq]; exact not_dvd_167 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 168) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 169) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 170) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 171) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 172) hp_prime)
  · rw [hEq]; exact not_dvd_173 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 174) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 175) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 176) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 177) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 178) hp_prime)
  · rw [hEq]; exact not_dvd_179 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 180) hp_prime)
  · rw [hEq]; exact not_dvd_181 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 182) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 183) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 184) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 185) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 186) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 187) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 188) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 189) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 190) hp_prime)
  · rw [hEq]; exact not_dvd_191 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 192) hp_prime)
  · rw [hEq]; exact not_dvd_193 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 194) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 195) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 196) hp_prime)
  · rw [hEq]; exact not_dvd_197 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 198) hp_prime)
  · rw [hEq]; exact not_dvd_199 n hC1 hC2 hC3

lemma no_small_prime_200_250 (N n p : ℕ) (hEq : N = 2^(2^(58*n+26)+2) + 3)
  (hC1 : ¬ covered_by_C1 (58 * n + 26))
  (hC2 : ¬ covered_by_C2 (58 * n + 26))
  (hC3 : ¬ covered_by_C3 (58 * n + 26))
  (hp_ge : 200 ≤ p) (hp_lt : p < 250) (hp_prime : p.Prime) : ¬ p ∣ N := by
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 200) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 201) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 202) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 203) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 204) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 205) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 206) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 207) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 208) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 209) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 210) hp_prime)
  · rw [hEq]; exact not_dvd_211 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 212) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 213) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 214) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 215) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 216) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 217) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 218) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 219) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 220) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 221) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 222) hp_prime)
  · rw [hEq]; exact not_dvd_223 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 224) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 225) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 226) hp_prime)
  · rw [hEq]; exact not_dvd_227 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 228) hp_prime)
  · rw [hEq]; exact not_dvd_229 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 230) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 231) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 232) hp_prime)
  · rw [hEq]; exact not_dvd_233 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 234) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 235) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 236) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 237) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 238) hp_prime)
  · rw [hEq]; exact not_dvd_239 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 240) hp_prime)
  · rw [hEq]; exact not_dvd_241 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 242) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 243) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 244) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 245) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 246) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 247) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 248) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 249) hp_prime)

lemma no_small_prime_250_300 (N n p : ℕ) (hEq : N = 2^(2^(58*n+26)+2) + 3)
  (hC1 : ¬ covered_by_C1 (58 * n + 26))
  (hC2 : ¬ covered_by_C2 (58 * n + 26))
  (hC3 : ¬ covered_by_C3 (58 * n + 26))
  (hp_ge : 250 ≤ p) (hp_lt : p < 300) (hp_prime : p.Prime) : ¬ p ∣ N := by
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 250) hp_prime)
  · rw [hEq]; exact not_dvd_251 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 252) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 253) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 254) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 255) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 256) hp_prime)
  · rw [hEq]; exact not_dvd_257 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 258) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 259) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 260) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 261) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 262) hp_prime)
  · rw [hEq]; exact not_dvd_263 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 264) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 265) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 266) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 267) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 268) hp_prime)
  · rw [hEq]; exact not_dvd_269 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 270) hp_prime)
  · rw [hEq]; exact not_dvd_271 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 272) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 273) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 274) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 275) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 276) hp_prime)
  · rw [hEq]; exact not_dvd_277 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 278) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 279) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 280) hp_prime)
  · rw [hEq]; exact not_dvd_281 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 282) hp_prime)
  · rw [hEq]; exact not_dvd_283 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 284) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 285) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 286) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 287) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 288) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 289) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 290) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 291) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 292) hp_prime)
  · rw [hEq]; exact not_dvd_293 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 294) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 295) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 296) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 297) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 298) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 299) hp_prime)

lemma no_small_prime_300_350 (N n p : ℕ) (hEq : N = 2^(2^(58*n+26)+2) + 3)
  (hC1 : ¬ covered_by_C1 (58 * n + 26))
  (hC2 : ¬ covered_by_C2 (58 * n + 26))
  (hC3 : ¬ covered_by_C3 (58 * n + 26))
  (hp_ge : 300 ≤ p) (hp_lt : p < 350) (hp_prime : p.Prime) : ¬ p ∣ N := by
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 300) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 301) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 302) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 303) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 304) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 305) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 306) hp_prime)
  · rw [hEq]; exact not_dvd_307 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 308) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 309) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 310) hp_prime)
  · rw [hEq]; exact not_dvd_311 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 312) hp_prime)
  · rw [hEq]; exact not_dvd_313 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 314) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 315) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 316) hp_prime)
  · rw [hEq]; exact not_dvd_317 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 318) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 319) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 320) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 321) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 322) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 323) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 324) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 325) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 326) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 327) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 328) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 329) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 330) hp_prime)
  · rw [hEq]; exact not_dvd_331 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 332) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 333) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 334) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 335) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 336) hp_prime)
  · rw [hEq]; exact not_dvd_337 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 338) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 339) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 340) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 341) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 342) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 343) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 344) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 345) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 346) hp_prime)
  · rw [hEq]; exact not_dvd_347 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 348) hp_prime)
  · rw [hEq]; exact not_dvd_349 n hC1 hC2 hC3

lemma no_small_prime_350_400 (N n p : ℕ) (hEq : N = 2^(2^(58*n+26)+2) + 3)
  (hC1 : ¬ covered_by_C1 (58 * n + 26))
  (hC2 : ¬ covered_by_C2 (58 * n + 26))
  (hC3 : ¬ covered_by_C3 (58 * n + 26))
  (hp_ge : 350 ≤ p) (hp_lt : p < 400) (hp_prime : p.Prime) : ¬ p ∣ N := by
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 350) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 351) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 352) hp_prime)
  · rw [hEq]; exact not_dvd_353 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 354) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 355) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 356) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 357) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 358) hp_prime)
  · rw [hEq]; exact not_dvd_359 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 360) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 361) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 362) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 363) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 364) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 365) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 366) hp_prime)
  · rw [hEq]; exact not_dvd_367 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 368) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 369) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 370) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 371) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 372) hp_prime)
  · rw [hEq]; exact not_dvd_373 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 374) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 375) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 376) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 377) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 378) hp_prime)
  · rw [hEq]; exact not_dvd_379 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 380) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 381) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 382) hp_prime)
  · rw [hEq]; exact not_dvd_383 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 384) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 385) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 386) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 387) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 388) hp_prime)
  · rw [hEq]; exact not_dvd_389 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 390) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 391) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 392) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 393) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 394) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 395) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 396) hp_prime)
  · rw [hEq]; exact not_dvd_397 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 398) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 399) hp_prime)

lemma no_small_prime_400_450 (N n p : ℕ) (hEq : N = 2^(2^(58*n+26)+2) + 3)
  (hC1 : ¬ covered_by_C1 (58 * n + 26))
  (hC2 : ¬ covered_by_C2 (58 * n + 26))
  (hC3 : ¬ covered_by_C3 (58 * n + 26))
  (hp_ge : 400 ≤ p) (hp_lt : p < 450) (hp_prime : p.Prime) : ¬ p ∣ N := by
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 400) hp_prime)
  · rw [hEq]; exact not_dvd_401 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 402) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 403) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 404) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 405) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 406) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 407) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 408) hp_prime)
  · rw [hEq]; exact not_dvd_409 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 410) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 411) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 412) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 413) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 414) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 415) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 416) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 417) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 418) hp_prime)
  · rw [hEq]; exact not_dvd_419 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 420) hp_prime)
  · rw [hEq]; exact not_dvd_421 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 422) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 423) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 424) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 425) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 426) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 427) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 428) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 429) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 430) hp_prime)
  · rw [hEq]; exact not_dvd_431 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 432) hp_prime)
  · rw [hEq]; exact not_dvd_433 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 434) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 435) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 436) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 437) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 438) hp_prime)
  · rw [hEq]; exact not_dvd_439 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 440) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 441) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 442) hp_prime)
  · rw [hEq]; exact not_dvd_443 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 444) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 445) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 446) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 447) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 448) hp_prime)
  · rw [hEq]; exact not_dvd_449 n hC1 hC2 hC3

lemma no_small_prime_450_500 (N n p : ℕ) (hEq : N = 2^(2^(58*n+26)+2) + 3)
  (hC1 : ¬ covered_by_C1 (58 * n + 26))
  (hC2 : ¬ covered_by_C2 (58 * n + 26))
  (hC3 : ¬ covered_by_C3 (58 * n + 26))
  (hp_ge : 450 ≤ p) (hp_lt : p < 500) (hp_prime : p.Prime) : ¬ p ∣ N := by
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 450) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 451) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 452) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 453) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 454) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 455) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 456) hp_prime)
  · rw [hEq]; exact not_dvd_457 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 458) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 459) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 460) hp_prime)
  · rw [hEq]; exact not_dvd_461 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 462) hp_prime)
  · rw [hEq]; exact not_dvd_463 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 464) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 465) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 466) hp_prime)
  · rw [hEq]; exact not_dvd_467 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 468) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 469) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 470) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 471) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 472) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 473) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 474) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 475) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 476) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 477) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 478) hp_prime)
  · rw [hEq]; exact not_dvd_479 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 480) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 481) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 482) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 483) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 484) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 485) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 486) hp_prime)
  · rw [hEq]; exact not_dvd_487 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 488) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 489) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 490) hp_prime)
  · rw [hEq]; exact not_dvd_491 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 492) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 493) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 494) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 495) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 496) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 497) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 498) hp_prime)
  · rw [hEq]; exact not_dvd_499 n hC1 hC2 hC3

lemma no_small_prime_500_550 (N n p : ℕ) (hEq : N = 2^(2^(58*n+26)+2) + 3)
  (hC1 : ¬ covered_by_C1 (58 * n + 26))
  (hC2 : ¬ covered_by_C2 (58 * n + 26))
  (hC3 : ¬ covered_by_C3 (58 * n + 26))
  (hp_ge : 500 ≤ p) (hp_lt : p < 550) (hp_prime : p.Prime) : ¬ p ∣ N := by
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 500) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 501) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 502) hp_prime)
  · rw [hEq]; exact not_dvd_503 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 504) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 505) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 506) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 507) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 508) hp_prime)
  · rw [hEq]; exact not_dvd_509 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 510) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 511) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 512) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 513) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 514) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 515) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 516) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 517) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 518) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 519) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 520) hp_prime)
  · rw [hEq]; exact not_dvd_521 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 522) hp_prime)
  · rw [hEq]; exact not_dvd_523 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 524) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 525) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 526) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 527) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 528) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 529) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 530) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 531) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 532) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 533) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 534) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 535) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 536) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 537) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 538) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 539) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 540) hp_prime)
  · rw [hEq]; exact not_dvd_541 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 542) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 543) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 544) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 545) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 546) hp_prime)
  · rw [hEq]; exact not_dvd_547 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 548) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 549) hp_prime)

lemma no_small_prime_550_600 (N n p : ℕ) (hEq : N = 2^(2^(58*n+26)+2) + 3)
  (hC1 : ¬ covered_by_C1 (58 * n + 26))
  (hC2 : ¬ covered_by_C2 (58 * n + 26))
  (hC3 : ¬ covered_by_C3 (58 * n + 26))
  (hp_ge : 550 ≤ p) (hp_lt : p < 600) (hp_prime : p.Prime) : ¬ p ∣ N := by
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 550) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 551) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 552) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 553) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 554) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 555) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 556) hp_prime)
  · rw [hEq]; exact not_dvd_557 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 558) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 559) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 560) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 561) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 562) hp_prime)
  · rw [hEq]; exact not_dvd_563 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 564) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 565) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 566) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 567) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 568) hp_prime)
  · rw [hEq]; exact not_dvd_569 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 570) hp_prime)
  · rw [hEq]; exact not_dvd_571 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 572) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 573) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 574) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 575) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 576) hp_prime)
  · rw [hEq]; exact not_dvd_577 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 578) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 579) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 580) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 581) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 582) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 583) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 584) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 585) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 586) hp_prime)
  · rw [hEq]; exact not_dvd_587 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 588) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 589) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 590) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 591) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 592) hp_prime)
  · rw [hEq]; exact not_dvd_593 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 594) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 595) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 596) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 597) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 598) hp_prime)
  · rw [hEq]; exact not_dvd_599 n hC1 hC2 hC3

lemma no_small_prime_600_650 (N n p : ℕ) (hEq : N = 2^(2^(58*n+26)+2) + 3)
  (hC1 : ¬ covered_by_C1 (58 * n + 26))
  (hC2 : ¬ covered_by_C2 (58 * n + 26))
  (hC3 : ¬ covered_by_C3 (58 * n + 26))
  (hp_ge : 600 ≤ p) (hp_lt : p < 650) (hp_prime : p.Prime) : ¬ p ∣ N := by
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 600) hp_prime)
  · rw [hEq]; exact not_dvd_601 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 602) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 603) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 604) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 605) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 606) hp_prime)
  · rw [hEq]; exact not_dvd_607 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 608) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 609) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 610) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 611) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 612) hp_prime)
  · rw [hEq]; exact not_dvd_613 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 614) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 615) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 616) hp_prime)
  · rw [hEq]; exact not_dvd_617 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 618) hp_prime)
  · rw [hEq]; exact not_dvd_619 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 620) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 621) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 622) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 623) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 624) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 625) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 626) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 627) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 628) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 629) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 630) hp_prime)
  · rw [hEq]; exact not_dvd_631 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 632) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 633) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 634) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 635) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 636) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 637) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 638) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 639) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 640) hp_prime)
  · rw [hEq]; exact not_dvd_641 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 642) hp_prime)
  · rw [hEq]; exact not_dvd_643 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 644) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 645) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 646) hp_prime)
  · rw [hEq]; exact not_dvd_647 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 648) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 649) hp_prime)

lemma no_small_prime_650_700 (N n p : ℕ) (hEq : N = 2^(2^(58*n+26)+2) + 3)
  (hC1 : ¬ covered_by_C1 (58 * n + 26))
  (hC2 : ¬ covered_by_C2 (58 * n + 26))
  (hC3 : ¬ covered_by_C3 (58 * n + 26))
  (hp_ge : 650 ≤ p) (hp_lt : p < 700) (hp_prime : p.Prime) : ¬ p ∣ N := by
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 650) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 651) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 652) hp_prime)
  · rw [hEq]; exact not_dvd_653 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 654) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 655) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 656) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 657) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 658) hp_prime)
  · rw [hEq]; exact not_dvd_659 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 660) hp_prime)
  · rw [hEq]; exact not_dvd_661 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 662) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 663) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 664) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 665) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 666) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 667) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 668) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 669) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 670) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 671) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 672) hp_prime)
  · rw [hEq]; exact not_dvd_673 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 674) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 675) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 676) hp_prime)
  · rw [hEq]; exact not_dvd_677 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 678) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 679) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 680) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 681) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 682) hp_prime)
  · rw [hEq]; exact not_dvd_683 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 684) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 685) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 686) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 687) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 688) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 689) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 690) hp_prime)
  · rw [hEq]; exact not_dvd_691 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 692) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 693) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 694) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 695) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 696) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 697) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 698) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 699) hp_prime)

lemma no_small_prime_700_750 (N n p : ℕ) (hEq : N = 2^(2^(58*n+26)+2) + 3)
  (hC1 : ¬ covered_by_C1 (58 * n + 26))
  (hC2 : ¬ covered_by_C2 (58 * n + 26))
  (hC3 : ¬ covered_by_C3 (58 * n + 26))
  (hp_ge : 700 ≤ p) (hp_lt : p < 750) (hp_prime : p.Prime) : ¬ p ∣ N := by
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 700) hp_prime)
  · rw [hEq]; exact not_dvd_701 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 702) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 703) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 704) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 705) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 706) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 707) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 708) hp_prime)
  · rw [hEq]; exact not_dvd_709 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 710) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 711) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 712) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 713) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 714) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 715) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 716) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 717) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 718) hp_prime)
  · rw [hEq]; exact not_dvd_719 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 720) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 721) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 722) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 723) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 724) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 725) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 726) hp_prime)
  · rw [hEq]; exact not_dvd_727 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 728) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 729) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 730) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 731) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 732) hp_prime)
  · rw [hEq]; exact not_dvd_733 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 734) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 735) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 736) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 737) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 738) hp_prime)
  · rw [hEq]; exact not_dvd_739 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 740) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 741) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 742) hp_prime)
  · rw [hEq]; exact not_dvd_743 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 744) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 745) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 746) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 747) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 748) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 749) hp_prime)

lemma no_small_prime_750_800 (N n p : ℕ) (hEq : N = 2^(2^(58*n+26)+2) + 3)
  (hC1 : ¬ covered_by_C1 (58 * n + 26))
  (hC2 : ¬ covered_by_C2 (58 * n + 26))
  (hC3 : ¬ covered_by_C3 (58 * n + 26))
  (hp_ge : 750 ≤ p) (hp_lt : p < 800) (hp_prime : p.Prime) : ¬ p ∣ N := by
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 750) hp_prime)
  · rw [hEq]; exact not_dvd_751 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 752) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 753) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 754) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 755) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 756) hp_prime)
  · rw [hEq]; exact not_dvd_757 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 758) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 759) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 760) hp_prime)
  · rw [hEq]; exact not_dvd_761 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 762) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 763) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 764) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 765) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 766) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 767) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 768) hp_prime)
  · rw [hEq]; exact not_dvd_769 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 770) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 771) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 772) hp_prime)
  · rw [hEq]; exact not_dvd_773 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 774) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 775) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 776) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 777) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 778) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 779) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 780) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 781) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 782) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 783) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 784) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 785) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 786) hp_prime)
  · rw [hEq]; exact not_dvd_787 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 788) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 789) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 790) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 791) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 792) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 793) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 794) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 795) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 796) hp_prime)
  · rw [hEq]; exact not_dvd_797 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 798) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 799) hp_prime)

lemma no_small_prime_800_850 (N n p : ℕ) (hEq : N = 2^(2^(58*n+26)+2) + 3)
  (hC1 : ¬ covered_by_C1 (58 * n + 26))
  (hC2 : ¬ covered_by_C2 (58 * n + 26))
  (hC3 : ¬ covered_by_C3 (58 * n + 26))
  (hp_ge : 800 ≤ p) (hp_lt : p < 850) (hp_prime : p.Prime) : ¬ p ∣ N := by
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 800) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 801) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 802) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 803) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 804) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 805) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 806) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 807) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 808) hp_prime)
  · rw [hEq]; exact not_dvd_809 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 810) hp_prime)
  · rw [hEq]; exact not_dvd_811 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 812) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 813) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 814) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 815) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 816) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 817) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 818) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 819) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 820) hp_prime)
  · rw [hEq]; exact not_dvd_821 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 822) hp_prime)
  · rw [hEq]; exact not_dvd_823 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 824) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 825) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 826) hp_prime)
  · rw [hEq]; exact not_dvd_827 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 828) hp_prime)
  · rw [hEq]; exact not_dvd_829 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 830) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 831) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 832) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 833) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 834) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 835) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 836) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 837) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 838) hp_prime)
  · rw [hEq]; exact not_dvd_839 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 840) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 841) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 842) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 843) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 844) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 845) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 846) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 847) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 848) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 849) hp_prime)

lemma no_small_prime_850_900 (N n p : ℕ) (hEq : N = 2^(2^(58*n+26)+2) + 3)
  (hC1 : ¬ covered_by_C1 (58 * n + 26))
  (hC2 : ¬ covered_by_C2 (58 * n + 26))
  (hC3 : ¬ covered_by_C3 (58 * n + 26))
  (hp_ge : 850 ≤ p) (hp_lt : p < 900) (hp_prime : p.Prime) : ¬ p ∣ N := by
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 850) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 851) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 852) hp_prime)
  · rw [hEq]; exact not_dvd_853 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 854) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 855) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 856) hp_prime)
  · rw [hEq]; exact not_dvd_857 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 858) hp_prime)
  · rw [hEq]; exact not_dvd_859 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 860) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 861) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 862) hp_prime)
  · rw [hEq]; exact not_dvd_863 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 864) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 865) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 866) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 867) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 868) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 869) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 870) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 871) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 872) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 873) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 874) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 875) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 876) hp_prime)
  · rw [hEq]; exact not_dvd_877 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 878) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 879) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 880) hp_prime)
  · rw [hEq]; exact not_dvd_881 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 882) hp_prime)
  · rw [hEq]; exact not_dvd_883 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 884) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 885) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 886) hp_prime)
  · rw [hEq]; exact not_dvd_887 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 888) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 889) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 890) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 891) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 892) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 893) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 894) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 895) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 896) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 897) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 898) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 899) hp_prime)

lemma no_small_prime_900_950 (N n p : ℕ) (hEq : N = 2^(2^(58*n+26)+2) + 3)
  (hC1 : ¬ covered_by_C1 (58 * n + 26))
  (hC2 : ¬ covered_by_C2 (58 * n + 26))
  (hC3 : ¬ covered_by_C3 (58 * n + 26))
  (hp_ge : 900 ≤ p) (hp_lt : p < 950) (hp_prime : p.Prime) : ¬ p ∣ N := by
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 900) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 901) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 902) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 903) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 904) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 905) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 906) hp_prime)
  · rw [hEq]; exact not_dvd_907 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 908) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 909) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 910) hp_prime)
  · rw [hEq]; exact not_dvd_911 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 912) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 913) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 914) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 915) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 916) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 917) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 918) hp_prime)
  · rw [hEq]; exact not_dvd_919 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 920) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 921) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 922) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 923) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 924) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 925) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 926) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 927) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 928) hp_prime)
  · rw [hEq]; exact not_dvd_929 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 930) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 931) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 932) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 933) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 934) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 935) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 936) hp_prime)
  · rw [hEq]; exact not_dvd_937 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 938) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 939) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 940) hp_prime)
  · rw [hEq]; exact not_dvd_941 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 942) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 943) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 944) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 945) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 946) hp_prime)
  · rw [hEq]; exact not_dvd_947 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 948) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 949) hp_prime)

lemma no_small_prime_950_1000 (N n p : ℕ) (hEq : N = 2^(2^(58*n+26)+2) + 3)
  (hC1 : ¬ covered_by_C1 (58 * n + 26))
  (hC2 : ¬ covered_by_C2 (58 * n + 26))
  (hC3 : ¬ covered_by_C3 (58 * n + 26))
  (hp_ge : 950 ≤ p) (hp_lt : p < 1000) (hp_prime : p.Prime) : ¬ p ∣ N := by
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 950) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 951) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 952) hp_prime)
  · rw [hEq]; exact not_dvd_953 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 954) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 955) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 956) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 957) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 958) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 959) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 960) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 961) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 962) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 963) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 964) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 965) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 966) hp_prime)
  · rw [hEq]; exact not_dvd_967 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 968) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 969) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 970) hp_prime)
  · rw [hEq]; exact not_dvd_971 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 972) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 973) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 974) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 975) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 976) hp_prime)
  · rw [hEq]; exact not_dvd_977 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 978) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 979) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 980) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 981) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 982) hp_prime)
  · rw [hEq]; exact not_dvd_983 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 984) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 985) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 986) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 987) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 988) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 989) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 990) hp_prime)
  · rw [hEq]; exact not_dvd_991 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 992) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 993) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 994) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 995) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 996) hp_prime)
  · rw [hEq]; exact not_dvd_997 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 998) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 999) hp_prime)

lemma no_small_prime_1000_1050 (N n p : ℕ) (hEq : N = 2^(2^(58*n+26)+2) + 3)
  (hC1 : ¬ covered_by_C1 (58 * n + 26))
  (hC2 : ¬ covered_by_C2 (58 * n + 26))
  (hC3 : ¬ covered_by_C3 (58 * n + 26))
  (hp_ge : 1000 ≤ p) (hp_lt : p < 1050) (hp_prime : p.Prime) : ¬ p ∣ N := by
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 1000) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1001) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1002) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1003) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1004) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1005) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1006) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1007) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1008) hp_prime)
  · rw [hEq]; exact not_dvd_1009 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1010) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1011) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1012) hp_prime)
  · rw [hEq]; exact not_dvd_1013 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1014) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1015) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1016) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1017) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1018) hp_prime)
  · rw [hEq]; exact not_dvd_1019 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1020) hp_prime)
  · rw [hEq]; exact not_dvd_1021 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1022) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1023) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1024) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1025) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1026) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1027) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1028) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1029) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1030) hp_prime)
  · rw [hEq]; exact not_dvd_1031 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1032) hp_prime)
  · rw [hEq]; exact not_dvd_1033 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1034) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1035) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1036) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1037) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1038) hp_prime)
  · rw [hEq]; exact not_dvd_1039 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1040) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1041) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1042) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1043) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1044) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1045) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1046) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1047) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1048) hp_prime)
  · rw [hEq]; exact not_dvd_1049 n hC1 hC2 hC3

lemma no_small_prime_1050_1100 (N n p : ℕ) (hEq : N = 2^(2^(58*n+26)+2) + 3)
  (hC1 : ¬ covered_by_C1 (58 * n + 26))
  (hC2 : ¬ covered_by_C2 (58 * n + 26))
  (hC3 : ¬ covered_by_C3 (58 * n + 26))
  (hp_ge : 1050 ≤ p) (hp_lt : p < 1100) (hp_prime : p.Prime) : ¬ p ∣ N := by
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 1050) hp_prime)
  · rw [hEq]; exact not_dvd_1051 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1052) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1053) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1054) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1055) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1056) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1057) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1058) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1059) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1060) hp_prime)
  · rw [hEq]; exact not_dvd_1061 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1062) hp_prime)
  · rw [hEq]; exact not_dvd_1063 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1064) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1065) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1066) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1067) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1068) hp_prime)
  · rw [hEq]; exact not_dvd_1069 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1070) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1071) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1072) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1073) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1074) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1075) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1076) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1077) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1078) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1079) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1080) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1081) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1082) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1083) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1084) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1085) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1086) hp_prime)
  · rw [hEq]; exact not_dvd_1087 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1088) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1089) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1090) hp_prime)
  · rw [hEq]; exact not_dvd_1091 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1092) hp_prime)
  · rw [hEq]; exact not_dvd_1093 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1094) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1095) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1096) hp_prime)
  · rw [hEq]; exact not_dvd_1097 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1098) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1099) hp_prime)

lemma no_small_prime_1100_1150 (N n p : ℕ) (hEq : N = 2^(2^(58*n+26)+2) + 3)
  (hC1 : ¬ covered_by_C1 (58 * n + 26))
  (hC2 : ¬ covered_by_C2 (58 * n + 26))
  (hC3 : ¬ covered_by_C3 (58 * n + 26))
  (hp_ge : 1100 ≤ p) (hp_lt : p < 1150) (hp_prime : p.Prime) : ¬ p ∣ N := by
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 1100) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1101) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1102) hp_prime)
  · rw [hEq]; exact not_dvd_1103 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1104) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1105) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1106) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1107) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1108) hp_prime)
  · rw [hEq]; exact not_dvd_1109 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1110) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1111) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1112) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1113) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1114) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1115) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1116) hp_prime)
  · rw [hEq]; exact not_dvd_1117 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1118) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1119) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1120) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1121) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1122) hp_prime)
  · rw [hEq]; exact not_dvd_1123 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1124) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1125) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1126) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1127) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1128) hp_prime)
  · rw [hEq]; exact not_dvd_1129 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1130) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1131) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1132) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1133) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1134) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1135) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1136) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1137) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1138) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1139) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1140) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1141) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1142) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1143) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1144) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1145) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1146) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1147) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1148) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1149) hp_prime)

lemma no_small_prime_1150_1200 (N n p : ℕ) (hEq : N = 2^(2^(58*n+26)+2) + 3)
  (hC1 : ¬ covered_by_C1 (58 * n + 26))
  (hC2 : ¬ covered_by_C2 (58 * n + 26))
  (hC3 : ¬ covered_by_C3 (58 * n + 26))
  (hp_ge : 1150 ≤ p) (hp_lt : p < 1200) (hp_prime : p.Prime) : ¬ p ∣ N := by
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 1150) hp_prime)
  · rw [hEq]; exact not_dvd_1151 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1152) hp_prime)
  · rw [hEq]; exact not_dvd_1153 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1154) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1155) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1156) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1157) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1158) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1159) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1160) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1161) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1162) hp_prime)
  · rw [hEq]; exact not_dvd_1163 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1164) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1165) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1166) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1167) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1168) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1169) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1170) hp_prime)
  · rw [hEq]; exact not_dvd_1171 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1172) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1173) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1174) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1175) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1176) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1177) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1178) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1179) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1180) hp_prime)
  · rw [hEq]; exact not_dvd_1181 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1182) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1183) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1184) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1185) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1186) hp_prime)
  · rw [hEq]; exact not_dvd_1187 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1188) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1189) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1190) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1191) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1192) hp_prime)
  · rw [hEq]; exact not_dvd_1193 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1194) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1195) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1196) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1197) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1198) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1199) hp_prime)

lemma no_small_prime_1200_1250 (N n p : ℕ) (hEq : N = 2^(2^(58*n+26)+2) + 3)
  (hC1 : ¬ covered_by_C1 (58 * n + 26))
  (hC2 : ¬ covered_by_C2 (58 * n + 26))
  (hC3 : ¬ covered_by_C3 (58 * n + 26))
  (hp_ge : 1200 ≤ p) (hp_lt : p < 1250) (hp_prime : p.Prime) : ¬ p ∣ N := by
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 1200) hp_prime)
  · rw [hEq]; exact not_dvd_1201 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1202) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1203) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1204) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1205) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1206) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1207) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1208) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1209) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1210) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1211) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1212) hp_prime)
  · rw [hEq]; exact not_dvd_1213 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1214) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1215) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1216) hp_prime)
  · rw [hEq]; exact not_dvd_1217 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1218) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1219) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1220) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1221) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1222) hp_prime)
  · rw [hEq]; exact not_dvd_1223 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1224) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1225) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1226) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1227) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1228) hp_prime)
  · rw [hEq]; exact not_dvd_1229 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1230) hp_prime)
  · rw [hEq]; exact not_dvd_1231 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1232) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1233) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1234) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1235) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1236) hp_prime)
  · rw [hEq]; exact not_dvd_1237 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1238) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1239) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1240) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1241) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1242) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1243) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1244) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1245) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1246) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1247) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1248) hp_prime)
  · rw [hEq]; exact not_dvd_1249 n hC1 hC2 hC3

lemma no_small_prime_1250_1300 (N n p : ℕ) (hEq : N = 2^(2^(58*n+26)+2) + 3)
  (hC1 : ¬ covered_by_C1 (58 * n + 26))
  (hC2 : ¬ covered_by_C2 (58 * n + 26))
  (hC3 : ¬ covered_by_C3 (58 * n + 26))
  (hp_ge : 1250 ≤ p) (hp_lt : p < 1300) (hp_prime : p.Prime) : ¬ p ∣ N := by
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 1250) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1251) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1252) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1253) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1254) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1255) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1256) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1257) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1258) hp_prime)
  · rw [hEq]; exact not_dvd_1259 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1260) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1261) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1262) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1263) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1264) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1265) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1266) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1267) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1268) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1269) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1270) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1271) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1272) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1273) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1274) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1275) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1276) hp_prime)
  · rw [hEq]; exact not_dvd_1277 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1278) hp_prime)
  · rw [hEq]; exact not_dvd_1279 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1280) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1281) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1282) hp_prime)
  · rw [hEq]; exact not_dvd_1283 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1284) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1285) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1286) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1287) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1288) hp_prime)
  · rw [hEq]; exact not_dvd_1289 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1290) hp_prime)
  · rw [hEq]; exact not_dvd_1291 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1292) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1293) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1294) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1295) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1296) hp_prime)
  · rw [hEq]; exact not_dvd_1297 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1298) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1299) hp_prime)

lemma no_small_prime_1300_1350 (N n p : ℕ) (hEq : N = 2^(2^(58*n+26)+2) + 3)
  (hC1 : ¬ covered_by_C1 (58 * n + 26))
  (hC2 : ¬ covered_by_C2 (58 * n + 26))
  (hC3 : ¬ covered_by_C3 (58 * n + 26))
  (hp_ge : 1300 ≤ p) (hp_lt : p < 1350) (hp_prime : p.Prime) : ¬ p ∣ N := by
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 1300) hp_prime)
  · rw [hEq]; exact not_dvd_1301 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1302) hp_prime)
  · rw [hEq]; exact not_dvd_1303 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1304) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1305) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1306) hp_prime)
  · rw [hEq]; exact not_dvd_1307 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1308) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1309) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1310) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1311) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1312) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1313) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1314) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1315) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1316) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1317) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1318) hp_prime)
  · rw [hEq]; exact not_dvd_1319 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1320) hp_prime)
  · rw [hEq]; exact not_dvd_1321 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1322) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1323) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1324) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1325) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1326) hp_prime)
  · rw [hEq]; exact not_dvd_1327 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1328) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1329) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1330) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1331) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1332) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1333) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1334) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1335) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1336) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1337) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1338) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1339) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1340) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1341) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1342) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1343) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1344) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1345) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1346) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1347) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1348) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1349) hp_prime)

lemma no_small_prime_1350_1399 (N n p : ℕ) (hEq : N = 2^(2^(58*n+26)+2) + 3)
  (hC1 : ¬ covered_by_C1 (58 * n + 26))
  (hC2 : ¬ covered_by_C2 (58 * n + 26))
  (hC3 : ¬ covered_by_C3 (58 * n + 26))
  (hp_ge : 1350 ≤ p) (hp_lt : p < 1399) (hp_prime : p.Prime) : ¬ p ∣ N := by
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 1350) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1351) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1352) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1353) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1354) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1355) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1356) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1357) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1358) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1359) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1360) hp_prime)
  · rw [hEq]; exact not_dvd_1361 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1362) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1363) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1364) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1365) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1366) hp_prime)
  · rw [hEq]; exact not_dvd_1367 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1368) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1369) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1370) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1371) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1372) hp_prime)
  · rw [hEq]; exact not_dvd_1373 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1374) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1375) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1376) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1377) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1378) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1379) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1380) hp_prime)
  · rw [hEq]; exact not_dvd_1381 n hC1 hC2 hC3
  · exact False.elim ((by decide : ¬ Nat.Prime 1382) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1383) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1384) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1385) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1386) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1387) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1388) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1389) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1390) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1391) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1392) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1393) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1394) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1395) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1396) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1397) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 1398) hp_prime)

lemma no_small_prime (N n : ℕ) (hEq : N = 2^(2^(58*n+26)+2) + 3)
  (hC1 : ¬ covered_by_C1 (58 * n + 26))
  (hC2 : ¬ covered_by_C2 (58 * n + 26))
  (hC3 : ¬ covered_by_C3 (58 * n + 26)) :
  ∀ p < 1399, p.Prime → ¬ p ∣ N := by
  intro p hp_lt hp_prime
  have hp_two : 2 ≤ p := hp_prime.two_le
  by_cases h_0 : p < 50
  · apply no_small_prime_0_50 N n p hEq hC1 hC2 hC3 (by omega) h_0 hp_prime
  by_cases h_50 : p < 100
  · apply no_small_prime_50_100 N n p hEq hC1 hC2 hC3 (by omega) h_50 hp_prime
  by_cases h_100 : p < 150
  · apply no_small_prime_100_150 N n p hEq hC1 hC2 hC3 (by omega) h_100 hp_prime
  by_cases h_150 : p < 200
  · apply no_small_prime_150_200 N n p hEq hC1 hC2 hC3 (by omega) h_150 hp_prime
  by_cases h_200 : p < 250
  · apply no_small_prime_200_250 N n p hEq hC1 hC2 hC3 (by omega) h_200 hp_prime
  by_cases h_250 : p < 300
  · apply no_small_prime_250_300 N n p hEq hC1 hC2 hC3 (by omega) h_250 hp_prime
  by_cases h_300 : p < 350
  · apply no_small_prime_300_350 N n p hEq hC1 hC2 hC3 (by omega) h_300 hp_prime
  by_cases h_350 : p < 400
  · apply no_small_prime_350_400 N n p hEq hC1 hC2 hC3 (by omega) h_350 hp_prime
  by_cases h_400 : p < 450
  · apply no_small_prime_400_450 N n p hEq hC1 hC2 hC3 (by omega) h_400 hp_prime
  by_cases h_450 : p < 500
  · apply no_small_prime_450_500 N n p hEq hC1 hC2 hC3 (by omega) h_450 hp_prime
  by_cases h_500 : p < 550
  · apply no_small_prime_500_550 N n p hEq hC1 hC2 hC3 (by omega) h_500 hp_prime
  by_cases h_550 : p < 600
  · apply no_small_prime_550_600 N n p hEq hC1 hC2 hC3 (by omega) h_550 hp_prime
  by_cases h_600 : p < 650
  · apply no_small_prime_600_650 N n p hEq hC1 hC2 hC3 (by omega) h_600 hp_prime
  by_cases h_650 : p < 700
  · apply no_small_prime_650_700 N n p hEq hC1 hC2 hC3 (by omega) h_650 hp_prime
  by_cases h_700 : p < 750
  · apply no_small_prime_700_750 N n p hEq hC1 hC2 hC3 (by omega) h_700 hp_prime
  by_cases h_750 : p < 800
  · apply no_small_prime_750_800 N n p hEq hC1 hC2 hC3 (by omega) h_750 hp_prime
  by_cases h_800 : p < 850
  · apply no_small_prime_800_850 N n p hEq hC1 hC2 hC3 (by omega) h_800 hp_prime
  by_cases h_850 : p < 900
  · apply no_small_prime_850_900 N n p hEq hC1 hC2 hC3 (by omega) h_850 hp_prime
  by_cases h_900 : p < 950
  · apply no_small_prime_900_950 N n p hEq hC1 hC2 hC3 (by omega) h_900 hp_prime
  by_cases h_950 : p < 1000
  · apply no_small_prime_950_1000 N n p hEq hC1 hC2 hC3 (by omega) h_950 hp_prime
  by_cases h_1000 : p < 1050
  · apply no_small_prime_1000_1050 N n p hEq hC1 hC2 hC3 (by omega) h_1000 hp_prime
  by_cases h_1050 : p < 1100
  · apply no_small_prime_1050_1100 N n p hEq hC1 hC2 hC3 (by omega) h_1050 hp_prime
  by_cases h_1100 : p < 1150
  · apply no_small_prime_1100_1150 N n p hEq hC1 hC2 hC3 (by omega) h_1100 hp_prime
  by_cases h_1150 : p < 1200
  · apply no_small_prime_1150_1200 N n p hEq hC1 hC2 hC3 (by omega) h_1150 hp_prime
  by_cases h_1200 : p < 1250
  · apply no_small_prime_1200_1250 N n p hEq hC1 hC2 hC3 (by omega) h_1200 hp_prime
  by_cases h_1250 : p < 1300
  · apply no_small_prime_1250_1300 N n p hEq hC1 hC2 hC3 (by omega) h_1250 hp_prime
  by_cases h_1300 : p < 1350
  · apply no_small_prime_1300_1350 N n p hEq hC1 hC2 hC3 (by omega) h_1300 hp_prime
  by_cases h_1350 : p < 1399
  · apply no_small_prime_1350_1399 N n p hEq hC1 hC2 hC3 (by omega) h_1350 hp_prime
  · exact False.elim (h_1350 hp_lt)


theorem oeis_248802_conjecture_4 (n : ℕ) :
  (¬ covered_by_C1 (58 * n + 26) ∧
   ¬ covered_by_C2 (58 * n + 26) ∧
   ¬ covered_by_C3 (58 * n + 26)) →
  a (58 * n + 26) = 1399 := by
  rintro ⟨hC1, hC2, hC3⟩
  dsimp [a]
  have H_val : (2 ^ (2 ^ (58 * n + 26) + 2) + 3) % 1399 = 0 := a_mod_1399 n
  have H_dvd : 1399 ∣ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := Nat.dvd_of_mod_eq_zero H_val
  have H_ge : 1399 ≤ (2 ^ (2 ^ (58 * n + 26) + 2) + 3).minFac := by
    have h_gt : 1 < 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := by
      calc 1 < 3 := by decide
        _ ≤ 2 ^ (2 ^ (58 * n + 26) + 2) + 3 := Nat.le_add_left 3 _
    apply minFac_ge _ h_gt
    exact no_small_prime _ n rfl hC1 hC2 hC3
  exact le_antisymm (Nat.minFac_le_of_dvd (by decide) H_dvd) H_ge

theorem oeis_248802_conjecture_4.disproof : ¬ (type_of% @oeis_248802_conjecture_4) := sorry

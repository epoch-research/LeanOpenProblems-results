import Submission.SimpleRootValuationObstruction
/-! An irreducible binary polynomial of degree37 with two-adic valuation47.
Its odd cofactor4745 excludes it from the original conjecture. -/
namespace Erdos406IrreducibleValuation
open Polynomial Erdos406Cyclotomic Erdos406FactorCount Erdos406FactorBridge
  Erdos406SimpleModTwoRoot
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private lemma modular_pow_step {p a e r b s : ℕ}
    (h : (a : ZMod p) ^ e = r)
    (hc : (r : ZMod p) ^ 2 * (a : ZMod p) ^ b = s) :
    (a : ZMod p) ^ (e * 2 + b) = s := by
  rw [pow_add, pow_mul, h]
  exact hc
private lemma prime_2 : Nat.Prime 2 := by norm_num
private lemma prime_53 : Nat.Prime 53 := by norm_num
private lemma prime_5 : Nat.Prime 5 := by norm_num
private lemma prime_29 : Nat.Prime 29 := by norm_num
private lemma prime_3 : Nat.Prime 3 := by norm_num
private lemma prime_31 : Nat.Prime 31 := by norm_num
lemma prime_4651 : Nat.Prime 4651 := by
  have h0 : (3 : ZMod 4651) ^ 0 = 1 := by simp
  have h1 : (3 : ZMod 4651) ^ 1 = 3 :=
    modular_pow_step (p := 4651) (a := 3) (e := 0) (r := 1) (b := 1) (s := 3) h0 (by decide +kernel)
  have h2 : (3 : ZMod 4651) ^ 2 = 9 :=
    modular_pow_step (p := 4651) (a := 3) (e := 1) (r := 3) (b := 0) (s := 9) h1 (by decide +kernel)
  have h3 : (3 : ZMod 4651) ^ 3 = 27 :=
    modular_pow_step (p := 4651) (a := 3) (e := 1) (r := 3) (b := 1) (s := 27) h1 (by decide +kernel)
  have h4 : (3 : ZMod 4651) ^ 4 = 81 :=
    modular_pow_step (p := 4651) (a := 3) (e := 2) (r := 9) (b := 0) (s := 81) h2 (by decide +kernel)
  have h6 : (3 : ZMod 4651) ^ 6 = 729 :=
    modular_pow_step (p := 4651) (a := 3) (e := 3) (r := 27) (b := 0) (s := 729) h3 (by decide +kernel)
  have h7 : (3 : ZMod 4651) ^ 7 = 2187 :=
    modular_pow_step (p := 4651) (a := 3) (e := 3) (r := 27) (b := 1) (s := 2187) h3 (by decide +kernel)
  have h9 : (3 : ZMod 4651) ^ 9 = 1079 :=
    modular_pow_step (p := 4651) (a := 3) (e := 4) (r := 81) (b := 1) (s := 1079) h4 (by decide +kernel)
  have h12 : (3 : ZMod 4651) ^ 12 = 1227 :=
    modular_pow_step (p := 4651) (a := 3) (e := 6) (r := 729) (b := 0) (s := 1227) h6 (by decide +kernel)
  have h14 : (3 : ZMod 4651) ^ 14 = 1741 :=
    modular_pow_step (p := 4651) (a := 3) (e := 7) (r := 2187) (b := 0) (s := 1741) h7 (by decide +kernel)
  have h18 : (3 : ZMod 4651) ^ 18 = 1491 :=
    modular_pow_step (p := 4651) (a := 3) (e := 9) (r := 1079) (b := 0) (s := 1491) h9 (by decide +kernel)
  have h24 : (3 : ZMod 4651) ^ 24 = 3256 :=
    modular_pow_step (p := 4651) (a := 3) (e := 12) (r := 1227) (b := 0) (s := 3256) h12 (by decide +kernel)
  have h29 : (3 : ZMod 4651) ^ 29 = 538 :=
    modular_pow_step (p := 4651) (a := 3) (e := 14) (r := 1741) (b := 1) (s := 538) h14 (by decide +kernel)
  have h36 : (3 : ZMod 4651) ^ 36 = 4554 :=
    modular_pow_step (p := 4651) (a := 3) (e := 18) (r := 1491) (b := 0) (s := 4554) h18 (by decide +kernel)
  have h37 : (3 : ZMod 4651) ^ 37 = 4360 :=
    modular_pow_step (p := 4651) (a := 3) (e := 18) (r := 1491) (b := 1) (s := 4360) h18 (by decide +kernel)
  have h48 : (3 : ZMod 4651) ^ 48 = 1907 :=
    modular_pow_step (p := 4651) (a := 3) (e := 24) (r := 3256) (b := 0) (s := 1907) h24 (by decide +kernel)
  have h58 : (3 : ZMod 4651) ^ 58 = 1082 :=
    modular_pow_step (p := 4651) (a := 3) (e := 29) (r := 538) (b := 0) (s := 1082) h29 (by decide +kernel)
  have h72 : (3 : ZMod 4651) ^ 72 = 107 :=
    modular_pow_step (p := 4651) (a := 3) (e := 36) (r := 4554) (b := 0) (s := 107) h36 (by decide +kernel)
  have h75 : (3 : ZMod 4651) ^ 75 = 2889 :=
    modular_pow_step (p := 4651) (a := 3) (e := 37) (r := 4360) (b := 1) (s := 2889) h37 (by decide +kernel)
  have h96 : (3 : ZMod 4651) ^ 96 = 4218 :=
    modular_pow_step (p := 4651) (a := 3) (e := 48) (r := 1907) (b := 0) (s := 4218) h48 (by decide +kernel)
  have h116 : (3 : ZMod 4651) ^ 116 = 3323 :=
    modular_pow_step (p := 4651) (a := 3) (e := 58) (r := 1082) (b := 0) (s := 3323) h58 (by decide +kernel)
  have h145 : (3 : ZMod 4651) ^ 145 = 1790 :=
    modular_pow_step (p := 4651) (a := 3) (e := 72) (r := 107) (b := 1) (s := 1790) h72 (by decide +kernel)
  have h150 : (3 : ZMod 4651) ^ 150 = 2427 :=
    modular_pow_step (p := 4651) (a := 3) (e := 75) (r := 2889) (b := 0) (s := 2427) h75 (by decide +kernel)
  have h193 : (3 : ZMod 4651) ^ 193 = 4347 :=
    modular_pow_step (p := 4651) (a := 3) (e := 96) (r := 4218) (b := 1) (s := 4347) h96 (by decide +kernel)
  have h232 : (3 : ZMod 4651) ^ 232 = 855 :=
    modular_pow_step (p := 4651) (a := 3) (e := 116) (r := 3323) (b := 0) (s := 855) h116 (by decide +kernel)
  have h290 : (3 : ZMod 4651) ^ 290 = 4212 :=
    modular_pow_step (p := 4651) (a := 3) (e := 145) (r := 1790) (b := 0) (s := 4212) h145 (by decide +kernel)
  have h387 : (3 : ZMod 4651) ^ 387 = 2839 :=
    modular_pow_step (p := 4651) (a := 3) (e := 193) (r := 4347) (b := 1) (s := 2839) h193 (by decide +kernel)
  have h465 : (3 : ZMod 4651) ^ 465 = 2454 :=
    modular_pow_step (p := 4651) (a := 3) (e := 232) (r := 855) (b := 1) (s := 2454) h232 (by decide +kernel)
  have h581 : (3 : ZMod 4651) ^ 581 = 1439 :=
    modular_pow_step (p := 4651) (a := 3) (e := 290) (r := 4212) (b := 1) (s := 1439) h290 (by decide +kernel)
  have h775 : (3 : ZMod 4651) ^ 775 = 3865 :=
    modular_pow_step (p := 4651) (a := 3) (e := 387) (r := 2839) (b := 1) (s := 3865) h387 (by decide +kernel)
  have h930 : (3 : ZMod 4651) ^ 930 = 3722 :=
    modular_pow_step (p := 4651) (a := 3) (e := 465) (r := 2454) (b := 0) (s := 3722) h465 (by decide +kernel)
  have h1162 : (3 : ZMod 4651) ^ 1162 = 1026 :=
    modular_pow_step (p := 4651) (a := 3) (e := 581) (r := 1439) (b := 0) (s := 1026) h581 (by decide +kernel)
  have h1550 : (3 : ZMod 4651) ^ 1550 = 3864 :=
    modular_pow_step (p := 4651) (a := 3) (e := 775) (r := 3865) (b := 0) (s := 3864) h775 (by decide +kernel)
  have h2325 : (3 : ZMod 4651) ^ 2325 = 4650 :=
    modular_pow_step (p := 4651) (a := 3) (e := 1162) (r := 1026) (b := 1) (s := 4650) h1162 (by decide +kernel)
  have h4650 : (3 : ZMod 4651) ^ 4650 = 1 :=
    modular_pow_step (p := 4651) (a := 3) (e := 2325) (r := 4650) (b := 0) (s := 1) h2325 (by decide +kernel)
  apply lucas_primality 4651 3 (by simpa using h4650)
  intro q hq hqd
  rw [show 4651 - 1 = (2 * 3 * 5 * 5 * 31 : ℕ) by norm_num] at hqd
  simp only [hq.dvd_mul, Nat.dvd_prime prime_2, Nat.dvd_prime prime_3, Nat.dvd_prime prime_5, Nat.dvd_prime prime_31, hq.ne_one, false_or] at hqd
  rcases hqd with ((((rfl | rfl) | rfl) | rfl) | rfl)
  · change (3 : ZMod 4651) ^ 2325 ≠ 1
    rw [h2325]
    decide +kernel
  · change (3 : ZMod 4651) ^ 1550 ≠ 1
    rw [h1550]
    decide +kernel
  · change (3 : ZMod 4651) ^ 930 ≠ 1
    rw [h930]
    decide +kernel
  · change (3 : ZMod 4651) ^ 930 ≠ 1
    rw [h930]
    decide +kernel
  · change (3 : ZMod 4651) ^ 150 ≠ 1
    rw [h150]
    decide +kernel

lemma prime_83719 : Nat.Prime 83719 := by
  have h0 : (6 : ZMod 83719) ^ 0 = 1 := by simp
  have h1 : (6 : ZMod 83719) ^ 1 = 6 :=
    modular_pow_step (p := 83719) (a := 6) (e := 0) (r := 1) (b := 1) (s := 6) h0 (by decide +kernel)
  have h2 : (6 : ZMod 83719) ^ 2 = 36 :=
    modular_pow_step (p := 83719) (a := 6) (e := 1) (r := 6) (b := 0) (s := 36) h1 (by decide +kernel)
  have h3 : (6 : ZMod 83719) ^ 3 = 216 :=
    modular_pow_step (p := 83719) (a := 6) (e := 1) (r := 6) (b := 1) (s := 216) h1 (by decide +kernel)
  have h4 : (6 : ZMod 83719) ^ 4 = 1296 :=
    modular_pow_step (p := 83719) (a := 6) (e := 2) (r := 36) (b := 0) (s := 1296) h2 (by decide +kernel)
  have h5 : (6 : ZMod 83719) ^ 5 = 7776 :=
    modular_pow_step (p := 83719) (a := 6) (e := 2) (r := 36) (b := 1) (s := 7776) h2 (by decide +kernel)
  have h6 : (6 : ZMod 83719) ^ 6 = 46656 :=
    modular_pow_step (p := 83719) (a := 6) (e := 3) (r := 216) (b := 0) (s := 46656) h3 (by decide +kernel)
  have h9 : (6 : ZMod 83719) ^ 9 = 31416 :=
    modular_pow_step (p := 83719) (a := 6) (e := 4) (r := 1296) (b := 1) (s := 31416) h4 (by decide +kernel)
  have h10 : (6 : ZMod 83719) ^ 10 = 21058 :=
    modular_pow_step (p := 83719) (a := 6) (e := 5) (r := 7776) (b := 0) (s := 21058) h5 (by decide +kernel)
  have h13 : (6 : ZMod 83719) ^ 13 = 27702 :=
    modular_pow_step (p := 83719) (a := 6) (e := 6) (r := 46656) (b := 1) (s := 27702) h6 (by decide +kernel)
  have h18 : (6 : ZMod 83719) ^ 18 = 1765 :=
    modular_pow_step (p := 83719) (a := 6) (e := 9) (r := 31416) (b := 0) (s := 1765) h9 (by decide +kernel)
  have h20 : (6 : ZMod 83719) ^ 20 = 63540 :=
    modular_pow_step (p := 83719) (a := 6) (e := 10) (r := 21058) (b := 0) (s := 63540) h10 (by decide +kernel)
  have h27 : (6 : ZMod 83719) ^ 27 = 27262 :=
    modular_pow_step (p := 83719) (a := 6) (e := 13) (r := 27702) (b := 1) (s := 27262) h13 (by decide +kernel)
  have h40 : (6 : ZMod 83719) ^ 40 = 66544 :=
    modular_pow_step (p := 83719) (a := 6) (e := 20) (r := 63540) (b := 0) (s := 66544) h20 (by decide +kernel)
  have h54 : (6 : ZMod 83719) ^ 54 = 43081 :=
    modular_pow_step (p := 83719) (a := 6) (e := 27) (r := 27262) (b := 0) (s := 43081) h27 (by decide +kernel)
  have h81 : (6 : ZMod 83719) ^ 81 = 64090 :=
    modular_pow_step (p := 83719) (a := 6) (e := 40) (r := 66544) (b := 1) (s := 64090) h40 (by decide +kernel)
  have h109 : (6 : ZMod 83719) ^ 109 = 36300 :=
    modular_pow_step (p := 83719) (a := 6) (e := 54) (r := 43081) (b := 1) (s := 36300) h54 (by decide +kernel)
  have h163 : (6 : ZMod 83719) ^ 163 = 53099 :=
    modular_pow_step (p := 83719) (a := 6) (e := 81) (r := 64090) (b := 1) (s := 53099) h81 (by decide +kernel)
  have h218 : (6 : ZMod 83719) ^ 218 = 36659 :=
    modular_pow_step (p := 83719) (a := 6) (e := 109) (r := 36300) (b := 0) (s := 36659) h109 (by decide +kernel)
  have h327 : (6 : ZMod 83719) ^ 327 = 8195 :=
    modular_pow_step (p := 83719) (a := 6) (e := 163) (r := 53099) (b := 1) (s := 8195) h163 (by decide +kernel)
  have h436 : (6 : ZMod 83719) ^ 436 = 24893 :=
    modular_pow_step (p := 83719) (a := 6) (e := 218) (r := 36659) (b := 0) (s := 24893) h218 (by decide +kernel)
  have h654 : (6 : ZMod 83719) ^ 654 = 15387 :=
    modular_pow_step (p := 83719) (a := 6) (e := 327) (r := 8195) (b := 0) (s := 15387) h327 (by decide +kernel)
  have h872 : (6 : ZMod 83719) ^ 872 = 57130 :=
    modular_pow_step (p := 83719) (a := 6) (e := 436) (r := 24893) (b := 0) (s := 57130) h436 (by decide +kernel)
  have h1308 : (6 : ZMod 83719) ^ 1308 = 2437 :=
    modular_pow_step (p := 83719) (a := 6) (e := 654) (r := 15387) (b := 0) (s := 2437) h654 (by decide +kernel)
  have h1744 : (6 : ZMod 83719) ^ 1744 = 51685 :=
    modular_pow_step (p := 83719) (a := 6) (e := 872) (r := 57130) (b := 0) (s := 51685) h872 (by decide +kernel)
  have h2616 : (6 : ZMod 83719) ^ 2616 = 78639 :=
    modular_pow_step (p := 83719) (a := 6) (e := 1308) (r := 2437) (b := 0) (s := 78639) h1308 (by decide +kernel)
  have h3488 : (6 : ZMod 83719) ^ 3488 = 33373 :=
    modular_pow_step (p := 83719) (a := 6) (e := 1744) (r := 51685) (b := 0) (s := 33373) h1744 (by decide +kernel)
  have h5232 : (6 : ZMod 83719) ^ 5232 = 20948 :=
    modular_pow_step (p := 83719) (a := 6) (e := 2616) (r := 78639) (b := 0) (s := 20948) h2616 (by decide +kernel)
  have h6976 : (6 : ZMod 83719) ^ 6976 = 43272 :=
    modular_pow_step (p := 83719) (a := 6) (e := 3488) (r := 33373) (b := 0) (s := 43272) h3488 (by decide +kernel)
  have h10464 : (6 : ZMod 83719) ^ 10464 = 47425 :=
    modular_pow_step (p := 83719) (a := 6) (e := 5232) (r := 20948) (b := 0) (s := 47425) h5232 (by decide +kernel)
  have h13953 : (6 : ZMod 83719) ^ 13953 = 40980 :=
    modular_pow_step (p := 83719) (a := 6) (e := 6976) (r := 43272) (b := 1) (s := 40980) h6976 (by decide +kernel)
  have h20929 : (6 : ZMod 83719) ^ 20929 = 34421 :=
    modular_pow_step (p := 83719) (a := 6) (e := 10464) (r := 47425) (b := 1) (s := 34421) h10464 (by decide +kernel)
  have h27906 : (6 : ZMod 83719) ^ 27906 = 40979 :=
    modular_pow_step (p := 83719) (a := 6) (e := 13953) (r := 40980) (b := 0) (s := 40979) h13953 (by decide +kernel)
  have h41859 : (6 : ZMod 83719) ^ 41859 = 83718 :=
    modular_pow_step (p := 83719) (a := 6) (e := 20929) (r := 34421) (b := 1) (s := 83718) h20929 (by decide +kernel)
  have h83718 : (6 : ZMod 83719) ^ 83718 = 1 :=
    modular_pow_step (p := 83719) (a := 6) (e := 41859) (r := 83718) (b := 0) (s := 1) h41859 (by decide +kernel)
  apply lucas_primality 83719 6 (by simpa using h83718)
  intro q hq hqd
  rw [show 83719 - 1 = (2 * 3 * 3 * 4651 : ℕ) by norm_num] at hqd
  simp only [hq.dvd_mul, Nat.dvd_prime prime_2, Nat.dvd_prime prime_3, Nat.dvd_prime prime_4651, hq.ne_one, false_or] at hqd
  rcases hqd with (((rfl | rfl) | rfl) | rfl)
  · change (6 : ZMod 83719) ^ 41859 ≠ 1
    rw [h41859]
    decide +kernel
  · change (6 : ZMod 83719) ^ 27906 ≠ 1
    rw [h27906]
    decide +kernel
  · change (6 : ZMod 83719) ^ 27906 ≠ 1
    rw [h27906]
    decide +kernel
  · change (6 : ZMod 83719) ^ 18 ≠ 1
    rw [h18]
    decide +kernel

lemma prime_48557021 : Nat.Prime 48557021 := by
  have h0 : (2 : ZMod 48557021) ^ 0 = 1 := by simp
  have h1 : (2 : ZMod 48557021) ^ 1 = 2 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 0) (r := 1) (b := 1) (s := 2) h0 (by decide +kernel)
  have h2 : (2 : ZMod 48557021) ^ 2 = 4 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 1) (r := 2) (b := 0) (s := 4) h1 (by decide +kernel)
  have h3 : (2 : ZMod 48557021) ^ 3 = 8 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 1) (r := 2) (b := 1) (s := 8) h1 (by decide +kernel)
  have h4 : (2 : ZMod 48557021) ^ 4 = 16 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 2) (r := 4) (b := 0) (s := 16) h2 (by decide +kernel)
  have h5 : (2 : ZMod 48557021) ^ 5 = 32 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 2) (r := 4) (b := 1) (s := 32) h2 (by decide +kernel)
  have h6 : (2 : ZMod 48557021) ^ 6 = 64 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 3) (r := 8) (b := 0) (s := 64) h3 (by decide +kernel)
  have h9 : (2 : ZMod 48557021) ^ 9 = 512 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 4) (r := 16) (b := 1) (s := 512) h4 (by decide +kernel)
  have h11 : (2 : ZMod 48557021) ^ 11 = 2048 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 5) (r := 32) (b := 1) (s := 2048) h5 (by decide +kernel)
  have h12 : (2 : ZMod 48557021) ^ 12 = 4096 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 6) (r := 64) (b := 0) (s := 4096) h6 (by decide +kernel)
  have h18 : (2 : ZMod 48557021) ^ 18 = 262144 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 9) (r := 512) (b := 0) (s := 262144) h9 (by decide +kernel)
  have h23 : (2 : ZMod 48557021) ^ 23 = 8388608 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 11) (r := 2048) (b := 1) (s := 8388608) h11 (by decide +kernel)
  have h25 : (2 : ZMod 48557021) ^ 25 = 33554432 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 12) (r := 4096) (b := 1) (s := 33554432) h12 (by decide +kernel)
  have h36 : (2 : ZMod 48557021) ^ 36 = 11292021 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 18) (r := 262144) (b := 0) (s := 11292021) h18 (by decide +kernel)
  have h37 : (2 : ZMod 48557021) ^ 37 = 22584042 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 18) (r := 262144) (b := 1) (s := 22584042) h18 (by decide +kernel)
  have h46 : (2 : ZMod 48557021) ^ 46 = 6458506 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 23) (r := 8388608) (b := 0) (s := 6458506) h23 (by decide +kernel)
  have h51 : (2 : ZMod 48557021) ^ 51 = 12444108 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 25) (r := 33554432) (b := 1) (s := 12444108) h25 (by decide +kernel)
  have h72 : (2 : ZMod 48557021) ^ 72 = 20815882 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 36) (r := 11292021) (b := 0) (s := 20815882) h36 (by decide +kernel)
  have h74 : (2 : ZMod 48557021) ^ 74 = 34706507 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 37) (r := 22584042) (b := 0) (s := 34706507) h37 (by decide +kernel)
  have h92 : (2 : ZMod 48557021) ^ 92 = 22103259 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 46) (r := 6458506) (b := 0) (s := 22103259) h46 (by decide +kernel)
  have h102 : (2 : ZMod 48557021) ^ 102 = 6165430 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 51) (r := 12444108) (b := 0) (s := 6165430) h51 (by decide +kernel)
  have h145 : (2 : ZMod 48557021) ^ 145 = 23057811 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 72) (r := 20815882) (b := 1) (s := 23057811) h72 (by decide +kernel)
  have h148 : (2 : ZMod 48557021) ^ 148 = 38791425 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 74) (r := 34706507) (b := 0) (s := 38791425) h74 (by decide +kernel)
  have h185 : (2 : ZMod 48557021) ^ 185 = 38961262 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 92) (r := 22103259) (b := 1) (s := 38961262) h92 (by decide +kernel)
  have h204 : (2 : ZMod 48557021) ^ 204 = 3094197 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 102) (r := 6165430) (b := 0) (s := 3094197) h102 (by decide +kernel)
  have h290 : (2 : ZMod 48557021) ^ 290 = 25826618 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 145) (r := 23057811) (b := 0) (s := 25826618) h145 (by decide +kernel)
  have h296 : (2 : ZMod 48557021) ^ 296 = 1964838 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 148) (r := 38791425) (b := 0) (s := 1964838) h148 (by decide +kernel)
  have h370 : (2 : ZMod 48557021) ^ 370 = 8977823 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 185) (r := 38961262) (b := 0) (s := 8977823) h185 (by decide +kernel)
  have h408 : (2 : ZMod 48557021) ^ 408 = 18687218 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 204) (r := 3094197) (b := 0) (s := 18687218) h204 (by decide +kernel)
  have h580 : (2 : ZMod 48557021) ^ 580 = 44363825 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 290) (r := 25826618) (b := 0) (s := 44363825) h290 (by decide +kernel)
  have h592 : (2 : ZMod 48557021) ^ 592 = 13854618 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 296) (r := 1964838) (b := 0) (s := 13854618) h296 (by decide +kernel)
  have h740 : (2 : ZMod 48557021) ^ 740 = 1393778 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 370) (r := 8977823) (b := 0) (s := 1393778) h370 (by decide +kernel)
  have h817 : (2 : ZMod 48557021) ^ 817 = 30679 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 408) (r := 18687218) (b := 1) (s := 30679) h408 (by decide +kernel)
  have h1185 : (2 : ZMod 48557021) ^ 1185 = 40219942 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 592) (r := 13854618) (b := 1) (s := 40219942) h592 (by decide +kernel)
  have h1481 : (2 : ZMod 48557021) ^ 1481 = 41305295 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 740) (r := 1393778) (b := 1) (s := 41305295) h740 (by decide +kernel)
  have h1635 : (2 : ZMod 48557021) ^ 1635 = 37235284 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 817) (r := 30679) (b := 1) (s := 37235284) h817 (by decide +kernel)
  have h2370 : (2 : ZMod 48557021) ^ 2370 = 35655833 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 1185) (r := 40219942) (b := 0) (s := 35655833) h1185 (by decide +kernel)
  have h2963 : (2 : ZMod 48557021) ^ 2963 = 18344921 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 1481) (r := 41305295) (b := 1) (s := 18344921) h1481 (by decide +kernel)
  have h3270 : (2 : ZMod 48557021) ^ 3270 = 30634991 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 1635) (r := 37235284) (b := 0) (s := 30634991) h1635 (by decide +kernel)
  have h4741 : (2 : ZMod 48557021) ^ 4741 = 5753776 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 2370) (r := 35655833) (b := 1) (s := 5753776) h2370 (by decide +kernel)
  have h5927 : (2 : ZMod 48557021) ^ 5927 = 28984381 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 2963) (r := 18344921) (b := 1) (s := 28984381) h2963 (by decide +kernel)
  have h6540 : (2 : ZMod 48557021) ^ 6540 = 906294 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 3270) (r := 30634991) (b := 0) (s := 906294) h3270 (by decide +kernel)
  have h9483 : (2 : ZMod 48557021) ^ 9483 = 8250962 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 4741) (r := 5753776) (b := 1) (s := 8250962) h4741 (by decide +kernel)
  have h11854 : (2 : ZMod 48557021) ^ 11854 = 47241150 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 5927) (r := 28984381) (b := 0) (s := 47241150) h5927 (by decide +kernel)
  have h13081 : (2 : ZMod 48557021) ^ 13081 = 5051421 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 6540) (r := 906294) (b := 1) (s := 5051421) h6540 (by decide +kernel)
  have h18967 : (2 : ZMod 48557021) ^ 18967 = 44659670 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 9483) (r := 8250962) (b := 1) (s := 44659670) h9483 (by decide +kernel)
  have h23709 : (2 : ZMod 48557021) ^ 23709 = 43353604 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 11854) (r := 47241150) (b := 1) (s := 43353604) h11854 (by decide +kernel)
  have h26162 : (2 : ZMod 48557021) ^ 26162 = 42469699 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 13081) (r := 5051421) (b := 0) (s := 42469699) h13081 (by decide +kernel)
  have h37935 : (2 : ZMod 48557021) ^ 37935 = 9143193 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 18967) (r := 44659670) (b := 1) (s := 9143193) h18967 (by decide +kernel)
  have h47418 : (2 : ZMod 48557021) ^ 47418 = 7895226 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 23709) (r := 43353604) (b := 0) (s := 7895226) h23709 (by decide +kernel)
  have h52324 : (2 : ZMod 48557021) ^ 52324 = 24024891 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 26162) (r := 42469699) (b := 0) (s := 24024891) h26162 (by decide +kernel)
  have h75870 : (2 : ZMod 48557021) ^ 75870 = 25815704 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 37935) (r := 9143193) (b := 0) (s := 25815704) h37935 (by decide +kernel)
  have h94837 : (2 : ZMod 48557021) ^ 94837 = 6905072 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 47418) (r := 7895226) (b := 1) (s := 6905072) h47418 (by decide +kernel)
  have h104648 : (2 : ZMod 48557021) ^ 104648 = 21215721 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 52324) (r := 24024891) (b := 0) (s := 21215721) h52324 (by decide +kernel)
  have h151740 : (2 : ZMod 48557021) ^ 151740 = 21404264 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 75870) (r := 25815704) (b := 0) (s := 21404264) h75870 (by decide +kernel)
  have h189675 : (2 : ZMod 48557021) ^ 189675 = 21919951 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 94837) (r := 6905072) (b := 1) (s := 21919951) h94837 (by decide +kernel)
  have h209297 : (2 : ZMod 48557021) ^ 209297 = 18661193 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 104648) (r := 21215721) (b := 1) (s := 18661193) h104648 (by decide +kernel)
  have h303481 : (2 : ZMod 48557021) ^ 303481 = 15514323 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 151740) (r := 21404264) (b := 1) (s := 15514323) h151740 (by decide +kernel)
  have h379351 : (2 : ZMod 48557021) ^ 379351 = 2671966 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 189675) (r := 21919951) (b := 1) (s := 2671966) h189675 (by decide +kernel)
  have h418595 : (2 : ZMod 48557021) ^ 418595 = 44130885 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 209297) (r := 18661193) (b := 1) (s := 44130885) h209297 (by decide +kernel)
  have h606962 : (2 : ZMod 48557021) ^ 606962 = 27029610 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 303481) (r := 15514323) (b := 0) (s := 27029610) h303481 (by decide +kernel)
  have h758703 : (2 : ZMod 48557021) ^ 758703 = 29901010 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 379351) (r := 2671966) (b := 1) (s := 29901010) h379351 (by decide +kernel)
  have h837190 : (2 : ZMod 48557021) ^ 837190 = 9868899 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 418595) (r := 44130885) (b := 0) (s := 9868899) h418595 (by decide +kernel)
  have h1213925 : (2 : ZMod 48557021) ^ 1213925 = 4026792 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 606962) (r := 27029610) (b := 1) (s := 4026792) h606962 (by decide +kernel)
  have h1517406 : (2 : ZMod 48557021) ^ 1517406 = 22650447 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 758703) (r := 29901010) (b := 0) (s := 22650447) h758703 (by decide +kernel)
  have h1674380 : (2 : ZMod 48557021) ^ 1674380 = 28877632 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 837190) (r := 9868899) (b := 0) (s := 28877632) h837190 (by decide +kernel)
  have h2427851 : (2 : ZMod 48557021) ^ 2427851 = 38665132 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 1213925) (r := 4026792) (b := 1) (s := 38665132) h1213925 (by decide +kernel)
  have h3034813 : (2 : ZMod 48557021) ^ 3034813 = 41587921 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 1517406) (r := 22650447) (b := 1) (s := 41587921) h1517406 (by decide +kernel)
  have h4855702 : (2 : ZMod 48557021) ^ 4855702 = 29905276 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 2427851) (r := 38665132) (b := 0) (s := 29905276) h2427851 (by decide +kernel)
  have h6069627 : (2 : ZMod 48557021) ^ 6069627 = 40048214 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 3034813) (r := 41587921) (b := 1) (s := 40048214) h3034813 (by decide +kernel)
  have h9711404 : (2 : ZMod 48557021) ^ 9711404 = 37678189 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 4855702) (r := 29905276) (b := 0) (s := 37678189) h4855702 (by decide +kernel)
  have h12139255 : (2 : ZMod 48557021) ^ 12139255 = 31539406 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 6069627) (r := 40048214) (b := 1) (s := 31539406) h6069627 (by decide +kernel)
  have h24278510 : (2 : ZMod 48557021) ^ 24278510 = 48557020 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 12139255) (r := 31539406) (b := 0) (s := 48557020) h12139255 (by decide +kernel)
  have h48557020 : (2 : ZMod 48557021) ^ 48557020 = 1 :=
    modular_pow_step (p := 48557021) (a := 2) (e := 24278510) (r := 48557020) (b := 0) (s := 1) h24278510 (by decide +kernel)
  apply lucas_primality 48557021 2 (by simpa using h48557020)
  intro q hq hqd
  rw [show 48557021 - 1 = (2 * 2 * 5 * 29 * 83719 : ℕ) by norm_num] at hqd
  simp only [hq.dvd_mul, Nat.dvd_prime prime_2, Nat.dvd_prime prime_5, Nat.dvd_prime prime_29, Nat.dvd_prime prime_83719, hq.ne_one, false_or] at hqd
  rcases hqd with ((((rfl | rfl) | rfl) | rfl) | rfl)
  · change (2 : ZMod 48557021) ^ 24278510 ≠ 1
    rw [h24278510]
    decide +kernel
  · change (2 : ZMod 48557021) ^ 24278510 ≠ 1
    rw [h24278510]
    decide +kernel
  · change (2 : ZMod 48557021) ^ 9711404 ≠ 1
    rw [h9711404]
    decide +kernel
  · change (2 : ZMod 48557021) ^ 1674380 ≠ 1
    rw [h1674380]
    decide +kernel
  · change (2 : ZMod 48557021) ^ 580 ≠ 1
    rw [h580]
    decide +kernel

private lemma prime_101 : Nat.Prime 101 := by norm_num
private lemma prime_281 : Nat.Prime 281 := by norm_num
private lemma prime_7 : Nat.Prime 7 := by norm_num
private lemma prime_23 : Nat.Prime 23 := by norm_num
private lemma prime_233 : Nat.Prime 233 := by norm_num
lemma prime_225079 : Nat.Prime 225079 := by
  have h0 : (3 : ZMod 225079) ^ 0 = 1 := by simp
  have h1 : (3 : ZMod 225079) ^ 1 = 3 :=
    modular_pow_step (p := 225079) (a := 3) (e := 0) (r := 1) (b := 1) (s := 3) h0 (by decide +kernel)
  have h2 : (3 : ZMod 225079) ^ 2 = 9 :=
    modular_pow_step (p := 225079) (a := 3) (e := 1) (r := 3) (b := 0) (s := 9) h1 (by decide +kernel)
  have h3 : (3 : ZMod 225079) ^ 3 = 27 :=
    modular_pow_step (p := 225079) (a := 3) (e := 1) (r := 3) (b := 1) (s := 27) h1 (by decide +kernel)
  have h4 : (3 : ZMod 225079) ^ 4 = 81 :=
    modular_pow_step (p := 225079) (a := 3) (e := 2) (r := 9) (b := 0) (s := 81) h2 (by decide +kernel)
  have h6 : (3 : ZMod 225079) ^ 6 = 729 :=
    modular_pow_step (p := 225079) (a := 3) (e := 3) (r := 27) (b := 0) (s := 729) h3 (by decide +kernel)
  have h7 : (3 : ZMod 225079) ^ 7 = 2187 :=
    modular_pow_step (p := 225079) (a := 3) (e := 3) (r := 27) (b := 1) (s := 2187) h3 (by decide +kernel)
  have h9 : (3 : ZMod 225079) ^ 9 = 19683 :=
    modular_pow_step (p := 225079) (a := 3) (e := 4) (r := 81) (b := 1) (s := 19683) h4 (by decide +kernel)
  have h13 : (3 : ZMod 225079) ^ 13 = 18770 :=
    modular_pow_step (p := 225079) (a := 3) (e := 6) (r := 729) (b := 1) (s := 18770) h6 (by decide +kernel)
  have h15 : (3 : ZMod 225079) ^ 15 = 168930 :=
    modular_pow_step (p := 225079) (a := 3) (e := 7) (r := 2187) (b := 1) (s := 168930) h7 (by decide +kernel)
  have h18 : (3 : ZMod 225079) ^ 18 = 59530 :=
    modular_pow_step (p := 225079) (a := 3) (e := 9) (r := 19683) (b := 0) (s := 59530) h9 (by decide +kernel)
  have h19 : (3 : ZMod 225079) ^ 19 = 178590 :=
    modular_pow_step (p := 225079) (a := 3) (e := 9) (r := 19683) (b := 1) (s := 178590) h9 (by decide +kernel)
  have h27 : (3 : ZMod 225079) ^ 27 = 192795 :=
    modular_pow_step (p := 225079) (a := 3) (e := 13) (r := 18770) (b := 1) (s := 192795) h13 (by decide +kernel)
  have h30 : (3 : ZMod 225079) ^ 30 = 28648 :=
    modular_pow_step (p := 225079) (a := 3) (e := 15) (r := 168930) (b := 0) (s := 28648) h15 (by decide +kernel)
  have h31 : (3 : ZMod 225079) ^ 31 = 85944 :=
    modular_pow_step (p := 225079) (a := 3) (e := 15) (r := 168930) (b := 1) (s := 85944) h15 (by decide +kernel)
  have h36 : (3 : ZMod 225079) ^ 36 = 177124 :=
    modular_pow_step (p := 225079) (a := 3) (e := 18) (r := 59530) (b := 0) (s := 177124) h18 (by decide +kernel)
  have h38 : (3 : ZMod 225079) ^ 38 = 18563 :=
    modular_pow_step (p := 225079) (a := 3) (e := 19) (r := 178590) (b := 0) (s := 18563) h19 (by decide +kernel)
  have h54 : (3 : ZMod 225079) ^ 54 = 140886 :=
    modular_pow_step (p := 225079) (a := 3) (e := 27) (r := 192795) (b := 0) (s := 140886) h27 (by decide +kernel)
  have h60 : (3 : ZMod 225079) ^ 60 = 69870 :=
    modular_pow_step (p := 225079) (a := 3) (e := 30) (r := 28648) (b := 0) (s := 69870) h30 (by decide +kernel)
  have h62 : (3 : ZMod 225079) ^ 62 = 178672 :=
    modular_pow_step (p := 225079) (a := 3) (e := 31) (r := 85944) (b := 0) (s := 178672) h31 (by decide +kernel)
  have h73 : (3 : ZMod 225079) ^ 73 = 149646 :=
    modular_pow_step (p := 225079) (a := 3) (e := 36) (r := 177124) (b := 1) (s := 149646) h36 (by decide +kernel)
  have h76 : (3 : ZMod 225079) ^ 76 = 214099 :=
    modular_pow_step (p := 225079) (a := 3) (e := 38) (r := 18563) (b := 0) (s := 214099) h38 (by decide +kernel)
  have h109 : (3 : ZMod 225079) ^ 109 = 144906 :=
    modular_pow_step (p := 225079) (a := 3) (e := 54) (r := 140886) (b := 1) (s := 144906) h54 (by decide +kernel)
  have h120 : (3 : ZMod 225079) ^ 120 = 78469 :=
    modular_pow_step (p := 225079) (a := 3) (e := 60) (r := 69870) (b := 0) (s := 78469) h60 (by decide +kernel)
  have h125 : (3 : ZMod 225079) ^ 125 = 161331 :=
    modular_pow_step (p := 225079) (a := 3) (e := 62) (r := 178672) (b := 1) (s := 161331) h62 (by decide +kernel)
  have h146 : (3 : ZMod 225079) ^ 146 = 140369 :=
    modular_pow_step (p := 225079) (a := 3) (e := 73) (r := 149646) (b := 0) (s := 140369) h73 (by decide +kernel)
  have h152 : (3 : ZMod 225079) ^ 152 = 143135 :=
    modular_pow_step (p := 225079) (a := 3) (e := 76) (r := 214099) (b := 0) (s := 143135) h76 (by decide +kernel)
  have h219 : (3 : ZMod 225079) ^ 219 = 161699 :=
    modular_pow_step (p := 225079) (a := 3) (e := 109) (r := 144906) (b := 1) (s := 161699) h109 (by decide +kernel)
  have h241 : (3 : ZMod 225079) ^ 241 = 143432 :=
    modular_pow_step (p := 225079) (a := 3) (e := 120) (r := 78469) (b := 1) (s := 143432) h120 (by decide +kernel)
  have h251 : (3 : ZMod 225079) ^ 251 = 18477 :=
    modular_pow_step (p := 225079) (a := 3) (e := 125) (r := 161331) (b := 1) (s := 18477) h125 (by decide +kernel)
  have h293 : (3 : ZMod 225079) ^ 293 = 121503 :=
    modular_pow_step (p := 225079) (a := 3) (e := 146) (r := 140369) (b := 1) (s := 121503) h146 (by decide +kernel)
  have h305 : (3 : ZMod 225079) ^ 305 = 111987 :=
    modular_pow_step (p := 225079) (a := 3) (e := 152) (r := 143135) (b := 1) (s := 111987) h152 (by decide +kernel)
  have h439 : (3 : ZMod 225079) ^ 439 = 118461 :=
    modular_pow_step (p := 225079) (a := 3) (e := 219) (r := 161699) (b := 1) (s := 118461) h219 (by decide +kernel)
  have h483 : (3 : ZMod 225079) ^ 483 = 203598 :=
    modular_pow_step (p := 225079) (a := 3) (e := 241) (r := 143432) (b := 1) (s := 203598) h241 (by decide +kernel)
  have h502 : (3 : ZMod 225079) ^ 502 = 179765 :=
    modular_pow_step (p := 225079) (a := 3) (e := 251) (r := 18477) (b := 0) (s := 179765) h251 (by decide +kernel)
  have h586 : (3 : ZMod 225079) ^ 586 = 47399 :=
    modular_pow_step (p := 225079) (a := 3) (e := 293) (r := 121503) (b := 0) (s := 47399) h293 (by decide +kernel)
  have h611 : (3 : ZMod 225079) ^ 611 = 184262 :=
    modular_pow_step (p := 225079) (a := 3) (e := 305) (r := 111987) (b := 1) (s := 184262) h305 (by decide +kernel)
  have h879 : (3 : ZMod 225079) ^ 879 = 24324 :=
    modular_pow_step (p := 225079) (a := 3) (e := 439) (r := 118461) (b := 1) (s := 24324) h439 (by decide +kernel)
  have h966 : (3 : ZMod 225079) ^ 966 = 21411 :=
    modular_pow_step (p := 225079) (a := 3) (e := 483) (r := 203598) (b := 0) (s := 21411) h483 (by decide +kernel)
  have h1004 : (3 : ZMod 225079) ^ 1004 = 187958 :=
    modular_pow_step (p := 225079) (a := 3) (e := 502) (r := 179765) (b := 0) (s := 187958) h502 (by decide +kernel)
  have h1172 : (3 : ZMod 225079) ^ 1172 = 151702 :=
    modular_pow_step (p := 225079) (a := 3) (e := 586) (r := 47399) (b := 0) (s := 151702) h586 (by decide +kernel)
  have h1223 : (3 : ZMod 225079) ^ 1223 = 203272 :=
    modular_pow_step (p := 225079) (a := 3) (e := 611) (r := 184262) (b := 1) (s := 203272) h611 (by decide +kernel)
  have h1758 : (3 : ZMod 225079) ^ 1758 = 149364 :=
    modular_pow_step (p := 225079) (a := 3) (e := 879) (r := 24324) (b := 0) (s := 149364) h879 (by decide +kernel)
  have h2009 : (3 : ZMod 225079) ^ 2009 = 105009 :=
    modular_pow_step (p := 225079) (a := 3) (e := 1004) (r := 187958) (b := 1) (s := 105009) h1004 (by decide +kernel)
  have h2344 : (3 : ZMod 225079) ^ 2344 = 69370 :=
    modular_pow_step (p := 225079) (a := 3) (e := 1172) (r := 151702) (b := 0) (s := 69370) h1172 (by decide +kernel)
  have h2446 : (3 : ZMod 225079) ^ 2446 = 178401 :=
    modular_pow_step (p := 225079) (a := 3) (e := 1223) (r := 203272) (b := 0) (s := 178401) h1223 (by decide +kernel)
  have h3516 : (3 : ZMod 225079) ^ 3516 = 224174 :=
    modular_pow_step (p := 225079) (a := 3) (e := 1758) (r := 149364) (b := 0) (s := 224174) h1758 (by decide +kernel)
  have h4019 : (3 : ZMod 225079) ^ 4019 = 134376 :=
    modular_pow_step (p := 225079) (a := 3) (e := 2009) (r := 105009) (b := 1) (s := 134376) h2009 (by decide +kernel)
  have h4689 : (3 : ZMod 225079) ^ 4689 = 23640 :=
    modular_pow_step (p := 225079) (a := 3) (e := 2344) (r := 69370) (b := 1) (s := 23640) h2344 (by decide +kernel)
  have h4893 : (3 : ZMod 225079) ^ 4893 = 212892 :=
    modular_pow_step (p := 225079) (a := 3) (e := 2446) (r := 178401) (b := 1) (s := 212892) h2446 (by decide +kernel)
  have h7033 : (3 : ZMod 225079) ^ 7033 = 206285 :=
    modular_pow_step (p := 225079) (a := 3) (e := 3516) (r := 224174) (b := 1) (s := 206285) h3516 (by decide +kernel)
  have h8038 : (3 : ZMod 225079) ^ 8038 = 171680 :=
    modular_pow_step (p := 225079) (a := 3) (e := 4019) (r := 134376) (b := 0) (s := 171680) h4019 (by decide +kernel)
  have h9378 : (3 : ZMod 225079) ^ 9378 = 203522 :=
    modular_pow_step (p := 225079) (a := 3) (e := 4689) (r := 23640) (b := 0) (s := 203522) h4689 (by decide +kernel)
  have h9786 : (3 : ZMod 225079) ^ 9786 = 195908 :=
    modular_pow_step (p := 225079) (a := 3) (e := 4893) (r := 212892) (b := 0) (s := 195908) h4893 (by decide +kernel)
  have h14067 : (3 : ZMod 225079) ^ 14067 = 196455 :=
    modular_pow_step (p := 225079) (a := 3) (e := 7033) (r := 206285) (b := 1) (s := 196455) h7033 (by decide +kernel)
  have h16077 : (3 : ZMod 225079) ^ 16077 = 7129 :=
    modular_pow_step (p := 225079) (a := 3) (e := 8038) (r := 171680) (b := 1) (s := 7129) h8038 (by decide +kernel)
  have h18756 : (3 : ZMod 225079) ^ 18756 = 141193 :=
    modular_pow_step (p := 225079) (a := 3) (e := 9378) (r := 203522) (b := 0) (s := 141193) h9378 (by decide +kernel)
  have h28134 : (3 : ZMod 225079) ^ 28134 = 45816 :=
    modular_pow_step (p := 225079) (a := 3) (e := 14067) (r := 196455) (b := 0) (s := 45816) h14067 (by decide +kernel)
  have h32154 : (3 : ZMod 225079) ^ 32154 = 179866 :=
    modular_pow_step (p := 225079) (a := 3) (e := 16077) (r := 7129) (b := 0) (s := 179866) h16077 (by decide +kernel)
  have h37513 : (3 : ZMod 225079) ^ 37513 = 198499 :=
    modular_pow_step (p := 225079) (a := 3) (e := 18756) (r := 141193) (b := 1) (s := 198499) h18756 (by decide +kernel)
  have h56269 : (3 : ZMod 225079) ^ 56269 = 57306 :=
    modular_pow_step (p := 225079) (a := 3) (e := 28134) (r := 45816) (b := 1) (s := 57306) h28134 (by decide +kernel)
  have h75026 : (3 : ZMod 225079) ^ 75026 = 198498 :=
    modular_pow_step (p := 225079) (a := 3) (e := 37513) (r := 198499) (b := 0) (s := 198498) h37513 (by decide +kernel)
  have h112539 : (3 : ZMod 225079) ^ 112539 = 225078 :=
    modular_pow_step (p := 225079) (a := 3) (e := 56269) (r := 57306) (b := 1) (s := 225078) h56269 (by decide +kernel)
  have h225078 : (3 : ZMod 225079) ^ 225078 = 1 :=
    modular_pow_step (p := 225079) (a := 3) (e := 112539) (r := 225078) (b := 0) (s := 1) h112539 (by decide +kernel)
  apply lucas_primality 225079 3 (by simpa using h225078)
  intro q hq hqd
  rw [show 225079 - 1 = (2 * 3 * 7 * 23 * 233 : ℕ) by norm_num] at hqd
  simp only [hq.dvd_mul, Nat.dvd_prime prime_2, Nat.dvd_prime prime_3, Nat.dvd_prime prime_7, Nat.dvd_prime prime_23, Nat.dvd_prime prime_233, hq.ne_one, false_or] at hqd
  rcases hqd with ((((rfl | rfl) | rfl) | rfl) | rfl)
  · change (3 : ZMod 225079) ^ 112539 ≠ 1
    rw [h112539]
    decide +kernel
  · change (3 : ZMod 225079) ^ 75026 ≠ 1
    rw [h75026]
    decide +kernel
  · change (3 : ZMod 225079) ^ 32154 ≠ 1
    rw [h32154]
    decide +kernel
  · change (3 : ZMod 225079) ^ 9786 ≠ 1
    rw [h9786]
    decide +kernel
  · change (3 : ZMod 225079) ^ 966 ≠ 1
    rw [h966]
    decide +kernel

lemma prime_63879670991 : Nat.Prime 63879670991 := by
  have h0 : (11 : ZMod 63879670991) ^ 0 = 1 := by simp
  have h1 : (11 : ZMod 63879670991) ^ 1 = 11 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 0) (r := 1) (b := 1) (s := 11) h0 (by decide +kernel)
  have h2 : (11 : ZMod 63879670991) ^ 2 = 121 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 1) (r := 11) (b := 0) (s := 121) h1 (by decide +kernel)
  have h3 : (11 : ZMod 63879670991) ^ 3 = 1331 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 1) (r := 11) (b := 1) (s := 1331) h1 (by decide +kernel)
  have h4 : (11 : ZMod 63879670991) ^ 4 = 14641 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 2) (r := 121) (b := 0) (s := 14641) h2 (by decide +kernel)
  have h5 : (11 : ZMod 63879670991) ^ 5 = 161051 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 2) (r := 121) (b := 1) (s := 161051) h2 (by decide +kernel)
  have h6 : (11 : ZMod 63879670991) ^ 6 = 1771561 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 3) (r := 1331) (b := 0) (s := 1771561) h3 (by decide +kernel)
  have h7 : (11 : ZMod 63879670991) ^ 7 = 19487171 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 3) (r := 1331) (b := 1) (s := 19487171) h3 (by decide +kernel)
  have h8 : (11 : ZMod 63879670991) ^ 8 = 214358881 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 4) (r := 14641) (b := 0) (s := 214358881) h4 (by decide +kernel)
  have h9 : (11 : ZMod 63879670991) ^ 9 = 2357947691 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 4) (r := 14641) (b := 1) (s := 2357947691) h4 (by decide +kernel)
  have h11 : (11 : ZMod 63879670991) ^ 11 = 29792986647 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 5) (r := 161051) (b := 1) (s := 29792986647) h5 (by decide +kernel)
  have h13 : (11 : ZMod 63879670991) ^ 13 = 27689808791 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 6) (r := 1771561) (b := 1) (s := 27689808791) h6 (by decide +kernel)
  have h14 : (11 : ZMod 63879670991) ^ 14 = 49069212737 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 7) (r := 19487171) (b := 0) (s := 49069212737) h7 (by decide +kernel)
  have h17 : (11 : ZMod 63879670991) ^ 17 = 26098400145 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 8) (r := 214358881) (b := 1) (s := 26098400145) h8 (by decide +kernel)
  have h18 : (11 : ZMod 63879670991) ^ 18 = 31563717631 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 9) (r := 2357947691) (b := 0) (s := 31563717631) h9 (by decide +kernel)
  have h23 : (11 : ZMod 63879670991) ^ 23 = 15709739374 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 11) (r := 29792986647) (b := 1) (s := 15709739374) h11 (by decide +kernel)
  have h27 : (11 : ZMod 63879670991) ^ 27 = 39478607134 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 13) (r := 27689808791) (b := 1) (s := 39478607134) h13 (by decide +kernel)
  have h29 : (11 : ZMod 63879670991) ^ 29 = 49815809880 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 14) (r := 49069212737) (b := 1) (s := 49815809880) h14 (by decide +kernel)
  have h34 : (11 : ZMod 63879670991) ^ 34 = 46478211217 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 17) (r := 26098400145) (b := 0) (s := 46478211217) h17 (by decide +kernel)
  have h37 : (11 : ZMod 63879670991) ^ 37 = 26977610539 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 18) (r := 31563717631) (b := 1) (s := 26977610539) h18 (by decide +kernel)
  have h47 : (11 : ZMod 63879670991) ^ 47 = 24567330912 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 23) (r := 15709739374) (b := 1) (s := 24567330912) h23 (by decide +kernel)
  have h54 : (11 : ZMod 63879670991) ^ 54 = 51141576668 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 27) (r := 39478607134) (b := 0) (s := 51141576668) h27 (by decide +kernel)
  have h59 : (11 : ZMod 63879670991) ^ 59 = 12805062492 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 29) (r := 49815809880) (b := 1) (s := 12805062492) h29 (by decide +kernel)
  have h69 : (11 : ZMod 63879670991) ^ 69 = 19320108106 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 34) (r := 46478211217) (b := 1) (s := 19320108106) h34 (by decide +kernel)
  have h75 : (11 : ZMod 63879670991) ^ 75 = 22319395666 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 37) (r := 26977610539) (b := 1) (s := 22319395666) h37 (by decide +kernel)
  have h95 : (11 : ZMod 63879670991) ^ 95 = 17853503006 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 47) (r := 24567330912) (b := 1) (s := 17853503006) h47 (by decide +kernel)
  have h108 : (11 : ZMod 63879670991) ^ 108 = 29102504065 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 54) (r := 51141576668) (b := 0) (s := 29102504065) h54 (by decide +kernel)
  have h118 : (11 : ZMod 63879670991) ^ 118 = 17930344015 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 59) (r := 12805062492) (b := 0) (s := 17930344015) h59 (by decide +kernel)
  have h138 : (11 : ZMod 63879670991) ^ 138 = 28188774295 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 69) (r := 19320108106) (b := 0) (s := 28188774295) h69 (by decide +kernel)
  have h150 : (11 : ZMod 63879670991) ^ 150 = 34855987696 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 75) (r := 22319395666) (b := 0) (s := 34855987696) h75 (by decide +kernel)
  have h190 : (11 : ZMod 63879670991) ^ 190 = 21293942952 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 95) (r := 17853503006) (b := 0) (s := 21293942952) h95 (by decide +kernel)
  have h216 : (11 : ZMod 63879670991) ^ 216 = 8425030067 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 108) (r := 29102504065) (b := 0) (s := 8425030067) h108 (by decide +kernel)
  have h237 : (11 : ZMod 63879670991) ^ 237 = 24999571621 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 118) (r := 17930344015) (b := 1) (s := 24999571621) h118 (by decide +kernel)
  have h277 : (11 : ZMod 63879670991) ^ 277 = 16821890268 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 138) (r := 28188774295) (b := 1) (s := 16821890268) h138 (by decide +kernel)
  have h301 : (11 : ZMod 63879670991) ^ 301 = 43827999261 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 150) (r := 34855987696) (b := 1) (s := 43827999261) h150 (by decide +kernel)
  have h380 : (11 : ZMod 63879670991) ^ 380 = 56022527090 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 190) (r := 21293942952) (b := 0) (s := 56022527090) h190 (by decide +kernel)
  have h433 : (11 : ZMod 63879670991) ^ 433 = 20348662688 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 216) (r := 8425030067) (b := 1) (s := 20348662688) h216 (by decide +kernel)
  have h475 : (11 : ZMod 63879670991) ^ 475 = 21927307696 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 237) (r := 24999571621) (b := 1) (s := 21927307696) h237 (by decide +kernel)
  have h554 : (11 : ZMod 63879670991) ^ 554 = 15584060035 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 277) (r := 16821890268) (b := 0) (s := 15584060035) h277 (by decide +kernel)
  have h603 : (11 : ZMod 63879670991) ^ 603 = 58768314015 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 301) (r := 43827999261) (b := 1) (s := 58768314015) h301 (by decide +kernel)
  have h761 : (11 : ZMod 63879670991) ^ 761 = 63093380672 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 380) (r := 56022527090) (b := 1) (s := 63093380672) h380 (by decide +kernel)
  have h867 : (11 : ZMod 63879670991) ^ 867 = 15271448803 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 433) (r := 20348662688) (b := 1) (s := 15271448803) h433 (by decide +kernel)
  have h951 : (11 : ZMod 63879670991) ^ 951 = 21153884669 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 475) (r := 21927307696) (b := 1) (s := 21153884669) h475 (by decide +kernel)
  have h1108 : (11 : ZMod 63879670991) ^ 1108 = 8731794006 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 554) (r := 15584060035) (b := 0) (s := 8731794006) h554 (by decide +kernel)
  have h1206 : (11 : ZMod 63879670991) ^ 1206 = 60905393700 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 603) (r := 58768314015) (b := 0) (s := 60905393700) h603 (by decide +kernel)
  have h1523 : (11 : ZMod 63879670991) ^ 1523 = 43061174125 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 761) (r := 63093380672) (b := 1) (s := 43061174125) h761 (by decide +kernel)
  have h1734 : (11 : ZMod 63879670991) ^ 1734 = 17884893871 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 867) (r := 15271448803) (b := 0) (s := 17884893871) h867 (by decide +kernel)
  have h1903 : (11 : ZMod 63879670991) ^ 1903 = 19953163122 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 951) (r := 21153884669) (b := 1) (s := 19953163122) h951 (by decide +kernel)
  have h2217 : (11 : ZMod 63879670991) ^ 2217 = 36880777395 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 1108) (r := 8731794006) (b := 1) (s := 36880777395) h1108 (by decide +kernel)
  have h2412 : (11 : ZMod 63879670991) ^ 2412 = 14787772517 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 1206) (r := 60905393700) (b := 0) (s := 14787772517) h1206 (by decide +kernel)
  have h3046 : (11 : ZMod 63879670991) ^ 3046 = 61827365878 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 1523) (r := 43061174125) (b := 0) (s := 61827365878) h1523 (by decide +kernel)
  have h3468 : (11 : ZMod 63879670991) ^ 3468 = 23335031178 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 1734) (r := 17884893871) (b := 0) (s := 23335031178) h1734 (by decide +kernel)
  have h3807 : (11 : ZMod 63879670991) ^ 3807 = 26545189140 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 1903) (r := 19953163122) (b := 1) (s := 26545189140) h1903 (by decide +kernel)
  have h4434 : (11 : ZMod 63879670991) ^ 4434 = 40000904675 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 2217) (r := 36880777395) (b := 0) (s := 40000904675) h2217 (by decide +kernel)
  have h4825 : (11 : ZMod 63879670991) ^ 4825 = 30762284781 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 2412) (r := 14787772517) (b := 1) (s := 30762284781) h2412 (by decide +kernel)
  have h6092 : (11 : ZMod 63879670991) ^ 6092 = 24512629834 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 3046) (r := 61827365878) (b := 0) (s := 24512629834) h3046 (by decide +kernel)
  have h6937 : (11 : ZMod 63879670991) ^ 6937 = 4676567755 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 3468) (r := 23335031178) (b := 1) (s := 4676567755) h3468 (by decide +kernel)
  have h7615 : (11 : ZMod 63879670991) ^ 7615 = 41148514072 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 3807) (r := 26545189140) (b := 1) (s := 41148514072) h3807 (by decide +kernel)
  have h8869 : (11 : ZMod 63879670991) ^ 8869 = 5139520384 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 4434) (r := 40000904675) (b := 1) (s := 5139520384) h4434 (by decide +kernel)
  have h9650 : (11 : ZMod 63879670991) ^ 9650 = 31494441800 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 4825) (r := 30762284781) (b := 0) (s := 31494441800) h4825 (by decide +kernel)
  have h12184 : (11 : ZMod 63879670991) ^ 12184 = 39033821578 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 6092) (r := 24512629834) (b := 0) (s := 39033821578) h6092 (by decide +kernel)
  have h13875 : (11 : ZMod 63879670991) ^ 13875 = 35287126977 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 6937) (r := 4676567755) (b := 1) (s := 35287126977) h6937 (by decide +kernel)
  have h15230 : (11 : ZMod 63879670991) ^ 15230 = 58801144351 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 7615) (r := 41148514072) (b := 0) (s := 58801144351) h7615 (by decide +kernel)
  have h17738 : (11 : ZMod 63879670991) ^ 17738 = 886181450 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 8869) (r := 5139520384) (b := 0) (s := 886181450) h8869 (by decide +kernel)
  have h19301 : (11 : ZMod 63879670991) ^ 19301 = 1527374373 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 9650) (r := 31494441800) (b := 1) (s := 1527374373) h9650 (by decide +kernel)
  have h24368 : (11 : ZMod 63879670991) ^ 24368 = 12247658485 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 12184) (r := 39033821578) (b := 0) (s := 12247658485) h12184 (by decide +kernel)
  have h27750 : (11 : ZMod 63879670991) ^ 27750 = 5820721708 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 13875) (r := 35287126977) (b := 0) (s := 5820721708) h13875 (by decide +kernel)
  have h30460 : (11 : ZMod 63879670991) ^ 30460 = 20054046805 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 15230) (r := 58801144351) (b := 0) (s := 20054046805) h15230 (by decide +kernel)
  have h35476 : (11 : ZMod 63879670991) ^ 35476 = 51062045800 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 17738) (r := 886181450) (b := 0) (s := 51062045800) h17738 (by decide +kernel)
  have h38603 : (11 : ZMod 63879670991) ^ 38603 = 38061152097 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 19301) (r := 1527374373) (b := 1) (s := 38061152097) h19301 (by decide +kernel)
  have h48736 : (11 : ZMod 63879670991) ^ 48736 = 45196325087 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 24368) (r := 12247658485) (b := 0) (s := 45196325087) h24368 (by decide +kernel)
  have h55500 : (11 : ZMod 63879670991) ^ 55500 = 45247463708 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 27750) (r := 5820721708) (b := 0) (s := 45247463708) h27750 (by decide +kernel)
  have h60920 : (11 : ZMod 63879670991) ^ 60920 = 45345958641 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 30460) (r := 20054046805) (b := 0) (s := 45345958641) h30460 (by decide +kernel)
  have h70952 : (11 : ZMod 63879670991) ^ 70952 = 21581534495 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 35476) (r := 51062045800) (b := 0) (s := 21581534495) h35476 (by decide +kernel)
  have h77206 : (11 : ZMod 63879670991) ^ 77206 = 47243035661 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 38603) (r := 38061152097) (b := 0) (s := 47243035661) h38603 (by decide +kernel)
  have h97472 : (11 : ZMod 63879670991) ^ 97472 = 56695412781 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 48736) (r := 45196325087) (b := 0) (s := 56695412781) h48736 (by decide +kernel)
  have h111000 : (11 : ZMod 63879670991) ^ 111000 = 38033442274 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 55500) (r := 45247463708) (b := 0) (s := 38033442274) h55500 (by decide +kernel)
  have h121840 : (11 : ZMod 63879670991) ^ 121840 = 35121356428 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 60920) (r := 45345958641) (b := 0) (s := 35121356428) h60920 (by decide +kernel)
  have h141905 : (11 : ZMod 63879670991) ^ 141905 = 57636901342 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 70952) (r := 21581534495) (b := 1) (s := 57636901342) h70952 (by decide +kernel)
  have h154412 : (11 : ZMod 63879670991) ^ 154412 = 26471844244 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 77206) (r := 47243035661) (b := 0) (s := 26471844244) h77206 (by decide +kernel)
  have h194945 : (11 : ZMod 63879670991) ^ 194945 = 2341741749 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 97472) (r := 56695412781) (b := 1) (s := 2341741749) h97472 (by decide +kernel)
  have h222001 : (11 : ZMod 63879670991) ^ 222001 = 8285485966 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 111000) (r := 38033442274) (b := 1) (s := 8285485966) h111000 (by decide +kernel)
  have h243681 : (11 : ZMod 63879670991) ^ 243681 = 39070648733 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 121840) (r := 35121356428) (b := 1) (s := 39070648733) h121840 (by decide +kernel)
  have h283810 : (11 : ZMod 63879670991) ^ 283810 = 20791947460 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 141905) (r := 57636901342) (b := 0) (s := 20791947460) h141905 (by decide +kernel)
  have h308824 : (11 : ZMod 63879670991) ^ 308824 = 42081634804 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 154412) (r := 26471844244) (b := 0) (s := 42081634804) h154412 (by decide +kernel)
  have h389890 : (11 : ZMod 63879670991) ^ 389890 = 38367911568 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 194945) (r := 2341741749) (b := 0) (s := 38367911568) h194945 (by decide +kernel)
  have h444003 : (11 : ZMod 63879670991) ^ 444003 = 47279188857 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 222001) (r := 8285485966) (b := 1) (s := 47279188857) h222001 (by decide +kernel)
  have h487363 : (11 : ZMod 63879670991) ^ 487363 = 11576302603 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 243681) (r := 39070648733) (b := 1) (s := 11576302603) h243681 (by decide +kernel)
  have h617648 : (11 : ZMod 63879670991) ^ 617648 = 29583367868 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 308824) (r := 42081634804) (b := 0) (s := 29583367868) h308824 (by decide +kernel)
  have h779781 : (11 : ZMod 63879670991) ^ 779781 = 32212744210 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 389890) (r := 38367911568) (b := 1) (s := 32212744210) h389890 (by decide +kernel)
  have h888006 : (11 : ZMod 63879670991) ^ 888006 = 38796687055 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 444003) (r := 47279188857) (b := 0) (s := 38796687055) h444003 (by decide +kernel)
  have h974726 : (11 : ZMod 63879670991) ^ 974726 = 21348445314 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 487363) (r := 11576302603) (b := 0) (s := 21348445314) h487363 (by decide +kernel)
  have h1235296 : (11 : ZMod 63879670991) ^ 1235296 = 53838900575 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 617648) (r := 29583367868) (b := 0) (s := 53838900575) h617648 (by decide +kernel)
  have h1559562 : (11 : ZMod 63879670991) ^ 1559562 = 21501094619 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 779781) (r := 32212744210) (b := 0) (s := 21501094619) h779781 (by decide +kernel)
  have h1776013 : (11 : ZMod 63879670991) ^ 1776013 = 43991784443 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 888006) (r := 38796687055) (b := 1) (s := 43991784443) h888006 (by decide +kernel)
  have h1949452 : (11 : ZMod 63879670991) ^ 1949452 = 56495628115 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 974726) (r := 21348445314) (b := 0) (s := 56495628115) h974726 (by decide +kernel)
  have h2470593 : (11 : ZMod 63879670991) ^ 2470593 = 46986379523 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 1235296) (r := 53838900575) (b := 1) (s := 46986379523) h1235296 (by decide +kernel)
  have h3119124 : (11 : ZMod 63879670991) ^ 3119124 = 23681478780 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 1559562) (r := 21501094619) (b := 0) (s := 23681478780) h1559562 (by decide +kernel)
  have h3552027 : (11 : ZMod 63879670991) ^ 3552027 = 14327746770 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 1776013) (r := 43991784443) (b := 1) (s := 14327746770) h1776013 (by decide +kernel)
  have h3898905 : (11 : ZMod 63879670991) ^ 3898905 = 11933804051 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 1949452) (r := 56495628115) (b := 1) (s := 11933804051) h1949452 (by decide +kernel)
  have h4941187 : (11 : ZMod 63879670991) ^ 4941187 = 9289833109 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 2470593) (r := 46986379523) (b := 1) (s := 9289833109) h2470593 (by decide +kernel)
  have h6238249 : (11 : ZMod 63879670991) ^ 6238249 = 35593234336 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 3119124) (r := 23681478780) (b := 1) (s := 35593234336) h3119124 (by decide +kernel)
  have h7104055 : (11 : ZMod 63879670991) ^ 7104055 = 42751194817 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 3552027) (r := 14327746770) (b := 1) (s := 42751194817) h3552027 (by decide +kernel)
  have h7797811 : (11 : ZMod 63879670991) ^ 7797811 = 58342123070 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 3898905) (r := 11933804051) (b := 1) (s := 58342123070) h3898905 (by decide +kernel)
  have h9882374 : (11 : ZMod 63879670991) ^ 9882374 = 46264145402 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 4941187) (r := 9289833109) (b := 0) (s := 46264145402) h4941187 (by decide +kernel)
  have h12476498 : (11 : ZMod 63879670991) ^ 12476498 = 4726166109 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 6238249) (r := 35593234336) (b := 0) (s := 4726166109) h6238249 (by decide +kernel)
  have h14208111 : (11 : ZMod 63879670991) ^ 14208111 = 241792577 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 7104055) (r := 42751194817) (b := 1) (s := 241792577) h7104055 (by decide +kernel)
  have h15595622 : (11 : ZMod 63879670991) ^ 15595622 = 60075842472 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 7797811) (r := 58342123070) (b := 0) (s := 60075842472) h7797811 (by decide +kernel)
  have h19764749 : (11 : ZMod 63879670991) ^ 19764749 = 22402172658 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 9882374) (r := 46264145402) (b := 1) (s := 22402172658) h9882374 (by decide +kernel)
  have h24952996 : (11 : ZMod 63879670991) ^ 24952996 = 19900958552 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 12476498) (r := 4726166109) (b := 0) (s := 19900958552) h12476498 (by decide +kernel)
  have h28416223 : (11 : ZMod 63879670991) ^ 28416223 = 61509659522 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 14208111) (r := 241792577) (b := 1) (s := 61509659522) h14208111 (by decide +kernel)
  have h31191245 : (11 : ZMod 63879670991) ^ 31191245 = 25509753070 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 15595622) (r := 60075842472) (b := 1) (s := 25509753070) h15595622 (by decide +kernel)
  have h39529499 : (11 : ZMod 63879670991) ^ 39529499 = 40277111626 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 19764749) (r := 22402172658) (b := 1) (s := 40277111626) h19764749 (by decide +kernel)
  have h49905992 : (11 : ZMod 63879670991) ^ 49905992 = 42103503289 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 24952996) (r := 19900958552) (b := 0) (s := 42103503289) h24952996 (by decide +kernel)
  have h56832447 : (11 : ZMod 63879670991) ^ 56832447 = 35005566647 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 28416223) (r := 61509659522) (b := 1) (s := 35005566647) h28416223 (by decide +kernel)
  have h62382491 : (11 : ZMod 63879670991) ^ 62382491 = 57523377400 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 31191245) (r := 25509753070) (b := 1) (s := 57523377400) h31191245 (by decide +kernel)
  have h79058998 : (11 : ZMod 63879670991) ^ 79058998 = 26950873640 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 39529499) (r := 40277111626) (b := 0) (s := 26950873640) h39529499 (by decide +kernel)
  have h99811985 : (11 : ZMod 63879670991) ^ 99811985 = 36632856179 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 49905992) (r := 42103503289) (b := 1) (s := 36632856179) h49905992 (by decide +kernel)
  have h113664895 : (11 : ZMod 63879670991) ^ 113664895 = 22493531 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 56832447) (r := 35005566647) (b := 1) (s := 22493531) h56832447 (by decide +kernel)
  have h124764982 : (11 : ZMod 63879670991) ^ 124764982 = 63287222689 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 62382491) (r := 57523377400) (b := 0) (s := 63287222689) h62382491 (by decide +kernel)
  have h158117997 : (11 : ZMod 63879670991) ^ 158117997 = 28380975355 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 79058998) (r := 26950873640) (b := 1) (s := 28380975355) h79058998 (by decide +kernel)
  have h199623971 : (11 : ZMod 63879670991) ^ 199623971 = 17026275906 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 99811985) (r := 36632856179) (b := 1) (s := 17026275906) h99811985 (by decide +kernel)
  have h227329790 : (11 : ZMod 63879670991) ^ 227329790 = 31942599241 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 113664895) (r := 22493531) (b := 0) (s := 31942599241) h113664895 (by decide +kernel)
  have h249529964 : (11 : ZMod 63879670991) ^ 249529964 = 25564417847 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 124764982) (r := 63287222689) (b := 0) (s := 25564417847) h124764982 (by decide +kernel)
  have h316235995 : (11 : ZMod 63879670991) ^ 316235995 = 2921946234 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 158117997) (r := 28380975355) (b := 1) (s := 2921946234) h158117997 (by decide +kernel)
  have h399247943 : (11 : ZMod 63879670991) ^ 399247943 = 13819301097 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 199623971) (r := 17026275906) (b := 1) (s := 13819301097) h199623971 (by decide +kernel)
  have h499059929 : (11 : ZMod 63879670991) ^ 499059929 = 51123430551 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 249529964) (r := 25564417847) (b := 1) (s := 51123430551) h249529964 (by decide +kernel)
  have h632471990 : (11 : ZMod 63879670991) ^ 632471990 = 16656257225 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 316235995) (r := 2921946234) (b := 0) (s := 16656257225) h316235995 (by decide +kernel)
  have h798495887 : (11 : ZMod 63879670991) ^ 798495887 = 125223376 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 399247943) (r := 13819301097) (b := 1) (s := 125223376) h399247943 (by decide +kernel)
  have h998119859 : (11 : ZMod 63879670991) ^ 998119859 = 14970448974 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 499059929) (r := 51123430551) (b := 1) (s := 14970448974) h499059929 (by decide +kernel)
  have h1596991774 : (11 : ZMod 63879670991) ^ 1596991774 = 31660321651 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 798495887) (r := 125223376) (b := 0) (s := 31660321651) h798495887 (by decide +kernel)
  have h1996239718 : (11 : ZMod 63879670991) ^ 1996239718 = 59152064362 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 998119859) (r := 14970448974) (b := 0) (s := 59152064362) h998119859 (by decide +kernel)
  have h3193983549 : (11 : ZMod 63879670991) ^ 3193983549 = 29345354113 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 1596991774) (r := 31660321651) (b := 1) (s := 29345354113) h1596991774 (by decide +kernel)
  have h3992479436 : (11 : ZMod 63879670991) ^ 3992479436 = 53185943995 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 1996239718) (r := 59152064362) (b := 0) (s := 53185943995) h1996239718 (by decide +kernel)
  have h6387967099 : (11 : ZMod 63879670991) ^ 6387967099 = 19911520249 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 3193983549) (r := 29345354113) (b := 1) (s := 19911520249) h3193983549 (by decide +kernel)
  have h7984958873 : (11 : ZMod 63879670991) ^ 7984958873 = 49282437093 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 3992479436) (r := 53185943995) (b := 1) (s := 49282437093) h3992479436 (by decide +kernel)
  have h12775934198 : (11 : ZMod 63879670991) ^ 12775934198 = 20637370005 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 6387967099) (r := 19911520249) (b := 0) (s := 20637370005) h6387967099 (by decide +kernel)
  have h15969917747 : (11 : ZMod 63879670991) ^ 15969917747 = 5140050696 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 7984958873) (r := 49282437093) (b := 1) (s := 5140050696) h7984958873 (by decide +kernel)
  have h31939835495 : (11 : ZMod 63879670991) ^ 31939835495 = 63879670990 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 15969917747) (r := 5140050696) (b := 1) (s := 63879670990) h15969917747 (by decide +kernel)
  have h63879670990 : (11 : ZMod 63879670991) ^ 63879670990 = 1 :=
    modular_pow_step (p := 63879670991) (a := 11) (e := 31939835495) (r := 63879670990) (b := 0) (s := 1) h31939835495 (by decide +kernel)
  apply lucas_primality 63879670991 11 (by simpa using h63879670990)
  intro q hq hqd
  rw [show 63879670991 - 1 = (2 * 5 * 101 * 281 * 225079 : ℕ) by norm_num] at hqd
  simp only [hq.dvd_mul, Nat.dvd_prime prime_2, Nat.dvd_prime prime_5, Nat.dvd_prime prime_101, Nat.dvd_prime prime_281, Nat.dvd_prime prime_225079, hq.ne_one, false_or] at hqd
  rcases hqd with ((((rfl | rfl) | rfl) | rfl) | rfl)
  · change (11 : ZMod 63879670991) ^ 31939835495 ≠ 1
    rw [h31939835495]
    decide +kernel
  · change (11 : ZMod 63879670991) ^ 12775934198 ≠ 1
    rw [h12775934198]
    decide +kernel
  · change (11 : ZMod 63879670991) ^ 632471990 ≠ 1
    rw [h632471990]
    decide +kernel
  · change (11 : ZMod 63879670991) ^ 227329790 ≠ 1
    rw [h227329790]
    decide +kernel
  · change (11 : ZMod 63879670991) ^ 283810 ≠ 1
    rw [h283810]
    decide +kernel

private lemma prime_19 : Nat.Prime 19 := by norm_num
private lemma prime_73 : Nat.Prime 73 := by norm_num
private lemma prime_409 : Nat.Prime 409 := by norm_num
lemma prime_22691321 : Nat.Prime 22691321 := by
  have h0 : (3 : ZMod 22691321) ^ 0 = 1 := by simp
  have h1 : (3 : ZMod 22691321) ^ 1 = 3 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 0) (r := 1) (b := 1) (s := 3) h0 (by decide +kernel)
  have h2 : (3 : ZMod 22691321) ^ 2 = 9 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 1) (r := 3) (b := 0) (s := 9) h1 (by decide +kernel)
  have h3 : (3 : ZMod 22691321) ^ 3 = 27 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 1) (r := 3) (b := 1) (s := 27) h1 (by decide +kernel)
  have h4 : (3 : ZMod 22691321) ^ 4 = 81 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 2) (r := 9) (b := 0) (s := 81) h2 (by decide +kernel)
  have h5 : (3 : ZMod 22691321) ^ 5 = 243 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 2) (r := 9) (b := 1) (s := 243) h2 (by decide +kernel)
  have h6 : (3 : ZMod 22691321) ^ 6 = 729 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 3) (r := 27) (b := 0) (s := 729) h3 (by decide +kernel)
  have h8 : (3 : ZMod 22691321) ^ 8 = 6561 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 4) (r := 81) (b := 0) (s := 6561) h4 (by decide +kernel)
  have h9 : (3 : ZMod 22691321) ^ 9 = 19683 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 4) (r := 81) (b := 1) (s := 19683) h4 (by decide +kernel)
  have h10 : (3 : ZMod 22691321) ^ 10 = 59049 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 5) (r := 243) (b := 0) (s := 59049) h5 (by decide +kernel)
  have h13 : (3 : ZMod 22691321) ^ 13 = 1594323 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 6) (r := 729) (b := 1) (s := 1594323) h6 (by decide +kernel)
  have h17 : (3 : ZMod 22691321) ^ 17 = 15683558 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 8) (r := 6561) (b := 1) (s := 15683558) h8 (by decide +kernel)
  have h18 : (3 : ZMod 22691321) ^ 18 = 1668032 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 9) (r := 19683) (b := 0) (s := 1668032) h9 (by decide +kernel)
  have h21 : (3 : ZMod 22691321) ^ 21 = 22345543 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 10) (r := 59049) (b := 1) (s := 22345543) h10 (by decide +kernel)
  have h27 : (3 : ZMod 22691321) ^ 27 = 20223690 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 13) (r := 1594323) (b := 1) (s := 20223690) h13 (by decide +kernel)
  have h34 : (3 : ZMod 22691321) ^ 34 = 3825401 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 17) (r := 15683558) (b := 0) (s := 3825401) h17 (by decide +kernel)
  have h36 : (3 : ZMod 22691321) ^ 36 = 11737288 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 18) (r := 1668032) (b := 0) (s := 11737288) h18 (by decide +kernel)
  have h37 : (3 : ZMod 22691321) ^ 37 = 12520543 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 18) (r := 1668032) (b := 1) (s := 12520543) h18 (by decide +kernel)
  have h43 : (3 : ZMod 22691321) ^ 43 = 5564805 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 21) (r := 22345543) (b := 1) (s := 5564805) h21 (by decide +kernel)
  have h54 : (3 : ZMod 22691321) ^ 54 = 9453132 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 27) (r := 20223690) (b := 0) (s := 9453132) h27 (by decide +kernel)
  have h69 : (3 : ZMod 22691321) ^ 69 = 20854456 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 34) (r := 3825401) (b := 1) (s := 20854456) h34 (by decide +kernel)
  have h72 : (3 : ZMod 22691321) ^ 72 = 18478608 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 36) (r := 11737288) (b := 0) (s := 18478608) h36 (by decide +kernel)
  have h75 : (3 : ZMod 22691321) ^ 75 = 22404675 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 37) (r := 12520543) (b := 1) (s := 22404675) h37 (by decide +kernel)
  have h86 : (3 : ZMod 22691321) ^ 86 = 4697436 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 43) (r := 5564805) (b := 0) (s := 4697436) h43 (by decide +kernel)
  have h108 : (3 : ZMod 22691321) ^ 108 = 14961200 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 54) (r := 9453132) (b := 0) (s := 14961200) h54 (by decide +kernel)
  have h138 : (3 : ZMod 22691321) ^ 138 = 9743451 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 69) (r := 20854456) (b := 0) (s := 9743451) h69 (by decide +kernel)
  have h145 : (3 : ZMod 22691321) ^ 145 = 1776918 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 72) (r := 18478608) (b := 1) (s := 1776918) h72 (by decide +kernel)
  have h151 : (3 : ZMod 22691321) ^ 151 = 1967925 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 75) (r := 22404675) (b := 1) (s := 1967925) h75 (by decide +kernel)
  have h173 : (3 : ZMod 22691321) ^ 173 = 6490494 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 86) (r := 4697436) (b := 1) (s := 6490494) h86 (by decide +kernel)
  have h216 : (3 : ZMod 22691321) ^ 216 = 13236266 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 108) (r := 14961200) (b := 0) (s := 13236266) h108 (by decide +kernel)
  have h276 : (3 : ZMod 22691321) ^ 276 = 464330 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 138) (r := 9743451) (b := 0) (s := 464330) h138 (by decide +kernel)
  have h291 : (3 : ZMod 22691321) ^ 291 = 2315290 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 145) (r := 1776918) (b := 1) (s := 2315290) h145 (by decide +kernel)
  have h303 : (3 : ZMod 22691321) ^ 303 = 3151665 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 151) (r := 1967925) (b := 1) (s := 3151665) h151 (by decide +kernel)
  have h346 : (3 : ZMod 22691321) ^ 346 = 6853573 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 173) (r := 6490494) (b := 0) (s := 6853573) h173 (by decide +kernel)
  have h433 : (3 : ZMod 22691321) ^ 433 = 3651714 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 216) (r := 13236266) (b := 1) (s := 3651714) h216 (by decide +kernel)
  have h553 : (3 : ZMod 22691321) ^ 553 = 13632916 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 276) (r := 464330) (b := 1) (s := 13632916) h276 (by decide +kernel)
  have h583 : (3 : ZMod 22691321) ^ 583 = 1098464 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 291) (r := 2315290) (b := 1) (s := 1098464) h291 (by decide +kernel)
  have h607 : (3 : ZMod 22691321) ^ 607 = 7957203 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 303) (r := 3151665) (b := 1) (s := 7957203) h303 (by decide +kernel)
  have h692 : (3 : ZMod 22691321) ^ 692 = 19952551 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 346) (r := 6853573) (b := 0) (s := 19952551) h346 (by decide +kernel)
  have h866 : (3 : ZMod 22691321) ^ 866 = 6525726 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 433) (r := 3651714) (b := 0) (s := 6525726) h433 (by decide +kernel)
  have h1107 : (3 : ZMod 22691321) ^ 1107 = 7830774 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 553) (r := 13632916) (b := 1) (s := 7830774) h553 (by decide +kernel)
  have h1166 : (3 : ZMod 22691321) ^ 1166 = 12165121 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 583) (r := 1098464) (b := 0) (s := 12165121) h583 (by decide +kernel)
  have h1214 : (3 : ZMod 22691321) ^ 1214 = 11661044 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 607) (r := 7957203) (b := 0) (s := 11661044) h607 (by decide +kernel)
  have h1384 : (3 : ZMod 22691321) ^ 1384 = 18043140 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 692) (r := 19952551) (b := 0) (s := 18043140) h692 (by decide +kernel)
  have h1733 : (3 : ZMod 22691321) ^ 1733 = 8157609 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 866) (r := 6525726) (b := 1) (s := 8157609) h866 (by decide +kernel)
  have h2215 : (3 : ZMod 22691321) ^ 2215 = 9397349 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 1107) (r := 7830774) (b := 1) (s := 9397349) h1107 (by decide +kernel)
  have h2332 : (3 : ZMod 22691321) ^ 2332 = 5575877 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 1166) (r := 12165121) (b := 0) (s := 5575877) h1166 (by decide +kernel)
  have h2428 : (3 : ZMod 22691321) ^ 2428 = 5019299 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 1214) (r := 11661044) (b := 0) (s := 5019299) h1214 (by decide +kernel)
  have h2769 : (3 : ZMod 22691321) ^ 2769 = 22499228 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 1384) (r := 18043140) (b := 1) (s := 22499228) h1384 (by decide +kernel)
  have h3467 : (3 : ZMod 22691321) ^ 3467 = 14005457 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 1733) (r := 8157609) (b := 1) (s := 14005457) h1733 (by decide +kernel)
  have h4431 : (3 : ZMod 22691321) ^ 4431 = 5875472 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 2215) (r := 9397349) (b := 1) (s := 5875472) h2215 (by decide +kernel)
  have h4665 : (3 : ZMod 22691321) ^ 4665 = 12922752 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 2332) (r := 5575877) (b := 1) (s := 12922752) h2332 (by decide +kernel)
  have h4856 : (3 : ZMod 22691321) ^ 4856 = 5632657 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 2428) (r := 5019299) (b := 0) (s := 5632657) h2428 (by decide +kernel)
  have h5539 : (3 : ZMod 22691321) ^ 5539 = 10898109 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 2769) (r := 22499228) (b := 1) (s := 10898109) h2769 (by decide +kernel)
  have h6935 : (3 : ZMod 22691321) ^ 6935 = 2344631 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 3467) (r := 14005457) (b := 1) (s := 2344631) h3467 (by decide +kernel)
  have h8863 : (3 : ZMod 22691321) ^ 8863 = 6945858 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 4431) (r := 5875472) (b := 1) (s := 6945858) h4431 (by decide +kernel)
  have h9330 : (3 : ZMod 22691321) ^ 9330 = 16231732 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 4665) (r := 12922752) (b := 0) (s := 16231732) h4665 (by decide +kernel)
  have h9713 : (3 : ZMod 22691321) ^ 9713 = 4164051 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 4856) (r := 5632657) (b := 1) (s := 4164051) h4856 (by decide +kernel)
  have h11079 : (3 : ZMod 22691321) ^ 11079 = 1145565 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 5539) (r := 10898109) (b := 1) (s := 1145565) h5539 (by decide +kernel)
  have h13870 : (3 : ZMod 22691321) ^ 13870 = 4335417 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 6935) (r := 2344631) (b := 0) (s := 4335417) h6935 (by decide +kernel)
  have h17727 : (3 : ZMod 22691321) ^ 17727 = 8993030 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 8863) (r := 6945858) (b := 1) (s := 8993030) h8863 (by decide +kernel)
  have h18660 : (3 : ZMod 22691321) ^ 18660 = 14058256 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 9330) (r := 16231732) (b := 0) (s := 14058256) h9330 (by decide +kernel)
  have h19427 : (3 : ZMod 22691321) ^ 19427 = 14870267 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 9713) (r := 4164051) (b := 1) (s := 14870267) h9713 (by decide +kernel)
  have h22159 : (3 : ZMod 22691321) ^ 22159 = 13314175 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 11079) (r := 1145565) (b := 1) (s := 13314175) h11079 (by decide +kernel)
  have h27740 : (3 : ZMod 22691321) ^ 27740 = 6713922 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 13870) (r := 4335417) (b := 0) (s := 6713922) h13870 (by decide +kernel)
  have h35455 : (3 : ZMod 22691321) ^ 35455 = 15426461 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 17727) (r := 8993030) (b := 1) (s := 15426461) h17727 (by decide +kernel)
  have h37321 : (3 : ZMod 22691321) ^ 37321 = 3200113 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 18660) (r := 14058256) (b := 1) (s := 3200113) h18660 (by decide +kernel)
  have h38855 : (3 : ZMod 22691321) ^ 38855 = 15323463 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 19427) (r := 14870267) (b := 1) (s := 15323463) h19427 (by decide +kernel)
  have h44318 : (3 : ZMod 22691321) ^ 44318 = 1394068 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 22159) (r := 13314175) (b := 0) (s := 1394068) h22159 (by decide +kernel)
  have h55480 : (3 : ZMod 22691321) ^ 55480 = 8320485 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 27740) (r := 6713922) (b := 0) (s := 8320485) h27740 (by decide +kernel)
  have h70910 : (3 : ZMod 22691321) ^ 70910 = 16170601 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 35455) (r := 15426461) (b := 0) (s := 16170601) h35455 (by decide +kernel)
  have h74642 : (3 : ZMod 22691321) ^ 74642 = 16588864 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 37321) (r := 3200113) (b := 0) (s := 16588864) h37321 (by decide +kernel)
  have h77710 : (3 : ZMod 22691321) ^ 77710 = 22009666 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 38855) (r := 15323463) (b := 0) (s := 22009666) h38855 (by decide +kernel)
  have h88637 : (3 : ZMod 22691321) ^ 88637 = 14130774 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 44318) (r := 1394068) (b := 1) (s := 14130774) h44318 (by decide +kernel)
  have h141820 : (3 : ZMod 22691321) ^ 141820 = 20523686 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 70910) (r := 16170601) (b := 0) (s := 20523686) h70910 (by decide +kernel)
  have h149285 : (3 : ZMod 22691321) ^ 149285 = 19563282 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 74642) (r := 16588864) (b := 1) (s := 19563282) h74642 (by decide +kernel)
  have h155420 : (3 : ZMod 22691321) ^ 155420 = 3358908 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 77710) (r := 22009666) (b := 0) (s := 3358908) h77710 (by decide +kernel)
  have h177275 : (3 : ZMod 22691321) ^ 177275 = 14945310 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 88637) (r := 14130774) (b := 1) (s := 14945310) h88637 (by decide +kernel)
  have h283641 : (3 : ZMod 22691321) ^ 283641 = 7800512 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 141820) (r := 20523686) (b := 1) (s := 7800512) h141820 (by decide +kernel)
  have h298570 : (3 : ZMod 22691321) ^ 298570 = 16913716 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 149285) (r := 19563282) (b := 0) (s := 16913716) h149285 (by decide +kernel)
  have h310840 : (3 : ZMod 22691321) ^ 310840 = 2003338 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 155420) (r := 3358908) (b := 0) (s := 2003338) h155420 (by decide +kernel)
  have h354551 : (3 : ZMod 22691321) ^ 354551 = 1310244 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 177275) (r := 14945310) (b := 1) (s := 1310244) h177275 (by decide +kernel)
  have h567283 : (3 : ZMod 22691321) ^ 567283 = 22681893 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 283641) (r := 7800512) (b := 1) (s := 22681893) h283641 (by decide +kernel)
  have h597140 : (3 : ZMod 22691321) ^ 597140 = 16421987 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 298570) (r := 16913716) (b := 0) (s := 16421987) h298570 (by decide +kernel)
  have h709103 : (3 : ZMod 22691321) ^ 709103 = 14273880 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 354551) (r := 1310244) (b := 1) (s := 14273880) h354551 (by decide +kernel)
  have h1134566 : (3 : ZMod 22691321) ^ 1134566 = 20813221 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 567283) (r := 22681893) (b := 0) (s := 20813221) h567283 (by decide +kernel)
  have h1194280 : (3 : ZMod 22691321) ^ 1194280 = 4046616 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 597140) (r := 16421987) (b := 0) (s := 4046616) h597140 (by decide +kernel)
  have h1418207 : (3 : ZMod 22691321) ^ 1418207 = 10607388 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 709103) (r := 14273880) (b := 1) (s := 10607388) h709103 (by decide +kernel)
  have h2269132 : (3 : ZMod 22691321) ^ 2269132 = 7217155 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 1134566) (r := 20813221) (b := 0) (s := 7217155) h1134566 (by decide +kernel)
  have h2836415 : (3 : ZMod 22691321) ^ 2836415 = 7934339 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 1418207) (r := 10607388) (b := 1) (s := 7934339) h1418207 (by decide +kernel)
  have h4538264 : (3 : ZMod 22691321) ^ 4538264 = 11604192 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 2269132) (r := 7217155) (b := 0) (s := 11604192) h2269132 (by decide +kernel)
  have h5672830 : (3 : ZMod 22691321) ^ 5672830 = 876608 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 2836415) (r := 7934339) (b := 0) (s := 876608) h2836415 (by decide +kernel)
  have h11345660 : (3 : ZMod 22691321) ^ 11345660 = 22691320 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 5672830) (r := 876608) (b := 0) (s := 22691320) h5672830 (by decide +kernel)
  have h22691320 : (3 : ZMod 22691321) ^ 22691320 = 1 :=
    modular_pow_step (p := 22691321) (a := 3) (e := 11345660) (r := 22691320) (b := 0) (s := 1) h11345660 (by decide +kernel)
  apply lucas_primality 22691321 3 (by simpa using h22691320)
  intro q hq hqd
  rw [show 22691321 - 1 = (2 * 2 * 2 * 5 * 19 * 73 * 409 : ℕ) by norm_num] at hqd
  simp only [hq.dvd_mul, Nat.dvd_prime prime_2, Nat.dvd_prime prime_5, Nat.dvd_prime prime_19, Nat.dvd_prime prime_73, Nat.dvd_prime prime_409, hq.ne_one, false_or] at hqd
  rcases hqd with ((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl)
  · change (3 : ZMod 22691321) ^ 11345660 ≠ 1
    rw [h11345660]
    decide +kernel
  · change (3 : ZMod 22691321) ^ 11345660 ≠ 1
    rw [h11345660]
    decide +kernel
  · change (3 : ZMod 22691321) ^ 11345660 ≠ 1
    rw [h11345660]
    decide +kernel
  · change (3 : ZMod 22691321) ^ 4538264 ≠ 1
    rw [h4538264]
    decide +kernel
  · change (3 : ZMod 22691321) ^ 1194280 ≠ 1
    rw [h1194280]
    decide +kernel
  · change (3 : ZMod 22691321) ^ 310840 ≠ 1
    rw [h310840]
    decide +kernel
  · change (3 : ZMod 22691321) ^ 55480 ≠ 1
    rw [h55480]
    decide +kernel

private lemma prime_61 : Nat.Prime 61 := by norm_num
private lemma prime_547 : Nat.Prime 547 := by norm_num
private lemma prime_17 : Nat.Prime 17 := by norm_num
lemma prime_3571 : Nat.Prime 3571 := by
  have h0 : (2 : ZMod 3571) ^ 0 = 1 := by simp
  have h1 : (2 : ZMod 3571) ^ 1 = 2 :=
    modular_pow_step (p := 3571) (a := 2) (e := 0) (r := 1) (b := 1) (s := 2) h0 (by decide +kernel)
  have h2 : (2 : ZMod 3571) ^ 2 = 4 :=
    modular_pow_step (p := 3571) (a := 2) (e := 1) (r := 2) (b := 0) (s := 4) h1 (by decide +kernel)
  have h3 : (2 : ZMod 3571) ^ 3 = 8 :=
    modular_pow_step (p := 3571) (a := 2) (e := 1) (r := 2) (b := 1) (s := 8) h1 (by decide +kernel)
  have h4 : (2 : ZMod 3571) ^ 4 = 16 :=
    modular_pow_step (p := 3571) (a := 2) (e := 2) (r := 4) (b := 0) (s := 16) h2 (by decide +kernel)
  have h5 : (2 : ZMod 3571) ^ 5 = 32 :=
    modular_pow_step (p := 3571) (a := 2) (e := 2) (r := 4) (b := 1) (s := 32) h2 (by decide +kernel)
  have h6 : (2 : ZMod 3571) ^ 6 = 64 :=
    modular_pow_step (p := 3571) (a := 2) (e := 3) (r := 8) (b := 0) (s := 64) h3 (by decide +kernel)
  have h7 : (2 : ZMod 3571) ^ 7 = 128 :=
    modular_pow_step (p := 3571) (a := 2) (e := 3) (r := 8) (b := 1) (s := 128) h3 (by decide +kernel)
  have h9 : (2 : ZMod 3571) ^ 9 = 512 :=
    modular_pow_step (p := 3571) (a := 2) (e := 4) (r := 16) (b := 1) (s := 512) h4 (by decide +kernel)
  have h11 : (2 : ZMod 3571) ^ 11 = 2048 :=
    modular_pow_step (p := 3571) (a := 2) (e := 5) (r := 32) (b := 1) (s := 2048) h5 (by decide +kernel)
  have h13 : (2 : ZMod 3571) ^ 13 = 1050 :=
    modular_pow_step (p := 3571) (a := 2) (e := 6) (r := 64) (b := 1) (s := 1050) h6 (by decide +kernel)
  have h15 : (2 : ZMod 3571) ^ 15 = 629 :=
    modular_pow_step (p := 3571) (a := 2) (e := 7) (r := 128) (b := 1) (s := 629) h7 (by decide +kernel)
  have h18 : (2 : ZMod 3571) ^ 18 = 1461 :=
    modular_pow_step (p := 3571) (a := 2) (e := 9) (r := 512) (b := 0) (s := 1461) h9 (by decide +kernel)
  have h22 : (2 : ZMod 3571) ^ 22 = 1950 :=
    modular_pow_step (p := 3571) (a := 2) (e := 11) (r := 2048) (b := 0) (s := 1950) h11 (by decide +kernel)
  have h26 : (2 : ZMod 3571) ^ 26 = 2632 :=
    modular_pow_step (p := 3571) (a := 2) (e := 13) (r := 1050) (b := 0) (s := 2632) h13 (by decide +kernel)
  have h27 : (2 : ZMod 3571) ^ 27 = 1693 :=
    modular_pow_step (p := 3571) (a := 2) (e := 13) (r := 1050) (b := 1) (s := 1693) h13 (by decide +kernel)
  have h31 : (2 : ZMod 3571) ^ 31 = 2091 :=
    modular_pow_step (p := 3571) (a := 2) (e := 15) (r := 629) (b := 1) (s := 2091) h15 (by decide +kernel)
  have h37 : (2 : ZMod 3571) ^ 37 = 1697 :=
    modular_pow_step (p := 3571) (a := 2) (e := 18) (r := 1461) (b := 1) (s := 1697) h18 (by decide +kernel)
  have h44 : (2 : ZMod 3571) ^ 44 = 2956 :=
    modular_pow_step (p := 3571) (a := 2) (e := 22) (r := 1950) (b := 0) (s := 2956) h22 (by decide +kernel)
  have h52 : (2 : ZMod 3571) ^ 52 = 3255 :=
    modular_pow_step (p := 3571) (a := 2) (e := 26) (r := 2632) (b := 0) (s := 3255) h26 (by decide +kernel)
  have h55 : (2 : ZMod 3571) ^ 55 = 1043 :=
    modular_pow_step (p := 3571) (a := 2) (e := 27) (r := 1693) (b := 1) (s := 1043) h27 (by decide +kernel)
  have h63 : (2 : ZMod 3571) ^ 63 = 2754 :=
    modular_pow_step (p := 3571) (a := 2) (e := 31) (r := 2091) (b := 1) (s := 2754) h31 (by decide +kernel)
  have h74 : (2 : ZMod 3571) ^ 74 = 1583 :=
    modular_pow_step (p := 3571) (a := 2) (e := 37) (r := 1697) (b := 0) (s := 1583) h37 (by decide +kernel)
  have h89 : (2 : ZMod 3571) ^ 89 = 2969 :=
    modular_pow_step (p := 3571) (a := 2) (e := 44) (r := 2956) (b := 1) (s := 2969) h44 (by decide +kernel)
  have h105 : (2 : ZMod 3571) ^ 105 = 3307 :=
    modular_pow_step (p := 3571) (a := 2) (e := 52) (r := 3255) (b := 1) (s := 3307) h52 (by decide +kernel)
  have h111 : (2 : ZMod 3571) ^ 111 = 959 :=
    modular_pow_step (p := 3571) (a := 2) (e := 55) (r := 1043) (b := 1) (s := 959) h55 (by decide +kernel)
  have h127 : (2 : ZMod 3571) ^ 127 = 2995 :=
    modular_pow_step (p := 3571) (a := 2) (e := 63) (r := 2754) (b := 1) (s := 2995) h63 (by decide +kernel)
  have h148 : (2 : ZMod 3571) ^ 148 = 2618 :=
    modular_pow_step (p := 3571) (a := 2) (e := 74) (r := 1583) (b := 0) (s := 2618) h74 (by decide +kernel)
  have h178 : (2 : ZMod 3571) ^ 178 = 1733 :=
    modular_pow_step (p := 3571) (a := 2) (e := 89) (r := 2969) (b := 0) (s := 1733) h89 (by decide +kernel)
  have h210 : (2 : ZMod 3571) ^ 210 = 1847 :=
    modular_pow_step (p := 3571) (a := 2) (e := 105) (r := 3307) (b := 0) (s := 1847) h105 (by decide +kernel)
  have h223 : (2 : ZMod 3571) ^ 223 = 297 :=
    modular_pow_step (p := 3571) (a := 2) (e := 111) (r := 959) (b := 1) (s := 297) h111 (by decide +kernel)
  have h255 : (2 : ZMod 3571) ^ 255 = 2917 :=
    modular_pow_step (p := 3571) (a := 2) (e := 127) (r := 2995) (b := 1) (s := 2917) h127 (by decide +kernel)
  have h297 : (2 : ZMod 3571) ^ 297 = 2350 :=
    modular_pow_step (p := 3571) (a := 2) (e := 148) (r := 2618) (b := 1) (s := 2350) h148 (by decide +kernel)
  have h357 : (2 : ZMod 3571) ^ 357 = 156 :=
    modular_pow_step (p := 3571) (a := 2) (e := 178) (r := 1733) (b := 1) (s := 156) h178 (by decide +kernel)
  have h446 : (2 : ZMod 3571) ^ 446 = 2505 :=
    modular_pow_step (p := 3571) (a := 2) (e := 223) (r := 297) (b := 0) (s := 2505) h223 (by decide +kernel)
  have h510 : (2 : ZMod 3571) ^ 510 = 2767 :=
    modular_pow_step (p := 3571) (a := 2) (e := 255) (r := 2917) (b := 0) (s := 2767) h255 (by decide +kernel)
  have h595 : (2 : ZMod 3571) ^ 595 = 3468 :=
    modular_pow_step (p := 3571) (a := 2) (e := 297) (r := 2350) (b := 1) (s := 3468) h297 (by decide +kernel)
  have h714 : (2 : ZMod 3571) ^ 714 = 2910 :=
    modular_pow_step (p := 3571) (a := 2) (e := 357) (r := 156) (b := 0) (s := 2910) h357 (by decide +kernel)
  have h892 : (2 : ZMod 3571) ^ 892 = 778 :=
    modular_pow_step (p := 3571) (a := 2) (e := 446) (r := 2505) (b := 0) (s := 778) h446 (by decide +kernel)
  have h1190 : (2 : ZMod 3571) ^ 1190 = 3467 :=
    modular_pow_step (p := 3571) (a := 2) (e := 595) (r := 3468) (b := 0) (s := 3467) h595 (by decide +kernel)
  have h1785 : (2 : ZMod 3571) ^ 1785 = 3570 :=
    modular_pow_step (p := 3571) (a := 2) (e := 892) (r := 778) (b := 1) (s := 3570) h892 (by decide +kernel)
  have h3570 : (2 : ZMod 3571) ^ 3570 = 1 :=
    modular_pow_step (p := 3571) (a := 2) (e := 1785) (r := 3570) (b := 0) (s := 1) h1785 (by decide +kernel)
  apply lucas_primality 3571 2 (by simpa using h3570)
  intro q hq hqd
  rw [show 3571 - 1 = (2 * 3 * 5 * 7 * 17 : ℕ) by norm_num] at hqd
  simp only [hq.dvd_mul, Nat.dvd_prime prime_2, Nat.dvd_prime prime_3, Nat.dvd_prime prime_5, Nat.dvd_prime prime_7, Nat.dvd_prime prime_17, hq.ne_one, false_or] at hqd
  rcases hqd with ((((rfl | rfl) | rfl) | rfl) | rfl)
  · change (2 : ZMod 3571) ^ 1785 ≠ 1
    rw [h1785]
    decide +kernel
  · change (2 : ZMod 3571) ^ 1190 ≠ 1
    rw [h1190]
    decide +kernel
  · change (2 : ZMod 3571) ^ 714 ≠ 1
    rw [h714]
    decide +kernel
  · change (2 : ZMod 3571) ^ 510 ≠ 1
    rw [h510]
    decide +kernel
  · change (2 : ZMod 3571) ^ 210 ≠ 1
    rw [h210]
    decide +kernel

lemma prime_7813349 : Nat.Prime 7813349 := by
  have h0 : (2 : ZMod 7813349) ^ 0 = 1 := by simp
  have h1 : (2 : ZMod 7813349) ^ 1 = 2 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 0) (r := 1) (b := 1) (s := 2) h0 (by decide +kernel)
  have h2 : (2 : ZMod 7813349) ^ 2 = 4 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 1) (r := 2) (b := 0) (s := 4) h1 (by decide +kernel)
  have h3 : (2 : ZMod 7813349) ^ 3 = 8 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 1) (r := 2) (b := 1) (s := 8) h1 (by decide +kernel)
  have h4 : (2 : ZMod 7813349) ^ 4 = 16 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 2) (r := 4) (b := 0) (s := 16) h2 (by decide +kernel)
  have h6 : (2 : ZMod 7813349) ^ 6 = 64 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 3) (r := 8) (b := 0) (s := 64) h3 (by decide +kernel)
  have h7 : (2 : ZMod 7813349) ^ 7 = 128 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 3) (r := 8) (b := 1) (s := 128) h3 (by decide +kernel)
  have h8 : (2 : ZMod 7813349) ^ 8 = 256 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 4) (r := 16) (b := 0) (s := 256) h4 (by decide +kernel)
  have h13 : (2 : ZMod 7813349) ^ 13 = 8192 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 6) (r := 64) (b := 1) (s := 8192) h6 (by decide +kernel)
  have h14 : (2 : ZMod 7813349) ^ 14 = 16384 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 7) (r := 128) (b := 0) (s := 16384) h7 (by decide +kernel)
  have h17 : (2 : ZMod 7813349) ^ 17 = 131072 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 8) (r := 256) (b := 1) (s := 131072) h8 (by decide +kernel)
  have h27 : (2 : ZMod 7813349) ^ 27 = 1390795 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 13) (r := 8192) (b := 1) (s := 1390795) h13 (by decide +kernel)
  have h29 : (2 : ZMod 7813349) ^ 29 = 5563180 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 14) (r := 16384) (b := 1) (s := 5563180) h14 (by decide +kernel)
  have h34 : (2 : ZMod 7813349) ^ 34 = 6128082 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 17) (r := 131072) (b := 0) (s := 6128082) h17 (by decide +kernel)
  have h55 : (2 : ZMod 7813349) ^ 55 = 5787029 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 27) (r := 1390795) (b := 1) (s := 5787029) h27 (by decide +kernel)
  have h59 : (2 : ZMod 7813349) ^ 59 = 6645625 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 29) (r := 5563180) (b := 1) (s := 6645625) h29 (by decide +kernel)
  have h68 : (2 : ZMod 7813349) ^ 68 = 3753185 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 34) (r := 6128082) (b := 0) (s := 3753185) h34 (by decide +kernel)
  have h111 : (2 : ZMod 7813349) ^ 111 = 6298914 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 55) (r := 5787029) (b := 1) (s := 6298914) h55 (by decide +kernel)
  have h119 : (2 : ZMod 7813349) ^ 119 = 2972090 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 59) (r := 6645625) (b := 1) (s := 2972090) h59 (by decide +kernel)
  have h136 : (2 : ZMod 7813349) ^ 136 = 7639387 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 68) (r := 3753185) (b := 0) (s := 7639387) h68 (by decide +kernel)
  have h223 : (2 : ZMod 7813349) ^ 223 = 4874275 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 111) (r := 6298914) (b := 1) (s := 4874275) h111 (by decide +kernel)
  have h238 : (2 : ZMod 7813349) ^ 238 = 7576291 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 119) (r := 2972090) (b := 0) (s := 7576291) h119 (by decide +kernel)
  have h273 : (2 : ZMod 7813349) ^ 273 = 3353534 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 136) (r := 7639387) (b := 1) (s := 3353534) h136 (by decide +kernel)
  have h446 : (2 : ZMod 7813349) ^ 446 = 6416989 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 223) (r := 4874275) (b := 0) (s := 6416989) h223 (by decide +kernel)
  have h476 : (2 : ZMod 7813349) ^ 476 = 2889356 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 238) (r := 7576291) (b := 0) (s := 2889356) h238 (by decide +kernel)
  have h547 : (2 : ZMod 7813349) ^ 547 = 6865173 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 273) (r := 3353534) (b := 1) (s := 6865173) h273 (by decide +kernel)
  have h892 : (2 : ZMod 7813349) ^ 892 = 6650 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 446) (r := 6416989) (b := 0) (s := 6650) h446 (by decide +kernel)
  have h953 : (2 : ZMod 7813349) ^ 953 = 4417224 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 476) (r := 2889356) (b := 1) (s := 4417224) h476 (by decide +kernel)
  have h1094 : (2 : ZMod 7813349) ^ 1094 = 2537640 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 547) (r := 6865173) (b := 0) (s := 2537640) h547 (by decide +kernel)
  have h1785 : (2 : ZMod 7813349) ^ 1785 = 2498161 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 892) (r := 6650) (b := 1) (s := 2498161) h892 (by decide +kernel)
  have h1907 : (2 : ZMod 7813349) ^ 1907 = 3218597 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 953) (r := 4417224) (b := 1) (s := 3218597) h953 (by decide +kernel)
  have h2188 : (2 : ZMod 7813349) ^ 2188 = 2977431 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 1094) (r := 2537640) (b := 0) (s := 2977431) h1094 (by decide +kernel)
  have h3571 : (2 : ZMod 7813349) ^ 3571 = 2696765 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 1785) (r := 2498161) (b := 1) (s := 2696765) h1785 (by decide +kernel)
  have h3815 : (2 : ZMod 7813349) ^ 3815 = 5433377 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 1907) (r := 3218597) (b := 1) (s := 5433377) h1907 (by decide +kernel)
  have h7142 : (2 : ZMod 7813349) ^ 7142 = 1229609 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 3571) (r := 2696765) (b := 0) (s := 1229609) h3571 (by decide +kernel)
  have h7630 : (2 : ZMod 7813349) ^ 7630 = 2803281 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 3815) (r := 5433377) (b := 0) (s := 2803281) h3815 (by decide +kernel)
  have h14284 : (2 : ZMod 7813349) ^ 14284 = 567938 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 7142) (r := 1229609) (b := 0) (s := 567938) h7142 (by decide +kernel)
  have h15260 : (2 : ZMod 7813349) ^ 15260 = 7034674 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 7630) (r := 2803281) (b := 0) (s := 7034674) h7630 (by decide +kernel)
  have h30520 : (2 : ZMod 7813349) ^ 30520 = 3246527 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 15260) (r := 7034674) (b := 0) (s := 3246527) h15260 (by decide +kernel)
  have h61041 : (2 : ZMod 7813349) ^ 61041 = 6455888 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 30520) (r := 3246527) (b := 1) (s := 6455888) h30520 (by decide +kernel)
  have h122083 : (2 : ZMod 7813349) ^ 122083 = 276722 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 61041) (r := 6455888) (b := 1) (s := 276722) h61041 (by decide +kernel)
  have h244167 : (2 : ZMod 7813349) ^ 244167 = 676819 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 122083) (r := 276722) (b := 1) (s := 676819) h122083 (by decide +kernel)
  have h488334 : (2 : ZMod 7813349) ^ 488334 = 2933589 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 244167) (r := 676819) (b := 0) (s := 2933589) h244167 (by decide +kernel)
  have h976668 : (2 : ZMod 7813349) ^ 976668 = 1485012 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 488334) (r := 2933589) (b := 0) (s := 1485012) h488334 (by decide +kernel)
  have h1953337 : (2 : ZMod 7813349) ^ 1953337 = 2970023 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 976668) (r := 1485012) (b := 1) (s := 2970023) h976668 (by decide +kernel)
  have h3906674 : (2 : ZMod 7813349) ^ 3906674 = 7813348 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 1953337) (r := 2970023) (b := 0) (s := 7813348) h1953337 (by decide +kernel)
  have h7813348 : (2 : ZMod 7813349) ^ 7813348 = 1 :=
    modular_pow_step (p := 7813349) (a := 2) (e := 3906674) (r := 7813348) (b := 0) (s := 1) h3906674 (by decide +kernel)
  apply lucas_primality 7813349 2 (by simpa using h7813348)
  intro q hq hqd
  rw [show 7813349 - 1 = (2 * 2 * 547 * 3571 : ℕ) by norm_num] at hqd
  simp only [hq.dvd_mul, Nat.dvd_prime prime_2, Nat.dvd_prime prime_547, Nat.dvd_prime prime_3571, hq.ne_one, false_or] at hqd
  rcases hqd with (((rfl | rfl) | rfl) | rfl)
  · change (2 : ZMod 7813349) ^ 3906674 ≠ 1
    rw [h3906674]
    decide +kernel
  · change (2 : ZMod 7813349) ^ 3906674 ≠ 1
    rw [h3906674]
    decide +kernel
  · change (2 : ZMod 7813349) ^ 14284 ≠ 1
    rw [h14284]
    decide +kernel
  · change (2 : ZMod 7813349) ^ 2188 ≠ 1
    rw [h2188]
    decide +kernel

lemma prime_12110690951 : Nat.Prime 12110690951 := by
  have h0 : (7 : ZMod 12110690951) ^ 0 = 1 := by simp
  have h1 : (7 : ZMod 12110690951) ^ 1 = 7 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 0) (r := 1) (b := 1) (s := 7) h0 (by decide +kernel)
  have h2 : (7 : ZMod 12110690951) ^ 2 = 49 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 1) (r := 7) (b := 0) (s := 49) h1 (by decide +kernel)
  have h3 : (7 : ZMod 12110690951) ^ 3 = 343 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 1) (r := 7) (b := 1) (s := 343) h1 (by decide +kernel)
  have h4 : (7 : ZMod 12110690951) ^ 4 = 2401 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 2) (r := 49) (b := 0) (s := 2401) h2 (by decide +kernel)
  have h5 : (7 : ZMod 12110690951) ^ 5 = 16807 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 2) (r := 49) (b := 1) (s := 16807) h2 (by decide +kernel)
  have h6 : (7 : ZMod 12110690951) ^ 6 = 117649 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 3) (r := 343) (b := 0) (s := 117649) h3 (by decide +kernel)
  have h9 : (7 : ZMod 12110690951) ^ 9 = 40353607 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 4) (r := 2401) (b := 1) (s := 40353607) h4 (by decide +kernel)
  have h11 : (7 : ZMod 12110690951) ^ 11 = 1977326743 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 5) (r := 16807) (b := 1) (s := 1977326743) h5 (by decide +kernel)
  have h12 : (7 : ZMod 12110690951) ^ 12 = 1730596250 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 6) (r := 117649) (b := 0) (s := 1730596250) h6 (by decide +kernel)
  have h18 : (7 : ZMod 12110690951) ^ 18 = 10092638989 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 9) (r := 40353607) (b := 0) (s := 10092638989) h9 (by decide +kernel)
  have h22 : (7 : ZMod 12110690951) ^ 22 = 11044310589 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 11) (r := 1977326743) (b := 0) (s := 11044310589) h11 (by decide +kernel)
  have h23 : (7 : ZMod 12110690951) ^ 23 = 4646028417 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 11) (r := 1977326743) (b := 1) (s := 4646028417) h11 (by decide +kernel)
  have h24 : (7 : ZMod 12110690951) ^ 24 = 8300817017 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 12) (r := 1730596250) (b := 0) (s := 8300817017) h12 (by decide +kernel)
  have h36 : (7 : ZMod 12110690951) ^ 36 = 4170231426 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 18) (r := 10092638989) (b := 0) (s := 4170231426) h18 (by decide +kernel)
  have h45 : (7 : ZMod 12110690951) ^ 45 = 4057361151 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 22) (r := 11044310589) (b := 1) (s := 4057361151) h22 (by decide +kernel)
  have h46 : (7 : ZMod 12110690951) ^ 46 = 4180146155 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 23) (r := 4646028417) (b := 0) (s := 4180146155) h23 (by decide +kernel)
  have h48 : (7 : ZMod 12110690951) ^ 48 = 11056106379 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 24) (r := 8300817017) (b := 0) (s := 11056106379) h24 (by decide +kernel)
  have h72 : (7 : ZMod 12110690951) ^ 72 = 4416088605 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 36) (r := 4170231426) (b := 0) (s := 4416088605) h36 (by decide +kernel)
  have h90 : (7 : ZMod 12110690951) ^ 90 = 7907884366 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 45) (r := 4057361151) (b := 0) (s := 7907884366) h45 (by decide +kernel)
  have h93 : (7 : ZMod 12110690951) ^ 93 = 11720255465 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 46) (r := 4180146155) (b := 1) (s := 11720255465) h46 (by decide +kernel)
  have h96 : (7 : ZMod 12110690951) ^ 96 = 11408919714 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 48) (r := 11056106379) (b := 0) (s := 11408919714) h48 (by decide +kernel)
  have h144 : (7 : ZMod 12110690951) ^ 144 = 1459061409 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 72) (r := 4416088605) (b := 0) (s := 1459061409) h72 (by decide +kernel)
  have h180 : (7 : ZMod 12110690951) ^ 180 = 3313594429 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 90) (r := 7907884366) (b := 0) (s := 3313594429) h90 (by decide +kernel)
  have h186 : (7 : ZMod 12110690951) ^ 186 = 10039955682 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 93) (r := 11720255465) (b := 0) (s := 10039955682) h93 (by decide +kernel)
  have h193 : (7 : ZMod 12110690951) ^ 193 = 3189245096 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 96) (r := 11408919714) (b := 1) (s := 3189245096) h96 (by decide +kernel)
  have h288 : (7 : ZMod 12110690951) ^ 288 = 7466863986 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 144) (r := 1459061409) (b := 0) (s := 7466863986) h144 (by decide +kernel)
  have h360 : (7 : ZMod 12110690951) ^ 360 = 5394150877 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 180) (r := 3313594429) (b := 0) (s := 5394150877) h180 (by decide +kernel)
  have h372 : (7 : ZMod 12110690951) ^ 372 = 11769327111 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 186) (r := 10039955682) (b := 0) (s := 11769327111) h186 (by decide +kernel)
  have h387 : (7 : ZMod 12110690951) ^ 387 = 9510375921 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 193) (r := 3189245096) (b := 1) (s := 9510375921) h193 (by decide +kernel)
  have h577 : (7 : ZMod 12110690951) ^ 577 = 10988610747 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 288) (r := 7466863986) (b := 1) (s := 10988610747) h288 (by decide +kernel)
  have h721 : (7 : ZMod 12110690951) ^ 721 = 2301360878 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 360) (r := 5394150877) (b := 1) (s := 2301360878) h360 (by decide +kernel)
  have h745 : (7 : ZMod 12110690951) ^ 745 = 3552323933 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 372) (r := 11769327111) (b := 1) (s := 3552323933) h372 (by decide +kernel)
  have h775 : (7 : ZMod 12110690951) ^ 775 = 10266550321 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 387) (r := 9510375921) (b := 1) (s := 10266550321) h387 (by decide +kernel)
  have h1154 : (7 : ZMod 12110690951) ^ 1154 = 2877431498 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 577) (r := 10988610747) (b := 0) (s := 2877431498) h577 (by decide +kernel)
  have h1443 : (7 : ZMod 12110690951) ^ 1443 = 11543433494 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 721) (r := 2301360878) (b := 1) (s := 11543433494) h721 (by decide +kernel)
  have h1490 : (7 : ZMod 12110690951) ^ 1490 = 8745637472 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 745) (r := 3552323933) (b := 0) (s := 8745637472) h745 (by decide +kernel)
  have h1550 : (7 : ZMod 12110690951) ^ 1550 = 6276490395 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 775) (r := 10266550321) (b := 0) (s := 6276490395) h775 (by decide +kernel)
  have h2309 : (7 : ZMod 12110690951) ^ 2309 = 12104416874 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 1154) (r := 2877431498) (b := 1) (s := 12104416874) h1154 (by decide +kernel)
  have h2887 : (7 : ZMod 12110690951) ^ 2887 = 2002767914 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 1443) (r := 11543433494) (b := 1) (s := 2002767914) h1443 (by decide +kernel)
  have h2980 : (7 : ZMod 12110690951) ^ 2980 = 9094805003 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 1490) (r := 8745637472) (b := 0) (s := 9094805003) h1490 (by decide +kernel)
  have h4619 : (7 : ZMod 12110690951) ^ 4619 = 5854896351 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 2309) (r := 12104416874) (b := 1) (s := 5854896351) h2309 (by decide +kernel)
  have h5774 : (7 : ZMod 12110690951) ^ 5774 = 5573011121 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 2887) (r := 2002767914) (b := 0) (s := 5573011121) h2887 (by decide +kernel)
  have h5961 : (7 : ZMod 12110690951) ^ 5961 = 9647991451 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 2980) (r := 9094805003) (b := 1) (s := 9647991451) h2980 (by decide +kernel)
  have h9239 : (7 : ZMod 12110690951) ^ 9239 = 4480817842 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 4619) (r := 5854896351) (b := 1) (s := 4480817842) h4619 (by decide +kernel)
  have h11549 : (7 : ZMod 12110690951) ^ 11549 = 3965768522 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 5774) (r := 5573011121) (b := 1) (s := 3965768522) h5774 (by decide +kernel)
  have h11922 : (7 : ZMod 12110690951) ^ 11922 = 6223952490 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 5961) (r := 9647991451) (b := 0) (s := 6223952490) h5961 (by decide +kernel)
  have h18479 : (7 : ZMod 12110690951) ^ 18479 = 2347708154 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 9239) (r := 4480817842) (b := 1) (s := 2347708154) h9239 (by decide +kernel)
  have h23099 : (7 : ZMod 12110690951) ^ 23099 = 10749417305 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 11549) (r := 3965768522) (b := 1) (s := 10749417305) h11549 (by decide +kernel)
  have h23844 : (7 : ZMod 12110690951) ^ 23844 = 7305863274 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 11922) (r := 6223952490) (b := 0) (s := 7305863274) h11922 (by decide +kernel)
  have h36958 : (7 : ZMod 12110690951) ^ 36958 = 7376931460 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 18479) (r := 2347708154) (b := 0) (s := 7376931460) h18479 (by decide +kernel)
  have h46198 : (7 : ZMod 12110690951) ^ 46198 = 9642028164 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 23099) (r := 10749417305) (b := 0) (s := 9642028164) h23099 (by decide +kernel)
  have h47688 : (7 : ZMod 12110690951) ^ 47688 = 5962823592 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 23844) (r := 7305863274) (b := 0) (s := 5962823592) h23844 (by decide +kernel)
  have h73917 : (7 : ZMod 12110690951) ^ 73917 = 4472846930 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 36958) (r := 7376931460) (b := 1) (s := 4472846930) h36958 (by decide +kernel)
  have h92397 : (7 : ZMod 12110690951) ^ 92397 = 403606339 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 46198) (r := 9642028164) (b := 1) (s := 403606339) h46198 (by decide +kernel)
  have h95377 : (7 : ZMod 12110690951) ^ 95377 = 1353388751 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 47688) (r := 5962823592) (b := 1) (s := 1353388751) h47688 (by decide +kernel)
  have h147835 : (7 : ZMod 12110690951) ^ 147835 = 5580329487 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 73917) (r := 4472846930) (b := 1) (s := 5580329487) h73917 (by decide +kernel)
  have h184794 : (7 : ZMod 12110690951) ^ 184794 = 6800764455 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 92397) (r := 403606339) (b := 0) (s := 6800764455) h92397 (by decide +kernel)
  have h190755 : (7 : ZMod 12110690951) ^ 190755 = 6649616865 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 95377) (r := 1353388751) (b := 1) (s := 6649616865) h95377 (by decide +kernel)
  have h295671 : (7 : ZMod 12110690951) ^ 295671 = 6741969425 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 147835) (r := 5580329487) (b := 1) (s := 6741969425) h147835 (by decide +kernel)
  have h369588 : (7 : ZMod 12110690951) ^ 369588 = 9129994454 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 184794) (r := 6800764455) (b := 0) (s := 9129994454) h184794 (by decide +kernel)
  have h381511 : (7 : ZMod 12110690951) ^ 381511 = 3864681279 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 190755) (r := 6649616865) (b := 1) (s := 3864681279) h190755 (by decide +kernel)
  have h591342 : (7 : ZMod 12110690951) ^ 591342 = 1417806521 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 295671) (r := 6741969425) (b := 0) (s := 1417806521) h295671 (by decide +kernel)
  have h739177 : (7 : ZMod 12110690951) ^ 739177 = 7695076250 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 369588) (r := 9129994454) (b := 1) (s := 7695076250) h369588 (by decide +kernel)
  have h763022 : (7 : ZMod 12110690951) ^ 763022 = 3778145502 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 381511) (r := 3864681279) (b := 0) (s := 3778145502) h381511 (by decide +kernel)
  have h1182684 : (7 : ZMod 12110690951) ^ 1182684 = 11429249754 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 591342) (r := 1417806521) (b := 0) (s := 11429249754) h591342 (by decide +kernel)
  have h1478355 : (7 : ZMod 12110690951) ^ 1478355 = 4227000851 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 739177) (r := 7695076250) (b := 1) (s := 4227000851) h739177 (by decide +kernel)
  have h1526044 : (7 : ZMod 12110690951) ^ 1526044 = 10631002549 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 763022) (r := 3778145502) (b := 0) (s := 10631002549) h763022 (by decide +kernel)
  have h2365369 : (7 : ZMod 12110690951) ^ 2365369 = 8521134926 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 1182684) (r := 11429249754) (b := 1) (s := 8521134926) h1182684 (by decide +kernel)
  have h2956711 : (7 : ZMod 12110690951) ^ 2956711 = 4006233900 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 1478355) (r := 4227000851) (b := 1) (s := 4006233900) h1478355 (by decide +kernel)
  have h3052089 : (7 : ZMod 12110690951) ^ 3052089 = 795378299 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 1526044) (r := 10631002549) (b := 1) (s := 795378299) h1526044 (by decide +kernel)
  have h4730738 : (7 : ZMod 12110690951) ^ 4730738 = 1930386061 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 2365369) (r := 8521134926) (b := 0) (s := 1930386061) h2365369 (by decide +kernel)
  have h5913423 : (7 : ZMod 12110690951) ^ 5913423 = 3100366444 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 2956711) (r := 4006233900) (b := 1) (s := 3100366444) h2956711 (by decide +kernel)
  have h6104178 : (7 : ZMod 12110690951) ^ 6104178 = 2995799312 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 3052089) (r := 795378299) (b := 0) (s := 2995799312) h3052089 (by decide +kernel)
  have h9461477 : (7 : ZMod 12110690951) ^ 9461477 = 11564302381 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 4730738) (r := 1930386061) (b := 1) (s := 11564302381) h4730738 (by decide +kernel)
  have h11826846 : (7 : ZMod 12110690951) ^ 11826846 = 2851065609 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 5913423) (r := 3100366444) (b := 0) (s := 2851065609) h5913423 (by decide +kernel)
  have h12208357 : (7 : ZMod 12110690951) ^ 12208357 = 8399939957 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 6104178) (r := 2995799312) (b := 1) (s := 8399939957) h6104178 (by decide +kernel)
  have h18922954 : (7 : ZMod 12110690951) ^ 18922954 = 8453908165 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 9461477) (r := 11564302381) (b := 0) (s := 8453908165) h9461477 (by decide +kernel)
  have h23653693 : (7 : ZMod 12110690951) ^ 23653693 = 7387690809 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 11826846) (r := 2851065609) (b := 1) (s := 7387690809) h11826846 (by decide +kernel)
  have h24416715 : (7 : ZMod 12110690951) ^ 24416715 = 4598977587 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 12208357) (r := 8399939957) (b := 1) (s := 4598977587) h12208357 (by decide +kernel)
  have h37845909 : (7 : ZMod 12110690951) ^ 37845909 = 10459074765 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 18922954) (r := 8453908165) (b := 1) (s := 10459074765) h18922954 (by decide +kernel)
  have h47307386 : (7 : ZMod 12110690951) ^ 47307386 = 5818188095 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 23653693) (r := 7387690809) (b := 0) (s := 5818188095) h23653693 (by decide +kernel)
  have h48833431 : (7 : ZMod 12110690951) ^ 48833431 = 5450960633 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 24416715) (r := 4598977587) (b := 1) (s := 5450960633) h24416715 (by decide +kernel)
  have h75691818 : (7 : ZMod 12110690951) ^ 75691818 = 4775172665 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 37845909) (r := 10459074765) (b := 0) (s := 4775172665) h37845909 (by decide +kernel)
  have h94614773 : (7 : ZMod 12110690951) ^ 94614773 = 8798497265 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 47307386) (r := 5818188095) (b := 1) (s := 8798497265) h47307386 (by decide +kernel)
  have h97666862 : (7 : ZMod 12110690951) ^ 97666862 = 3239947978 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 48833431) (r := 5450960633) (b := 0) (s := 3239947978) h48833431 (by decide +kernel)
  have h151383636 : (7 : ZMod 12110690951) ^ 151383636 = 3438248639 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 75691818) (r := 4775172665) (b := 0) (s := 3438248639) h75691818 (by decide +kernel)
  have h189229546 : (7 : ZMod 12110690951) ^ 189229546 = 7082880282 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 94614773) (r := 8798497265) (b := 0) (s := 7082880282) h94614773 (by decide +kernel)
  have h195333725 : (7 : ZMod 12110690951) ^ 195333725 = 1984317450 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 97666862) (r := 3239947978) (b := 1) (s := 1984317450) h97666862 (by decide +kernel)
  have h302767273 : (7 : ZMod 12110690951) ^ 302767273 = 5507498969 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 151383636) (r := 3438248639) (b := 1) (s := 5507498969) h151383636 (by decide +kernel)
  have h378459092 : (7 : ZMod 12110690951) ^ 378459092 = 2326241965 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 189229546) (r := 7082880282) (b := 0) (s := 2326241965) h189229546 (by decide +kernel)
  have h390667450 : (7 : ZMod 12110690951) ^ 390667450 = 990460142 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 195333725) (r := 1984317450) (b := 0) (s := 990460142) h195333725 (by decide +kernel)
  have h605534547 : (7 : ZMod 12110690951) ^ 605534547 = 4273580058 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 302767273) (r := 5507498969) (b := 1) (s := 4273580058) h302767273 (by decide +kernel)
  have h756918184 : (7 : ZMod 12110690951) ^ 756918184 = 1899212941 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 378459092) (r := 2326241965) (b := 0) (s := 1899212941) h378459092 (by decide +kernel)
  have h1211069095 : (7 : ZMod 12110690951) ^ 1211069095 = 6073307983 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 605534547) (r := 4273580058) (b := 1) (s := 6073307983) h605534547 (by decide +kernel)
  have h1513836368 : (7 : ZMod 12110690951) ^ 1513836368 = 5417035102 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 756918184) (r := 1899212941) (b := 0) (s := 5417035102) h756918184 (by decide +kernel)
  have h2422138190 : (7 : ZMod 12110690951) ^ 2422138190 = 1675043752 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 1211069095) (r := 6073307983) (b := 0) (s := 1675043752) h1211069095 (by decide +kernel)
  have h3027672737 : (7 : ZMod 12110690951) ^ 3027672737 = 7782657188 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 1513836368) (r := 5417035102) (b := 1) (s := 7782657188) h1513836368 (by decide +kernel)
  have h6055345475 : (7 : ZMod 12110690951) ^ 6055345475 = 12110690950 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 3027672737) (r := 7782657188) (b := 1) (s := 12110690950) h3027672737 (by decide +kernel)
  have h12110690950 : (7 : ZMod 12110690951) ^ 12110690950 = 1 :=
    modular_pow_step (p := 12110690951) (a := 7) (e := 6055345475) (r := 12110690950) (b := 0) (s := 1) h6055345475 (by decide +kernel)
  apply lucas_primality 12110690951 7 (by simpa using h12110690950)
  intro q hq hqd
  rw [show 12110690951 - 1 = (2 * 5 * 5 * 31 * 7813349 : ℕ) by norm_num] at hqd
  simp only [hq.dvd_mul, Nat.dvd_prime prime_2, Nat.dvd_prime prime_5, Nat.dvd_prime prime_31, Nat.dvd_prime prime_7813349, hq.ne_one, false_or] at hqd
  rcases hqd with ((((rfl | rfl) | rfl) | rfl) | rfl)
  · change (7 : ZMod 12110690951) ^ 6055345475 ≠ 1
    rw [h6055345475]
    decide +kernel
  · change (7 : ZMod 12110690951) ^ 2422138190 ≠ 1
    rw [h2422138190]
    decide +kernel
  · change (7 : ZMod 12110690951) ^ 2422138190 ≠ 1
    rw [h2422138190]
    decide +kernel
  · change (7 : ZMod 12110690951) ^ 390667450 ≠ 1
    rw [h390667450]
    decide +kernel
  · change (7 : ZMod 12110690951) ^ 1550 ≠ 1
    rw [h1550]
    decide +kernel

lemma prime_13297538664199 : Nat.Prime 13297538664199 := by
  have h0 : (3 : ZMod 13297538664199) ^ 0 = 1 := by simp
  have h1 : (3 : ZMod 13297538664199) ^ 1 = 3 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 0) (r := 1) (b := 1) (s := 3) h0 (by decide +kernel)
  have h2 : (3 : ZMod 13297538664199) ^ 2 = 9 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 1) (r := 3) (b := 0) (s := 9) h1 (by decide +kernel)
  have h3 : (3 : ZMod 13297538664199) ^ 3 = 27 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 1) (r := 3) (b := 1) (s := 27) h1 (by decide +kernel)
  have h4 : (3 : ZMod 13297538664199) ^ 4 = 81 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 2) (r := 9) (b := 0) (s := 81) h2 (by decide +kernel)
  have h6 : (3 : ZMod 13297538664199) ^ 6 = 729 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 3) (r := 27) (b := 0) (s := 729) h3 (by decide +kernel)
  have h8 : (3 : ZMod 13297538664199) ^ 8 = 6561 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 4) (r := 81) (b := 0) (s := 6561) h4 (by decide +kernel)
  have h12 : (3 : ZMod 13297538664199) ^ 12 = 531441 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 6) (r := 729) (b := 0) (s := 531441) h6 (by decide +kernel)
  have h16 : (3 : ZMod 13297538664199) ^ 16 = 43046721 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 8) (r := 6561) (b := 0) (s := 43046721) h8 (by decide +kernel)
  have h17 : (3 : ZMod 13297538664199) ^ 17 = 129140163 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 8) (r := 6561) (b := 1) (s := 129140163) h8 (by decide +kernel)
  have h24 : (3 : ZMod 13297538664199) ^ 24 = 282429536481 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 12) (r := 531441) (b := 0) (s := 282429536481) h12 (by decide +kernel)
  have h25 : (3 : ZMod 13297538664199) ^ 25 = 847288609443 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 12) (r := 531441) (b := 1) (s := 847288609443) h12 (by decide +kernel)
  have h32 : (3 : ZMod 13297538664199) ^ 32 = 4662314528180 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 16) (r := 43046721) (b := 0) (s := 4662314528180) h16 (by decide +kernel)
  have h34 : (3 : ZMod 13297538664199) ^ 34 = 2068214761023 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 17) (r := 129140163) (b := 0) (s := 2068214761023) h17 (by decide +kernel)
  have h48 : (3 : ZMod 13297538664199) ^ 48 = 8504553810799 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 24) (r := 282429536481) (b := 0) (s := 8504553810799) h24 (by decide +kernel)
  have h50 : (3 : ZMod 13297538664199) ^ 50 = 10053290976196 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 25) (r := 847288609443) (b := 0) (s := 10053290976196) h25 (by decide +kernel)
  have h64 : (3 : ZMod 13297538664199) ^ 64 = 1102909747775 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 32) (r := 4662314528180) (b := 0) (s := 1102909747775) h32 (by decide +kernel)
  have h68 : (3 : ZMod 13297538664199) ^ 68 = 9550457584581 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 34) (r := 2068214761023) (b := 0) (s := 9550457584581) h34 (by decide +kernel)
  have h96 : (3 : ZMod 13297538664199) ^ 96 = 8386930088416 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 48) (r := 8504553810799) (b := 0) (s := 8386930088416) h48 (by decide +kernel)
  have h101 : (3 : ZMod 13297538664199) ^ 101 = 3500595862641 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 50) (r := 10053290976196) (b := 1) (s := 3500595862641) h50 (by decide +kernel)
  have h129 : (3 : ZMod 13297538664199) ^ 129 = 6894645365458 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 64) (r := 1102909747775) (b := 1) (s := 6894645365458) h64 (by decide +kernel)
  have h137 : (3 : ZMod 13297538664199) ^ 137 = 10839245829139 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 68) (r := 9550457584581) (b := 1) (s := 10839245829139) h68 (by decide +kernel)
  have h193 : (3 : ZMod 13297538664199) ^ 193 = 3781656247512 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 96) (r := 8386930088416) (b := 1) (s := 3781656247512) h96 (by decide +kernel)
  have h203 : (3 : ZMod 13297538664199) ^ 203 = 10750510106480 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 101) (r := 3500595862641) (b := 1) (s := 10750510106480) h101 (by decide +kernel)
  have h258 : (3 : ZMod 13297538664199) ^ 258 = 1722063726039 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 129) (r := 6894645365458) (b := 0) (s := 1722063726039) h129 (by decide +kernel)
  have h274 : (3 : ZMod 13297538664199) ^ 274 = 6356950991774 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 137) (r := 10839245829139) (b := 0) (s := 6356950991774) h137 (by decide +kernel)
  have h387 : (3 : ZMod 13297538664199) ^ 387 = 10586819102164 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 193) (r := 3781656247512) (b := 1) (s := 10586819102164) h193 (by decide +kernel)
  have h406 : (3 : ZMod 13297538664199) ^ 406 = 10586415015429 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 203) (r := 10750510106480) (b := 0) (s := 10586415015429) h203 (by decide +kernel)
  have h516 : (3 : ZMod 13297538664199) ^ 516 = 1308172858861 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 258) (r := 1722063726039) (b := 0) (s := 1308172858861) h258 (by decide +kernel)
  have h549 : (3 : ZMod 13297538664199) ^ 549 = 11727458116389 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 274) (r := 6356950991774) (b := 1) (s := 11727458116389) h274 (by decide +kernel)
  have h774 : (3 : ZMod 13297538664199) ^ 774 = 13117070419208 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 387) (r := 10586819102164) (b := 0) (s := 13117070419208) h387 (by decide +kernel)
  have h812 : (3 : ZMod 13297538664199) ^ 812 = 3244174951716 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 406) (r := 10586415015429) (b := 0) (s := 3244174951716) h406 (by decide +kernel)
  have h1032 : (3 : ZMod 13297538664199) ^ 1032 = 7749848225369 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 516) (r := 1308172858861) (b := 0) (s := 7749848225369) h516 (by decide +kernel)
  have h1098 : (3 : ZMod 13297538664199) ^ 1098 = 1972126447124 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 549) (r := 11727458116389) (b := 0) (s := 1972126447124) h549 (by decide +kernel)
  have h1548 : (3 : ZMod 13297538664199) ^ 1548 = 7232767697754 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 774) (r := 13117070419208) (b := 0) (s := 7232767697754) h774 (by decide +kernel)
  have h1624 : (3 : ZMod 13297538664199) ^ 1624 = 12342989057731 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 812) (r := 3244174951716) (b := 0) (s := 12342989057731) h812 (by decide +kernel)
  have h2064 : (3 : ZMod 13297538664199) ^ 2064 = 2390805487667 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 1032) (r := 7749848225369) (b := 0) (s := 2390805487667) h1032 (by decide +kernel)
  have h3096 : (3 : ZMod 13297538664199) ^ 3096 = 13153202795038 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 1548) (r := 7232767697754) (b := 0) (s := 13153202795038) h1548 (by decide +kernel)
  have h3248 : (3 : ZMod 13297538664199) ^ 3248 = 11963464547122 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 1624) (r := 12342989057731) (b := 0) (s := 11963464547122) h1624 (by decide +kernel)
  have h4128 : (3 : ZMod 13297538664199) ^ 4128 = 3912790730452 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 2064) (r := 2390805487667) (b := 0) (s := 3912790730452) h2064 (by decide +kernel)
  have h6192 : (3 : ZMod 13297538664199) ^ 6192 = 9039919994235 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 3096) (r := 13153202795038) (b := 0) (s := 9039919994235) h3096 (by decide +kernel)
  have h6496 : (3 : ZMod 13297538664199) ^ 6496 = 12947707475712 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 3248) (r := 11963464547122) (b := 0) (s := 12947707475712) h3248 (by decide +kernel)
  have h8256 : (3 : ZMod 13297538664199) ^ 8256 = 611867443924 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 4128) (r := 3912790730452) (b := 0) (s := 611867443924) h4128 (by decide +kernel)
  have h12384 : (3 : ZMod 13297538664199) ^ 12384 = 102601857898 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 6192) (r := 9039919994235) (b := 0) (s := 102601857898) h6192 (by decide +kernel)
  have h12993 : (3 : ZMod 13297538664199) ^ 12993 = 6474778032425 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 6496) (r := 12947707475712) (b := 1) (s := 6474778032425) h6496 (by decide +kernel)
  have h16512 : (3 : ZMod 13297538664199) ^ 16512 = 2004199588858 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 8256) (r := 611867443924) (b := 0) (s := 2004199588858) h8256 (by decide +kernel)
  have h24768 : (3 : ZMod 13297538664199) ^ 24768 = 3602348158090 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 12384) (r := 102601857898) (b := 0) (s := 3602348158090) h12384 (by decide +kernel)
  have h25986 : (3 : ZMod 13297538664199) ^ 25986 = 13239255183446 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 12993) (r := 6474778032425) (b := 0) (s := 13239255183446) h12993 (by decide +kernel)
  have h33024 : (3 : ZMod 13297538664199) ^ 33024 = 7870450293091 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 16512) (r := 2004199588858) (b := 0) (s := 7870450293091) h16512 (by decide +kernel)
  have h49537 : (3 : ZMod 13297538664199) ^ 49537 = 4256029906063 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 24768) (r := 3602348158090) (b := 1) (s := 4256029906063) h24768 (by decide +kernel)
  have h51973 : (3 : ZMod 13297538664199) ^ 51973 = 8548590079964 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 25986) (r := 13239255183446) (b := 1) (s := 8548590079964) h25986 (by decide +kernel)
  have h66049 : (3 : ZMod 13297538664199) ^ 66049 = 3002831854406 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 33024) (r := 7870450293091) (b := 1) (s := 3002831854406) h33024 (by decide +kernel)
  have h99074 : (3 : ZMod 13297538664199) ^ 99074 = 4719949013297 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 49537) (r := 4256029906063) (b := 0) (s := 4719949013297) h49537 (by decide +kernel)
  have h103946 : (3 : ZMod 13297538664199) ^ 103946 = 1669362504520 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 51973) (r := 8548590079964) (b := 0) (s := 1669362504520) h51973 (by decide +kernel)
  have h132099 : (3 : ZMod 13297538664199) ^ 132099 = 887555121834 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 66049) (r := 3002831854406) (b := 1) (s := 887555121834) h66049 (by decide +kernel)
  have h198148 : (3 : ZMod 13297538664199) ^ 198148 = 490721643183 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 99074) (r := 4719949013297) (b := 0) (s := 490721643183) h99074 (by decide +kernel)
  have h207893 : (3 : ZMod 13297538664199) ^ 207893 = 4823580067599 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 103946) (r := 1669362504520) (b := 1) (s := 4823580067599) h103946 (by decide +kernel)
  have h264198 : (3 : ZMod 13297538664199) ^ 264198 = 8991519593538 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 132099) (r := 887555121834) (b := 0) (s := 8991519593538) h132099 (by decide +kernel)
  have h396297 : (3 : ZMod 13297538664199) ^ 396297 = 11884914152812 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 198148) (r := 490721643183) (b := 1) (s := 11884914152812) h198148 (by decide +kernel)
  have h415787 : (3 : ZMod 13297538664199) ^ 415787 = 11723432980668 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 207893) (r := 4823580067599) (b := 1) (s := 11723432980668) h207893 (by decide +kernel)
  have h528396 : (3 : ZMod 13297538664199) ^ 528396 = 1958061937708 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 264198) (r := 8991519593538) (b := 0) (s := 1958061937708) h264198 (by decide +kernel)
  have h792595 : (3 : ZMod 13297538664199) ^ 792595 = 704830266171 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 396297) (r := 11884914152812) (b := 1) (s := 704830266171) h396297 (by decide +kernel)
  have h831575 : (3 : ZMod 13297538664199) ^ 831575 = 717485511536 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 415787) (r := 11723432980668) (b := 1) (s := 717485511536) h415787 (by decide +kernel)
  have h1056793 : (3 : ZMod 13297538664199) ^ 1056793 = 1645203090809 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 528396) (r := 1958061937708) (b := 1) (s := 1645203090809) h528396 (by decide +kernel)
  have h1585190 : (3 : ZMod 13297538664199) ^ 1585190 = 8331505435024 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 792595) (r := 704830266171) (b := 0) (s := 8331505435024) h792595 (by decide +kernel)
  have h1663150 : (3 : ZMod 13297538664199) ^ 1663150 = 9245776826032 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 831575) (r := 717485511536) (b := 0) (s := 9245776826032) h831575 (by decide +kernel)
  have h2113586 : (3 : ZMod 13297538664199) ^ 2113586 = 13217947783202 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 1056793) (r := 1645203090809) (b := 0) (s := 13217947783202) h1056793 (by decide +kernel)
  have h3170380 : (3 : ZMod 13297538664199) ^ 3170380 = 1199793402545 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 1585190) (r := 8331505435024) (b := 0) (s := 1199793402545) h1585190 (by decide +kernel)
  have h3326300 : (3 : ZMod 13297538664199) ^ 3326300 = 2288073058828 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 1663150) (r := 9245776826032) (b := 0) (s := 2288073058828) h1663150 (by decide +kernel)
  have h4227173 : (3 : ZMod 13297538664199) ^ 4227173 = 10700644571888 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 2113586) (r := 13217947783202) (b := 1) (s := 10700644571888) h2113586 (by decide +kernel)
  have h6340760 : (3 : ZMod 13297538664199) ^ 6340760 = 1850960260870 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 3170380) (r := 1199793402545) (b := 0) (s := 1850960260870) h3170380 (by decide +kernel)
  have h6652601 : (3 : ZMod 13297538664199) ^ 6652601 = 7494433253222 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 3326300) (r := 2288073058828) (b := 1) (s := 7494433253222) h3326300 (by decide +kernel)
  have h8454347 : (3 : ZMod 13297538664199) ^ 8454347 = 5787731449202 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 4227173) (r := 10700644571888) (b := 1) (s := 5787731449202) h4227173 (by decide +kernel)
  have h12681521 : (3 : ZMod 13297538664199) ^ 12681521 = 12528580561167 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 6340760) (r := 1850960260870) (b := 1) (s := 12528580561167) h6340760 (by decide +kernel)
  have h13305202 : (3 : ZMod 13297538664199) ^ 13305202 = 6204013725494 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 6652601) (r := 7494433253222) (b := 0) (s := 6204013725494) h6652601 (by decide +kernel)
  have h16908694 : (3 : ZMod 13297538664199) ^ 16908694 = 11964577656282 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 8454347) (r := 5787731449202) (b := 0) (s := 11964577656282) h8454347 (by decide +kernel)
  have h25363042 : (3 : ZMod 13297538664199) ^ 25363042 = 9440223809429 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 12681521) (r := 12528580561167) (b := 0) (s := 9440223809429) h12681521 (by decide +kernel)
  have h26610404 : (3 : ZMod 13297538664199) ^ 26610404 = 6602541849073 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 13305202) (r := 6204013725494) (b := 0) (s := 6602541849073) h13305202 (by decide +kernel)
  have h33817389 : (3 : ZMod 13297538664199) ^ 33817389 = 1896955996216 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 16908694) (r := 11964577656282) (b := 1) (s := 1896955996216) h16908694 (by decide +kernel)
  have h50726084 : (3 : ZMod 13297538664199) ^ 50726084 = 12399806518978 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 25363042) (r := 9440223809429) (b := 0) (s := 12399806518978) h25363042 (by decide +kernel)
  have h53220809 : (3 : ZMod 13297538664199) ^ 53220809 = 4955540154484 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 26610404) (r := 6602541849073) (b := 1) (s := 4955540154484) h26610404 (by decide +kernel)
  have h67634779 : (3 : ZMod 13297538664199) ^ 67634779 = 3294720634782 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 33817389) (r := 1896955996216) (b := 1) (s := 3294720634782) h33817389 (by decide +kernel)
  have h101452168 : (3 : ZMod 13297538664199) ^ 101452168 = 8766034509760 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 50726084) (r := 12399806518978) (b := 0) (s := 8766034509760) h50726084 (by decide +kernel)
  have h106441619 : (3 : ZMod 13297538664199) ^ 106441619 = 1622563108710 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 53220809) (r := 4955540154484) (b := 1) (s := 1622563108710) h53220809 (by decide +kernel)
  have h135269558 : (3 : ZMod 13297538664199) ^ 135269558 = 4204235181460 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 67634779) (r := 3294720634782) (b := 0) (s := 4204235181460) h67634779 (by decide +kernel)
  have h202904337 : (3 : ZMod 13297538664199) ^ 202904337 = 11794037465744 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 101452168) (r := 8766034509760) (b := 1) (s := 11794037465744) h101452168 (by decide +kernel)
  have h212883239 : (3 : ZMod 13297538664199) ^ 212883239 = 4503428596493 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 106441619) (r := 1622563108710) (b := 1) (s := 4503428596493) h106441619 (by decide +kernel)
  have h270539116 : (3 : ZMod 13297538664199) ^ 270539116 = 9713006915909 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 135269558) (r := 4204235181460) (b := 0) (s := 9713006915909) h135269558 (by decide +kernel)
  have h405808675 : (3 : ZMod 13297538664199) ^ 405808675 = 11595576017460 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 202904337) (r := 11794037465744) (b := 1) (s := 11595576017460) h202904337 (by decide +kernel)
  have h425766478 : (3 : ZMod 13297538664199) ^ 425766478 = 2389264835547 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 212883239) (r := 4503428596493) (b := 0) (s := 2389264835547) h212883239 (by decide +kernel)
  have h541078233 : (3 : ZMod 13297538664199) ^ 541078233 = 7240568432506 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 270539116) (r := 9713006915909) (b := 1) (s := 7240568432506) h270539116 (by decide +kernel)
  have h811617350 : (3 : ZMod 13297538664199) ^ 811617350 = 10716857096336 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 405808675) (r := 11595576017460) (b := 0) (s := 10716857096336) h405808675 (by decide +kernel)
  have h851532957 : (3 : ZMod 13297538664199) ^ 851532957 = 2888060137639 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 425766478) (r := 2389264835547) (b := 1) (s := 2888060137639) h425766478 (by decide +kernel)
  have h1082156466 : (3 : ZMod 13297538664199) ^ 1082156466 = 2019281629547 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 541078233) (r := 7240568432506) (b := 0) (s := 2019281629547) h541078233 (by decide +kernel)
  have h1623234700 : (3 : ZMod 13297538664199) ^ 1623234700 = 6150323167905 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 811617350) (r := 10716857096336) (b := 0) (s := 6150323167905) h811617350 (by decide +kernel)
  have h1703065914 : (3 : ZMod 13297538664199) ^ 1703065914 = 1997557186149 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 851532957) (r := 2888060137639) (b := 0) (s := 1997557186149) h851532957 (by decide +kernel)
  have h2164312933 : (3 : ZMod 13297538664199) ^ 2164312933 = 5451648001692 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 1082156466) (r := 2019281629547) (b := 1) (s := 5451648001692) h1082156466 (by decide +kernel)
  have h3246469400 : (3 : ZMod 13297538664199) ^ 3246469400 = 5231324403213 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 1623234700) (r := 6150323167905) (b := 0) (s := 5231324403213) h1623234700 (by decide +kernel)
  have h3406131829 : (3 : ZMod 13297538664199) ^ 3406131829 = 6024180552731 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 1703065914) (r := 1997557186149) (b := 1) (s := 6024180552731) h1703065914 (by decide +kernel)
  have h4328625867 : (3 : ZMod 13297538664199) ^ 4328625867 = 12398103685917 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 2164312933) (r := 5451648001692) (b := 1) (s := 12398103685917) h2164312933 (by decide +kernel)
  have h6492938800 : (3 : ZMod 13297538664199) ^ 6492938800 = 3866435250105 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 3246469400) (r := 5231324403213) (b := 0) (s := 3866435250105) h3246469400 (by decide +kernel)
  have h6812263659 : (3 : ZMod 13297538664199) ^ 6812263659 = 913903522677 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 3406131829) (r := 6024180552731) (b := 1) (s := 913903522677) h3406131829 (by decide +kernel)
  have h8657251734 : (3 : ZMod 13297538664199) ^ 8657251734 = 938451480943 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 4328625867) (r := 12398103685917) (b := 0) (s := 938451480943) h4328625867 (by decide +kernel)
  have h12985877601 : (3 : ZMod 13297538664199) ^ 12985877601 = 7988995466131 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 6492938800) (r := 3866435250105) (b := 1) (s := 7988995466131) h6492938800 (by decide +kernel)
  have h13624527319 : (3 : ZMod 13297538664199) ^ 13624527319 = 5354747000325 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 6812263659) (r := 913903522677) (b := 1) (s := 5354747000325) h6812263659 (by decide +kernel)
  have h17314503469 : (3 : ZMod 13297538664199) ^ 17314503469 = 4206918890017 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 8657251734) (r := 938451480943) (b := 1) (s := 4206918890017) h8657251734 (by decide +kernel)
  have h25971755203 : (3 : ZMod 13297538664199) ^ 25971755203 = 731959936829 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 12985877601) (r := 7988995466131) (b := 1) (s := 731959936829) h12985877601 (by decide +kernel)
  have h27249054639 : (3 : ZMod 13297538664199) ^ 27249054639 = 6457128976190 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 13624527319) (r := 5354747000325) (b := 1) (s := 6457128976190) h13624527319 (by decide +kernel)
  have h34629006938 : (3 : ZMod 13297538664199) ^ 34629006938 = 795581048273 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 17314503469) (r := 4206918890017) (b := 0) (s := 795581048273) h17314503469 (by decide +kernel)
  have h51943510407 : (3 : ZMod 13297538664199) ^ 51943510407 = 4466378219652 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 25971755203) (r := 731959936829) (b := 1) (s := 4466378219652) h25971755203 (by decide +kernel)
  have h54498109279 : (3 : ZMod 13297538664199) ^ 54498109279 = 4207079439095 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 27249054639) (r := 6457128976190) (b := 1) (s := 4207079439095) h27249054639 (by decide +kernel)
  have h69258013876 : (3 : ZMod 13297538664199) ^ 69258013876 = 9399129796472 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 34629006938) (r := 795581048273) (b := 0) (s := 9399129796472) h34629006938 (by decide +kernel)
  have h103887020814 : (3 : ZMod 13297538664199) ^ 103887020814 = 5411277352337 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 51943510407) (r := 4466378219652) (b := 0) (s := 5411277352337) h51943510407 (by decide +kernel)
  have h108996218559 : (3 : ZMod 13297538664199) ^ 108996218559 = 11393934968816 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 54498109279) (r := 4207079439095) (b := 1) (s := 11393934968816) h54498109279 (by decide +kernel)
  have h138516027752 : (3 : ZMod 13297538664199) ^ 138516027752 = 10448943486418 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 69258013876) (r := 9399129796472) (b := 0) (s := 10448943486418) h69258013876 (by decide +kernel)
  have h207774041628 : (3 : ZMod 13297538664199) ^ 207774041628 = 3312865312660 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 103887020814) (r := 5411277352337) (b := 0) (s := 3312865312660) h103887020814 (by decide +kernel)
  have h217992437118 : (3 : ZMod 13297538664199) ^ 217992437118 = 10457554539209 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 108996218559) (r := 11393934968816) (b := 0) (s := 10457554539209) h108996218559 (by decide +kernel)
  have h277032055504 : (3 : ZMod 13297538664199) ^ 277032055504 = 3886091121023 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 138516027752) (r := 10448943486418) (b := 0) (s := 3886091121023) h138516027752 (by decide +kernel)
  have h415548083256 : (3 : ZMod 13297538664199) ^ 415548083256 = 9949624374569 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 207774041628) (r := 3312865312660) (b := 0) (s := 9949624374569) h207774041628 (by decide +kernel)
  have h554064111008 : (3 : ZMod 13297538664199) ^ 554064111008 = 5040084839548 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 277032055504) (r := 3886091121023) (b := 0) (s := 5040084839548) h277032055504 (by decide +kernel)
  have h831096166512 : (3 : ZMod 13297538664199) ^ 831096166512 = 11453732991414 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 415548083256) (r := 9949624374569) (b := 0) (s := 11453732991414) h415548083256 (by decide +kernel)
  have h1108128222016 : (3 : ZMod 13297538664199) ^ 1108128222016 = 11590066340606 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 554064111008) (r := 5040084839548) (b := 0) (s := 11590066340606) h554064111008 (by decide +kernel)
  have h1662192333024 : (3 : ZMod 13297538664199) ^ 1662192333024 = 3536620943702 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 831096166512) (r := 11453732991414) (b := 0) (s := 3536620943702) h831096166512 (by decide +kernel)
  have h2216256444033 : (3 : ZMod 13297538664199) ^ 2216256444033 = 5122416970778 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 1108128222016) (r := 11590066340606) (b := 1) (s := 5122416970778) h1108128222016 (by decide +kernel)
  have h3324384666049 : (3 : ZMod 13297538664199) ^ 3324384666049 = 9882594017014 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 1662192333024) (r := 3536620943702) (b := 1) (s := 9882594017014) h1662192333024 (by decide +kernel)
  have h4432512888066 : (3 : ZMod 13297538664199) ^ 4432512888066 = 5122416970777 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 2216256444033) (r := 5122416970778) (b := 0) (s := 5122416970777) h2216256444033 (by decide +kernel)
  have h6648769332099 : (3 : ZMod 13297538664199) ^ 6648769332099 = 13297538664198 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 3324384666049) (r := 9882594017014) (b := 1) (s := 13297538664198) h3324384666049 (by decide +kernel)
  have h13297538664198 : (3 : ZMod 13297538664199) ^ 13297538664198 = 1 :=
    modular_pow_step (p := 13297538664199) (a := 3) (e := 6648769332099) (r := 13297538664198) (b := 0) (s := 1) h6648769332099 (by decide +kernel)
  apply lucas_primality 13297538664199 3 (by simpa using h13297538664198)
  intro q hq hqd
  rw [show 13297538664199 - 1 = (2 * 3 * 3 * 61 * 12110690951 : ℕ) by norm_num] at hqd
  simp only [hq.dvd_mul, Nat.dvd_prime prime_2, Nat.dvd_prime prime_3, Nat.dvd_prime prime_61, Nat.dvd_prime prime_12110690951, hq.ne_one, false_or] at hqd
  rcases hqd with ((((rfl | rfl) | rfl) | rfl) | rfl)
  · change (3 : ZMod 13297538664199) ^ 6648769332099 ≠ 1
    rw [h6648769332099]
    decide +kernel
  · change (3 : ZMod 13297538664199) ^ 4432512888066 ≠ 1
    rw [h4432512888066]
    decide +kernel
  · change (3 : ZMod 13297538664199) ^ 4432512888066 ≠ 1
    rw [h4432512888066]
    decide +kernel
  · change (3 : ZMod 13297538664199) ^ 217992437118 ≠ 1
    rw [h217992437118]
    decide +kernel
  · change (3 : ZMod 13297538664199) ^ 1098 ≠ 1
    rw [h1098]
    decide +kernel

lemma prime_7241729240142017205097 : Nat.Prime 7241729240142017205097 := by
  have h0 : (11 : ZMod 7241729240142017205097) ^ 0 = 1 := by simp
  have h1 : (11 : ZMod 7241729240142017205097) ^ 1 = 11 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 0) (r := 1) (b := 1) (s := 11) h0 (by decide +kernel)
  have h2 : (11 : ZMod 7241729240142017205097) ^ 2 = 121 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 1) (r := 11) (b := 0) (s := 121) h1 (by decide +kernel)
  have h3 : (11 : ZMod 7241729240142017205097) ^ 3 = 1331 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 1) (r := 11) (b := 1) (s := 1331) h1 (by decide +kernel)
  have h4 : (11 : ZMod 7241729240142017205097) ^ 4 = 14641 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 2) (r := 121) (b := 0) (s := 14641) h2 (by decide +kernel)
  have h6 : (11 : ZMod 7241729240142017205097) ^ 6 = 1771561 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 3) (r := 1331) (b := 0) (s := 1771561) h3 (by decide +kernel)
  have h8 : (11 : ZMod 7241729240142017205097) ^ 8 = 214358881 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 4) (r := 14641) (b := 0) (s := 214358881) h4 (by decide +kernel)
  have h9 : (11 : ZMod 7241729240142017205097) ^ 9 = 2357947691 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 4) (r := 14641) (b := 1) (s := 2357947691) h4 (by decide +kernel)
  have h12 : (11 : ZMod 7241729240142017205097) ^ 12 = 3138428376721 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 6) (r := 1771561) (b := 0) (s := 3138428376721) h6 (by decide +kernel)
  have h16 : (11 : ZMod 7241729240142017205097) ^ 16 = 45949729863572161 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 8) (r := 214358881) (b := 0) (s := 45949729863572161) h8 (by decide +kernel)
  have h18 : (11 : ZMod 7241729240142017205097) ^ 18 = 5559917313492231481 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 9) (r := 2357947691) (b := 0) (s := 5559917313492231481) h9 (by decide +kernel)
  have h24 : (11 : ZMod 7241729240142017205097) ^ 24 = 980909214467695779921 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 12) (r := 3138428376721) (b := 0) (s := 980909214467695779921) h12 (by decide +kernel)
  have h32 : (11 : ZMod 7241729240142017205097) ^ 32 = 2254184629829190728340 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 16) (r := 45949729863572161) (b := 0) (s := 2254184629829190728340) h16 (by decide +kernel)
  have h36 : (11 : ZMod 7241729240142017205097) ^ 36 = 2957018002009049998911 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 18) (r := 5559917313492231481) (b := 0) (s := 2957018002009049998911) h18 (by decide +kernel)
  have h49 : (11 : ZMod 7241729240142017205097) ^ 49 = 5484404182936150388749 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 24) (r := 980909214467695779921) (b := 1) (s := 5484404182936150388749) h24 (by decide +kernel)
  have h64 : (11 : ZMod 7241729240142017205097) ^ 64 = 5201849658244820094976 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 32) (r := 2254184629829190728340) (b := 0) (s := 5201849658244820094976) h32 (by decide +kernel)
  have h65 : (11 : ZMod 7241729240142017205097) ^ 65 = 6528241559698900609057 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 32) (r := 2254184629829190728340) (b := 1) (s := 6528241559698900609057) h32 (by decide +kernel)
  have h72 : (11 : ZMod 7241729240142017205097) ^ 72 = 3003631659041197453668 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 36) (r := 2957018002009049998911) (b := 0) (s := 3003631659041197453668) h36 (by decide +kernel)
  have h98 : (11 : ZMod 7241729240142017205097) ^ 98 = 1250543686263110660598 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 49) (r := 5484404182936150388749) (b := 0) (s := 1250543686263110660598) h49 (by decide +kernel)
  have h129 : (11 : ZMod 7241729240142017205097) ^ 129 = 3160953738173197172331 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 64) (r := 5201849658244820094976) (b := 1) (s := 3160953738173197172331) h64 (by decide +kernel)
  have h130 : (11 : ZMod 7241729240142017205097) ^ 130 = 5803574159337100075253 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 65) (r := 6528241559698900609057) (b := 0) (s := 5803574159337100075253) h65 (by decide +kernel)
  have h145 : (11 : ZMod 7241729240142017205097) ^ 145 = 2117327600457163404649 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 72) (r := 3003631659041197453668) (b := 1) (s := 2117327600457163404649) h72 (by decide +kernel)
  have h196 : (11 : ZMod 7241729240142017205097) ^ 196 = 968349912978095272880 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 98) (r := 1250543686263110660598) (b := 0) (s := 968349912978095272880) h98 (by decide +kernel)
  have h259 : (11 : ZMod 7241729240142017205097) ^ 259 = 3920012389088474787263 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 129) (r := 3160953738173197172331) (b := 1) (s := 3920012389088474787263) h129 (by decide +kernel)
  have h261 : (11 : ZMod 7241729240142017205097) ^ 261 = 3609098470474330927518 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 130) (r := 5803574159337100075253) (b := 1) (s := 3609098470474330927518) h130 (by decide +kernel)
  have h290 : (11 : ZMod 7241729240142017205097) ^ 290 = 3985968691475124656217 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 145) (r := 2117327600457163404649) (b := 0) (s := 3985968691475124656217) h145 (by decide +kernel)
  have h392 : (11 : ZMod 7241729240142017205097) ^ 392 = 6237621635542197197022 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 196) (r := 968349912978095272880) (b := 0) (s := 6237621635542197197022) h196 (by decide +kernel)
  have h519 : (11 : ZMod 7241729240142017205097) ^ 519 = 2633922535858369544967 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 259) (r := 3920012389088474787263) (b := 1) (s := 2633922535858369544967) h259 (by decide +kernel)
  have h523 : (11 : ZMod 7241729240142017205097) ^ 523 = 1051643746146890720322 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 261) (r := 3609098470474330927518) (b := 1) (s := 1051643746146890720322) h261 (by decide +kernel)
  have h580 : (11 : ZMod 7241729240142017205097) ^ 580 = 4958312552581414382309 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 290) (r := 3985968691475124656217) (b := 0) (s := 4958312552581414382309) h290 (by decide +kernel)
  have h785 : (11 : ZMod 7241729240142017205097) ^ 785 = 5349286607651177653144 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 392) (r := 6237621635542197197022) (b := 1) (s := 5349286607651177653144) h392 (by decide +kernel)
  have h1038 : (11 : ZMod 7241729240142017205097) ^ 1038 = 457487424730402107217 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 519) (r := 2633922535858369544967) (b := 0) (s := 457487424730402107217) h519 (by decide +kernel)
  have h1046 : (11 : ZMod 7241729240142017205097) ^ 1046 = 1667141905132046078660 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 523) (r := 1051643746146890720322) (b := 0) (s := 1667141905132046078660) h523 (by decide +kernel)
  have h1161 : (11 : ZMod 7241729240142017205097) ^ 1161 = 128033319453726472129 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 580) (r := 4958312552581414382309) (b := 1) (s := 128033319453726472129) h580 (by decide +kernel)
  have h1570 : (11 : ZMod 7241729240142017205097) ^ 1570 = 1192311154741247246093 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 785) (r := 5349286607651177653144) (b := 0) (s := 1192311154741247246093) h785 (by decide +kernel)
  have h2077 : (11 : ZMod 7241729240142017205097) ^ 2077 = 4334781058734272619837 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 1038) (r := 457487424730402107217) (b := 1) (s := 4334781058734272619837) h1038 (by decide +kernel)
  have h2093 : (11 : ZMod 7241729240142017205097) ^ 2093 = 3114096226593959771949 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 1046) (r := 1667141905132046078660) (b := 1) (s := 3114096226593959771949) h1046 (by decide +kernel)
  have h2322 : (11 : ZMod 7241729240142017205097) ^ 2322 = 5073323917457410282784 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 1161) (r := 128033319453726472129) (b := 0) (s := 5073323917457410282784) h1161 (by decide +kernel)
  have h3140 : (11 : ZMod 7241729240142017205097) ^ 3140 = 4471053025630701380015 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 1570) (r := 1192311154741247246093) (b := 0) (s := 4471053025630701380015) h1570 (by decide +kernel)
  have h4154 : (11 : ZMod 7241729240142017205097) ^ 4154 = 1240214020871036800620 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 2077) (r := 4334781058734272619837) (b := 0) (s := 1240214020871036800620) h2077 (by decide +kernel)
  have h4187 : (11 : ZMod 7241729240142017205097) ^ 4187 = 408540366059624130352 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 2093) (r := 3114096226593959771949) (b := 1) (s := 408540366059624130352) h2093 (by decide +kernel)
  have h4644 : (11 : ZMod 7241729240142017205097) ^ 4644 = 6687366285265314749915 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 2322) (r := 5073323917457410282784) (b := 0) (s := 6687366285265314749915) h2322 (by decide +kernel)
  have h6281 : (11 : ZMod 7241729240142017205097) ^ 6281 = 1404488352166602127472 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 3140) (r := 4471053025630701380015) (b := 1) (s := 1404488352166602127472) h3140 (by decide +kernel)
  have h8309 : (11 : ZMod 7241729240142017205097) ^ 8309 = 4109856953600786383877 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 4154) (r := 1240214020871036800620) (b := 1) (s := 4109856953600786383877) h4154 (by decide +kernel)
  have h8374 : (11 : ZMod 7241729240142017205097) ^ 8374 = 2533408067120982748396 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 4187) (r := 408540366059624130352) (b := 0) (s := 2533408067120982748396) h4187 (by decide +kernel)
  have h9288 : (11 : ZMod 7241729240142017205097) ^ 9288 = 5309138824567213884677 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 4644) (r := 6687366285265314749915) (b := 0) (s := 5309138824567213884677) h4644 (by decide +kernel)
  have h12562 : (11 : ZMod 7241729240142017205097) ^ 12562 = 5310674368818501248835 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 6281) (r := 1404488352166602127472) (b := 0) (s := 5310674368818501248835) h6281 (by decide +kernel)
  have h16619 : (11 : ZMod 7241729240142017205097) ^ 16619 = 5393523313133822071509 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 8309) (r := 4109856953600786383877) (b := 1) (s := 5393523313133822071509) h8309 (by decide +kernel)
  have h16749 : (11 : ZMod 7241729240142017205097) ^ 16749 = 6236562587007148595902 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 8374) (r := 2533408067120982748396) (b := 1) (s := 6236562587007148595902) h8374 (by decide +kernel)
  have h18576 : (11 : ZMod 7241729240142017205097) ^ 18576 = 3630850199512635313667 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 9288) (r := 5309138824567213884677) (b := 0) (s := 3630850199512635313667) h9288 (by decide +kernel)
  have h25124 : (11 : ZMod 7241729240142017205097) ^ 25124 = 910778389974391071112 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 12562) (r := 5310674368818501248835) (b := 0) (s := 910778389974391071112) h12562 (by decide +kernel)
  have h33239 : (11 : ZMod 7241729240142017205097) ^ 33239 = 3978279730275237141700 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 16619) (r := 5393523313133822071509) (b := 1) (s := 3978279730275237141700) h16619 (by decide +kernel)
  have h33499 : (11 : ZMod 7241729240142017205097) ^ 33499 = 6120055170953469045708 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 16749) (r := 6236562587007148595902) (b := 1) (s := 6120055170953469045708) h16749 (by decide +kernel)
  have h37152 : (11 : ZMod 7241729240142017205097) ^ 37152 = 5071702294458243729635 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 18576) (r := 3630850199512635313667) (b := 0) (s := 5071702294458243729635) h18576 (by decide +kernel)
  have h50249 : (11 : ZMod 7241729240142017205097) ^ 50249 = 1636281560096178858616 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 25124) (r := 910778389974391071112) (b := 1) (s := 1636281560096178858616) h25124 (by decide +kernel)
  have h66478 : (11 : ZMod 7241729240142017205097) ^ 66478 = 2828889651185567325873 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 33239) (r := 3978279730275237141700) (b := 0) (s := 2828889651185567325873) h33239 (by decide +kernel)
  have h66999 : (11 : ZMod 7241729240142017205097) ^ 66999 = 7222500018978976882695 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 33499) (r := 6120055170953469045708) (b := 1) (s := 7222500018978976882695) h33499 (by decide +kernel)
  have h74305 : (11 : ZMod 7241729240142017205097) ^ 74305 = 2967712078041964159792 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 37152) (r := 5071702294458243729635) (b := 1) (s := 2967712078041964159792) h37152 (by decide +kernel)
  have h100499 : (11 : ZMod 7241729240142017205097) ^ 100499 = 224027211855989017047 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 50249) (r := 1636281560096178858616) (b := 1) (s := 224027211855989017047) h50249 (by decide +kernel)
  have h132956 : (11 : ZMod 7241729240142017205097) ^ 132956 = 2789023541015741858210 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 66478) (r := 2828889651185567325873) (b := 0) (s := 2789023541015741858210) h66478 (by decide +kernel)
  have h133998 : (11 : ZMod 7241729240142017205097) ^ 133998 = 6107178775133804995427 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 66999) (r := 7222500018978976882695) (b := 0) (s := 6107178775133804995427) h66999 (by decide +kernel)
  have h148611 : (11 : ZMod 7241729240142017205097) ^ 148611 = 5707876539038847446997 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 74305) (r := 2967712078041964159792) (b := 1) (s := 5707876539038847446997) h74305 (by decide +kernel)
  have h200998 : (11 : ZMod 7241729240142017205097) ^ 200998 = 1957792337773872823435 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 100499) (r := 224027211855989017047) (b := 0) (s := 1957792337773872823435) h100499 (by decide +kernel)
  have h265913 : (11 : ZMod 7241729240142017205097) ^ 265913 = 372784022401826112151 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 132956) (r := 2789023541015741858210) (b := 1) (s := 372784022401826112151) h132956 (by decide +kernel)
  have h267997 : (11 : ZMod 7241729240142017205097) ^ 267997 = 4822633563601680599146 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 133998) (r := 6107178775133804995427) (b := 1) (s := 4822633563601680599146) h133998 (by decide +kernel)
  have h297223 : (11 : ZMod 7241729240142017205097) ^ 297223 = 5867498809722406934193 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 148611) (r := 5707876539038847446997) (b := 1) (s := 5867498809722406934193) h148611 (by decide +kernel)
  have h401996 : (11 : ZMod 7241729240142017205097) ^ 401996 = 2232614686911520252421 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 200998) (r := 1957792337773872823435) (b := 0) (s := 2232614686911520252421) h200998 (by decide +kernel)
  have h531827 : (11 : ZMod 7241729240142017205097) ^ 531827 = 5718904633689516845533 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 265913) (r := 372784022401826112151) (b := 1) (s := 5718904633689516845533) h265913 (by decide +kernel)
  have h535995 : (11 : ZMod 7241729240142017205097) ^ 535995 = 6715301805519420737783 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 267997) (r := 4822633563601680599146) (b := 1) (s := 6715301805519420737783) h267997 (by decide +kernel)
  have h594446 : (11 : ZMod 7241729240142017205097) ^ 594446 = 1295879416443425499763 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 297223) (r := 5867498809722406934193) (b := 0) (s := 1295879416443425499763) h297223 (by decide +kernel)
  have h803993 : (11 : ZMod 7241729240142017205097) ^ 803993 = 5451797953235718065959 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 401996) (r := 2232614686911520252421) (b := 1) (s := 5451797953235718065959) h401996 (by decide +kernel)
  have h1063655 : (11 : ZMod 7241729240142017205097) ^ 1063655 = 6510157635053055753093 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 531827) (r := 5718904633689516845533) (b := 1) (s := 6510157635053055753093) h531827 (by decide +kernel)
  have h1071991 : (11 : ZMod 7241729240142017205097) ^ 1071991 = 4567695221352766804848 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 535995) (r := 6715301805519420737783) (b := 1) (s := 4567695221352766804848) h535995 (by decide +kernel)
  have h1188892 : (11 : ZMod 7241729240142017205097) ^ 1188892 = 2843153120746287510514 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 594446) (r := 1295879416443425499763) (b := 0) (s := 2843153120746287510514) h594446 (by decide +kernel)
  have h1607986 : (11 : ZMod 7241729240142017205097) ^ 1607986 = 2324677806641937378854 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 803993) (r := 5451797953235718065959) (b := 0) (s := 2324677806641937378854) h803993 (by decide +kernel)
  have h2127311 : (11 : ZMod 7241729240142017205097) ^ 2127311 = 6952329893160647901317 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 1063655) (r := 6510157635053055753093) (b := 1) (s := 6952329893160647901317) h1063655 (by decide +kernel)
  have h2143982 : (11 : ZMod 7241729240142017205097) ^ 2143982 = 2665577814261262549832 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 1071991) (r := 4567695221352766804848) (b := 0) (s := 2665577814261262549832) h1071991 (by decide +kernel)
  have h2377785 : (11 : ZMod 7241729240142017205097) ^ 2377785 = 3932999286277926405328 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 1188892) (r := 2843153120746287510514) (b := 1) (s := 3932999286277926405328) h1188892 (by decide +kernel)
  have h3215973 : (11 : ZMod 7241729240142017205097) ^ 3215973 = 4199087767060870271047 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 1607986) (r := 2324677806641937378854) (b := 1) (s := 4199087767060870271047) h1607986 (by decide +kernel)
  have h4254622 : (11 : ZMod 7241729240142017205097) ^ 4254622 = 3172001811571968191313 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 2127311) (r := 6952329893160647901317) (b := 0) (s := 3172001811571968191313) h2127311 (by decide +kernel)
  have h4287965 : (11 : ZMod 7241729240142017205097) ^ 4287965 = 3679695967458353018118 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 2143982) (r := 2665577814261262549832) (b := 1) (s := 3679695967458353018118) h2143982 (by decide +kernel)
  have h4755570 : (11 : ZMod 7241729240142017205097) ^ 4755570 = 6668407537398434903513 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 2377785) (r := 3932999286277926405328) (b := 0) (s := 6668407537398434903513) h2377785 (by decide +kernel)
  have h6431947 : (11 : ZMod 7241729240142017205097) ^ 6431947 = 6441880525337007488999 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 3215973) (r := 4199087767060870271047) (b := 1) (s := 6441880525337007488999) h3215973 (by decide +kernel)
  have h8509245 : (11 : ZMod 7241729240142017205097) ^ 8509245 = 3882725753351842939060 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 4254622) (r := 3172001811571968191313) (b := 1) (s := 3882725753351842939060) h4254622 (by decide +kernel)
  have h8575930 : (11 : ZMod 7241729240142017205097) ^ 8575930 = 4695135641983122287203 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 4287965) (r := 3679695967458353018118) (b := 0) (s := 4695135641983122287203) h4287965 (by decide +kernel)
  have h9511140 : (11 : ZMod 7241729240142017205097) ^ 9511140 = 4939492489632475151370 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 4755570) (r := 6668407537398434903513) (b := 0) (s := 4939492489632475151370) h4755570 (by decide +kernel)
  have h12863895 : (11 : ZMod 7241729240142017205097) ^ 12863895 = 2016534552185595026718 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 6431947) (r := 6441880525337007488999) (b := 1) (s := 2016534552185595026718) h6431947 (by decide +kernel)
  have h17018490 : (11 : ZMod 7241729240142017205097) ^ 17018490 = 5877416286698485011754 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 8509245) (r := 3882725753351842939060) (b := 0) (s := 5877416286698485011754) h8509245 (by decide +kernel)
  have h17151860 : (11 : ZMod 7241729240142017205097) ^ 17151860 = 910495821982195024417 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 8575930) (r := 4695135641983122287203) (b := 0) (s := 910495821982195024417) h8575930 (by decide +kernel)
  have h19022281 : (11 : ZMod 7241729240142017205097) ^ 19022281 = 2077349358193796954412 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 9511140) (r := 4939492489632475151370) (b := 1) (s := 2077349358193796954412) h9511140 (by decide +kernel)
  have h25727790 : (11 : ZMod 7241729240142017205097) ^ 25727790 = 267086042634148854863 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 12863895) (r := 2016534552185595026718) (b := 0) (s := 267086042634148854863) h12863895 (by decide +kernel)
  have h34036981 : (11 : ZMod 7241729240142017205097) ^ 34036981 = 6524321412275764284403 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 17018490) (r := 5877416286698485011754) (b := 1) (s := 6524321412275764284403) h17018490 (by decide +kernel)
  have h34303720 : (11 : ZMod 7241729240142017205097) ^ 34303720 = 1637898632473672594361 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 17151860) (r := 910495821982195024417) (b := 0) (s := 1637898632473672594361) h17151860 (by decide +kernel)
  have h38044563 : (11 : ZMod 7241729240142017205097) ^ 38044563 = 6238140467878753696913 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 19022281) (r := 2077349358193796954412) (b := 1) (s := 6238140467878753696913) h19022281 (by decide +kernel)
  have h51455581 : (11 : ZMod 7241729240142017205097) ^ 51455581 = 6331867780024036174777 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 25727790) (r := 267086042634148854863) (b := 1) (s := 6331867780024036174777) h25727790 (by decide +kernel)
  have h68073963 : (11 : ZMod 7241729240142017205097) ^ 68073963 = 6016074759969504844454 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 34036981) (r := 6524321412275764284403) (b := 1) (s := 6016074759969504844454) h34036981 (by decide +kernel)
  have h68607441 : (11 : ZMod 7241729240142017205097) ^ 68607441 = 2088600557506613853252 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 34303720) (r := 1637898632473672594361) (b := 1) (s := 2088600557506613853252) h34303720 (by decide +kernel)
  have h76089126 : (11 : ZMod 7241729240142017205097) ^ 76089126 = 4402293999641198530323 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 38044563) (r := 6238140467878753696913) (b := 0) (s := 4402293999641198530323) h38044563 (by decide +kernel)
  have h102911162 : (11 : ZMod 7241729240142017205097) ^ 102911162 = 2509124480650912604336 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 51455581) (r := 6331867780024036174777) (b := 0) (s := 2509124480650912604336) h51455581 (by decide +kernel)
  have h136147926 : (11 : ZMod 7241729240142017205097) ^ 136147926 = 1276044295244929983402 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 68073963) (r := 6016074759969504844454) (b := 0) (s := 1276044295244929983402) h68073963 (by decide +kernel)
  have h137214882 : (11 : ZMod 7241729240142017205097) ^ 137214882 = 3431350983864787763388 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 68607441) (r := 2088600557506613853252) (b := 0) (s := 3431350983864787763388) h68607441 (by decide +kernel)
  have h152178253 : (11 : ZMod 7241729240142017205097) ^ 152178253 = 369935432448169994739 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 76089126) (r := 4402293999641198530323) (b := 1) (s := 369935432448169994739) h76089126 (by decide +kernel)
  have h205822324 : (11 : ZMod 7241729240142017205097) ^ 205822324 = 869343522646187223301 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 102911162) (r := 2509124480650912604336) (b := 0) (s := 869343522646187223301) h102911162 (by decide +kernel)
  have h272295852 : (11 : ZMod 7241729240142017205097) ^ 272295852 = 4938230029541022327468 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 136147926) (r := 1276044295244929983402) (b := 0) (s := 4938230029541022327468) h136147926 (by decide +kernel)
  have h274429765 : (11 : ZMod 7241729240142017205097) ^ 274429765 = 6510687946664689891078 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 137214882) (r := 3431350983864787763388) (b := 1) (s := 6510687946664689891078) h137214882 (by decide +kernel)
  have h304356506 : (11 : ZMod 7241729240142017205097) ^ 304356506 = 374821741982681243140 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 152178253) (r := 369935432448169994739) (b := 0) (s := 374821741982681243140) h152178253 (by decide +kernel)
  have h411644648 : (11 : ZMod 7241729240142017205097) ^ 411644648 = 6127115647029138365660 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 205822324) (r := 869343522646187223301) (b := 0) (s := 6127115647029138365660) h205822324 (by decide +kernel)
  have h544591704 : (11 : ZMod 7241729240142017205097) ^ 544591704 = 928251171929905318043 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 272295852) (r := 4938230029541022327468) (b := 0) (s := 928251171929905318043) h272295852 (by decide +kernel)
  have h548859531 : (11 : ZMod 7241729240142017205097) ^ 548859531 = 1792722130056688785210 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 274429765) (r := 6510687946664689891078) (b := 1) (s := 1792722130056688785210) h274429765 (by decide +kernel)
  have h608713012 : (11 : ZMod 7241729240142017205097) ^ 608713012 = 1443572951585860151049 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 304356506) (r := 374821741982681243140) (b := 0) (s := 1443572951585860151049) h304356506 (by decide +kernel)
  have h823289296 : (11 : ZMod 7241729240142017205097) ^ 823289296 = 5434476435822126669434 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 411644648) (r := 6127115647029138365660) (b := 0) (s := 5434476435822126669434) h411644648 (by decide +kernel)
  have h1097719062 : (11 : ZMod 7241729240142017205097) ^ 1097719062 = 1383874635963372410578 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 548859531) (r := 1792722130056688785210) (b := 0) (s := 1383874635963372410578) h548859531 (by decide +kernel)
  have h1217426025 : (11 : ZMod 7241729240142017205097) ^ 1217426025 = 7141975000885556854665 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 608713012) (r := 1443572951585860151049) (b := 1) (s := 7141975000885556854665) h608713012 (by decide +kernel)
  have h1646578593 : (11 : ZMod 7241729240142017205097) ^ 1646578593 = 4160193313823022361948 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 823289296) (r := 5434476435822126669434) (b := 1) (s := 4160193313823022361948) h823289296 (by decide +kernel)
  have h2195438125 : (11 : ZMod 7241729240142017205097) ^ 2195438125 = 6605714208014242459222 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 1097719062) (r := 1383874635963372410578) (b := 1) (s := 6605714208014242459222) h1097719062 (by decide +kernel)
  have h2434852050 : (11 : ZMod 7241729240142017205097) ^ 2434852050 = 5225083631329715952122 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 1217426025) (r := 7141975000885556854665) (b := 0) (s := 5225083631329715952122) h1217426025 (by decide +kernel)
  have h3293157187 : (11 : ZMod 7241729240142017205097) ^ 3293157187 = 2722406634399750194633 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 1646578593) (r := 4160193313823022361948) (b := 1) (s := 2722406634399750194633) h1646578593 (by decide +kernel)
  have h4390876250 : (11 : ZMod 7241729240142017205097) ^ 4390876250 = 6879764486859483445708 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 2195438125) (r := 6605714208014242459222) (b := 0) (s := 6879764486859483445708) h2195438125 (by decide +kernel)
  have h4869704100 : (11 : ZMod 7241729240142017205097) ^ 4869704100 = 5731555770650357885120 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 2434852050) (r := 5225083631329715952122) (b := 0) (s := 5731555770650357885120) h2434852050 (by decide +kernel)
  have h6586314375 : (11 : ZMod 7241729240142017205097) ^ 6586314375 = 2339948023845143619616 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 3293157187) (r := 2722406634399750194633) (b := 1) (s := 2339948023845143619616) h3293157187 (by decide +kernel)
  have h8781752500 : (11 : ZMod 7241729240142017205097) ^ 8781752500 = 2808410520882785884470 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 4390876250) (r := 6879764486859483445708) (b := 0) (s := 2808410520882785884470) h4390876250 (by decide +kernel)
  have h9739408201 : (11 : ZMod 7241729240142017205097) ^ 9739408201 = 22304564359606236533 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 4869704100) (r := 5731555770650357885120) (b := 1) (s := 22304564359606236533) h4869704100 (by decide +kernel)
  have h13172628751 : (11 : ZMod 7241729240142017205097) ^ 13172628751 = 6633255140199833325000 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 6586314375) (r := 2339948023845143619616) (b := 1) (s := 6633255140199833325000) h6586314375 (by decide +kernel)
  have h17563505001 : (11 : ZMod 7241729240142017205097) ^ 17563505001 = 3791527691735321377602 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 8781752500) (r := 2808410520882785884470) (b := 1) (s := 3791527691735321377602) h8781752500 (by decide +kernel)
  have h19478816402 : (11 : ZMod 7241729240142017205097) ^ 19478816402 = 3145909164456466841824 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 9739408201) (r := 22304564359606236533) (b := 0) (s := 3145909164456466841824) h9739408201 (by decide +kernel)
  have h26345257502 : (11 : ZMod 7241729240142017205097) ^ 26345257502 = 5754127629312734749517 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 13172628751) (r := 6633255140199833325000) (b := 0) (s := 5754127629312734749517) h13172628751 (by decide +kernel)
  have h35127010003 : (11 : ZMod 7241729240142017205097) ^ 35127010003 = 6888059077369736876533 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 17563505001) (r := 3791527691735321377602) (b := 1) (s := 6888059077369736876533) h17563505001 (by decide +kernel)
  have h38957632805 : (11 : ZMod 7241729240142017205097) ^ 38957632805 = 5695248377401589690886 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 19478816402) (r := 3145909164456466841824) (b := 1) (s := 5695248377401589690886) h19478816402 (by decide +kernel)
  have h52690515004 : (11 : ZMod 7241729240142017205097) ^ 52690515004 = 6357935934710324804271 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 26345257502) (r := 5754127629312734749517) (b := 0) (s := 6357935934710324804271) h26345257502 (by decide +kernel)
  have h70254020006 : (11 : ZMod 7241729240142017205097) ^ 70254020006 = 7226986009879603123304 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 35127010003) (r := 6888059077369736876533) (b := 0) (s := 7226986009879603123304) h35127010003 (by decide +kernel)
  have h77915265610 : (11 : ZMod 7241729240142017205097) ^ 77915265610 = 5487586943228378368288 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 38957632805) (r := 5695248377401589690886) (b := 0) (s := 5487586943228378368288) h38957632805 (by decide +kernel)
  have h105381030009 : (11 : ZMod 7241729240142017205097) ^ 105381030009 = 6874203288110997714347 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 52690515004) (r := 6357935934710324804271) (b := 1) (s := 6874203288110997714347) h52690515004 (by decide +kernel)
  have h140508040012 : (11 : ZMod 7241729240142017205097) ^ 140508040012 = 4316674464774570882380 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 70254020006) (r := 7226986009879603123304) (b := 0) (s := 4316674464774570882380) h70254020006 (by decide +kernel)
  have h155830531221 : (11 : ZMod 7241729240142017205097) ^ 155830531221 = 768651662022157899057 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 77915265610) (r := 5487586943228378368288) (b := 1) (s := 768651662022157899057) h77915265610 (by decide +kernel)
  have h210762060018 : (11 : ZMod 7241729240142017205097) ^ 210762060018 = 7160752769509425558242 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 105381030009) (r := 6874203288110997714347) (b := 0) (s := 7160752769509425558242) h105381030009 (by decide +kernel)
  have h281016080024 : (11 : ZMod 7241729240142017205097) ^ 281016080024 = 4219680178798472804360 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 140508040012) (r := 4316674464774570882380) (b := 0) (s := 4219680178798472804360) h140508040012 (by decide +kernel)
  have h311661062442 : (11 : ZMod 7241729240142017205097) ^ 311661062442 = 6982212450132074896388 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 155830531221) (r := 768651662022157899057) (b := 0) (s := 6982212450132074896388) h155830531221 (by decide +kernel)
  have h421524120037 : (11 : ZMod 7241729240142017205097) ^ 421524120037 = 3900387161425193076803 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 210762060018) (r := 7160752769509425558242) (b := 1) (s := 3900387161425193076803) h210762060018 (by decide +kernel)
  have h562032160049 : (11 : ZMod 7241729240142017205097) ^ 562032160049 = 1028019096697077226411 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 281016080024) (r := 4219680178798472804360) (b := 1) (s := 1028019096697077226411) h281016080024 (by decide +kernel)
  have h623322124884 : (11 : ZMod 7241729240142017205097) ^ 623322124884 = 3828796128910586930782 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 311661062442) (r := 6982212450132074896388) (b := 0) (s := 3828796128910586930782) h311661062442 (by decide +kernel)
  have h843048240074 : (11 : ZMod 7241729240142017205097) ^ 843048240074 = 757445867691082373818 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 421524120037) (r := 3900387161425193076803) (b := 0) (s := 757445867691082373818) h421524120037 (by decide +kernel)
  have h1124064320099 : (11 : ZMod 7241729240142017205097) ^ 1124064320099 = 853393969248588129734 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 562032160049) (r := 1028019096697077226411) (b := 1) (s := 853393969248588129734) h562032160049 (by decide +kernel)
  have h1246644249768 : (11 : ZMod 7241729240142017205097) ^ 1246644249768 = 1401121514790106205034 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 623322124884) (r := 3828796128910586930782) (b := 0) (s := 1401121514790106205034) h623322124884 (by decide +kernel)
  have h1686096480149 : (11 : ZMod 7241729240142017205097) ^ 1686096480149 = 1608099766302958382089 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 843048240074) (r := 757445867691082373818) (b := 1) (s := 1608099766302958382089) h843048240074 (by decide +kernel)
  have h2248128640199 : (11 : ZMod 7241729240142017205097) ^ 2248128640199 = 4644154292493592473154 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 1124064320099) (r := 853393969248588129734) (b := 1) (s := 4644154292493592473154) h1124064320099 (by decide +kernel)
  have h2493288499537 : (11 : ZMod 7241729240142017205097) ^ 2493288499537 = 6857186098447818389935 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 1246644249768) (r := 1401121514790106205034) (b := 1) (s := 6857186098447818389935) h1246644249768 (by decide +kernel)
  have h3372192960298 : (11 : ZMod 7241729240142017205097) ^ 3372192960298 = 6978734405224168602668 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 1686096480149) (r := 1608099766302958382089) (b := 0) (s := 6978734405224168602668) h1686096480149 (by decide +kernel)
  have h4496257280398 : (11 : ZMod 7241729240142017205097) ^ 4496257280398 = 6743736002723955647757 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 2248128640199) (r := 4644154292493592473154) (b := 0) (s := 6743736002723955647757) h2248128640199 (by decide +kernel)
  have h4986576999074 : (11 : ZMod 7241729240142017205097) ^ 4986576999074 = 3577222979855148226901 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 2493288499537) (r := 6857186098447818389935) (b := 0) (s := 3577222979855148226901) h2493288499537 (by decide +kernel)
  have h6744385920597 : (11 : ZMod 7241729240142017205097) ^ 6744385920597 = 638036268553594361382 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 3372192960298) (r := 6978734405224168602668) (b := 1) (s := 638036268553594361382) h3372192960298 (by decide +kernel)
  have h8992514560796 : (11 : ZMod 7241729240142017205097) ^ 8992514560796 = 3186968011058019788500 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 4496257280398) (r := 6743736002723955647757) (b := 0) (s := 3186968011058019788500) h4496257280398 (by decide +kernel)
  have h9973153998149 : (11 : ZMod 7241729240142017205097) ^ 9973153998149 = 119405104815335206519 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 4986576999074) (r := 3577222979855148226901) (b := 1) (s := 119405104815335206519) h4986576999074 (by decide +kernel)
  have h13488771841194 : (11 : ZMod 7241729240142017205097) ^ 13488771841194 = 1669202153924283641382 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 6744385920597) (r := 638036268553594361382) (b := 0) (s := 1669202153924283641382) h6744385920597 (by decide +kernel)
  have h17985029121592 : (11 : ZMod 7241729240142017205097) ^ 17985029121592 = 3926468891527172901519 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 8992514560796) (r := 3186968011058019788500) (b := 0) (s := 3926468891527172901519) h8992514560796 (by decide +kernel)
  have h19946307996298 : (11 : ZMod 7241729240142017205097) ^ 19946307996298 = 4136729527730082489745 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 9973153998149) (r := 119405104815335206519) (b := 0) (s := 4136729527730082489745) h9973153998149 (by decide +kernel)
  have h26977543682389 : (11 : ZMod 7241729240142017205097) ^ 26977543682389 = 6574909661705552171714 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 13488771841194) (r := 1669202153924283641382) (b := 1) (s := 6574909661705552171714) h13488771841194 (by decide +kernel)
  have h35970058243185 : (11 : ZMod 7241729240142017205097) ^ 35970058243185 = 6374450611991229097120 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 17985029121592) (r := 3926468891527172901519) (b := 1) (s := 6374450611991229097120) h17985029121592 (by decide +kernel)
  have h39892615992597 : (11 : ZMod 7241729240142017205097) ^ 39892615992597 = 2517338115792469850957 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 19946307996298) (r := 4136729527730082489745) (b := 1) (s := 2517338115792469850957) h19946307996298 (by decide +kernel)
  have h53955087364778 : (11 : ZMod 7241729240142017205097) ^ 53955087364778 = 1979997361577448320726 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 26977543682389) (r := 6574909661705552171714) (b := 0) (s := 1979997361577448320726) h26977543682389 (by decide +kernel)
  have h71940116486370 : (11 : ZMod 7241729240142017205097) ^ 71940116486370 = 1089627916909332323741 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 35970058243185) (r := 6374450611991229097120) (b := 0) (s := 1089627916909332323741) h35970058243185 (by decide +kernel)
  have h79785231985194 : (11 : ZMod 7241729240142017205097) ^ 79785231985194 = 1268518495585795650143 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 39892615992597) (r := 2517338115792469850957) (b := 0) (s := 1268518495585795650143) h39892615992597 (by decide +kernel)
  have h107910174729556 : (11 : ZMod 7241729240142017205097) ^ 107910174729556 = 2533028908511545302945 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 53955087364778) (r := 1979997361577448320726) (b := 0) (s := 2533028908511545302945) h53955087364778 (by decide +kernel)
  have h143880232972741 : (11 : ZMod 7241729240142017205097) ^ 143880232972741 = 5855523208623856413839 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 71940116486370) (r := 1089627916909332323741) (b := 1) (s := 5855523208623856413839) h71940116486370 (by decide +kernel)
  have h159570463970388 : (11 : ZMod 7241729240142017205097) ^ 159570463970388 = 2171742931513869455784 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 79785231985194) (r := 1268518495585795650143) (b := 0) (s := 2171742931513869455784) h79785231985194 (by decide +kernel)
  have h215820349459112 : (11 : ZMod 7241729240142017205097) ^ 215820349459112 = 2997805153288986330898 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 107910174729556) (r := 2533028908511545302945) (b := 0) (s := 2997805153288986330898) h107910174729556 (by decide +kernel)
  have h287760465945482 : (11 : ZMod 7241729240142017205097) ^ 287760465945482 = 5106185071613245463161 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 143880232972741) (r := 5855523208623856413839) (b := 0) (s := 5106185071613245463161) h143880232972741 (by decide +kernel)
  have h319140927940776 : (11 : ZMod 7241729240142017205097) ^ 319140927940776 = 5650789035899516013226 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 159570463970388) (r := 2171742931513869455784) (b := 0) (s := 5650789035899516013226) h159570463970388 (by decide +kernel)
  have h431640698918224 : (11 : ZMod 7241729240142017205097) ^ 431640698918224 = 4604689826367861298911 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 215820349459112) (r := 2997805153288986330898) (b := 0) (s := 4604689826367861298911) h215820349459112 (by decide +kernel)
  have h575520931890965 : (11 : ZMod 7241729240142017205097) ^ 575520931890965 = 4231145899189584373153 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 287760465945482) (r := 5106185071613245463161) (b := 1) (s := 4231145899189584373153) h287760465945482 (by decide +kernel)
  have h863281397836448 : (11 : ZMod 7241729240142017205097) ^ 863281397836448 = 3633488008872903860829 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 431640698918224) (r := 4604689826367861298911) (b := 0) (s := 3633488008872903860829) h431640698918224 (by decide +kernel)
  have h1151041863781931 : (11 : ZMod 7241729240142017205097) ^ 1151041863781931 = 1106389568246281050400 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 575520931890965) (r := 4231145899189584373153) (b := 1) (s := 1106389568246281050400) h575520931890965 (by decide +kernel)
  have h1726562795672897 : (11 : ZMod 7241729240142017205097) ^ 1726562795672897 = 6242161708869900165287 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 863281397836448) (r := 3633488008872903860829) (b := 1) (s := 6242161708869900165287) h863281397836448 (by decide +kernel)
  have h2302083727563863 : (11 : ZMod 7241729240142017205097) ^ 2302083727563863 = 2598403797014318132615 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 1151041863781931) (r := 1106389568246281050400) (b := 1) (s := 2598403797014318132615) h1151041863781931 (by decide +kernel)
  have h3453125591345795 : (11 : ZMod 7241729240142017205097) ^ 3453125591345795 = 3179333950453427575372 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 1726562795672897) (r := 6242161708869900165287) (b := 1) (s := 3179333950453427575372) h1726562795672897 (by decide +kernel)
  have h4604167455127727 : (11 : ZMod 7241729240142017205097) ^ 4604167455127727 = 6020676730440709547148 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 2302083727563863) (r := 2598403797014318132615) (b := 1) (s := 6020676730440709547148) h2302083727563863 (by decide +kernel)
  have h6906251182691590 : (11 : ZMod 7241729240142017205097) ^ 6906251182691590 = 3012173848732803847794 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 3453125591345795) (r := 3179333950453427575372) (b := 0) (s := 3012173848732803847794) h3453125591345795 (by decide +kernel)
  have h9208334910255454 : (11 : ZMod 7241729240142017205097) ^ 9208334910255454 = 4835942273489208548404 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 4604167455127727) (r := 6020676730440709547148) (b := 0) (s := 4835942273489208548404) h4604167455127727 (by decide +kernel)
  have h13812502365383181 : (11 : ZMod 7241729240142017205097) ^ 13812502365383181 = 6552813309495194863393 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 6906251182691590) (r := 3012173848732803847794) (b := 1) (s := 6552813309495194863393) h6906251182691590 (by decide +kernel)
  have h18416669820510908 : (11 : ZMod 7241729240142017205097) ^ 18416669820510908 = 1508868463317843018603 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 9208334910255454) (r := 4835942273489208548404) (b := 0) (s := 1508868463317843018603) h9208334910255454 (by decide +kernel)
  have h27625004730766362 : (11 : ZMod 7241729240142017205097) ^ 27625004730766362 = 5956653581421909382940 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 13812502365383181) (r := 6552813309495194863393) (b := 0) (s := 5956653581421909382940) h13812502365383181 (by decide +kernel)
  have h36833339641021816 : (11 : ZMod 7241729240142017205097) ^ 36833339641021816 = 1792798989830512822258 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 18416669820510908) (r := 1508868463317843018603) (b := 0) (s := 1792798989830512822258) h18416669820510908 (by decide +kernel)
  have h55250009461532724 : (11 : ZMod 7241729240142017205097) ^ 55250009461532724 = 3643509876758910110907 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 27625004730766362) (r := 5956653581421909382940) (b := 0) (s := 3643509876758910110907) h27625004730766362 (by decide +kernel)
  have h73666679282043632 : (11 : ZMod 7241729240142017205097) ^ 73666679282043632 = 6995177086179697410268 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 36833339641021816) (r := 1792798989830512822258) (b := 0) (s := 6995177086179697410268) h36833339641021816 (by decide +kernel)
  have h110500018923065448 : (11 : ZMod 7241729240142017205097) ^ 110500018923065448 = 3675231184628766576782 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 55250009461532724) (r := 3643509876758910110907) (b := 0) (s := 3675231184628766576782) h55250009461532724 (by decide +kernel)
  have h147333358564087264 : (11 : ZMod 7241729240142017205097) ^ 147333358564087264 = 6505407956541538819597 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 73666679282043632) (r := 6995177086179697410268) (b := 0) (s := 6505407956541538819597) h73666679282043632 (by decide +kernel)
  have h221000037846130896 : (11 : ZMod 7241729240142017205097) ^ 221000037846130896 = 4475467273556677352364 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 110500018923065448) (r := 3675231184628766576782) (b := 0) (s := 4475467273556677352364) h110500018923065448 (by decide +kernel)
  have h294666717128174528 : (11 : ZMod 7241729240142017205097) ^ 294666717128174528 = 5606222764051944465241 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 147333358564087264) (r := 6505407956541538819597) (b := 0) (s := 5606222764051944465241) h147333358564087264 (by decide +kernel)
  have h442000075692261792 : (11 : ZMod 7241729240142017205097) ^ 442000075692261792 = 2513553137142605371524 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 221000037846130896) (r := 4475467273556677352364) (b := 0) (s := 2513553137142605371524) h221000037846130896 (by decide +kernel)
  have h589333434256349056 : (11 : ZMod 7241729240142017205097) ^ 589333434256349056 = 4122087291539457758030 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 294666717128174528) (r := 5606222764051944465241) (b := 0) (s := 4122087291539457758030) h294666717128174528 (by decide +kernel)
  have h884000151384523584 : (11 : ZMod 7241729240142017205097) ^ 884000151384523584 = 2438325613589603191205 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 442000075692261792) (r := 2513553137142605371524) (b := 0) (s := 2438325613589603191205) h442000075692261792 (by decide +kernel)
  have h1178666868512698112 : (11 : ZMod 7241729240142017205097) ^ 1178666868512698112 = 1297088632802937686196 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 589333434256349056) (r := 4122087291539457758030) (b := 0) (s := 1297088632802937686196) h589333434256349056 (by decide +kernel)
  have h1768000302769047169 : (11 : ZMod 7241729240142017205097) ^ 1768000302769047169 = 3278410721738773501505 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 884000151384523584) (r := 2438325613589603191205) (b := 1) (s := 3278410721738773501505) h884000151384523584 (by decide +kernel)
  have h2357333737025396225 : (11 : ZMod 7241729240142017205097) ^ 2357333737025396225 = 2873977726727148089933 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 1178666868512698112) (r := 1297088632802937686196) (b := 1) (s := 2873977726727148089933) h1178666868512698112 (by decide +kernel)
  have h3536000605538094338 : (11 : ZMod 7241729240142017205097) ^ 3536000605538094338 = 2127563510586128967800 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 1768000302769047169) (r := 3278410721738773501505) (b := 0) (s := 2127563510586128967800) h1768000302769047169 (by decide +kernel)
  have h4714667474050792451 : (11 : ZMod 7241729240142017205097) ^ 4714667474050792451 = 2783723780091849489832 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 2357333737025396225) (r := 2873977726727148089933) (b := 1) (s := 2783723780091849489832) h2357333737025396225 (by decide +kernel)
  have h7072001211076188676 : (11 : ZMod 7241729240142017205097) ^ 7072001211076188676 = 5412275307091421968004 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 3536000605538094338) (r := 2127563510586128967800) (b := 0) (s := 5412275307091421968004) h3536000605538094338 (by decide +kernel)
  have h9429334948101584902 : (11 : ZMod 7241729240142017205097) ^ 9429334948101584902 = 4868213153959740675786 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 4714667474050792451) (r := 2783723780091849489832) (b := 0) (s := 4868213153959740675786) h4714667474050792451 (by decide +kernel)
  have h14144002422152377353 : (11 : ZMod 7241729240142017205097) ^ 14144002422152377353 = 1563030078775580178839 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 7072001211076188676) (r := 5412275307091421968004) (b := 1) (s := 1563030078775580178839) h7072001211076188676 (by decide +kernel)
  have h18858669896203169804 : (11 : ZMod 7241729240142017205097) ^ 18858669896203169804 = 4692803556368506229572 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 9429334948101584902) (r := 4868213153959740675786) (b := 0) (s := 4692803556368506229572) h9429334948101584902 (by decide +kernel)
  have h28288004844304754707 : (11 : ZMod 7241729240142017205097) ^ 28288004844304754707 = 6262615613033957689477 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 14144002422152377353) (r := 1563030078775580178839) (b := 1) (s := 6262615613033957689477) h14144002422152377353 (by decide +kernel)
  have h37717339792406339609 : (11 : ZMod 7241729240142017205097) ^ 37717339792406339609 = 958976981015868813954 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 18858669896203169804) (r := 4692803556368506229572) (b := 1) (s := 958976981015868813954) h18858669896203169804 (by decide +kernel)
  have h56576009688609509414 : (11 : ZMod 7241729240142017205097) ^ 56576009688609509414 = 3447435768446215702246 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 28288004844304754707) (r := 6262615613033957689477) (b := 0) (s := 3447435768446215702246) h28288004844304754707 (by decide +kernel)
  have h75434679584812679219 : (11 : ZMod 7241729240142017205097) ^ 75434679584812679219 = 2742207727863207750511 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 37717339792406339609) (r := 958976981015868813954) (b := 1) (s := 2742207727863207750511) h37717339792406339609 (by decide +kernel)
  have h113152019377219018829 : (11 : ZMod 7241729240142017205097) ^ 113152019377219018829 = 1886973824040514664396 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 56576009688609509414) (r := 3447435768446215702246) (b := 1) (s := 1886973824040514664396) h56576009688609509414 (by decide +kernel)
  have h150869359169625358439 : (11 : ZMod 7241729240142017205097) ^ 150869359169625358439 = 4198970839094332041303 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 75434679584812679219) (r := 2742207727863207750511) (b := 1) (s := 4198970839094332041303) h75434679584812679219 (by decide +kernel)
  have h226304038754438037659 : (11 : ZMod 7241729240142017205097) ^ 226304038754438037659 = 3217261263861489203180 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 113152019377219018829) (r := 1886973824040514664396) (b := 1) (s := 3217261263861489203180) h113152019377219018829 (by decide +kernel)
  have h301738718339250716879 : (11 : ZMod 7241729240142017205097) ^ 301738718339250716879 = 2801734379910110032419 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 150869359169625358439) (r := 4198970839094332041303) (b := 1) (s := 2801734379910110032419) h150869359169625358439 (by decide +kernel)
  have h452608077508876075318 : (11 : ZMod 7241729240142017205097) ^ 452608077508876075318 = 2704769877626495688902 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 226304038754438037659) (r := 3217261263861489203180) (b := 0) (s := 2704769877626495688902) h226304038754438037659 (by decide +kernel)
  have h603477436678501433758 : (11 : ZMod 7241729240142017205097) ^ 603477436678501433758 = 1903506847982722821209 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 301738718339250716879) (r := 2801734379910110032419) (b := 0) (s := 1903506847982722821209) h301738718339250716879 (by decide +kernel)
  have h905216155017752150637 : (11 : ZMod 7241729240142017205097) ^ 905216155017752150637 = 103148820509761145330 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 452608077508876075318) (r := 2704769877626495688902) (b := 1) (s := 103148820509761145330) h452608077508876075318 (by decide +kernel)
  have h1206954873357002867516 : (11 : ZMod 7241729240142017205097) ^ 1206954873357002867516 = 165178552995531387481 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 603477436678501433758) (r := 1903506847982722821209) (b := 0) (s := 165178552995531387481) h603477436678501433758 (by decide +kernel)
  have h1810432310035504301274 : (11 : ZMod 7241729240142017205097) ^ 1810432310035504301274 = 3821023193761082476296 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 905216155017752150637) (r := 103148820509761145330) (b := 0) (s := 3821023193761082476296) h905216155017752150637 (by decide +kernel)
  have h2413909746714005735032 : (11 : ZMod 7241729240142017205097) ^ 2413909746714005735032 = 165178552995531387480 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 1206954873357002867516) (r := 165178552995531387481) (b := 0) (s := 165178552995531387480) h1206954873357002867516 (by decide +kernel)
  have h3620864620071008602548 : (11 : ZMod 7241729240142017205097) ^ 3620864620071008602548 = 7241729240142017205096 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 1810432310035504301274) (r := 3821023193761082476296) (b := 0) (s := 7241729240142017205096) h1810432310035504301274 (by decide +kernel)
  have h7241729240142017205096 : (11 : ZMod 7241729240142017205097) ^ 7241729240142017205096 = 1 :=
    modular_pow_step (p := 7241729240142017205097) (a := 11) (e := 3620864620071008602548) (r := 7241729240142017205096) (b := 0) (s := 1) h3620864620071008602548 (by decide +kernel)
  apply lucas_primality 7241729240142017205097 11 (by simpa using h7241729240142017205096)
  intro q hq hqd
  rw [show 7241729240142017205097 - 1 = (2 * 2 * 2 * 3 * 22691321 * 13297538664199 : ℕ) by norm_num] at hqd
  simp only [hq.dvd_mul, Nat.dvd_prime prime_2, Nat.dvd_prime prime_3, Nat.dvd_prime prime_22691321, Nat.dvd_prime prime_13297538664199, hq.ne_one, false_or] at hqd
  rcases hqd with (((((rfl | rfl) | rfl) | rfl) | rfl) | rfl)
  · change (11 : ZMod 7241729240142017205097) ^ 3620864620071008602548 ≠ 1
    rw [h3620864620071008602548]
    decide +kernel
  · change (11 : ZMod 7241729240142017205097) ^ 3620864620071008602548 ≠ 1
    rw [h3620864620071008602548]
    decide +kernel
  · change (11 : ZMod 7241729240142017205097) ^ 3620864620071008602548 ≠ 1
    rw [h3620864620071008602548]
    decide +kernel
  · change (11 : ZMod 7241729240142017205097) ^ 2413909746714005735032 ≠ 1
    rw [h2413909746714005735032]
    decide +kernel
  · change (11 : ZMod 7241729240142017205097) ^ 319140927940776 ≠ 1
    rw [h319140927940776]
    decide +kernel
  · change (11 : ZMod 7241729240142017205097) ^ 544591704 ≠ 1
    rw [h544591704]
    decide +kernel

lemma prime_2381018959592823667713667654121769861082703 : Nat.Prime 2381018959592823667713667654121769861082703 := by
  have h0 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 0 = 1 := by simp
  have h1 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1 = 5 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 0) (r := 1) (b := 1) (s := 5) h0 (by decide +kernel)
  have h2 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2 = 25 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1) (r := 5) (b := 0) (s := 25) h1 (by decide +kernel)
  have h3 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 3 = 125 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1) (r := 5) (b := 1) (s := 125) h1 (by decide +kernel)
  have h4 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 4 = 625 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2) (r := 25) (b := 0) (s := 625) h2 (by decide +kernel)
  have h6 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 6 = 15625 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 3) (r := 125) (b := 0) (s := 15625) h3 (by decide +kernel)
  have h7 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 7 = 78125 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 3) (r := 125) (b := 1) (s := 78125) h3 (by decide +kernel)
  have h8 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 8 = 390625 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4) (r := 625) (b := 0) (s := 390625) h4 (by decide +kernel)
  have h9 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 9 = 1953125 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4) (r := 625) (b := 1) (s := 1953125) h4 (by decide +kernel)
  have h13 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 13 = 1220703125 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 6) (r := 15625) (b := 1) (s := 1220703125) h6 (by decide +kernel)
  have h14 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 14 = 6103515625 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 7) (r := 78125) (b := 0) (s := 6103515625) h7 (by decide +kernel)
  have h16 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 16 = 152587890625 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 8) (r := 390625) (b := 0) (s := 152587890625) h8 (by decide +kernel)
  have h17 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 17 = 762939453125 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 8) (r := 390625) (b := 1) (s := 762939453125) h8 (by decide +kernel)
  have h18 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 18 = 3814697265625 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 9) (r := 1953125) (b := 0) (s := 3814697265625) h9 (by decide +kernel)
  have h27 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 27 = 7450580596923828125 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 13) (r := 1220703125) (b := 1) (s := 7450580596923828125) h13 (by decide +kernel)
  have h29 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 29 = 186264514923095703125 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 14) (r := 6103515625) (b := 1) (s := 186264514923095703125) h14 (by decide +kernel)
  have h33 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 33 = 116415321826934814453125 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 16) (r := 152587890625) (b := 1) (s := 116415321826934814453125) h16 (by decide +kernel)
  have h35 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 35 = 2910383045673370361328125 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 17) (r := 762939453125) (b := 1) (s := 2910383045673370361328125) h17 (by decide +kernel)
  have h37 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 37 = 72759576141834259033203125 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 18) (r := 3814697265625) (b := 1) (s := 72759576141834259033203125) h18 (by decide +kernel)
  have h54 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 54 = 55511151231257827021181583404541015625 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 27) (r := 7450580596923828125) (b := 0) (s := 55511151231257827021181583404541015625) h27 (by decide +kernel)
  have h58 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 58 = 34694469519536141888238489627838134765625 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 29) (r := 186264514923095703125) (b := 0) (s := 34694469519536141888238489627838134765625) h29 (by decide +kernel)
  have h66 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 66 = 2148257026045932134677391267279113400602852 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 33) (r := 116415321826934814453125) (b := 0) (s := 2148257026045932134677391267279113400602852) h33 (by decide +kernel)
  have h71 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 71 = 1210759301368001582018593277960138491772743 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 35) (r := 2910383045673370361328125) (b := 1) (s := 1210759301368001582018593277960138491772743) h35 (by decide +kernel)
  have h75 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 75 = 1941553164075886096388152368485511394747524 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 37) (r := 72759576141834259033203125) (b := 1) (s := 1941553164075886096388152368485511394747524) h37 (by decide +kernel)
  have h109 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 109 = 691903692090544115602175063790121679459944 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 54) (r := 55511151231257827021181583404541015625) (b := 1) (s := 691903692090544115602175063790121679459944) h54 (by decide +kernel)
  have h117 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 117 = 655581568194987585791538345940567820842064 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 58) (r := 34694469519536141888238489627838134765625) (b := 1) (s := 655581568194987585791538345940567820842064) h58 (by decide +kernel)
  have h132 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 132 = 209811232876508410432071892453120486077714 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 66) (r := 2148257026045932134677391267279113400602852) (b := 0) (s := 209811232876508410432071892453120486077714) h66 (by decide +kernel)
  have h142 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 142 = 1956780199487671727362003752250065038451363 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 71) (r := 1210759301368001582018593277960138491772743) (b := 0) (s := 1956780199487671727362003752250065038451363) h71 (by decide +kernel)
  have h151 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 151 = 888588968160041345071623548308185083623797 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 75) (r := 1941553164075886096388152368485511394747524) (b := 1) (s := 888588968160041345071623548308185083623797) h75 (by decide +kernel)
  have h218 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 218 = 1319659365179732047860143950128301118025824 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 109) (r := 691903692090544115602175063790121679459944) (b := 0) (s := 1319659365179732047860143950128301118025824) h109 (by decide +kernel)
  have h235 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 235 = 281745025708425616562547276020207323630503 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 117) (r := 655581568194987585791538345940567820842064) (b := 1) (s := 281745025708425616562547276020207323630503) h117 (by decide +kernel)
  have h264 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 264 = 991858246886369387259428324818310834000511 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 132) (r := 209811232876508410432071892453120486077714) (b := 0) (s := 991858246886369387259428324818310834000511) h132 (by decide +kernel)
  have h285 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 285 = 1206064982558193901667485956907562828819578 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 142) (r := 1956780199487671727362003752250065038451363) (b := 1) (s := 1206064982558193901667485956907562828819578) h142 (by decide +kernel)
  have h302 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 302 = 1340893209321689846323179088899140270124269 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 151) (r := 888588968160041345071623548308185083623797) (b := 0) (s := 1340893209321689846323179088899140270124269) h151 (by decide +kernel)
  have h437 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 437 = 2256868389191174820380740812191480295069166 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 218) (r := 1319659365179732047860143950128301118025824) (b := 1) (s := 2256868389191174820380740812191480295069166) h218 (by decide +kernel)
  have h470 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 470 = 277698188882235007685527579694008268461341 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 235) (r := 281745025708425616562547276020207323630503) (b := 0) (s := 277698188882235007685527579694008268461341) h235 (by decide +kernel)
  have h528 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 528 = 810261879455092107029495345307073581475653 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 264) (r := 991858246886369387259428324818310834000511) (b := 0) (s := 810261879455092107029495345307073581475653) h264 (by decide +kernel)
  have h570 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 570 = 2216899884941364619570804020810314448370658 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 285) (r := 1206064982558193901667485956907562828819578) (b := 0) (s := 2216899884941364619570804020810314448370658) h285 (by decide +kernel)
  have h604 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 604 = 146055180054837821881152409377833950340269 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 302) (r := 1340893209321689846323179088899140270124269) (b := 0) (s := 146055180054837821881152409377833950340269) h302 (by decide +kernel)
  have h874 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 874 = 73804701150936183597550953980118519150611 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 437) (r := 2256868389191174820380740812191480295069166) (b := 0) (s := 73804701150936183597550953980118519150611) h437 (by decide +kernel)
  have h940 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 940 = 2294675346746499614245539781402291620034692 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 470) (r := 277698188882235007685527579694008268461341) (b := 0) (s := 2294675346746499614245539781402291620034692) h470 (by decide +kernel)
  have h1056 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1056 = 1844084796446529842120524361875980687784179 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 528) (r := 810261879455092107029495345307073581475653) (b := 0) (s := 1844084796446529842120524361875980687784179) h528 (by decide +kernel)
  have h1140 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1140 = 1356618746901078470161921360220262864849315 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 570) (r := 2216899884941364619570804020810314448370658) (b := 0) (s := 1356618746901078470161921360220262864849315) h570 (by decide +kernel)
  have h1208 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1208 = 2174327923378042115878714979419782514969049 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 604) (r := 146055180054837821881152409377833950340269) (b := 0) (s := 2174327923378042115878714979419782514969049) h604 (by decide +kernel)
  have h1749 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1749 = 722124654913212471746165475225865879668798 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 874) (r := 73804701150936183597550953980118519150611) (b := 1) (s := 722124654913212471746165475225865879668798) h874 (by decide +kernel)
  have h1881 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1881 = 823253187530668453093383928717085373607861 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 940) (r := 2294675346746499614245539781402291620034692) (b := 1) (s := 823253187530668453093383928717085373607861) h940 (by decide +kernel)
  have h2112 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2112 = 2111532206162930266076090959577023743009680 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1056) (r := 1844084796446529842120524361875980687784179) (b := 0) (s := 2111532206162930266076090959577023743009680) h1056 (by decide +kernel)
  have h2281 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2281 = 2165256215082174053704342171481552244481375 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1140) (r := 1356618746901078470161921360220262864849315) (b := 1) (s := 2165256215082174053704342171481552244481375) h1140 (by decide +kernel)
  have h2417 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2417 = 1192498677530370335047794203099517599712113 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1208) (r := 2174327923378042115878714979419782514969049) (b := 1) (s := 1192498677530370335047794203099517599712113) h1208 (by decide +kernel)
  have h3498 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 3498 = 1292676632355170037201954079694576914613378 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1749) (r := 722124654913212471746165475225865879668798) (b := 0) (s := 1292676632355170037201954079694576914613378) h1749 (by decide +kernel)
  have h3763 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 3763 = 272507431792226617007957992797362191712080 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1881) (r := 823253187530668453093383928717085373607861) (b := 1) (s := 272507431792226617007957992797362191712080) h1881 (by decide +kernel)
  have h4224 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 4224 = 1135002353239396690863294562490486429262551 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2112) (r := 2111532206162930266076090959577023743009680) (b := 0) (s := 1135002353239396690863294562490486429262551) h2112 (by decide +kernel)
  have h4562 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 4562 = 1563663361482477379331583378625848722961538 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2281) (r := 2165256215082174053704342171481552244481375) (b := 0) (s := 1563663361482477379331583378625848722961538) h2281 (by decide +kernel)
  have h4835 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 4835 = 590469093940514577289107831637967054684986 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2417) (r := 1192498677530370335047794203099517599712113) (b := 1) (s := 590469093940514577289107831637967054684986) h2417 (by decide +kernel)
  have h6997 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 6997 = 320359124205816467488308192769521494187463 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 3498) (r := 1292676632355170037201954079694576914613378) (b := 1) (s := 320359124205816467488308192769521494187463) h3498 (by decide +kernel)
  have h7527 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 7527 = 1789236212662674851449959002167324623259770 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 3763) (r := 272507431792226617007957992797362191712080) (b := 1) (s := 1789236212662674851449959002167324623259770) h3763 (by decide +kernel)
  have h8449 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 8449 = 2187994654023098667032113610076828371626088 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4224) (r := 1135002353239396690863294562490486429262551) (b := 1) (s := 2187994654023098667032113610076828371626088) h4224 (by decide +kernel)
  have h9125 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 9125 = 112692770258293610424923876075340418486793 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4562) (r := 1563663361482477379331583378625848722961538) (b := 1) (s := 112692770258293610424923876075340418486793) h4562 (by decide +kernel)
  have h9670 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 9670 = 1108116811660653535692987389836519431675479 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4835) (r := 590469093940514577289107831637967054684986) (b := 0) (s := 1108116811660653535692987389836519431675479) h4835 (by decide +kernel)
  have h13994 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 13994 = 383274479380567577690778873365677364862702 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 6997) (r := 320359124205816467488308192769521494187463) (b := 0) (s := 383274479380567577690778873365677364862702) h6997 (by decide +kernel)
  have h15054 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 15054 = 1201656612877165874012409120987323683053840 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 7527) (r := 1789236212662674851449959002167324623259770) (b := 0) (s := 1201656612877165874012409120987323683053840) h7527 (by decide +kernel)
  have h16898 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 16898 = 917534801132656800873516412625060159295046 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 8449) (r := 2187994654023098667032113610076828371626088) (b := 0) (s := 917534801132656800873516412625060159295046) h8449 (by decide +kernel)
  have h18251 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 18251 = 377850118973397619386496444316049274942779 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 9125) (r := 112692770258293610424923876075340418486793) (b := 1) (s := 377850118973397619386496444316049274942779) h9125 (by decide +kernel)
  have h19341 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 19341 = 205576847162390648012709277247183093744742 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 9670) (r := 1108116811660653535692987389836519431675479) (b := 1) (s := 205576847162390648012709277247183093744742) h9670 (by decide +kernel)
  have h27988 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 27988 = 286195110626176500942129379707351217161156 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 13994) (r := 383274479380567577690778873365677364862702) (b := 0) (s := 286195110626176500942129379707351217161156) h13994 (by decide +kernel)
  have h30109 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 30109 = 1107934008032772591408676985524661651896598 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 15054) (r := 1201656612877165874012409120987323683053840) (b := 1) (s := 1107934008032772591408676985524661651896598) h15054 (by decide +kernel)
  have h33797 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 33797 = 2086346789391808192263473958910695826197634 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 16898) (r := 917534801132656800873516412625060159295046) (b := 1) (s := 2086346789391808192263473958910695826197634) h16898 (by decide +kernel)
  have h36503 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 36503 = 1077026550918455806881621350385293104370005 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 18251) (r := 377850118973397619386496444316049274942779) (b := 1) (s := 1077026550918455806881621350385293104370005) h18251 (by decide +kernel)
  have h38682 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 38682 = 1418415635807568254761202548059802054251157 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 19341) (r := 205576847162390648012709277247183093744742) (b := 0) (s := 1418415635807568254761202548059802054251157) h19341 (by decide +kernel)
  have h55977 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 55977 = 1463802687374406051966514516742542449144523 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 27988) (r := 286195110626176500942129379707351217161156) (b := 1) (s := 1463802687374406051966514516742542449144523) h27988 (by decide +kernel)
  have h60218 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 60218 = 1864694479828482021790288544920691862228302 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 30109) (r := 1107934008032772591408676985524661651896598) (b := 0) (s := 1864694479828482021790288544920691862228302) h30109 (by decide +kernel)
  have h67595 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 67595 = 672692486440637241429034857716356097037546 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 33797) (r := 2086346789391808192263473958910695826197634) (b := 1) (s := 672692486440637241429034857716356097037546) h33797 (by decide +kernel)
  have h73006 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 73006 = 556003877892546629518808906186393301030171 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 36503) (r := 1077026550918455806881621350385293104370005) (b := 0) (s := 556003877892546629518808906186393301030171) h36503 (by decide +kernel)
  have h77364 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 77364 = 711251665326101171339709117339709166423583 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 38682) (r := 1418415635807568254761202548059802054251157) (b := 0) (s := 711251665326101171339709117339709166423583) h38682 (by decide +kernel)
  have h111954 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 111954 = 597108281368506861010556344777898671730036 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 55977) (r := 1463802687374406051966514516742542449144523) (b := 0) (s := 597108281368506861010556344777898671730036) h55977 (by decide +kernel)
  have h120437 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 120437 = 1693420528184076253101228084296556204937724 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 60218) (r := 1864694479828482021790288544920691862228302) (b := 1) (s := 1693420528184076253101228084296556204937724) h60218 (by decide +kernel)
  have h135190 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 135190 = 363166733242325277710345776076550243771596 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 67595) (r := 672692486440637241429034857716356097037546) (b := 0) (s := 363166733242325277710345776076550243771596) h67595 (by decide +kernel)
  have h146012 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 146012 = 1867633250772249275638121722157081961882065 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 73006) (r := 556003877892546629518808906186393301030171) (b := 0) (s := 1867633250772249275638121722157081961882065) h73006 (by decide +kernel)
  have h154728 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 154728 = 1400531546214179093908765595811914131954554 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 77364) (r := 711251665326101171339709117339709166423583) (b := 0) (s := 1400531546214179093908765595811914131954554) h77364 (by decide +kernel)
  have h223909 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 223909 = 848887415777707047992739451594445506624714 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 111954) (r := 597108281368506861010556344777898671730036) (b := 1) (s := 848887415777707047992739451594445506624714) h111954 (by decide +kernel)
  have h240874 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 240874 = 25130223131020019256740556033421024059859 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 120437) (r := 1693420528184076253101228084296556204937724) (b := 0) (s := 25130223131020019256740556033421024059859) h120437 (by decide +kernel)
  have h270381 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 270381 = 925585354092740483044612634132315827079401 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 135190) (r := 363166733242325277710345776076550243771596) (b := 1) (s := 925585354092740483044612634132315827079401) h135190 (by decide +kernel)
  have h292025 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 292025 = 1736115410691373710964387768203099999354761 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 146012) (r := 1867633250772249275638121722157081961882065) (b := 1) (s := 1736115410691373710964387768203099999354761) h146012 (by decide +kernel)
  have h309457 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 309457 = 449876248589491294552057979883488486864544 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 154728) (r := 1400531546214179093908765595811914131954554) (b := 1) (s := 449876248589491294552057979883488486864544) h154728 (by decide +kernel)
  have h447819 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 447819 = 946177664448548128850554689604892355084702 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 223909) (r := 848887415777707047992739451594445506624714) (b := 1) (s := 946177664448548128850554689604892355084702) h223909 (by decide +kernel)
  have h481748 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 481748 = 1044192303122019506667590570123140028620727 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 240874) (r := 25130223131020019256740556033421024059859) (b := 0) (s := 1044192303122019506667590570123140028620727) h240874 (by decide +kernel)
  have h540763 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 540763 = 1839678416035630978030325041414470430861360 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 270381) (r := 925585354092740483044612634132315827079401) (b := 1) (s := 1839678416035630978030325041414470430861360) h270381 (by decide +kernel)
  have h584051 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 584051 = 863947939971006443381012146797401097899911 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 292025) (r := 1736115410691373710964387768203099999354761) (b := 1) (s := 863947939971006443381012146797401097899911) h292025 (by decide +kernel)
  have h618915 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 618915 = 1591792639875269868475488291615340685771734 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 309457) (r := 449876248589491294552057979883488486864544) (b := 1) (s := 1591792639875269868475488291615340685771734) h309457 (by decide +kernel)
  have h895639 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 895639 = 390310995742328604168918414531908726132130 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 447819) (r := 946177664448548128850554689604892355084702) (b := 1) (s := 390310995742328604168918414531908726132130) h447819 (by decide +kernel)
  have h963497 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 963497 = 730085083037802775542695375561871708220682 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 481748) (r := 1044192303122019506667590570123140028620727) (b := 1) (s := 730085083037802775542695375561871708220682) h481748 (by decide +kernel)
  have h1081527 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1081527 = 169213968320846971684527052904561617167495 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 540763) (r := 1839678416035630978030325041414470430861360) (b := 1) (s := 169213968320846971684527052904561617167495) h540763 (by decide +kernel)
  have h1168102 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1168102 = 1935480862248909557978430732580412845030055 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 584051) (r := 863947939971006443381012146797401097899911) (b := 0) (s := 1935480862248909557978430732580412845030055) h584051 (by decide +kernel)
  have h1237830 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1237830 = 1536187406177179002849414371206499411691821 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 618915) (r := 1591792639875269868475488291615340685771734) (b := 0) (s := 1536187406177179002849414371206499411691821) h618915 (by decide +kernel)
  have h1791279 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1791279 = 291382485890844891368602128488467811836637 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 895639) (r := 390310995742328604168918414531908726132130) (b := 1) (s := 291382485890844891368602128488467811836637) h895639 (by decide +kernel)
  have h1926994 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1926994 = 836118360086905915213851233619153671544936 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 963497) (r := 730085083037802775542695375561871708220682) (b := 0) (s := 836118360086905915213851233619153671544936) h963497 (by decide +kernel)
  have h2163054 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2163054 = 889990635942804529062004618499348214585051 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1081527) (r := 169213968320846971684527052904561617167495) (b := 0) (s := 889990635942804529062004618499348214585051) h1081527 (by decide +kernel)
  have h2336204 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2336204 = 39266034451284936986863033647786335629566 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1168102) (r := 1935480862248909557978430732580412845030055) (b := 0) (s := 39266034451284936986863033647786335629566) h1168102 (by decide +kernel)
  have h2475661 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2475661 = 615959492662882554285841848888394202869386 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1237830) (r := 1536187406177179002849414371206499411691821) (b := 1) (s := 615959492662882554285841848888394202869386) h1237830 (by decide +kernel)
  have h3582559 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 3582559 = 176002230601842432225560349339990959725755 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1791279) (r := 291382485890844891368602128488467811836637) (b := 1) (s := 176002230601842432225560349339990959725755) h1791279 (by decide +kernel)
  have h3853989 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 3853989 = 1128757524612328691594827041556661272182072 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1926994) (r := 836118360086905915213851233619153671544936) (b := 1) (s := 1128757524612328691594827041556661272182072) h1926994 (by decide +kernel)
  have h4326109 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 4326109 = 2127336780073172745451489868679302351236569 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2163054) (r := 889990635942804529062004618499348214585051) (b := 1) (s := 2127336780073172745451489868679302351236569) h2163054 (by decide +kernel)
  have h4672408 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 4672408 = 188569580443995005525370523977048300175364 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2336204) (r := 39266034451284936986863033647786335629566) (b := 0) (s := 188569580443995005525370523977048300175364) h2336204 (by decide +kernel)
  have h4951322 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 4951322 = 331339580926633005784267298537124071056191 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2475661) (r := 615959492662882554285841848888394202869386) (b := 0) (s := 331339580926633005784267298537124071056191) h2475661 (by decide +kernel)
  have h7165118 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 7165118 = 437583507252247880540071467390834783105668 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 3582559) (r := 176002230601842432225560349339990959725755) (b := 0) (s := 437583507252247880540071467390834783105668) h3582559 (by decide +kernel)
  have h7707979 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 7707979 = 1296789597779209730325378919919548168327540 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 3853989) (r := 1128757524612328691594827041556661272182072) (b := 1) (s := 1296789597779209730325378919919548168327540) h3853989 (by decide +kernel)
  have h8652218 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 8652218 = 892945911421535534392540502680505502339912 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4326109) (r := 2127336780073172745451489868679302351236569) (b := 0) (s := 892945911421535534392540502680505502339912) h4326109 (by decide +kernel)
  have h9344816 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 9344816 = 717234194563442991488576570957400960029535 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4672408) (r := 188569580443995005525370523977048300175364) (b := 0) (s := 717234194563442991488576570957400960029535) h4672408 (by decide +kernel)
  have h9902645 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 9902645 = 135915904781721127013527877978549096761732 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4951322) (r := 331339580926633005784267298537124071056191) (b := 1) (s := 135915904781721127013527877978549096761732) h4951322 (by decide +kernel)
  have h14330236 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 14330236 = 2223836991569562446627074098333555547404185 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 7165118) (r := 437583507252247880540071467390834783105668) (b := 0) (s := 2223836991569562446627074098333555547404185) h7165118 (by decide +kernel)
  have h15415958 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 15415958 = 1440749948358245240444950322120218225368006 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 7707979) (r := 1296789597779209730325378919919548168327540) (b := 0) (s := 1440749948358245240444950322120218225368006) h7707979 (by decide +kernel)
  have h17304436 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 17304436 = 142461532040824680450815994651923313571095 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 8652218) (r := 892945911421535534392540502680505502339912) (b := 0) (s := 142461532040824680450815994651923313571095) h8652218 (by decide +kernel)
  have h18689632 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 18689632 = 666749852112653365417621949425178056367244 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 9344816) (r := 717234194563442991488576570957400960029535) (b := 0) (s := 666749852112653365417621949425178056367244) h9344816 (by decide +kernel)
  have h19805290 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 19805290 = 2017717392364327358703624298418177509895295 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 9902645) (r := 135915904781721127013527877978549096761732) (b := 0) (s := 2017717392364327358703624298418177509895295) h9902645 (by decide +kernel)
  have h28660473 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 28660473 = 230159836300318822754868936858914382635866 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 14330236) (r := 2223836991569562446627074098333555547404185) (b := 1) (s := 230159836300318822754868936858914382635866) h14330236 (by decide +kernel)
  have h30831917 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 30831917 = 399911076611843569188986378600756140572879 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 15415958) (r := 1440749948358245240444950322120218225368006) (b := 1) (s := 399911076611843569188986378600756140572879) h15415958 (by decide +kernel)
  have h34608873 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 34608873 = 1359018708021483111811587376312987177415150 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 17304436) (r := 142461532040824680450815994651923313571095) (b := 1) (s := 1359018708021483111811587376312987177415150) h17304436 (by decide +kernel)
  have h37379264 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 37379264 = 2280737501505601821022911562059189234406801 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 18689632) (r := 666749852112653365417621949425178056367244) (b := 0) (s := 2280737501505601821022911562059189234406801) h18689632 (by decide +kernel)
  have h39610580 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 39610580 = 1626912988200562348714884083501182151452978 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 19805290) (r := 2017717392364327358703624298418177509895295) (b := 0) (s := 1626912988200562348714884083501182151452978) h19805290 (by decide +kernel)
  have h57320946 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 57320946 = 935449946689761674718688754357324442838499 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 28660473) (r := 230159836300318822754868936858914382635866) (b := 0) (s := 935449946689761674718688754357324442838499) h28660473 (by decide +kernel)
  have h61663834 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 61663834 = 1459099836673540604506442687867116552305122 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 30831917) (r := 399911076611843569188986378600756140572879) (b := 0) (s := 1459099836673540604506442687867116552305122) h30831917 (by decide +kernel)
  have h69217746 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 69217746 = 1914744274999528178150969178213795897594956 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 34608873) (r := 1359018708021483111811587376312987177415150) (b := 0) (s := 1914744274999528178150969178213795897594956) h34608873 (by decide +kernel)
  have h74758529 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 74758529 = 757945136593906097595520696494327747874978 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 37379264) (r := 2280737501505601821022911562059189234406801) (b := 1) (s := 757945136593906097595520696494327747874978) h37379264 (by decide +kernel)
  have h79221161 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 79221161 = 788064026356213567820043062821232334162231 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 39610580) (r := 1626912988200562348714884083501182151452978) (b := 1) (s := 788064026356213567820043062821232334162231) h39610580 (by decide +kernel)
  have h114641892 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 114641892 = 75227945038609851196970244469130059264344 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 57320946) (r := 935449946689761674718688754357324442838499) (b := 0) (s := 75227945038609851196970244469130059264344) h57320946 (by decide +kernel)
  have h123327668 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 123327668 = 244440577198126510678486589954324865844417 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 61663834) (r := 1459099836673540604506442687867116552305122) (b := 0) (s := 244440577198126510678486589954324865844417) h61663834 (by decide +kernel)
  have h138435493 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 138435493 = 1455662347207170250403977931330528165362490 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 69217746) (r := 1914744274999528178150969178213795897594956) (b := 1) (s := 1455662347207170250403977931330528165362490) h69217746 (by decide +kernel)
  have h149517059 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 149517059 = 2180483246061739373709559695406272924440889 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 74758529) (r := 757945136593906097595520696494327747874978) (b := 1) (s := 2180483246061739373709559695406272924440889) h74758529 (by decide +kernel)
  have h158442322 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 158442322 = 1607287898529618680512013583931280491926206 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 79221161) (r := 788064026356213567820043062821232334162231) (b := 0) (s := 1607287898529618680512013583931280491926206) h79221161 (by decide +kernel)
  have h229283785 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 229283785 = 144289388006528558551000421988349002898883 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 114641892) (r := 75227945038609851196970244469130059264344) (b := 1) (s := 144289388006528558551000421988349002898883) h114641892 (by decide +kernel)
  have h246655336 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 246655336 = 1228560100521681583219031741463304977815569 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 123327668) (r := 244440577198126510678486589954324865844417) (b := 0) (s := 1228560100521681583219031741463304977815569) h123327668 (by decide +kernel)
  have h276870986 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 276870986 = 642302446434258879161551273843411626235623 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 138435493) (r := 1455662347207170250403977931330528165362490) (b := 0) (s := 642302446434258879161551273843411626235623) h138435493 (by decide +kernel)
  have h299034119 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 299034119 = 332825156256125350109557616078753017093709 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 149517059) (r := 2180483246061739373709559695406272924440889) (b := 1) (s := 332825156256125350109557616078753017093709) h149517059 (by decide +kernel)
  have h316884645 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 316884645 = 1370579512189514168452524955025525267618258 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 158442322) (r := 1607287898529618680512013583931280491926206) (b := 1) (s := 1370579512189514168452524955025525267618258) h158442322 (by decide +kernel)
  have h458567571 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 458567571 = 581808372840011518035197174558071453787130 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 229283785) (r := 144289388006528558551000421988349002898883) (b := 1) (s := 581808372840011518035197174558071453787130) h229283785 (by decide +kernel)
  have h493310673 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 493310673 = 869172893801336358020921226341705046586703 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 246655336) (r := 1228560100521681583219031741463304977815569) (b := 1) (s := 869172893801336358020921226341705046586703) h246655336 (by decide +kernel)
  have h553741972 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 553741972 = 1558359977198443528234109333105494101695609 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 276870986) (r := 642302446434258879161551273843411626235623) (b := 0) (s := 1558359977198443528234109333105494101695609) h276870986 (by decide +kernel)
  have h598068239 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 598068239 = 1624379552635792572001896235827333964944881 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 299034119) (r := 332825156256125350109557616078753017093709) (b := 1) (s := 1624379552635792572001896235827333964944881) h299034119 (by decide +kernel)
  have h633769291 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 633769291 = 1462581001978234471472862365415573746451949 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 316884645) (r := 1370579512189514168452524955025525267618258) (b := 1) (s := 1462581001978234471472862365415573746451949) h316884645 (by decide +kernel)
  have h917135142 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 917135142 = 223785658922593819925763932206963839245322 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 458567571) (r := 581808372840011518035197174558071453787130) (b := 0) (s := 223785658922593819925763932206963839245322) h458567571 (by decide +kernel)
  have h986621347 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 986621347 = 1454455568563969533288273980503737987626037 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 493310673) (r := 869172893801336358020921226341705046586703) (b := 1) (s := 1454455568563969533288273980503737987626037) h493310673 (by decide +kernel)
  have h1107483945 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1107483945 = 1095969341199599098008595496125990189795572 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 553741972) (r := 1558359977198443528234109333105494101695609) (b := 1) (s := 1095969341199599098008595496125990189795572) h553741972 (by decide +kernel)
  have h1196136478 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1196136478 = 1578241513998584335461970332162319772523303 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 598068239) (r := 1624379552635792572001896235827333964944881) (b := 0) (s := 1578241513998584335461970332162319772523303) h598068239 (by decide +kernel)
  have h1267538582 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1267538582 = 1164622906012680891465682818334772756234238 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 633769291) (r := 1462581001978234471472862365415573746451949) (b := 0) (s := 1164622906012680891465682818334772756234238) h633769291 (by decide +kernel)
  have h1834270284 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1834270284 = 1977936220549757913378768553064495241905591 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 917135142) (r := 223785658922593819925763932206963839245322) (b := 0) (s := 1977936220549757913378768553064495241905591) h917135142 (by decide +kernel)
  have h1973242695 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1973242695 = 1755953040918551585124131918874171327718466 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 986621347) (r := 1454455568563969533288273980503737987626037) (b := 1) (s := 1755953040918551585124131918874171327718466) h986621347 (by decide +kernel)
  have h2214967891 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2214967891 = 1614240726301716305507600988855558134140912 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1107483945) (r := 1095969341199599098008595496125990189795572) (b := 1) (s := 1614240726301716305507600988855558134140912) h1107483945 (by decide +kernel)
  have h2392272957 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2392272957 = 576674234870571333954457428702148004855907 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1196136478) (r := 1578241513998584335461970332162319772523303) (b := 1) (s := 576674234870571333954457428702148004855907) h1196136478 (by decide +kernel)
  have h2535077164 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2535077164 = 2328232192845451381318372980654888423686868 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1267538582) (r := 1164622906012680891465682818334772756234238) (b := 0) (s := 2328232192845451381318372980654888423686868) h1267538582 (by decide +kernel)
  have h3668540569 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 3668540569 = 1406499074650607680995405927379466431576364 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1834270284) (r := 1977936220549757913378768553064495241905591) (b := 1) (s := 1406499074650607680995405927379466431576364) h1834270284 (by decide +kernel)
  have h3946485391 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 3946485391 = 1259621485041365375233076538494981160478385 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1973242695) (r := 1755953040918551585124131918874171327718466) (b := 1) (s := 1259621485041365375233076538494981160478385) h1973242695 (by decide +kernel)
  have h4429935782 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 4429935782 = 373950800740203402891748932351673299014173 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2214967891) (r := 1614240726301716305507600988855558134140912) (b := 0) (s := 373950800740203402891748932351673299014173) h2214967891 (by decide +kernel)
  have h4784545915 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 4784545915 = 1313044514529083237907213065499116138104410 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2392272957) (r := 576674234870571333954457428702148004855907) (b := 1) (s := 1313044514529083237907213065499116138104410) h2392272957 (by decide +kernel)
  have h5070154328 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 5070154328 = 1804614881202391627178160662032322228742580 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2535077164) (r := 2328232192845451381318372980654888423686868) (b := 0) (s := 1804614881202391627178160662032322228742580) h2535077164 (by decide +kernel)
  have h7337081139 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 7337081139 = 2071628293864772374658718442905156693395263 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 3668540569) (r := 1406499074650607680995405927379466431576364) (b := 1) (s := 2071628293864772374658718442905156693395263) h3668540569 (by decide +kernel)
  have h7892970782 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 7892970782 = 78693159523552107459946217835727025611848 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 3946485391) (r := 1259621485041365375233076538494981160478385) (b := 0) (s := 78693159523552107459946217835727025611848) h3946485391 (by decide +kernel)
  have h8859871565 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 8859871565 = 2275737190664233926601652752215951202052274 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4429935782) (r := 373950800740203402891748932351673299014173) (b := 1) (s := 2275737190664233926601652752215951202052274) h4429935782 (by decide +kernel)
  have h9569091831 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 9569091831 = 1758914826966794534508096234693414437557662 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4784545915) (r := 1313044514529083237907213065499116138104410) (b := 1) (s := 1758914826966794534508096234693414437557662) h4784545915 (by decide +kernel)
  have h10140308656 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 10140308656 = 708723919013258616839551147424746178692287 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 5070154328) (r := 1804614881202391627178160662032322228742580) (b := 0) (s := 708723919013258616839551147424746178692287) h5070154328 (by decide +kernel)
  have h14674162279 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 14674162279 = 2115773023414306587840675274644320264317311 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 7337081139) (r := 2071628293864772374658718442905156693395263) (b := 1) (s := 2115773023414306587840675274644320264317311) h7337081139 (by decide +kernel)
  have h15785941564 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 15785941564 = 1074637379244161097164473452449671410016483 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 7892970782) (r := 78693159523552107459946217835727025611848) (b := 0) (s := 1074637379244161097164473452449671410016483) h7892970782 (by decide +kernel)
  have h17719743130 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 17719743130 = 722190762288441042080139152643627651962959 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 8859871565) (r := 2275737190664233926601652752215951202052274) (b := 0) (s := 722190762288441042080139152643627651962959) h8859871565 (by decide +kernel)
  have h19138183662 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 19138183662 = 2078821227134615384971617840510039675841552 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 9569091831) (r := 1758914826966794534508096234693414437557662) (b := 0) (s := 2078821227134615384971617840510039675841552) h9569091831 (by decide +kernel)
  have h20280617312 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 20280617312 = 40504702224354578012506497375244896404105 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 10140308656) (r := 708723919013258616839551147424746178692287) (b := 0) (s := 40504702224354578012506497375244896404105) h10140308656 (by decide +kernel)
  have h29348324559 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 29348324559 = 1921863412266789056117058774543568015736839 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 14674162279) (r := 2115773023414306587840675274644320264317311) (b := 1) (s := 1921863412266789056117058774543568015736839) h14674162279 (by decide +kernel)
  have h31571883128 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 31571883128 = 82685589318035675886048686744299389590263 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 15785941564) (r := 1074637379244161097164473452449671410016483) (b := 0) (s := 82685589318035675886048686744299389590263) h15785941564 (by decide +kernel)
  have h35439486260 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 35439486260 = 95244811230226344574110805034716712726425 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 17719743130) (r := 722190762288441042080139152643627651962959) (b := 0) (s := 95244811230226344574110805034716712726425) h17719743130 (by decide +kernel)
  have h38276367324 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 38276367324 = 694721599081409210263774694578894447816845 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 19138183662) (r := 2078821227134615384971617840510039675841552) (b := 0) (s := 694721599081409210263774694578894447816845) h19138183662 (by decide +kernel)
  have h40561234625 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 40561234625 = 417543953967966016296783301908933092411389 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 20280617312) (r := 40504702224354578012506497375244896404105) (b := 1) (s := 417543953967966016296783301908933092411389) h20280617312 (by decide +kernel)
  have h58696649119 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 58696649119 = 2193417071985706642971839040050129722329962 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 29348324559) (r := 1921863412266789056117058774543568015736839) (b := 1) (s := 2193417071985706642971839040050129722329962) h29348324559 (by decide +kernel)
  have h63143766256 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 63143766256 = 1385809818733916420446157461766467046428051 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 31571883128) (r := 82685589318035675886048686744299389590263) (b := 0) (s := 1385809818733916420446157461766467046428051) h31571883128 (by decide +kernel)
  have h70878972521 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 70878972521 = 820670934111994784773564959560874184343758 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 35439486260) (r := 95244811230226344574110805034716712726425) (b := 1) (s := 820670934111994784773564959560874184343758) h35439486260 (by decide +kernel)
  have h76552734648 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 76552734648 = 1828346604967382185916657066746135226588332 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 38276367324) (r := 694721599081409210263774694578894447816845) (b := 0) (s := 1828346604967382185916657066746135226588332) h38276367324 (by decide +kernel)
  have h81122469251 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 81122469251 = 1619699076841468225874693942498368672280115 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 40561234625) (r := 417543953967966016296783301908933092411389) (b := 1) (s := 1619699076841468225874693942498368672280115) h40561234625 (by decide +kernel)
  have h117393298238 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 117393298238 = 139710386509875899422143260430626826801394 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 58696649119) (r := 2193417071985706642971839040050129722329962) (b := 0) (s := 139710386509875899422143260430626826801394) h58696649119 (by decide +kernel)
  have h126287532513 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 126287532513 = 1372829077936951946354182196028065035830162 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 63143766256) (r := 1385809818733916420446157461766467046428051) (b := 1) (s := 1372829077936951946354182196028065035830162) h63143766256 (by decide +kernel)
  have h141757945042 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 141757945042 = 256405522641067795214959036222592297778086 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 70878972521) (r := 820670934111994784773564959560874184343758) (b := 0) (s := 256405522641067795214959036222592297778086) h70878972521 (by decide +kernel)
  have h153105469296 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 153105469296 = 2257635102777967877495633443711466060681548 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 76552734648) (r := 1828346604967382185916657066746135226588332) (b := 0) (s := 2257635102777967877495633443711466060681548) h76552734648 (by decide +kernel)
  have h162244938502 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 162244938502 = 365477733104453863154797923271534650447255 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 81122469251) (r := 1619699076841468225874693942498368672280115) (b := 0) (s := 365477733104453863154797923271534650447255) h81122469251 (by decide +kernel)
  have h234786596476 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 234786596476 = 618330037336121960729011755598058970393397 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 117393298238) (r := 139710386509875899422143260430626826801394) (b := 0) (s := 618330037336121960729011755598058970393397) h117393298238 (by decide +kernel)
  have h252575065027 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 252575065027 = 623322494123446201948101173075048445070906 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 126287532513) (r := 1372829077936951946354182196028065035830162) (b := 1) (s := 623322494123446201948101173075048445070906) h126287532513 (by decide +kernel)
  have h283515890084 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 283515890084 = 1670644489164840660597364621311827109360889 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 141757945042) (r := 256405522641067795214959036222592297778086) (b := 0) (s := 1670644489164840660597364621311827109360889) h141757945042 (by decide +kernel)
  have h306210938592 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 306210938592 = 2054540133061043575376189503996754435561939 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 153105469296) (r := 2257635102777967877495633443711466060681548) (b := 0) (s := 2054540133061043575376189503996754435561939) h153105469296 (by decide +kernel)
  have h324489877004 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 324489877004 = 627835438721418289850228410070314523445416 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 162244938502) (r := 365477733104453863154797923271534650447255) (b := 0) (s := 627835438721418289850228410070314523445416) h162244938502 (by decide +kernel)
  have h469573192953 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 469573192953 = 1587126362720700512597999789822290319154119 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 234786596476) (r := 618330037336121960729011755598058970393397) (b := 1) (s := 1587126362720700512597999789822290319154119) h234786596476 (by decide +kernel)
  have h505150130055 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 505150130055 = 1580668106083738861355317062653353768571379 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 252575065027) (r := 623322494123446201948101173075048445070906) (b := 1) (s := 1580668106083738861355317062653353768571379) h252575065027 (by decide +kernel)
  have h567031780169 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 567031780169 = 528516300378148902708819924267667301875100 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 283515890084) (r := 1670644489164840660597364621311827109360889) (b := 1) (s := 528516300378148902708819924267667301875100) h283515890084 (by decide +kernel)
  have h612421877184 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 612421877184 = 2259309518864508728021883754154697634139499 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 306210938592) (r := 2054540133061043575376189503996754435561939) (b := 0) (s := 2259309518864508728021883754154697634139499) h306210938592 (by decide +kernel)
  have h648979754008 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 648979754008 = 1831906183129812014669897611050157877437958 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 324489877004) (r := 627835438721418289850228410070314523445416) (b := 0) (s := 1831906183129812014669897611050157877437958) h324489877004 (by decide +kernel)
  have h939146385906 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 939146385906 = 222011355868986648492332085326887016725287 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 469573192953) (r := 1587126362720700512597999789822290319154119) (b := 0) (s := 222011355868986648492332085326887016725287) h469573192953 (by decide +kernel)
  have h1010300260110 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1010300260110 = 1735064601253285428354325500830571829960811 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 505150130055) (r := 1580668106083738861355317062653353768571379) (b := 0) (s := 1735064601253285428354325500830571829960811) h505150130055 (by decide +kernel)
  have h1134063560339 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1134063560339 = 1752894708930856349172039825453850349150123 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 567031780169) (r := 528516300378148902708819924267667301875100) (b := 1) (s := 1752894708930856349172039825453850349150123) h567031780169 (by decide +kernel)
  have h1224843754369 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1224843754369 = 2060997446293500310883754524331196740015753 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 612421877184) (r := 2259309518864508728021883754154697634139499) (b := 1) (s := 2060997446293500310883754524331196740015753) h612421877184 (by decide +kernel)
  have h1297959508016 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1297959508016 = 1688166650361799412941794329699841641695160 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 648979754008) (r := 1831906183129812014669897611050157877437958) (b := 0) (s := 1688166650361799412941794329699841641695160) h648979754008 (by decide +kernel)
  have h1878292771812 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1878292771812 = 755175212136897291413589007376628706733581 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 939146385906) (r := 222011355868986648492332085326887016725287) (b := 0) (s := 755175212136897291413589007376628706733581) h939146385906 (by decide +kernel)
  have h2020600520221 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2020600520221 = 356224363477614271413443760601563389261401 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1010300260110) (r := 1735064601253285428354325500830571829960811) (b := 1) (s := 356224363477614271413443760601563389261401) h1010300260110 (by decide +kernel)
  have h2268127120679 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2268127120679 = 2010940893875371439752804886323601547398270 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1134063560339) (r := 1752894708930856349172039825453850349150123) (b := 1) (s := 2010940893875371439752804886323601547398270) h1134063560339 (by decide +kernel)
  have h2449687508739 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2449687508739 = 2335125211408031737215647302094759279522989 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1224843754369) (r := 2060997446293500310883754524331196740015753) (b := 1) (s := 2335125211408031737215647302094759279522989) h1224843754369 (by decide +kernel)
  have h2595919016032 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2595919016032 = 10714304793467576437200036742142581180726 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1297959508016) (r := 1688166650361799412941794329699841641695160) (b := 0) (s := 10714304793467576437200036742142581180726) h1297959508016 (by decide +kernel)
  have h3756585543625 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 3756585543625 = 126256356333633965859165843690090926966811 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1878292771812) (r := 755175212136897291413589007376628706733581) (b := 1) (s := 126256356333633965859165843690090926966811) h1878292771812 (by decide +kernel)
  have h4041201040442 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 4041201040442 = 1130220077772130503064309352628366055927908 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2020600520221) (r := 356224363477614271413443760601563389261401) (b := 0) (s := 1130220077772130503064309352628366055927908) h2020600520221 (by decide +kernel)
  have h4536254241359 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 4536254241359 = 1999487657945307594724048139972238227710173 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2268127120679) (r := 2010940893875371439752804886323601547398270) (b := 1) (s := 1999487657945307594724048139972238227710173) h2268127120679 (by decide +kernel)
  have h4899375017479 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 4899375017479 = 1061507449216528763360972187102432321990669 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2449687508739) (r := 2335125211408031737215647302094759279522989) (b := 1) (s := 1061507449216528763360972187102432321990669) h2449687508739 (by decide +kernel)
  have h5191838032064 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 5191838032064 = 2171260308230633625285012102415197662671136 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2595919016032) (r := 10714304793467576437200036742142581180726) (b := 0) (s := 2171260308230633625285012102415197662671136) h2595919016032 (by decide +kernel)
  have h7513171087251 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 7513171087251 = 937324124211535792723832589936149920429938 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 3756585543625) (r := 126256356333633965859165843690090926966811) (b := 1) (s := 937324124211535792723832589936149920429938) h3756585543625 (by decide +kernel)
  have h8082402080885 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 8082402080885 = 1761253440523477956102103211301561182703327 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4041201040442) (r := 1130220077772130503064309352628366055927908) (b := 1) (s := 1761253440523477956102103211301561182703327) h4041201040442 (by decide +kernel)
  have h9072508482718 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 9072508482718 = 812868129717817120772926707660765628771316 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4536254241359) (r := 1999487657945307594724048139972238227710173) (b := 0) (s := 812868129717817120772926707660765628771316) h4536254241359 (by decide +kernel)
  have h9798750034958 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 9798750034958 = 836484367727311296930164238489556777458758 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4899375017479) (r := 1061507449216528763360972187102432321990669) (b := 0) (s := 836484367727311296930164238489556777458758) h4899375017479 (by decide +kernel)
  have h10383676064128 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 10383676064128 = 71024636366801440438706866992915199294459 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 5191838032064) (r := 2171260308230633625285012102415197662671136) (b := 0) (s := 71024636366801440438706866992915199294459) h5191838032064 (by decide +kernel)
  have h15026342174502 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 15026342174502 = 2290719009697937593381927383247325509963124 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 7513171087251) (r := 937324124211535792723832589936149920429938) (b := 0) (s := 2290719009697937593381927383247325509963124) h7513171087251 (by decide +kernel)
  have h16164804161771 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 16164804161771 = 1050242576882577909582061659636059162755232 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 8082402080885) (r := 1761253440523477956102103211301561182703327) (b := 1) (s := 1050242576882577909582061659636059162755232) h8082402080885 (by decide +kernel)
  have h18145016965436 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 18145016965436 = 2010879231413318410775071304565371811612725 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 9072508482718) (r := 812868129717817120772926707660765628771316) (b := 0) (s := 2010879231413318410775071304565371811612725) h9072508482718 (by decide +kernel)
  have h19597500069916 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 19597500069916 = 821582230658247216189415093223283633294774 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 9798750034958) (r := 836484367727311296930164238489556777458758) (b := 0) (s := 821582230658247216189415093223283633294774) h9798750034958 (by decide +kernel)
  have h20767352128256 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 20767352128256 = 593111975845135207869901293095937248109665 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 10383676064128) (r := 71024636366801440438706866992915199294459) (b := 0) (s := 593111975845135207869901293095937248109665) h10383676064128 (by decide +kernel)
  have h30052684349004 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 30052684349004 = 2095345204599689920554358441363189295099412 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 15026342174502) (r := 2290719009697937593381927383247325509963124) (b := 0) (s := 2095345204599689920554358441363189295099412) h15026342174502 (by decide +kernel)
  have h32329608323542 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 32329608323542 = 2151009197173015642031557627519153205273681 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 16164804161771) (r := 1050242576882577909582061659636059162755232) (b := 0) (s := 2151009197173015642031557627519153205273681) h16164804161771 (by decide +kernel)
  have h36290033930873 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 36290033930873 = 563338913056432870655834470854934447590058 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 18145016965436) (r := 2010879231413318410775071304565371811612725) (b := 1) (s := 563338913056432870655834470854934447590058) h18145016965436 (by decide +kernel)
  have h39195000139833 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 39195000139833 = 775898584896371736317740350417377918347894 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 19597500069916) (r := 821582230658247216189415093223283633294774) (b := 1) (s := 775898584896371736317740350417377918347894) h19597500069916 (by decide +kernel)
  have h41534704256512 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 41534704256512 = 414556716512298898043514842085073283205661 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 20767352128256) (r := 593111975845135207869901293095937248109665) (b := 0) (s := 414556716512298898043514842085073283205661) h20767352128256 (by decide +kernel)
  have h60105368698009 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 60105368698009 = 1660565045037845329341115990783750837775250 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 30052684349004) (r := 2095345204599689920554358441363189295099412) (b := 1) (s := 1660565045037845329341115990783750837775250) h30052684349004 (by decide +kernel)
  have h64659216647084 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 64659216647084 = 1697800573246334442024037760754083641572763 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 32329608323542) (r := 2151009197173015642031557627519153205273681) (b := 0) (s := 1697800573246334442024037760754083641572763) h32329608323542 (by decide +kernel)
  have h72580067861746 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 72580067861746 = 1059918350020612621697602493560708122460460 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 36290033930873) (r := 563338913056432870655834470854934447590058) (b := 0) (s := 1059918350020612621697602493560708122460460) h36290033930873 (by decide +kernel)
  have h78390000279666 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 78390000279666 = 1697509377127471464950218785998050025413321 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 39195000139833) (r := 775898584896371736317740350417377918347894) (b := 0) (s := 1697509377127471464950218785998050025413321) h39195000139833 (by decide +kernel)
  have h83069408513025 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 83069408513025 = 1345125647988796485951363560474010650118110 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 41534704256512) (r := 414556716512298898043514842085073283205661) (b := 1) (s := 1345125647988796485951363560474010650118110) h41534704256512 (by decide +kernel)
  have h120210737396018 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 120210737396018 = 1598456954219126642721495363255336734536065 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 60105368698009) (r := 1660565045037845329341115990783750837775250) (b := 0) (s := 1598456954219126642721495363255336734536065) h60105368698009 (by decide +kernel)
  have h129318433294168 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 129318433294168 = 236922812695784453923358765924075045274469 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 64659216647084) (r := 1697800573246334442024037760754083641572763) (b := 0) (s := 236922812695784453923358765924075045274469) h64659216647084 (by decide +kernel)
  have h145160135723493 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 145160135723493 = 1828936536921738807713690637925736183601984 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 72580067861746) (r := 1059918350020612621697602493560708122460460) (b := 1) (s := 1828936536921738807713690637925736183601984) h72580067861746 (by decide +kernel)
  have h156780000559332 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 156780000559332 = 428466986190666818868726708605332062379253 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 78390000279666) (r := 1697509377127471464950218785998050025413321) (b := 0) (s := 428466986190666818868726708605332062379253) h78390000279666 (by decide +kernel)
  have h166138817026050 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 166138817026050 = 1111879819735650732480260042345701134646715 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 83069408513025) (r := 1345125647988796485951363560474010650118110) (b := 0) (s := 1111879819735650732480260042345701134646715) h83069408513025 (by decide +kernel)
  have h240421474792036 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 240421474792036 = 1199257209019566449027173715782703975862231 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 120210737396018) (r := 1598456954219126642721495363255336734536065) (b := 0) (s := 1199257209019566449027173715782703975862231) h120210737396018 (by decide +kernel)
  have h258636866588337 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 258636866588337 = 1130284628931299583098714879575862033777770 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 129318433294168) (r := 236922812695784453923358765924075045274469) (b := 1) (s := 1130284628931299583098714879575862033777770) h129318433294168 (by decide +kernel)
  have h290320271446987 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 290320271446987 = 506316957811542410967779768385211965212892 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 145160135723493) (r := 1828936536921738807713690637925736183601984) (b := 1) (s := 506316957811542410967779768385211965212892) h145160135723493 (by decide +kernel)
  have h313560001118665 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 313560001118665 = 1897331011786145510784994059309471948727590 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 156780000559332) (r := 428466986190666818868726708605332062379253) (b := 1) (s := 1897331011786145510784994059309471948727590) h156780000559332 (by decide +kernel)
  have h332277634052101 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 332277634052101 = 2365964916390770704300731221675451092752886 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 166138817026050) (r := 1111879819735650732480260042345701134646715) (b := 1) (s := 2365964916390770704300731221675451092752886) h166138817026050 (by decide +kernel)
  have h480842949584073 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 480842949584073 = 1395351145516658498755695391231773615597 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 240421474792036) (r := 1199257209019566449027173715782703975862231) (b := 1) (s := 1395351145516658498755695391231773615597) h240421474792036 (by decide +kernel)
  have h517273733176675 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 517273733176675 = 1830620751573469892352340630338504812993559 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 258636866588337) (r := 1130284628931299583098714879575862033777770) (b := 1) (s := 1830620751573469892352340630338504812993559) h258636866588337 (by decide +kernel)
  have h580640542893975 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 580640542893975 = 1097418839816442906830446606375065651398872 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 290320271446987) (r := 506316957811542410967779768385211965212892) (b := 1) (s := 1097418839816442906830446606375065651398872) h290320271446987 (by decide +kernel)
  have h627120002237331 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 627120002237331 = 1746124019349484660612568759246433028589257 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 313560001118665) (r := 1897331011786145510784994059309471948727590) (b := 1) (s := 1746124019349484660612568759246433028589257) h313560001118665 (by decide +kernel)
  have h664555268104203 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 664555268104203 = 1962946351194057652915714418567206366865832 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 332277634052101) (r := 2365964916390770704300731221675451092752886) (b := 1) (s := 1962946351194057652915714418567206366865832) h332277634052101 (by decide +kernel)
  have h961685899168146 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 961685899168146 = 351796795090569670478919543487646490471412 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 480842949584073) (r := 1395351145516658498755695391231773615597) (b := 0) (s := 351796795090569670478919543487646490471412) h480842949584073 (by decide +kernel)
  have h1034547466353350 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1034547466353350 = 2113124100966790864808436269071295396310529 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 517273733176675) (r := 1830620751573469892352340630338504812993559) (b := 0) (s := 2113124100966790864808436269071295396310529) h517273733176675 (by decide +kernel)
  have h1161281085787950 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1161281085787950 = 152937765781624779344611439985245081181482 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 580640542893975) (r := 1097418839816442906830446606375065651398872) (b := 0) (s := 152937765781624779344611439985245081181482) h580640542893975 (by decide +kernel)
  have h1254240004474663 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1254240004474663 = 1630477125842007184799384331362934906684709 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 627120002237331) (r := 1746124019349484660612568759246433028589257) (b := 1) (s := 1630477125842007184799384331362934906684709) h627120002237331 (by decide +kernel)
  have h1329110536208406 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1329110536208406 = 1200722312746834540901191083203599585145859 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 664555268104203) (r := 1962946351194057652915714418567206366865832) (b := 0) (s := 1200722312746834540901191083203599585145859) h664555268104203 (by decide +kernel)
  have h1923371798336293 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1923371798336293 = 1701606793674112229885612304259323884064889 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 961685899168146) (r := 351796795090569670478919543487646490471412) (b := 1) (s := 1701606793674112229885612304259323884064889) h961685899168146 (by decide +kernel)
  have h2069094932706701 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2069094932706701 = 1779630072499156423476941895989031635519572 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1034547466353350) (r := 2113124100966790864808436269071295396310529) (b := 1) (s := 1779630072499156423476941895989031635519572) h1034547466353350 (by decide +kernel)
  have h2322562171575901 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2322562171575901 = 759730667473658428631235988491448633097984 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1161281085787950) (r := 152937765781624779344611439985245081181482) (b := 1) (s := 759730667473658428631235988491448633097984) h1161281085787950 (by decide +kernel)
  have h2508480008949327 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2508480008949327 = 1794008719311854225677531837797350441808773 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1254240004474663) (r := 1630477125842007184799384331362934906684709) (b := 1) (s := 1794008719311854225677531837797350441808773) h1254240004474663 (by decide +kernel)
  have h2658221072416813 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2658221072416813 = 1049752790665793369996427935942030161328616 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1329110536208406) (r := 1200722312746834540901191083203599585145859) (b := 1) (s := 1049752790665793369996427935942030161328616) h1329110536208406 (by decide +kernel)
  have h3846743596672586 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 3846743596672586 = 578353869354214875762764273058047389243046 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1923371798336293) (r := 1701606793674112229885612304259323884064889) (b := 0) (s := 578353869354214875762764273058047389243046) h1923371798336293 (by decide +kernel)
  have h4138189865413403 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 4138189865413403 = 1265899920288409068803249557012633446070984 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2069094932706701) (r := 1779630072499156423476941895989031635519572) (b := 1) (s := 1265899920288409068803249557012633446070984) h2069094932706701 (by decide +kernel)
  have h4645124343151803 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 4645124343151803 = 717202231023252159360288596398644628799905 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2322562171575901) (r := 759730667473658428631235988491448633097984) (b := 1) (s := 717202231023252159360288596398644628799905) h2322562171575901 (by decide +kernel)
  have h5016960017898654 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 5016960017898654 = 1390582182395614517022864799540751609613866 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2508480008949327) (r := 1794008719311854225677531837797350441808773) (b := 0) (s := 1390582182395614517022864799540751609613866) h2508480008949327 (by decide +kernel)
  have h5316442144833627 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 5316442144833627 = 925307630905812657235996377802174870815269 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2658221072416813) (r := 1049752790665793369996427935942030161328616) (b := 1) (s := 925307630905812657235996377802174870815269) h2658221072416813 (by decide +kernel)
  have h7693487193345173 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 7693487193345173 = 1757657287833829062418591332090774945538965 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 3846743596672586) (r := 578353869354214875762764273058047389243046) (b := 1) (s := 1757657287833829062418591332090774945538965) h3846743596672586 (by decide +kernel)
  have h8276379730826807 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 8276379730826807 = 2252426914831719530027462390016197615029853 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4138189865413403) (r := 1265899920288409068803249557012633446070984) (b := 1) (s := 2252426914831719530027462390016197615029853) h4138189865413403 (by decide +kernel)
  have h9290248686303606 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 9290248686303606 = 2236706050791861290475128561341142834643767 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4645124343151803) (r := 717202231023252159360288596398644628799905) (b := 0) (s := 2236706050791861290475128561341142834643767) h4645124343151803 (by decide +kernel)
  have h10033920035797309 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 10033920035797309 = 2228061511112229130873082005262106310421910 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 5016960017898654) (r := 1390582182395614517022864799540751609613866) (b := 1) (s := 2228061511112229130873082005262106310421910) h5016960017898654 (by decide +kernel)
  have h10632884289667254 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 10632884289667254 = 1544282107718542918623862289481060592099748 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 5316442144833627) (r := 925307630905812657235996377802174870815269) (b := 0) (s := 1544282107718542918623862289481060592099748) h5316442144833627 (by decide +kernel)
  have h15386974386690347 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 15386974386690347 = 619190366189138294071681472604976636079332 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 7693487193345173) (r := 1757657287833829062418591332090774945538965) (b := 1) (s := 619190366189138294071681472604976636079332) h7693487193345173 (by decide +kernel)
  have h16552759461653615 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 16552759461653615 = 46348125155419809590689623884024269531659 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 8276379730826807) (r := 2252426914831719530027462390016197615029853) (b := 1) (s := 46348125155419809590689623884024269531659) h8276379730826807 (by decide +kernel)
  have h18580497372607212 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 18580497372607212 = 1554385022424103156760175174233037552042824 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 9290248686303606) (r := 2236706050791861290475128561341142834643767) (b := 0) (s := 1554385022424103156760175174233037552042824) h9290248686303606 (by decide +kernel)
  have h20067840071594619 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 20067840071594619 = 1105751454269125709580985205655852961976955 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 10033920035797309) (r := 2228061511112229130873082005262106310421910) (b := 1) (s := 1105751454269125709580985205655852961976955) h10033920035797309 (by decide +kernel)
  have h21265768579334509 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 21265768579334509 = 1684400341711384857380954952162523088847863 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 10632884289667254) (r := 1544282107718542918623862289481060592099748) (b := 1) (s := 1684400341711384857380954952162523088847863) h10632884289667254 (by decide +kernel)
  have h30773948773380695 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 30773948773380695 = 130209738823479212649169039785232599476218 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 15386974386690347) (r := 619190366189138294071681472604976636079332) (b := 1) (s := 130209738823479212649169039785232599476218) h15386974386690347 (by decide +kernel)
  have h33105518923307230 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 33105518923307230 = 1552710869938000118799334792475334854070909 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 16552759461653615) (r := 46348125155419809590689623884024269531659) (b := 0) (s := 1552710869938000118799334792475334854070909) h16552759461653615 (by decide +kernel)
  have h37160994745214425 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 37160994745214425 = 1817870464362567996916769326014512879743411 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 18580497372607212) (r := 1554385022424103156760175174233037552042824) (b := 1) (s := 1817870464362567996916769326014512879743411) h18580497372607212 (by decide +kernel)
  have h40135680143189239 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 40135680143189239 = 485972136299378594137089356483633753722851 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 20067840071594619) (r := 1105751454269125709580985205655852961976955) (b := 1) (s := 485972136299378594137089356483633753722851) h20067840071594619 (by decide +kernel)
  have h42531537158669019 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 42531537158669019 = 1414668287542288694759595729852774443645357 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 21265768579334509) (r := 1684400341711384857380954952162523088847863) (b := 1) (s := 1414668287542288694759595729852774443645357) h21265768579334509 (by decide +kernel)
  have h61547897546761391 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 61547897546761391 = 1164149977302758159885364849108755702995863 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 30773948773380695) (r := 130209738823479212649169039785232599476218) (b := 1) (s := 1164149977302758159885364849108755702995863) h30773948773380695 (by decide +kernel)
  have h66211037846614461 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 66211037846614461 = 213729452072602172270952168380891307224504 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 33105518923307230) (r := 1552710869938000118799334792475334854070909) (b := 1) (s := 213729452072602172270952168380891307224504) h33105518923307230 (by decide +kernel)
  have h74321989490428850 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 74321989490428850 = 2181615222638243092031713155821932575735122 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 37160994745214425) (r := 1817870464362567996916769326014512879743411) (b := 0) (s := 2181615222638243092031713155821932575735122) h37160994745214425 (by decide +kernel)
  have h80271360286378478 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 80271360286378478 = 1493913670293538342145472642753594715441780 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 40135680143189239) (r := 485972136299378594137089356483633753722851) (b := 0) (s := 1493913670293538342145472642753594715441780) h40135680143189239 (by decide +kernel)
  have h85063074317338039 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 85063074317338039 = 322474886147695354766583323522527690153100 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 42531537158669019) (r := 1414668287542288694759595729852774443645357) (b := 1) (s := 322474886147695354766583323522527690153100) h42531537158669019 (by decide +kernel)
  have h123095795093522783 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 123095795093522783 = 341319844799001698628148715584806079750143 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 61547897546761391) (r := 1164149977302758159885364849108755702995863) (b := 1) (s := 341319844799001698628148715584806079750143) h61547897546761391 (by decide +kernel)
  have h132422075693228922 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 132422075693228922 = 1675879825442568999885968073790902747818382 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 66211037846614461) (r := 213729452072602172270952168380891307224504) (b := 0) (s := 1675879825442568999885968073790902747818382) h66211037846614461 (by decide +kernel)
  have h148643978980857700 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 148643978980857700 = 95298328928180731740115326091646001519625 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 74321989490428850) (r := 2181615222638243092031713155821932575735122) (b := 0) (s := 95298328928180731740115326091646001519625) h74321989490428850 (by decide +kernel)
  have h160542720572756957 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 160542720572756957 = 1372419059938960504577301063156162406526547 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 80271360286378478) (r := 1493913670293538342145472642753594715441780) (b := 1) (s := 1372419059938960504577301063156162406526547) h80271360286378478 (by decide +kernel)
  have h170126148634676079 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 170126148634676079 = 1618948982478981417134748859409422816059534 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 85063074317338039) (r := 322474886147695354766583323522527690153100) (b := 1) (s := 1618948982478981417134748859409422816059534) h85063074317338039 (by decide +kernel)
  have h246191590187045566 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 246191590187045566 = 1195197781875371045704758012316427263872509 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 123095795093522783) (r := 341319844799001698628148715584806079750143) (b := 0) (s := 1195197781875371045704758012316427263872509) h123095795093522783 (by decide +kernel)
  have h264844151386457845 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 264844151386457845 = 1336631655155677171551275929392518622963544 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 132422075693228922) (r := 1675879825442568999885968073790902747818382) (b := 1) (s := 1336631655155677171551275929392518622963544) h132422075693228922 (by decide +kernel)
  have h297287957961715400 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 297287957961715400 = 2006861353590520591114273935510654849985272 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 148643978980857700) (r := 95298328928180731740115326091646001519625) (b := 0) (s := 2006861353590520591114273935510654849985272) h148643978980857700 (by decide +kernel)
  have h321085441145513914 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 321085441145513914 = 723177700344702387101141351932128729807558 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 160542720572756957) (r := 1372419059938960504577301063156162406526547) (b := 0) (s := 723177700344702387101141351932128729807558) h160542720572756957 (by decide +kernel)
  have h340252297269352159 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 340252297269352159 = 1462321166458284006538739939619613722616941 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 170126148634676079) (r := 1618948982478981417134748859409422816059534) (b := 1) (s := 1462321166458284006538739939619613722616941) h170126148634676079 (by decide +kernel)
  have h492383180374091132 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 492383180374091132 = 914811274794570608599414646334534536415266 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 246191590187045566) (r := 1195197781875371045704758012316427263872509) (b := 0) (s := 914811274794570608599414646334534536415266) h246191590187045566 (by decide +kernel)
  have h529688302772915691 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 529688302772915691 = 2186321829521449318297517321614323708115725 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 264844151386457845) (r := 1336631655155677171551275929392518622963544) (b := 1) (s := 2186321829521449318297517321614323708115725) h264844151386457845 (by decide +kernel)
  have h594575915923430801 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 594575915923430801 = 767653029454755142019897921111324028641703 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 297287957961715400) (r := 2006861353590520591114273935510654849985272) (b := 1) (s := 767653029454755142019897921111324028641703) h297287957961715400 (by decide +kernel)
  have h642170882291027828 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 642170882291027828 = 804542369222406529092371981230539241536481 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 321085441145513914) (r := 723177700344702387101141351932128729807558) (b := 0) (s := 804542369222406529092371981230539241536481) h321085441145513914 (by decide +kernel)
  have h680504594538704319 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 680504594538704319 = 678848219678463226541609586369650192884204 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 340252297269352159) (r := 1462321166458284006538739939619613722616941) (b := 1) (s := 678848219678463226541609586369650192884204) h340252297269352159 (by decide +kernel)
  have h984766360748182265 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 984766360748182265 = 929995145079961567708756363169093279352890 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 492383180374091132) (r := 914811274794570608599414646334534536415266) (b := 1) (s := 929995145079961567708756363169093279352890) h492383180374091132 (by decide +kernel)
  have h1059376605545831383 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1059376605545831383 = 1119556777716302332405453195032872429163806 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 529688302772915691) (r := 2186321829521449318297517321614323708115725) (b := 1) (s := 1119556777716302332405453195032872429163806) h529688302772915691 (by decide +kernel)
  have h1189151831846861603 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1189151831846861603 = 2173100686950156321740144855053411453219417 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 594575915923430801) (r := 767653029454755142019897921111324028641703) (b := 1) (s := 2173100686950156321740144855053411453219417) h594575915923430801 (by decide +kernel)
  have h1284341764582055656 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1284341764582055656 = 15293910771385270320488827862624518458505 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 642170882291027828) (r := 804542369222406529092371981230539241536481) (b := 0) (s := 15293910771385270320488827862624518458505) h642170882291027828 (by decide +kernel)
  have h1361009189077408639 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1361009189077408639 = 76884758672354794317737389344779870448555 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 680504594538704319) (r := 678848219678463226541609586369650192884204) (b := 1) (s := 76884758672354794317737389344779870448555) h680504594538704319 (by decide +kernel)
  have h1969532721496364531 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1969532721496364531 = 1965020553825937964174779000692094441076489 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 984766360748182265) (r := 929995145079961567708756363169093279352890) (b := 1) (s := 1965020553825937964174779000692094441076489) h984766360748182265 (by decide +kernel)
  have h2118753211091662767 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2118753211091662767 = 1631113915712775804603446841412448313789550 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1059376605545831383) (r := 1119556777716302332405453195032872429163806) (b := 1) (s := 1631113915712775804603446841412448313789550) h1059376605545831383 (by decide +kernel)
  have h2378303663693723207 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2378303663693723207 = 2077724803906592697568332837605956469662616 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1189151831846861603) (r := 2173100686950156321740144855053411453219417) (b := 1) (s := 2077724803906592697568332837605956469662616) h1189151831846861603 (by decide +kernel)
  have h2568683529164111312 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2568683529164111312 = 763574224510268900414316086823390332037321 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1284341764582055656) (r := 15293910771385270320488827862624518458505) (b := 0) (s := 763574224510268900414316086823390332037321) h1284341764582055656 (by decide +kernel)
  have h2722018378154817278 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2722018378154817278 = 1625679419281626285498997383654839361356676 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1361009189077408639) (r := 76884758672354794317737389344779870448555) (b := 0) (s := 1625679419281626285498997383654839361356676) h1361009189077408639 (by decide +kernel)
  have h3939065442992729062 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 3939065442992729062 = 1255554216971896222160840852429745709277482 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1969532721496364531) (r := 1965020553825937964174779000692094441076489) (b := 0) (s := 1255554216971896222160840852429745709277482) h1969532721496364531 (by decide +kernel)
  have h4237506422183325534 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 4237506422183325534 = 1559726255138535861278915290017006737431253 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2118753211091662767) (r := 1631113915712775804603446841412448313789550) (b := 0) (s := 1559726255138535861278915290017006737431253) h2118753211091662767 (by decide +kernel)
  have h4756607327387446415 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 4756607327387446415 = 878715658853957475842291886793688915891496 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2378303663693723207) (r := 2077724803906592697568332837605956469662616) (b := 1) (s := 878715658853957475842291886793688915891496) h2378303663693723207 (by decide +kernel)
  have h5137367058328222624 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 5137367058328222624 = 997242658032383551123761019456716592034507 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2568683529164111312) (r := 763574224510268900414316086823390332037321) (b := 0) (s := 997242658032383551123761019456716592034507) h2568683529164111312 (by decide +kernel)
  have h5444036756309634556 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 5444036756309634556 = 1763679387713254943842883956090702104212554 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2722018378154817278) (r := 1625679419281626285498997383654839361356676) (b := 0) (s := 1763679387713254943842883956090702104212554) h2722018378154817278 (by decide +kernel)
  have h7878130885985458125 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 7878130885985458125 = 1737118577398112651286569939166605995277629 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 3939065442992729062) (r := 1255554216971896222160840852429745709277482) (b := 1) (s := 1737118577398112651286569939166605995277629) h3939065442992729062 (by decide +kernel)
  have h8475012844366651069 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 8475012844366651069 = 1520708288734994055213853703742616038123363 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4237506422183325534) (r := 1559726255138535861278915290017006737431253) (b := 1) (s := 1520708288734994055213853703742616038123363) h4237506422183325534 (by decide +kernel)
  have h9513214654774892830 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 9513214654774892830 = 734832716059761423291172027447557752800604 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4756607327387446415) (r := 878715658853957475842291886793688915891496) (b := 0) (s := 734832716059761423291172027447557752800604) h4756607327387446415 (by decide +kernel)
  have h10274734116656445248 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 10274734116656445248 = 2014570290048235606294217361123691721932984 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 5137367058328222624) (r := 997242658032383551123761019456716592034507) (b := 0) (s := 2014570290048235606294217361123691721932984) h5137367058328222624 (by decide +kernel)
  have h10888073512619269112 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 10888073512619269112 = 139263046727878479429418060798255284643040 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 5444036756309634556) (r := 1763679387713254943842883956090702104212554) (b := 0) (s := 139263046727878479429418060798255284643040) h5444036756309634556 (by decide +kernel)
  have h15756261771970916250 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 15756261771970916250 = 679746243229250390623791777404580912392673 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 7878130885985458125) (r := 1737118577398112651286569939166605995277629) (b := 0) (s := 679746243229250390623791777404580912392673) h7878130885985458125 (by decide +kernel)
  have h16950025688733302138 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 16950025688733302138 = 2075040417255574645084667050226808969451208 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 8475012844366651069) (r := 1520708288734994055213853703742616038123363) (b := 0) (s := 2075040417255574645084667050226808969451208) h8475012844366651069 (by decide +kernel)
  have h19026429309549785661 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 19026429309549785661 = 684454404437064433816290723566004931910457 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 9513214654774892830) (r := 734832716059761423291172027447557752800604) (b := 1) (s := 684454404437064433816290723566004931910457) h9513214654774892830 (by decide +kernel)
  have h20549468233312890497 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 20549468233312890497 = 1592546092885071360108908964142595639403961 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 10274734116656445248) (r := 2014570290048235606294217361123691721932984) (b := 1) (s := 1592546092885071360108908964142595639403961) h10274734116656445248 (by decide +kernel)
  have h21776147025238538225 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 21776147025238538225 = 1518934692826162297998763104985522603993323 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 10888073512619269112) (r := 139263046727878479429418060798255284643040) (b := 1) (s := 1518934692826162297998763104985522603993323) h10888073512619269112 (by decide +kernel)
  have h31512523543941832501 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 31512523543941832501 = 99385732350774502553171842281333204337861 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 15756261771970916250) (r := 679746243229250390623791777404580912392673) (b := 1) (s := 99385732350774502553171842281333204337861) h15756261771970916250 (by decide +kernel)
  have h33900051377466604276 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 33900051377466604276 = 2117399393492149062118318598347441992998117 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 16950025688733302138) (r := 2075040417255574645084667050226808969451208) (b := 0) (s := 2117399393492149062118318598347441992998117) h16950025688733302138 (by decide +kernel)
  have h38052858619099571322 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 38052858619099571322 = 1165202771068099792728037574465674024801442 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 19026429309549785661) (r := 684454404437064433816290723566004931910457) (b := 0) (s := 1165202771068099792728037574465674024801442) h19026429309549785661 (by decide +kernel)
  have h41098936466625780995 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 41098936466625780995 = 445250289685722205778965874257855792018479 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 20549468233312890497) (r := 1592546092885071360108908964142595639403961) (b := 1) (s := 445250289685722205778965874257855792018479) h20549468233312890497 (by decide +kernel)
  have h43552294050477076450 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 43552294050477076450 = 298729931320084796099327469654490707002894 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 21776147025238538225) (r := 1518934692826162297998763104985522603993323) (b := 0) (s := 298729931320084796099327469654490707002894) h21776147025238538225 (by decide +kernel)
  have h63025047087883665002 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 63025047087883665002 = 1563774985457322642708439979085662709191380 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 31512523543941832501) (r := 99385732350774502553171842281333204337861) (b := 0) (s := 1563774985457322642708439979085662709191380) h31512523543941832501 (by decide +kernel)
  have h67800102754933208553 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 67800102754933208553 = 2169241118210748916048234019837109957764085 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 33900051377466604276) (r := 2117399393492149062118318598347441992998117) (b := 1) (s := 2169241118210748916048234019837109957764085) h33900051377466604276 (by decide +kernel)
  have h76105717238199142644 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 76105717238199142644 = 2147526303807941106578422408783521807308553 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 38052858619099571322) (r := 1165202771068099792728037574465674024801442) (b := 0) (s := 2147526303807941106578422408783521807308553) h38052858619099571322 (by decide +kernel)
  have h82197872933251561991 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 82197872933251561991 = 66044563788374086333259379429718444575248 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 41098936466625780995) (r := 445250289685722205778965874257855792018479) (b := 1) (s := 66044563788374086333259379429718444575248) h41098936466625780995 (by decide +kernel)
  have h87104588100954152900 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 87104588100954152900 = 1709650344186709397085927901804546423576553 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 43552294050477076450) (r := 298729931320084796099327469654490707002894) (b := 0) (s := 1709650344186709397085927901804546423576553) h43552294050477076450 (by decide +kernel)
  have h126050094175767330004 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 126050094175767330004 = 749621912991910816867390088310401724655798 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 63025047087883665002) (r := 1563774985457322642708439979085662709191380) (b := 0) (s := 749621912991910816867390088310401724655798) h63025047087883665002 (by decide +kernel)
  have h135600205509866417107 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 135600205509866417107 = 2170360743258392986767873504658840150211359 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 67800102754933208553) (r := 2169241118210748916048234019837109957764085) (b := 1) (s := 2170360743258392986767873504658840150211359) h67800102754933208553 (by decide +kernel)
  have h152211434476398285288 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 152211434476398285288 = 1611135507731395260537037750968584477807680 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 76105717238199142644) (r := 2147526303807941106578422408783521807308553) (b := 0) (s := 1611135507731395260537037750968584477807680) h76105717238199142644 (by decide +kernel)
  have h164395745866503123983 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 164395745866503123983 = 1540607740084935416049456061114073001093466 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 82197872933251561991) (r := 66044563788374086333259379429718444575248) (b := 1) (s := 1540607740084935416049456061114073001093466) h82197872933251561991 (by decide +kernel)
  have h174209176201908305801 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 174209176201908305801 = 1703644061764539328039507314088141311443143 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 87104588100954152900) (r := 1709650344186709397085927901804546423576553) (b := 1) (s := 1703644061764539328039507314088141311443143) h87104588100954152900 (by decide +kernel)
  have h252100188351534660008 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 252100188351534660008 = 116379854289114337482308126067044423315786 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 126050094175767330004) (r := 749621912991910816867390088310401724655798) (b := 0) (s := 116379854289114337482308126067044423315786) h126050094175767330004 (by decide +kernel)
  have h271200411019732834214 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 271200411019732834214 = 1174196897299412259583822928882877735821985 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 135600205509866417107) (r := 2170360743258392986767873504658840150211359) (b := 0) (s := 1174196897299412259583822928882877735821985) h135600205509866417107 (by decide +kernel)
  have h304422868952796570576 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 304422868952796570576 = 75127986496165575948407356186467988385607 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 152211434476398285288) (r := 1611135507731395260537037750968584477807680) (b := 0) (s := 75127986496165575948407356186467988385607) h152211434476398285288 (by decide +kernel)
  have h328791491733006247966 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 328791491733006247966 = 1396330430512996810880934583883199010003307 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 164395745866503123983) (r := 1540607740084935416049456061114073001093466) (b := 0) (s := 1396330430512996810880934583883199010003307) h164395745866503123983 (by decide +kernel)
  have h348418352403816611603 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 348418352403816611603 = 78112575019219662915870317230384243712406 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 174209176201908305801) (r := 1703644061764539328039507314088141311443143) (b := 1) (s := 78112575019219662915870317230384243712406) h174209176201908305801 (by decide +kernel)
  have h504200376703069320016 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 504200376703069320016 = 1939643839110407573565328315685857469902322 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 252100188351534660008) (r := 116379854289114337482308126067044423315786) (b := 0) (s := 1939643839110407573565328315685857469902322) h252100188351534660008 (by decide +kernel)
  have h542400822039465668429 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 542400822039465668429 = 301394178706891884181419145307733056139179 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 271200411019732834214) (r := 1174196897299412259583822928882877735821985) (b := 1) (s := 301394178706891884181419145307733056139179) h271200411019732834214 (by decide +kernel)
  have h608845737905593141152 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 608845737905593141152 = 790511417825798080417992801903973114280802 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 304422868952796570576) (r := 75127986496165575948407356186467988385607) (b := 0) (s := 790511417825798080417992801903973114280802) h304422868952796570576 (by decide +kernel)
  have h696836704807633223207 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 696836704807633223207 = 1942941543544229508216852369042143354311674 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 348418352403816611603) (r := 78112575019219662915870317230384243712406) (b := 1) (s := 1942941543544229508216852369042143354311674) h348418352403816611603 (by decide +kernel)
  have h1008400753406138640033 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1008400753406138640033 = 249834798925912899909102811882412282049286 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 504200376703069320016) (r := 1939643839110407573565328315685857469902322) (b := 1) (s := 249834798925912899909102811882412282049286) h504200376703069320016 (by decide +kernel)
  have h1084801644078931336858 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1084801644078931336858 = 1656729056982112702535135972258204886773319 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 542400822039465668429) (r := 301394178706891884181419145307733056139179) (b := 0) (s := 1656729056982112702535135972258204886773319) h542400822039465668429 (by decide +kernel)
  have h1217691475811186282304 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1217691475811186282304 = 1011911506578691678229728050310359496080868 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 608845737905593141152) (r := 790511417825798080417992801903973114280802) (b := 0) (s := 1011911506578691678229728050310359496080868) h608845737905593141152 (by decide +kernel)
  have h1393673409615266446414 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1393673409615266446414 = 2150995123004781300580508106281485050807728 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 696836704807633223207) (r := 1942941543544229508216852369042143354311674) (b := 0) (s := 2150995123004781300580508106281485050807728) h696836704807633223207 (by decide +kernel)
  have h2016801506812277280067 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2016801506812277280067 = 1740373774787685811737168135965629861007088 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1008400753406138640033) (r := 249834798925912899909102811882412282049286) (b := 1) (s := 1740373774787685811737168135965629861007088) h1008400753406138640033 (by decide +kernel)
  have h2169603288157862673716 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2169603288157862673716 = 1223415318260890708793795672169410737657377 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1084801644078931336858) (r := 1656729056982112702535135972258204886773319) (b := 0) (s := 1223415318260890708793795672169410737657377) h1084801644078931336858 (by decide +kernel)
  have h2435382951622372564609 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2435382951622372564609 = 1716410482495208463607191681415403691847378 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1217691475811186282304) (r := 1011911506578691678229728050310359496080868) (b := 1) (s := 1716410482495208463607191681415403691847378) h1217691475811186282304 (by decide +kernel)
  have h2787346819230532892829 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2787346819230532892829 = 2320870706891288003918904454147844644193071 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1393673409615266446414) (r := 2150995123004781300580508106281485050807728) (b := 1) (s := 2320870706891288003918904454147844644193071) h1393673409615266446414 (by decide +kernel)
  have h4033603013624554560134 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 4033603013624554560134 = 1850102899456485186821566896943374811908403 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2016801506812277280067) (r := 1740373774787685811737168135965629861007088) (b := 0) (s := 1850102899456485186821566896943374811908403) h2016801506812277280067 (by decide +kernel)
  have h4339206576315725347433 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 4339206576315725347433 = 1632397229961881832781202839208574813436426 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2169603288157862673716) (r := 1223415318260890708793795672169410737657377) (b := 1) (s := 1632397229961881832781202839208574813436426) h2169603288157862673716 (by decide +kernel)
  have h4870765903244745129219 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 4870765903244745129219 = 1941925771374762044976667314385951811095276 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2435382951622372564609) (r := 1716410482495208463607191681415403691847378) (b := 1) (s := 1941925771374762044976667314385951811095276) h2435382951622372564609 (by decide +kernel)
  have h5574693638461065785659 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 5574693638461065785659 = 2370321636700879521644470662032457481320906 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2787346819230532892829) (r := 2320870706891288003918904454147844644193071) (b := 1) (s := 2370321636700879521644470662032457481320906) h2787346819230532892829 (by decide +kernel)
  have h8067206027249109120269 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 8067206027249109120269 = 2066165597091728594807896731535766114815418 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4033603013624554560134) (r := 1850102899456485186821566896943374811908403) (b := 1) (s := 2066165597091728594807896731535766114815418) h4033603013624554560134 (by decide +kernel)
  have h8678413152631450694866 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 8678413152631450694866 = 1890527815276176038958702142365421721279386 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4339206576315725347433) (r := 1632397229961881832781202839208574813436426) (b := 0) (s := 1890527815276176038958702142365421721279386) h4339206576315725347433 (by decide +kernel)
  have h9741531806489490258438 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 9741531806489490258438 = 726590289458375122003607094337086758283797 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4870765903244745129219) (r := 1941925771374762044976667314385951811095276) (b := 0) (s := 726590289458375122003607094337086758283797) h4870765903244745129219 (by decide +kernel)
  have h11149387276922131571319 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 11149387276922131571319 = 1651206990919156651121677153457708712643954 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 5574693638461065785659) (r := 2370321636700879521644470662032457481320906) (b := 1) (s := 1651206990919156651121677153457708712643954) h5574693638461065785659 (by decide +kernel)
  have h16134412054498218240539 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 16134412054498218240539 = 2359931062404761000601574927156546200594167 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 8067206027249109120269) (r := 2066165597091728594807896731535766114815418) (b := 1) (s := 2359931062404761000601574927156546200594167) h8067206027249109120269 (by decide +kernel)
  have h17356826305262901389732 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 17356826305262901389732 = 1688342155207646156160719053615103532754987 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 8678413152631450694866) (r := 1890527815276176038958702142365421721279386) (b := 0) (s := 1688342155207646156160719053615103532754987) h8678413152631450694866 (by decide +kernel)
  have h19483063612978980516877 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 19483063612978980516877 = 1069259841637099831443589485410725153555741 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 9741531806489490258438) (r := 726590289458375122003607094337086758283797) (b := 1) (s := 1069259841637099831443589485410725153555741) h9741531806489490258438 (by decide +kernel)
  have h22298774553844263142639 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 22298774553844263142639 = 2075767048249934361947819515501175742880718 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 11149387276922131571319) (r := 1651206990919156651121677153457708712643954) (b := 1) (s := 2075767048249934361947819515501175742880718) h11149387276922131571319 (by decide +kernel)
  have h32268824108996436481078 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 32268824108996436481078 = 942531791599706187687182981676068961832653 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 16134412054498218240539) (r := 2359931062404761000601574927156546200594167) (b := 0) (s := 942531791599706187687182981676068961832653) h16134412054498218240539 (by decide +kernel)
  have h34713652610525802779465 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 34713652610525802779465 = 1149521501917302337448878081841999110518147 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 17356826305262901389732) (r := 1688342155207646156160719053615103532754987) (b := 1) (s := 1149521501917302337448878081841999110518147) h17356826305262901389732 (by decide +kernel)
  have h38966127225957961033755 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 38966127225957961033755 = 1512887399109077421854364887039147784179508 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 19483063612978980516877) (r := 1069259841637099831443589485410725153555741) (b := 1) (s := 1512887399109077421854364887039147784179508) h19483063612978980516877 (by decide +kernel)
  have h44597549107688526285279 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 44597549107688526285279 = 441977593538380236501202953444885366871715 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 22298774553844263142639) (r := 2075767048249934361947819515501175742880718) (b := 1) (s := 441977593538380236501202953444885366871715) h22298774553844263142639 (by decide +kernel)
  have h64537648217992872962157 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 64537648217992872962157 = 1019172372007801477296443129763631279890781 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 32268824108996436481078) (r := 942531791599706187687182981676068961832653) (b := 1) (s := 1019172372007801477296443129763631279890781) h32268824108996436481078 (by decide +kernel)
  have h69427305221051605558930 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 69427305221051605558930 = 1837305609195667505678935725548435464734992 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 34713652610525802779465) (r := 1149521501917302337448878081841999110518147) (b := 0) (s := 1837305609195667505678935725548435464734992) h34713652610525802779465 (by decide +kernel)
  have h77932254451915922067510 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 77932254451915922067510 = 843596527895453366231577532858722715526207 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 38966127225957961033755) (r := 1512887399109077421854364887039147784179508) (b := 0) (s := 843596527895453366231577532858722715526207) h38966127225957961033755 (by decide +kernel)
  have h89195098215377052570558 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 89195098215377052570558 = 2311699176364363016984167571847244845471961 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 44597549107688526285279) (r := 441977593538380236501202953444885366871715) (b := 0) (s := 2311699176364363016984167571847244845471961) h44597549107688526285279 (by decide +kernel)
  have h129075296435985745924314 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 129075296435985745924314 = 767290969537225555367760553583718762441849 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 64537648217992872962157) (r := 1019172372007801477296443129763631279890781) (b := 0) (s := 767290969537225555367760553583718762441849) h64537648217992872962157 (by decide +kernel)
  have h138854610442103211117860 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 138854610442103211117860 = 502644931626451467880003017551879216437862 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 69427305221051605558930) (r := 1837305609195667505678935725548435464734992) (b := 0) (s := 502644931626451467880003017551879216437862) h69427305221051605558930 (by decide +kernel)
  have h155864508903831844135021 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 155864508903831844135021 = 1300790133249526387537500961514531816027955 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 77932254451915922067510) (r := 843596527895453366231577532858722715526207) (b := 1) (s := 1300790133249526387537500961514531816027955) h77932254451915922067510 (by decide +kernel)
  have h178390196430754105141116 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 178390196430754105141116 = 782251365760276444462190990321851035746155 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 89195098215377052570558) (r := 2311699176364363016984167571847244845471961) (b := 0) (s := 782251365760276444462190990321851035746155) h89195098215377052570558 (by decide +kernel)
  have h258150592871971491848629 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 258150592871971491848629 = 2294901070489283707213610020745492604576617 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 129075296435985745924314) (r := 767290969537225555367760553583718762441849) (b := 1) (s := 2294901070489283707213610020745492604576617) h129075296435985745924314 (by decide +kernel)
  have h277709220884206422235721 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 277709220884206422235721 = 1408249021309090402905919491891786051306590 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 138854610442103211117860) (r := 502644931626451467880003017551879216437862) (b := 1) (s := 1408249021309090402905919491891786051306590) h138854610442103211117860 (by decide +kernel)
  have h311729017807663688270042 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 311729017807663688270042 = 2124695667448525455908281287907343014324538 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 155864508903831844135021) (r := 1300790133249526387537500961514531816027955) (b := 0) (s := 2124695667448525455908281287907343014324538) h155864508903831844135021 (by decide +kernel)
  have h356780392861508210282232 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 356780392861508210282232 = 1892625043245810347581775780676691983357960 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 178390196430754105141116) (r := 782251365760276444462190990321851035746155) (b := 0) (s := 1892625043245810347581775780676691983357960) h178390196430754105141116 (by decide +kernel)
  have h516301185743942983697258 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 516301185743942983697258 = 1188181579077901191366941292650097959801513 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 258150592871971491848629) (r := 2294901070489283707213610020745492604576617) (b := 0) (s := 1188181579077901191366941292650097959801513) h258150592871971491848629 (by decide +kernel)
  have h555418441768412844471442 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 555418441768412844471442 = 2376054395833065291861775544477293206156732 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 277709220884206422235721) (r := 1408249021309090402905919491891786051306590) (b := 0) (s := 2376054395833065291861775544477293206156732) h277709220884206422235721 (by decide +kernel)
  have h623458035615327376540085 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 623458035615327376540085 = 573512078129131553668094318291456806681009 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 311729017807663688270042) (r := 2124695667448525455908281287907343014324538) (b := 1) (s := 573512078129131553668094318291456806681009) h311729017807663688270042 (by decide +kernel)
  have h713560785723016420564464 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 713560785723016420564464 = 576767610079744089961625147058691201356187 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 356780392861508210282232) (r := 1892625043245810347581775780676691983357960) (b := 0) (s := 576767610079744089961625147058691201356187) h356780392861508210282232 (by decide +kernel)
  have h1032602371487885967394517 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1032602371487885967394517 = 1015535214584165152566537001824641634513237 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 516301185743942983697258) (r := 1188181579077901191366941292650097959801513) (b := 1) (s := 1015535214584165152566537001824641634513237) h516301185743942983697258 (by decide +kernel)
  have h1110836883536825688942884 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1110836883536825688942884 = 612971044752102982514650323242833261201949 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 555418441768412844471442) (r := 2376054395833065291861775544477293206156732) (b := 0) (s := 612971044752102982514650323242833261201949) h555418441768412844471442 (by decide +kernel)
  have h1246916071230654753080171 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1246916071230654753080171 = 1686397018616043740134615227526640750453306 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 623458035615327376540085) (r := 573512078129131553668094318291456806681009) (b := 1) (s := 1686397018616043740134615227526640750453306) h623458035615327376540085 (by decide +kernel)
  have h1427121571446032841128929 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1427121571446032841128929 = 1340196765626604060422569310647174157940548 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 713560785723016420564464) (r := 576767610079744089961625147058691201356187) (b := 1) (s := 1340196765626604060422569310647174157940548) h713560785723016420564464 (by decide +kernel)
  have h2065204742975771934789034 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2065204742975771934789034 = 1839975276961838603407048856296957335387439 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1032602371487885967394517) (r := 1015535214584165152566537001824641634513237) (b := 0) (s := 1839975276961838603407048856296957335387439) h1032602371487885967394517 (by decide +kernel)
  have h2221673767073651377885769 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2221673767073651377885769 = 1131872661661648040329064791425472271213461 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1110836883536825688942884) (r := 612971044752102982514650323242833261201949) (b := 1) (s := 1131872661661648040329064791425472271213461) h1110836883536825688942884 (by decide +kernel)
  have h2493832142461309506160343 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2493832142461309506160343 = 449984970331675946353454901509639475158754 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1246916071230654753080171) (r := 1686397018616043740134615227526640750453306) (b := 1) (s := 449984970331675946353454901509639475158754) h1246916071230654753080171 (by decide +kernel)
  have h2854243142892065682257858 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2854243142892065682257858 = 740370856926346392434699905509758346234154 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1427121571446032841128929) (r := 1340196765626604060422569310647174157940548) (b := 0) (s := 740370856926346392434699905509758346234154) h1427121571446032841128929 (by decide +kernel)
  have h4130409485951543869578068 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 4130409485951543869578068 = 680972295320984730865199773183350559238841 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2065204742975771934789034) (r := 1839975276961838603407048856296957335387439) (b := 0) (s := 680972295320984730865199773183350559238841) h2065204742975771934789034 (by decide +kernel)
  have h4443347534147302755771538 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 4443347534147302755771538 = 1085429424793254464937743219644771908801842 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2221673767073651377885769) (r := 1131872661661648040329064791425472271213461) (b := 0) (s := 1085429424793254464937743219644771908801842) h2221673767073651377885769 (by decide +kernel)
  have h4987664284922619012320686 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 4987664284922619012320686 = 1959389565505512550930338580119555753084214 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2493832142461309506160343) (r := 449984970331675946353454901509639475158754) (b := 0) (s := 1959389565505512550930338580119555753084214) h2493832142461309506160343 (by decide +kernel)
  have h5708486285784131364515717 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 5708486285784131364515717 = 626852171731494262842342198559171137079403 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2854243142892065682257858) (r := 740370856926346392434699905509758346234154) (b := 1) (s := 626852171731494262842342198559171137079403) h2854243142892065682257858 (by decide +kernel)
  have h8260818971903087739156136 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 8260818971903087739156136 = 528215272096998220615925395424920443550610 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4130409485951543869578068) (r := 680972295320984730865199773183350559238841) (b := 0) (s := 528215272096998220615925395424920443550610) h4130409485951543869578068 (by decide +kernel)
  have h8886695068294605511543076 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 8886695068294605511543076 = 709627317882030618331610396086086261737204 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4443347534147302755771538) (r := 1085429424793254464937743219644771908801842) (b := 0) (s := 709627317882030618331610396086086261737204) h4443347534147302755771538 (by decide +kernel)
  have h9975328569845238024641372 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 9975328569845238024641372 = 1977127909908631079288275982351617751916705 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4987664284922619012320686) (r := 1959389565505512550930338580119555753084214) (b := 0) (s := 1977127909908631079288275982351617751916705) h4987664284922619012320686 (by decide +kernel)
  have h11416972571568262729031434 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 11416972571568262729031434 = 80029385886531664254514827071327057123956 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 5708486285784131364515717) (r := 626852171731494262842342198559171137079403) (b := 0) (s := 80029385886531664254514827071327057123956) h5708486285784131364515717 (by decide +kernel)
  have h16521637943806175478312273 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 16521637943806175478312273 = 1028137479169063655321196496855083839870801 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 8260818971903087739156136) (r := 528215272096998220615925395424920443550610) (b := 1) (s := 1028137479169063655321196496855083839870801) h8260818971903087739156136 (by decide +kernel)
  have h17773390136589211023086152 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 17773390136589211023086152 = 798821709940451389420222593481010498157184 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 8886695068294605511543076) (r := 709627317882030618331610396086086261737204) (b := 0) (s := 798821709940451389420222593481010498157184) h8886695068294605511543076 (by decide +kernel)
  have h19950657139690476049282745 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 19950657139690476049282745 = 263498286587978186817379502927125869417544 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 9975328569845238024641372) (r := 1977127909908631079288275982351617751916705) (b := 1) (s := 263498286587978186817379502927125869417544) h9975328569845238024641372 (by decide +kernel)
  have h22833945143136525458062868 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 22833945143136525458062868 = 1700055648341570483148958125768872966577810 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 11416972571568262729031434) (r := 80029385886531664254514827071327057123956) (b := 0) (s := 1700055648341570483148958125768872966577810) h11416972571568262729031434 (by decide +kernel)
  have h33043275887612350956624546 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 33043275887612350956624546 = 1907187240265004327065875755765390534386296 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 16521637943806175478312273) (r := 1028137479169063655321196496855083839870801) (b := 0) (s := 1907187240265004327065875755765390534386296) h16521637943806175478312273 (by decide +kernel)
  have h35546780273178422046172305 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 35546780273178422046172305 = 1899470911822709280557123926258487459391391 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 17773390136589211023086152) (r := 798821709940451389420222593481010498157184) (b := 1) (s := 1899470911822709280557123926258487459391391) h17773390136589211023086152 (by decide +kernel)
  have h39901314279380952098565490 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 39901314279380952098565490 = 2199172795264690892203577963160407049981039 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 19950657139690476049282745) (r := 263498286587978186817379502927125869417544) (b := 0) (s := 2199172795264690892203577963160407049981039) h19950657139690476049282745 (by decide +kernel)
  have h45667890286273050916125736 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 45667890286273050916125736 = 101263466768913688110480176422917474464063 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 22833945143136525458062868) (r := 1700055648341570483148958125768872966577810) (b := 0) (s := 101263466768913688110480176422917474464063) h22833945143136525458062868 (by decide +kernel)
  have h66086551775224701913249093 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 66086551775224701913249093 = 265659319409909777976895036571311754157039 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 33043275887612350956624546) (r := 1907187240265004327065875755765390534386296) (b := 1) (s := 265659319409909777976895036571311754157039) h33043275887612350956624546 (by decide +kernel)
  have h71093560546356844092344611 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 71093560546356844092344611 = 999378132140290556955512646226507112867719 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 35546780273178422046172305) (r := 1899470911822709280557123926258487459391391) (b := 1) (s := 999378132140290556955512646226507112867719) h35546780273178422046172305 (by decide +kernel)
  have h79802628558761904197130981 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 79802628558761904197130981 = 2132344010544716452134533644319244271749024 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 39901314279380952098565490) (r := 2199172795264690892203577963160407049981039) (b := 1) (s := 2132344010544716452134533644319244271749024) h39901314279380952098565490 (by decide +kernel)
  have h91335780572546101832251472 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 91335780572546101832251472 = 1795718519899258211450745982395805926793792 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 45667890286273050916125736) (r := 101263466768913688110480176422917474464063) (b := 0) (s := 1795718519899258211450745982395805926793792) h45667890286273050916125736 (by decide +kernel)
  have h132173103550449403826498187 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 132173103550449403826498187 = 844838113624323547151722947672297828099818 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 66086551775224701913249093) (r := 265659319409909777976895036571311754157039) (b := 1) (s := 844838113624323547151722947672297828099818) h66086551775224701913249093 (by decide +kernel)
  have h142187121092713688184689222 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 142187121092713688184689222 = 1724333575481616201118965523386978089407066 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 71093560546356844092344611) (r := 999378132140290556955512646226507112867719) (b := 0) (s := 1724333575481616201118965523386978089407066) h71093560546356844092344611 (by decide +kernel)
  have h159605257117523808394261962 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 159605257117523808394261962 = 223631931614161429541887824060334039604764 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 79802628558761904197130981) (r := 2132344010544716452134533644319244271749024) (b := 0) (s := 223631931614161429541887824060334039604764) h79802628558761904197130981 (by decide +kernel)
  have h182671561145092203664502945 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 182671561145092203664502945 = 2074458644129703768801727617580550654755653 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 91335780572546101832251472) (r := 1795718519899258211450745982395805926793792) (b := 1) (s := 2074458644129703768801727617580550654755653) h91335780572546101832251472 (by decide +kernel)
  have h264346207100898807652996375 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 264346207100898807652996375 = 2246108797328748672268445934973825481408940 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 132173103550449403826498187) (r := 844838113624323547151722947672297828099818) (b := 1) (s := 2246108797328748672268445934973825481408940) h132173103550449403826498187 (by decide +kernel)
  have h284374242185427376369378445 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 284374242185427376369378445 = 1916591785037378788324837305147932558748732 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 142187121092713688184689222) (r := 1724333575481616201118965523386978089407066) (b := 1) (s := 1916591785037378788324837305147932558748732) h142187121092713688184689222 (by decide +kernel)
  have h319210514235047616788523925 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 319210514235047616788523925 = 2054055828934501891915588335457014181898642 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 159605257117523808394261962) (r := 223631931614161429541887824060334039604764) (b := 1) (s := 2054055828934501891915588335457014181898642) h159605257117523808394261962 (by decide +kernel)
  have h365343122290184407329005891 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 365343122290184407329005891 = 702135621185825005866399470762833192361141 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 182671561145092203664502945) (r := 2074458644129703768801727617580550654755653) (b := 1) (s := 702135621185825005866399470762833192361141) h182671561145092203664502945 (by decide +kernel)
  have h528692414201797615305992751 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 528692414201797615305992751 = 2144180448407542774460934730237679159677444 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 264346207100898807652996375) (r := 2246108797328748672268445934973825481408940) (b := 1) (s := 2144180448407542774460934730237679159677444) h264346207100898807652996375 (by decide +kernel)
  have h568748484370854752738756891 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 568748484370854752738756891 = 551183538348282027942872349943288431895532 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 284374242185427376369378445) (r := 1916591785037378788324837305147932558748732) (b := 1) (s := 551183538348282027942872349943288431895532) h284374242185427376369378445 (by decide +kernel)
  have h638421028470095233577047850 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 638421028470095233577047850 = 1681494472981601698341850584506020162767297 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 319210514235047616788523925) (r := 2054055828934501891915588335457014181898642) (b := 0) (s := 1681494472981601698341850584506020162767297) h319210514235047616788523925 (by decide +kernel)
  have h730686244580368814658011782 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 730686244580368814658011782 = 2240550555720695691356167709991957349001502 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 365343122290184407329005891) (r := 702135621185825005866399470762833192361141) (b := 0) (s := 2240550555720695691356167709991957349001502) h365343122290184407329005891 (by decide +kernel)
  have h1057384828403595230611985502 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1057384828403595230611985502 = 1010192110237485938242567191161245362269879 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 528692414201797615305992751) (r := 2144180448407542774460934730237679159677444) (b := 0) (s := 1010192110237485938242567191161245362269879) h528692414201797615305992751 (by decide +kernel)
  have h1137496968741709505477513782 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1137496968741709505477513782 = 1022821759794096873179099180426346891080261 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 568748484370854752738756891) (r := 551183538348282027942872349943288431895532) (b := 0) (s := 1022821759794096873179099180426346891080261) h568748484370854752738756891 (by decide +kernel)
  have h1276842056940190467154095700 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1276842056940190467154095700 = 1324532349141364796283208359640466371645866 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 638421028470095233577047850) (r := 1681494472981601698341850584506020162767297) (b := 0) (s := 1324532349141364796283208359640466371645866) h638421028470095233577047850 (by decide +kernel)
  have h1461372489160737629316023564 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1461372489160737629316023564 = 1090310525438665870749921688308530903119035 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 730686244580368814658011782) (r := 2240550555720695691356167709991957349001502) (b := 0) (s := 1090310525438665870749921688308530903119035) h730686244580368814658011782 (by decide +kernel)
  have h2114769656807190461223971004 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2114769656807190461223971004 = 1212102753363160521695009922546767335832894 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1057384828403595230611985502) (r := 1010192110237485938242567191161245362269879) (b := 0) (s := 1212102753363160521695009922546767335832894) h1057384828403595230611985502 (by decide +kernel)
  have h2274993937483419010955027564 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2274993937483419010955027564 = 1055586881895787211988228995736008619960220 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1137496968741709505477513782) (r := 1022821759794096873179099180426346891080261) (b := 0) (s := 1055586881895787211988228995736008619960220) h1137496968741709505477513782 (by decide +kernel)
  have h2553684113880380934308191401 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2553684113880380934308191401 = 1084445431144256590116293596072946011514030 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1276842056940190467154095700) (r := 1324532349141364796283208359640466371645866) (b := 1) (s := 1084445431144256590116293596072946011514030) h1276842056940190467154095700 (by decide +kernel)
  have h2922744978321475258632047128 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2922744978321475258632047128 = 1583679133845482513607454562279940342518264 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1461372489160737629316023564) (r := 1090310525438665870749921688308530903119035) (b := 0) (s := 1583679133845482513607454562279940342518264) h1461372489160737629316023564 (by decide +kernel)
  have h4229539313614380922447942009 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 4229539313614380922447942009 = 921943161866023860524346026524098646944232 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2114769656807190461223971004) (r := 1212102753363160521695009922546767335832894) (b := 1) (s := 921943161866023860524346026524098646944232) h2114769656807190461223971004 (by decide +kernel)
  have h4549987874966838021910055129 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 4549987874966838021910055129 = 39609801878034554413368582427865373678974 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2274993937483419010955027564) (r := 1055586881895787211988228995736008619960220) (b := 1) (s := 39609801878034554413368582427865373678974) h2274993937483419010955027564 (by decide +kernel)
  have h5107368227760761868616382803 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 5107368227760761868616382803 = 1128486731702976592725938155776023731010999 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2553684113880380934308191401) (r := 1084445431144256590116293596072946011514030) (b := 1) (s := 1128486731702976592725938155776023731010999) h2553684113880380934308191401 (by decide +kernel)
  have h5845489956642950517264094256 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 5845489956642950517264094256 = 994009757493780572737175304725219654259797 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2922744978321475258632047128) (r := 1583679133845482513607454562279940342518264) (b := 0) (s := 994009757493780572737175304725219654259797) h2922744978321475258632047128 (by decide +kernel)
  have h8459078627228761844895884018 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 8459078627228761844895884018 = 2035708849298036810782471487616588049555688 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4229539313614380922447942009) (r := 921943161866023860524346026524098646944232) (b := 0) (s := 2035708849298036810782471487616588049555688) h4229539313614380922447942009 (by decide +kernel)
  have h9099975749933676043820110258 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 9099975749933676043820110258 = 269276595897597539728616612241404223522746 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4549987874966838021910055129) (r := 39609801878034554413368582427865373678974) (b := 0) (s := 269276595897597539728616612241404223522746) h4549987874966838021910055129 (by decide +kernel)
  have h10214736455521523737232765606 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 10214736455521523737232765606 = 1758517155667677686011209046489528578173873 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 5107368227760761868616382803) (r := 1128486731702976592725938155776023731010999) (b := 0) (s := 1758517155667677686011209046489528578173873) h5107368227760761868616382803 (by decide +kernel)
  have h11690979913285901034528188513 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 11690979913285901034528188513 = 728820928212772695511182855244085346889723 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 5845489956642950517264094256) (r := 994009757493780572737175304725219654259797) (b := 1) (s := 728820928212772695511182855244085346889723) h5845489956642950517264094256 (by decide +kernel)
  have h16918157254457523689791768036 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 16918157254457523689791768036 = 1287711452550471575248017233656266222561285 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 8459078627228761844895884018) (r := 2035708849298036810782471487616588049555688) (b := 0) (s := 1287711452550471575248017233656266222561285) h8459078627228761844895884018 (by decide +kernel)
  have h18199951499867352087640220517 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 18199951499867352087640220517 = 300796264886786266185478860982094665782470 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 9099975749933676043820110258) (r := 269276595897597539728616612241404223522746) (b := 1) (s := 300796264886786266185478860982094665782470) h9099975749933676043820110258 (by decide +kernel)
  have h20429472911043047474465531213 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 20429472911043047474465531213 = 648476208114119951721449793966944356353299 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 10214736455521523737232765606) (r := 1758517155667677686011209046489528578173873) (b := 1) (s := 648476208114119951721449793966944356353299) h10214736455521523737232765606 (by decide +kernel)
  have h23381959826571802069056377026 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 23381959826571802069056377026 = 1959902097175521740557812084417238609343208 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 11690979913285901034528188513) (r := 728820928212772695511182855244085346889723) (b := 0) (s := 1959902097175521740557812084417238609343208) h11690979913285901034528188513 (by decide +kernel)
  have h33836314508915047379583536072 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 33836314508915047379583536072 = 1963202073546733906278783220591861947812384 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 16918157254457523689791768036) (r := 1287711452550471575248017233656266222561285) (b := 0) (s := 1963202073546733906278783220591861947812384) h16918157254457523689791768036 (by decide +kernel)
  have h36399902999734704175280441035 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 36399902999734704175280441035 = 1882138473743896212482878509747758152942895 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 18199951499867352087640220517) (r := 300796264886786266185478860982094665782470) (b := 1) (s := 1882138473743896212482878509747758152942895) h18199951499867352087640220517 (by decide +kernel)
  have h40858945822086094948931062426 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 40858945822086094948931062426 = 1037941812061349497514392550541253411994966 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 20429472911043047474465531213) (r := 648476208114119951721449793966944356353299) (b := 0) (s := 1037941812061349497514392550541253411994966) h20429472911043047474465531213 (by decide +kernel)
  have h46763919653143604138112754052 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 46763919653143604138112754052 = 1122637084977032506956488121716928613683715 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 23381959826571802069056377026) (r := 1959902097175521740557812084417238609343208) (b := 0) (s := 1122637084977032506956488121716928613683715) h23381959826571802069056377026 (by decide +kernel)
  have h67672629017830094759167072144 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 67672629017830094759167072144 = 1237709248309212883889012776697822223312743 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 33836314508915047379583536072) (r := 1963202073546733906278783220591861947812384) (b := 0) (s := 1237709248309212883889012776697822223312743) h33836314508915047379583536072 (by decide +kernel)
  have h72799805999469408350560882070 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 72799805999469408350560882070 = 489194983222733629653430118532853069541141 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 36399902999734704175280441035) (r := 1882138473743896212482878509747758152942895) (b := 0) (s := 489194983222733629653430118532853069541141) h36399902999734704175280441035 (by decide +kernel)
  have h81717891644172189897862124853 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 81717891644172189897862124853 = 2002248305073701302680477065919175326943141 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 40858945822086094948931062426) (r := 1037941812061349497514392550541253411994966) (b := 1) (s := 2002248305073701302680477065919175326943141) h40858945822086094948931062426 (by decide +kernel)
  have h93527839306287208276225508105 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 93527839306287208276225508105 = 650002992566211870383290340352037945877010 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 46763919653143604138112754052) (r := 1122637084977032506956488121716928613683715) (b := 1) (s := 650002992566211870383290340352037945877010) h46763919653143604138112754052 (by decide +kernel)
  have h135345258035660189518334144288 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 135345258035660189518334144288 = 183720343830085406636976865135998312080614 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 67672629017830094759167072144) (r := 1237709248309212883889012776697822223312743) (b := 0) (s := 183720343830085406636976865135998312080614) h67672629017830094759167072144 (by decide +kernel)
  have h145599611998938816701121764140 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 145599611998938816701121764140 = 1378056528147714681448161378459885111582201 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 72799805999469408350560882070) (r := 489194983222733629653430118532853069541141) (b := 0) (s := 1378056528147714681448161378459885111582201) h72799805999469408350560882070 (by decide +kernel)
  have h163435783288344379795724249706 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 163435783288344379795724249706 = 1189055813658308367392334280780556617069763 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 81717891644172189897862124853) (r := 2002248305073701302680477065919175326943141) (b := 0) (s := 1189055813658308367392334280780556617069763) h81717891644172189897862124853 (by decide +kernel)
  have h187055678612574416552451016210 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 187055678612574416552451016210 = 876125844618509251193888791900536536107857 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 93527839306287208276225508105) (r := 650002992566211870383290340352037945877010) (b := 0) (s := 876125844618509251193888791900536536107857) h93527839306287208276225508105 (by decide +kernel)
  have h270690516071320379036668288577 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 270690516071320379036668288577 = 262818031338848860876138632719049376502360 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 135345258035660189518334144288) (r := 183720343830085406636976865135998312080614) (b := 1) (s := 262818031338848860876138632719049376502360) h135345258035660189518334144288 (by decide +kernel)
  have h291199223997877633402243528280 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 291199223997877633402243528280 = 1935487545819412788426602124700702707117803 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 145599611998938816701121764140) (r := 1378056528147714681448161378459885111582201) (b := 0) (s := 1935487545819412788426602124700702707117803) h145599611998938816701121764140 (by decide +kernel)
  have h326871566576688759591448499413 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 326871566576688759591448499413 = 1360710845455007280993517665718927291924641 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 163435783288344379795724249706) (r := 1189055813658308367392334280780556617069763) (b := 1) (s := 1360710845455007280993517665718927291924641) h163435783288344379795724249706 (by decide +kernel)
  have h374111357225148833104902032421 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 374111357225148833104902032421 = 871011551619748853864402664011553838766479 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 187055678612574416552451016210) (r := 876125844618509251193888791900536536107857) (b := 1) (s := 871011551619748853864402664011553838766479) h187055678612574416552451016210 (by decide +kernel)
  have h541381032142640758073336577154 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 541381032142640758073336577154 = 1365099946041026253649226416977895393091513 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 270690516071320379036668288577) (r := 262818031338848860876138632719049376502360) (b := 0) (s := 1365099946041026253649226416977895393091513) h270690516071320379036668288577 (by decide +kernel)
  have h582398447995755266804487056561 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 582398447995755266804487056561 = 1912122164987563149559236183813543042317777 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 291199223997877633402243528280) (r := 1935487545819412788426602124700702707117803) (b := 1) (s := 1912122164987563149559236183813543042317777) h291199223997877633402243528280 (by decide +kernel)
  have h653743133153377519182896998827 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 653743133153377519182896998827 = 16486409641519995269274385222881180819225 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 326871566576688759591448499413) (r := 1360710845455007280993517665718927291924641) (b := 1) (s := 16486409641519995269274385222881180819225) h326871566576688759591448499413 (by decide +kernel)
  have h748222714450297666209804064843 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 748222714450297666209804064843 = 1141498640599904530539940525366568202931716 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 374111357225148833104902032421) (r := 871011551619748853864402664011553838766479) (b := 1) (s := 1141498640599904530539940525366568202931716) h374111357225148833104902032421 (by decide +kernel)
  have h1082762064285281516146673154308 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1082762064285281516146673154308 = 2236449166578986713676861367228000878394949 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 541381032142640758073336577154) (r := 1365099946041026253649226416977895393091513) (b := 0) (s := 2236449166578986713676861367228000878394949) h541381032142640758073336577154 (by decide +kernel)
  have h1164796895991510533608974113122 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1164796895991510533608974113122 = 2288730246170016937792957402155088412013860 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 582398447995755266804487056561) (r := 1912122164987563149559236183813543042317777) (b := 0) (s := 2288730246170016937792957402155088412013860) h582398447995755266804487056561 (by decide +kernel)
  have h1307486266306755038365793997655 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1307486266306755038365793997655 = 1096878604165746257988498857772332674462528 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 653743133153377519182896998827) (r := 16486409641519995269274385222881180819225) (b := 1) (s := 1096878604165746257988498857772332674462528) h653743133153377519182896998827 (by decide +kernel)
  have h1496445428900595332419608129686 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1496445428900595332419608129686 = 1802548761481313494500506926895992451192016 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 748222714450297666209804064843) (r := 1141498640599904530539940525366568202931716) (b := 0) (s := 1802548761481313494500506926895992451192016) h748222714450297666209804064843 (by decide +kernel)
  have h2165524128570563032293346308617 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2165524128570563032293346308617 = 2119467957894393453193227143816636622681029 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1082762064285281516146673154308) (r := 2236449166578986713676861367228000878394949) (b := 1) (s := 2119467957894393453193227143816636622681029) h1082762064285281516146673154308 (by decide +kernel)
  have h2329593791983021067217948226245 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2329593791983021067217948226245 = 1132132883444938288262339717098203190561145 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1164796895991510533608974113122) (r := 2288730246170016937792957402155088412013860) (b := 1) (s := 1132132883444938288262339717098203190561145) h1164796895991510533608974113122 (by decide +kernel)
  have h2614972532613510076731587995311 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2614972532613510076731587995311 = 1816789420323394174900938857852151494196182 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1307486266306755038365793997655) (r := 1096878604165746257988498857772332674462528) (b := 1) (s := 1816789420323394174900938857852151494196182) h1307486266306755038365793997655 (by decide +kernel)
  have h2992890857801190664839216259372 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2992890857801190664839216259372 = 685709006924157154602728631131136467702439 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1496445428900595332419608129686) (r := 1802548761481313494500506926895992451192016) (b := 0) (s := 685709006924157154602728631131136467702439) h1496445428900595332419608129686 (by decide +kernel)
  have h4331048257141126064586692617234 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 4331048257141126064586692617234 = 1422341219868040332301700994022250160810271 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2165524128570563032293346308617) (r := 2119467957894393453193227143816636622681029) (b := 0) (s := 1422341219868040332301700994022250160810271) h2165524128570563032293346308617 (by decide +kernel)
  have h4659187583966042134435896452490 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 4659187583966042134435896452490 = 248713634619924874457034324493260459506120 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2329593791983021067217948226245) (r := 1132132883444938288262339717098203190561145) (b := 0) (s := 248713634619924874457034324493260459506120) h2329593791983021067217948226245 (by decide +kernel)
  have h5229945065227020153463175990622 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 5229945065227020153463175990622 = 1832254776945743508207466638114555526624295 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2614972532613510076731587995311) (r := 1816789420323394174900938857852151494196182) (b := 0) (s := 1832254776945743508207466638114555526624295) h2614972532613510076731587995311 (by decide +kernel)
  have h5985781715602381329678432518745 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 5985781715602381329678432518745 = 1600913559298880786320049274924256314513910 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2992890857801190664839216259372) (r := 685709006924157154602728631131136467702439) (b := 1) (s := 1600913559298880786320049274924256314513910) h2992890857801190664839216259372 (by decide +kernel)
  have h8662096514282252129173385234468 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 8662096514282252129173385234468 = 1103634980579163181373664030491435893700652 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4331048257141126064586692617234) (r := 1422341219868040332301700994022250160810271) (b := 0) (s := 1103634980579163181373664030491435893700652) h4331048257141126064586692617234 (by decide +kernel)
  have h9318375167932084268871792904980 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 9318375167932084268871792904980 = 61226545943351292777325009984935625243648 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4659187583966042134435896452490) (r := 248713634619924874457034324493260459506120) (b := 0) (s := 61226545943351292777325009984935625243648) h4659187583966042134435896452490 (by decide +kernel)
  have h10459890130454040306926351981245 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 10459890130454040306926351981245 = 1249137745611377775596908321764800529377760 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 5229945065227020153463175990622) (r := 1832254776945743508207466638114555526624295) (b := 1) (s := 1249137745611377775596908321764800529377760) h5229945065227020153463175990622 (by decide +kernel)
  have h11971563431204762659356865037490 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 11971563431204762659356865037490 = 2315394226455017052126901600734738542433025 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 5985781715602381329678432518745) (r := 1600913559298880786320049274924256314513910) (b := 0) (s := 2315394226455017052126901600734738542433025) h5985781715602381329678432518745 (by decide +kernel)
  have h17324193028564504258346770468937 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 17324193028564504258346770468937 = 2079747832916082473827873649120304202759943 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 8662096514282252129173385234468) (r := 1103634980579163181373664030491435893700652) (b := 1) (s := 2079747832916082473827873649120304202759943) h8662096514282252129173385234468 (by decide +kernel)
  have h18636750335864168537743585809961 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 18636750335864168537743585809961 = 488710695492290417950125402814328670883928 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 9318375167932084268871792904980) (r := 61226545943351292777325009984935625243648) (b := 1) (s := 488710695492290417950125402814328670883928) h9318375167932084268871792904980 (by decide +kernel)
  have h20919780260908080613852703962490 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 20919780260908080613852703962490 = 2357736575619948926028684755982800985723296 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 10459890130454040306926351981245) (r := 1249137745611377775596908321764800529377760) (b := 0) (s := 2357736575619948926028684755982800985723296) h10459890130454040306926351981245 (by decide +kernel)
  have h23943126862409525318713730074980 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 23943126862409525318713730074980 = 1351912556268737946589039681556729149945175 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 11971563431204762659356865037490) (r := 2315394226455017052126901600734738542433025) (b := 0) (s := 1351912556268737946589039681556729149945175) h11971563431204762659356865037490 (by decide +kernel)
  have h34648386057129008516693540937875 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 34648386057129008516693540937875 = 2358602941312970051114640898729935830748928 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 17324193028564504258346770468937) (r := 2079747832916082473827873649120304202759943) (b := 1) (s := 2358602941312970051114640898729935830748928) h17324193028564504258346770468937 (by decide +kernel)
  have h37273500671728337075487171619922 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 37273500671728337075487171619922 = 803883118189234247070995362764943055567831 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 18636750335864168537743585809961) (r := 488710695492290417950125402814328670883928) (b := 0) (s := 803883118189234247070995362764943055567831) h18636750335864168537743585809961 (by decide +kernel)
  have h41839560521816161227705407924981 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 41839560521816161227705407924981 = 114395451246819669671303459863843001109015 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 20919780260908080613852703962490) (r := 2357736575619948926028684755982800985723296) (b := 1) (s := 114395451246819669671303459863843001109015) h20919780260908080613852703962490 (by decide +kernel)
  have h47886253724819050637427460149960 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 47886253724819050637427460149960 = 2036959690752750327853112491378103155721803 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 23943126862409525318713730074980) (r := 1351912556268737946589039681556729149945175) (b := 0) (s := 2036959690752750327853112491378103155721803) h23943126862409525318713730074980 (by decide +kernel)
  have h69296772114258017033387081875750 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 69296772114258017033387081875750 = 1102773128329273917966614238455169287734072 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 34648386057129008516693540937875) (r := 2358602941312970051114640898729935830748928) (b := 0) (s := 1102773128329273917966614238455169287734072) h34648386057129008516693540937875 (by decide +kernel)
  have h83679121043632322455410815849962 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 83679121043632322455410815849962 = 290672638095699215929945233769350232073499 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 41839560521816161227705407924981) (r := 114395451246819669671303459863843001109015) (b := 0) (s := 290672638095699215929945233769350232073499) h41839560521816161227705407924981 (by decide +kernel)
  have h95772507449638101274854920299920 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 95772507449638101274854920299920 = 1529178187232956714728692395258711311995705 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 47886253724819050637427460149960) (r := 2036959690752750327853112491378103155721803) (b := 0) (s := 1529178187232956714728692395258711311995705) h47886253724819050637427460149960 (by decide +kernel)
  have h138593544228516034066774163751500 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 138593544228516034066774163751500 = 2139610885897678991192034008852927086556932 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 69296772114258017033387081875750) (r := 1102773128329273917966614238455169287734072) (b := 0) (s := 2139610885897678991192034008852927086556932) h69296772114258017033387081875750 (by decide +kernel)
  have h167358242087264644910821631699924 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 167358242087264644910821631699924 = 1028482817175611900989488506693046168474951 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 83679121043632322455410815849962) (r := 290672638095699215929945233769350232073499) (b := 0) (s := 1028482817175611900989488506693046168474951) h83679121043632322455410815849962 (by decide +kernel)
  have h191545014899276202549709840599841 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 191545014899276202549709840599841 = 1990154051329569984888888729118252526765756 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 95772507449638101274854920299920) (r := 1529178187232956714728692395258711311995705) (b := 1) (s := 1990154051329569984888888729118252526765756) h95772507449638101274854920299920 (by decide +kernel)
  have h277187088457032068133548327503000 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 277187088457032068133548327503000 = 551442578836854025904591634338209490631303 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 138593544228516034066774163751500) (r := 2139610885897678991192034008852927086556932) (b := 0) (s := 551442578836854025904591634338209490631303) h138593544228516034066774163751500 (by decide +kernel)
  have h334716484174529289821643263399849 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 334716484174529289821643263399849 = 47190982378058333991603574479661660775863 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 167358242087264644910821631699924) (r := 1028482817175611900989488506693046168474951) (b := 1) (s := 47190982378058333991603574479661660775863) h167358242087264644910821631699924 (by decide +kernel)
  have h383090029798552405099419681199683 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 383090029798552405099419681199683 = 772200446028457329550222455068686719787658 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 191545014899276202549709840599841) (r := 1990154051329569984888888729118252526765756) (b := 1) (s := 772200446028457329550222455068686719787658) h191545014899276202549709840599841 (by decide +kernel)
  have h554374176914064136267096655006001 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 554374176914064136267096655006001 = 773354166891136876175086993756132067445439 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 277187088457032068133548327503000) (r := 551442578836854025904591634338209490631303) (b := 1) (s := 773354166891136876175086993756132067445439) h277187088457032068133548327503000 (by decide +kernel)
  have h669432968349058579643286526799699 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 669432968349058579643286526799699 = 1751429901631906802763540049694052622140337 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 334716484174529289821643263399849) (r := 47190982378058333991603574479661660775863) (b := 1) (s := 1751429901631906802763540049694052622140337) h334716484174529289821643263399849 (by decide +kernel)
  have h766180059597104810198839362399366 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 766180059597104810198839362399366 = 446549355196174622045056992553781373358853 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 383090029798552405099419681199683) (r := 772200446028457329550222455068686719787658) (b := 0) (s := 446549355196174622045056992553781373358853) h383090029798552405099419681199683 (by decide +kernel)
  have h1108748353828128272534193310012002 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1108748353828128272534193310012002 = 1701473827783127031285645002747589490672400 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 554374176914064136267096655006001) (r := 773354166891136876175086993756132067445439) (b := 0) (s := 1701473827783127031285645002747589490672400) h554374176914064136267096655006001 (by decide +kernel)
  have h1338865936698117159286573053599399 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1338865936698117159286573053599399 = 1123295575986683801454329384668140885135098 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 669432968349058579643286526799699) (r := 1751429901631906802763540049694052622140337) (b := 1) (s := 1123295575986683801454329384668140885135098) h669432968349058579643286526799699 (by decide +kernel)
  have h1532360119194209620397678724798733 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1532360119194209620397678724798733 = 1672243844696593714528247509639759672365196 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 766180059597104810198839362399366) (r := 446549355196174622045056992553781373358853) (b := 1) (s := 1672243844696593714528247509639759672365196) h766180059597104810198839362399366 (by decide +kernel)
  have h2217496707656256545068386620024004 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2217496707656256545068386620024004 = 1580455947350044206278703618425347837820758 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1108748353828128272534193310012002) (r := 1701473827783127031285645002747589490672400) (b := 0) (s := 1580455947350044206278703618425347837820758) h1108748353828128272534193310012002 (by decide +kernel)
  have h2677731873396234318573146107198798 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2677731873396234318573146107198798 = 54770786358133749706961245862040938830939 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1338865936698117159286573053599399) (r := 1123295575986683801454329384668140885135098) (b := 0) (s := 54770786358133749706961245862040938830939) h1338865936698117159286573053599399 (by decide +kernel)
  have h3064720238388419240795357449597466 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 3064720238388419240795357449597466 = 1679148024394016982855514002976070721035392 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1532360119194209620397678724798733) (r := 1672243844696593714528247509639759672365196) (b := 0) (s := 1679148024394016982855514002976070721035392) h1532360119194209620397678724798733 (by decide +kernel)
  have h4434993415312513090136773240048009 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 4434993415312513090136773240048009 = 209406964231135657228913617199013924870323 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2217496707656256545068386620024004) (r := 1580455947350044206278703618425347837820758) (b := 1) (s := 209406964231135657228913617199013924870323) h2217496707656256545068386620024004 (by decide +kernel)
  have h5355463746792468637146292214397596 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 5355463746792468637146292214397596 = 1608127287587032285757805603042496475531163 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2677731873396234318573146107198798) (r := 54770786358133749706961245862040938830939) (b := 0) (s := 1608127287587032285757805603042496475531163) h2677731873396234318573146107198798 (by decide +kernel)
  have h6129440476776838481590714899194932 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 6129440476776838481590714899194932 = 1820156275899408516795362910459337250125446 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 3064720238388419240795357449597466) (r := 1679148024394016982855514002976070721035392) (b := 0) (s := 1820156275899408516795362910459337250125446) h3064720238388419240795357449597466 (by decide +kernel)
  have h8869986830625026180273546480096019 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 8869986830625026180273546480096019 = 53487743915677147189183491550340959432558 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4434993415312513090136773240048009) (r := 209406964231135657228913617199013924870323) (b := 1) (s := 53487743915677147189183491550340959432558) h4434993415312513090136773240048009 (by decide +kernel)
  have h10710927493584937274292584428795193 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 10710927493584937274292584428795193 = 377081305304304426765654534006269622168727 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 5355463746792468637146292214397596) (r := 1608127287587032285757805603042496475531163) (b := 1) (s := 377081305304304426765654534006269622168727) h5355463746792468637146292214397596 (by decide +kernel)
  have h12258880953553676963181429798389865 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 12258880953553676963181429798389865 = 1777171697101262646782428108683575709788738 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 6129440476776838481590714899194932) (r := 1820156275899408516795362910459337250125446) (b := 1) (s := 1777171697101262646782428108683575709788738) h6129440476776838481590714899194932 (by decide +kernel)
  have h17739973661250052360547092960192038 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 17739973661250052360547092960192038 = 1177637079422775096798305781771676420069089 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 8869986830625026180273546480096019) (r := 53487743915677147189183491550340959432558) (b := 0) (s := 1177637079422775096798305781771676420069089) h8869986830625026180273546480096019 (by decide +kernel)
  have h21421854987169874548585168857590386 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 21421854987169874548585168857590386 = 375222309414749895734061749033170996321174 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 10710927493584937274292584428795193) (r := 377081305304304426765654534006269622168727) (b := 0) (s := 375222309414749895734061749033170996321174) h10710927493584937274292584428795193 (by decide +kernel)
  have h24517761907107353926362859596779731 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 24517761907107353926362859596779731 = 2223827411559458544190001889321706554703658 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 12258880953553676963181429798389865) (r := 1777171697101262646782428108683575709788738) (b := 1) (s := 2223827411559458544190001889321706554703658) h12258880953553676963181429798389865 (by decide +kernel)
  have h35479947322500104721094185920384077 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 35479947322500104721094185920384077 = 860597835992977883005492950773260682654755 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 17739973661250052360547092960192038) (r := 1177637079422775096798305781771676420069089) (b := 1) (s := 860597835992977883005492950773260682654755) h17739973661250052360547092960192038 (by decide +kernel)
  have h42843709974339749097170337715180772 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 42843709974339749097170337715180772 = 700303033951664079360978710586688097811469 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 21421854987169874548585168857590386) (r := 375222309414749895734061749033170996321174) (b := 0) (s := 700303033951664079360978710586688097811469) h21421854987169874548585168857590386 (by decide +kernel)
  have h49035523814214707852725719193559462 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 49035523814214707852725719193559462 = 1701132614878789180422784373224684362242295 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 24517761907107353926362859596779731) (r := 2223827411559458544190001889321706554703658) (b := 0) (s := 1701132614878789180422784373224684362242295) h24517761907107353926362859596779731 (by decide +kernel)
  have h70959894645000209442188371840768154 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 70959894645000209442188371840768154 = 1587904833656050927065524134008780272813133 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 35479947322500104721094185920384077) (r := 860597835992977883005492950773260682654755) (b := 0) (s := 1587904833656050927065524134008780272813133) h35479947322500104721094185920384077 (by decide +kernel)
  have h85687419948679498194340675430361544 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 85687419948679498194340675430361544 = 528596540641146648678502630073380798239957 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 42843709974339749097170337715180772) (r := 700303033951664079360978710586688097811469) (b := 0) (s := 528596540641146648678502630073380798239957) h42843709974339749097170337715180772 (by decide +kernel)
  have h141919789290000418884376743681536308 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 141919789290000418884376743681536308 = 1554493958887415027154150874640546472220142 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 70959894645000209442188371840768154) (r := 1587904833656050927065524134008780272813133) (b := 0) (s := 1554493958887415027154150874640546472220142) h70959894645000209442188371840768154 (by decide +kernel)
  have h171374839897358996388681350860723089 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 171374839897358996388681350860723089 = 2119954499765071332782767403224115815593788 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 85687419948679498194340675430361544) (r := 528596540641146648678502630073380798239957) (b := 1) (s := 2119954499765071332782767403224115815593788) h85687419948679498194340675430361544 (by decide +kernel)
  have h283839578580000837768753487363072617 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 283839578580000837768753487363072617 = 1674603801008222245227468462236604574850502 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 141919789290000418884376743681536308) (r := 1554493958887415027154150874640546472220142) (b := 1) (s := 1674603801008222245227468462236604574850502) h141919789290000418884376743681536308 (by decide +kernel)
  have h342749679794717992777362701721446179 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 342749679794717992777362701721446179 = 338840990664914039003213017023512792338752 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 171374839897358996388681350860723089) (r := 2119954499765071332782767403224115815593788) (b := 1) (s := 338840990664914039003213017023512792338752) h171374839897358996388681350860723089 (by decide +kernel)
  have h567679157160001675537506974726145234 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 567679157160001675537506974726145234 = 832453095162891109557333918947815881766552 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 283839578580000837768753487363072617) (r := 1674603801008222245227468462236604574850502) (b := 0) (s := 832453095162891109557333918947815881766552) h283839578580000837768753487363072617 (by decide +kernel)
  have h685499359589435985554725403442892358 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 685499359589435985554725403442892358 = 1086556300050122708885334433618384472142549 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 342749679794717992777362701721446179) (r := 338840990664914039003213017023512792338752) (b := 0) (s := 1086556300050122708885334433618384472142549) h342749679794717992777362701721446179 (by decide +kernel)
  have h1135358314320003351075013949452290468 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1135358314320003351075013949452290468 = 2189832038195929600289848730404371452068262 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 567679157160001675537506974726145234) (r := 832453095162891109557333918947815881766552) (b := 0) (s := 2189832038195929600289848730404371452068262) h567679157160001675537506974726145234 (by decide +kernel)
  have h1370998719178871971109450806885784716 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1370998719178871971109450806885784716 = 1244957943434552557727767349756994061101093 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 685499359589435985554725403442892358) (r := 1086556300050122708885334433618384472142549) (b := 0) (s := 1244957943434552557727767349756994061101093) h685499359589435985554725403442892358 (by decide +kernel)
  have h2270716628640006702150027898904580937 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2270716628640006702150027898904580937 = 360587436137960282134509821263951460536663 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1135358314320003351075013949452290468) (r := 2189832038195929600289848730404371452068262) (b := 1) (s := 360587436137960282134509821263951460536663) h1135358314320003351075013949452290468 (by decide +kernel)
  have h2741997438357743942218901613771569433 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2741997438357743942218901613771569433 = 1200885078582002893581849700255931659039329 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1370998719178871971109450806885784716) (r := 1244957943434552557727767349756994061101093) (b := 1) (s := 1200885078582002893581849700255931659039329) h1370998719178871971109450806885784716 (by decide +kernel)
  have h4541433257280013404300055797809161874 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 4541433257280013404300055797809161874 = 797871494418310371948111825426416342516207 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2270716628640006702150027898904580937) (r := 360587436137960282134509821263951460536663) (b := 0) (s := 797871494418310371948111825426416342516207) h2270716628640006702150027898904580937 (by decide +kernel)
  have h5483994876715487884437803227543138867 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 5483994876715487884437803227543138867 = 1881570863566529861169853090246342231538096 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2741997438357743942218901613771569433) (r := 1200885078582002893581849700255931659039329) (b := 1) (s := 1881570863566529861169853090246342231538096) h2741997438357743942218901613771569433 (by decide +kernel)
  have h9082866514560026808600111595618323749 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 9082866514560026808600111595618323749 = 2001455368357392767457675610730354535496422 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4541433257280013404300055797809161874) (r := 797871494418310371948111825426416342516207) (b := 1) (s := 2001455368357392767457675610730354535496422) h4541433257280013404300055797809161874 (by decide +kernel)
  have h10967989753430975768875606455086277735 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 10967989753430975768875606455086277735 = 737929900894387499465026048439730612733561 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 5483994876715487884437803227543138867) (r := 1881570863566529861169853090246342231538096) (b := 1) (s := 737929900894387499465026048439730612733561) h5483994876715487884437803227543138867 (by decide +kernel)
  have h18165733029120053617200223191236647499 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 18165733029120053617200223191236647499 = 601577860086454606706490189631236700043440 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 9082866514560026808600111595618323749) (r := 2001455368357392767457675610730354535496422) (b := 1) (s := 601577860086454606706490189631236700043440) h9082866514560026808600111595618323749 (by decide +kernel)
  have h21935979506861951537751212910172555471 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 21935979506861951537751212910172555471 = 72462530270885069285628451854271395155486 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 10967989753430975768875606455086277735) (r := 737929900894387499465026048439730612733561) (b := 1) (s := 72462530270885069285628451854271395155486) h10967989753430975768875606455086277735 (by decide +kernel)
  have h36331466058240107234400446382473294999 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 36331466058240107234400446382473294999 = 403703112901856564424743820085518063148218 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 18165733029120053617200223191236647499) (r := 601577860086454606706490189631236700043440) (b := 1) (s := 403703112901856564424743820085518063148218) h18165733029120053617200223191236647499 (by decide +kernel)
  have h43871959013723903075502425820345110942 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 43871959013723903075502425820345110942 = 2267660403253704105707364387257300317832788 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 21935979506861951537751212910172555471) (r := 72462530270885069285628451854271395155486) (b := 0) (s := 2267660403253704105707364387257300317832788) h21935979506861951537751212910172555471 (by decide +kernel)
  have h72662932116480214468800892764946589998 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 72662932116480214468800892764946589998 = 1041277757158278584518347093550741335584449 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 36331466058240107234400446382473294999) (r := 403703112901856564424743820085518063148218) (b := 0) (s := 1041277757158278584518347093550741335584449) h36331466058240107234400446382473294999 (by decide +kernel)
  have h87743918027447806151004851640690221885 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 87743918027447806151004851640690221885 = 881297894920819715220745931498912538372682 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 43871959013723903075502425820345110942) (r := 2267660403253704105707364387257300317832788) (b := 1) (s := 881297894920819715220745931498912538372682) h43871959013723903075502425820345110942 (by decide +kernel)
  have h145325864232960428937601785529893179997 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 145325864232960428937601785529893179997 = 1752126706494735250963058627546972865971268 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 72662932116480214468800892764946589998) (r := 1041277757158278584518347093550741335584449) (b := 1) (s := 1752126706494735250963058627546972865971268) h72662932116480214468800892764946589998 (by decide +kernel)
  have h175487836054895612302009703281380443770 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 175487836054895612302009703281380443770 = 547752667437073302289497906331121811870309 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 87743918027447806151004851640690221885) (r := 881297894920819715220745931498912538372682) (b := 0) (s := 547752667437073302289497906331121811870309) h87743918027447806151004851640690221885 (by decide +kernel)
  have h290651728465920857875203571059786359995 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 290651728465920857875203571059786359995 = 138547850718865136851312256012017309188123 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 145325864232960428937601785529893179997) (r := 1752126706494735250963058627546972865971268) (b := 1) (s := 138547850718865136851312256012017309188123) h145325864232960428937601785529893179997 (by decide +kernel)
  have h350975672109791224604019406562760887541 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 350975672109791224604019406562760887541 = 2078142098256816598564483753475446547613278 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 175487836054895612302009703281380443770) (r := 547752667437073302289497906331121811870309) (b := 1) (s := 2078142098256816598564483753475446547613278) h175487836054895612302009703281380443770 (by decide +kernel)
  have h581303456931841715750407142119572719990 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 581303456931841715750407142119572719990 = 1509171828876841147685187359728275551010841 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 290651728465920857875203571059786359995) (r := 138547850718865136851312256012017309188123) (b := 0) (s := 1509171828876841147685187359728275551010841) h290651728465920857875203571059786359995 (by decide +kernel)
  have h701951344219582449208038813125521775083 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 701951344219582449208038813125521775083 = 1354487684736709973600496022537405592007529 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 350975672109791224604019406562760887541) (r := 2078142098256816598564483753475446547613278) (b := 1) (s := 1354487684736709973600496022537405592007529) h350975672109791224604019406562760887541 (by decide +kernel)
  have h1162606913863683431500814284239145439981 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1162606913863683431500814284239145439981 = 1748415845522573711380510314575288792462736 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 581303456931841715750407142119572719990) (r := 1509171828876841147685187359728275551010841) (b := 1) (s := 1748415845522573711380510314575288792462736) h581303456931841715750407142119572719990 (by decide +kernel)
  have h1403902688439164898416077626251043550166 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1403902688439164898416077626251043550166 = 1717100033150670124842204714964656998791298 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 701951344219582449208038813125521775083) (r := 1354487684736709973600496022537405592007529) (b := 0) (s := 1717100033150670124842204714964656998791298) h701951344219582449208038813125521775083 (by decide +kernel)
  have h2325213827727366863001628568478290879963 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2325213827727366863001628568478290879963 = 131890427606352460602104413939060397260819 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1162606913863683431500814284239145439981) (r := 1748415845522573711380510314575288792462736) (b := 1) (s := 131890427606352460602104413939060397260819) h1162606913863683431500814284239145439981 (by decide +kernel)
  have h2807805376878329796832155252502087100333 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2807805376878329796832155252502087100333 = 1142263182419628750198260662852925657026781 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1403902688439164898416077626251043550166) (r := 1717100033150670124842204714964656998791298) (b := 1) (s := 1142263182419628750198260662852925657026781) h1403902688439164898416077626251043550166 (by decide +kernel)
  have h4650427655454733726003257136956581759927 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 4650427655454733726003257136956581759927 = 1928971858659397738364041917398885314291969 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2325213827727366863001628568478290879963) (r := 131890427606352460602104413939060397260819) (b := 1) (s := 1928971858659397738364041917398885314291969) h2325213827727366863001628568478290879963 (by decide +kernel)
  have h5615610753756659593664310505004174200666 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 5615610753756659593664310505004174200666 = 308473979038402584930799107430484476920714 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 2807805376878329796832155252502087100333) (r := 1142263182419628750198260662852925657026781) (b := 0) (s := 308473979038402584930799107430484476920714) h2807805376878329796832155252502087100333 (by decide +kernel)
  have h9300855310909467452006514273913163519854 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 9300855310909467452006514273913163519854 = 559307019937892846491370578629785466271820 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 4650427655454733726003257136956581759927) (r := 1928971858659397738364041917398885314291969) (b := 0) (s := 559307019937892846491370578629785466271820) h4650427655454733726003257136956581759927 (by decide +kernel)
  have h11231221507513319187328621010008348401333 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 11231221507513319187328621010008348401333 = 1652057873050656783440573586535282784497712 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 5615610753756659593664310505004174200666) (r := 308473979038402584930799107430484476920714) (b := 1) (s := 1652057873050656783440573586535282784497712) h5615610753756659593664310505004174200666 (by decide +kernel)
  have h18601710621818934904013028547826327039708 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 18601710621818934904013028547826327039708 = 797246870024230011830692395048848701763445 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 9300855310909467452006514273913163519854) (r := 559307019937892846491370578629785466271820) (b := 0) (s := 797246870024230011830692395048848701763445) h9300855310909467452006514273913163519854 (by decide +kernel)
  have h22462443015026638374657242020016696802667 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 22462443015026638374657242020016696802667 = 870303819420385694861527352973767526142775 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 11231221507513319187328621010008348401333) (r := 1652057873050656783440573586535282784497712) (b := 1) (s := 870303819420385694861527352973767526142775) h11231221507513319187328621010008348401333 (by decide +kernel)
  have h37203421243637869808026057095652654079417 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 37203421243637869808026057095652654079417 = 571247775988306514701869202219614293199414 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 18601710621818934904013028547826327039708) (r := 797246870024230011830692395048848701763445) (b := 1) (s := 571247775988306514701869202219614293199414) h18601710621818934904013028547826327039708 (by decide +kernel)
  have h44924886030053276749314484040033393605334 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 44924886030053276749314484040033393605334 = 1242541136787280037483687583873172420595396 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 22462443015026638374657242020016696802667) (r := 870303819420385694861527352973767526142775) (b := 0) (s := 1242541136787280037483687583873172420595396) h22462443015026638374657242020016696802667 (by decide +kernel)
  have h74406842487275739616052114191305308158834 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 74406842487275739616052114191305308158834 = 2012672253845400134465463771996185004994540 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 37203421243637869808026057095652654079417) (r := 571247775988306514701869202219614293199414) (b := 0) (s := 2012672253845400134465463771996185004994540) h37203421243637869808026057095652654079417 (by decide +kernel)
  have h148813684974551479232104228382610616317668 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 148813684974551479232104228382610616317668 = 1265299547367989870421352846616020544321903 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 74406842487275739616052114191305308158834) (r := 2012672253845400134465463771996185004994540) (b := 0) (s := 1265299547367989870421352846616020544321903) h74406842487275739616052114191305308158834 (by decide +kernel)
  have h297627369949102958464208456765221232635337 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 297627369949102958464208456765221232635337 = 2098586463683290212495295753804191115623462 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 148813684974551479232104228382610616317668) (r := 1265299547367989870421352846616020544321903) (b := 1) (s := 2098586463683290212495295753804191115623462) h148813684974551479232104228382610616317668 (by decide +kernel)
  have h595254739898205916928416913530442465270675 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 595254739898205916928416913530442465270675 = 730306400979615204943362749033302299535686 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 297627369949102958464208456765221232635337) (r := 2098586463683290212495295753804191115623462) (b := 1) (s := 730306400979615204943362749033302299535686) h297627369949102958464208456765221232635337 (by decide +kernel)
  have h1190509479796411833856833827060884930541351 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1190509479796411833856833827060884930541351 = 2381018959592823667713667654121769861082702 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 595254739898205916928416913530442465270675) (r := 730306400979615204943362749033302299535686) (b := 1) (s := 2381018959592823667713667654121769861082702) h595254739898205916928416913530442465270675 (by decide +kernel)
  have h2381018959592823667713667654121769861082702 : (5 : ZMod 2381018959592823667713667654121769861082703) ^ 2381018959592823667713667654121769861082702 = 1 :=
    modular_pow_step (p := 2381018959592823667713667654121769861082703) (a := 5) (e := 1190509479796411833856833827060884930541351) (r := 2381018959592823667713667654121769861082702) (b := 0) (s := 1) h1190509479796411833856833827060884930541351 (by decide +kernel)
  apply lucas_primality 2381018959592823667713667654121769861082703 5 (by simpa using h2381018959592823667713667654121769861082702)
  intro q hq hqd
  rw [show 2381018959592823667713667654121769861082703 - 1 = (2 * 53 * 48557021 * 63879670991 * 7241729240142017205097 : ℕ) by norm_num] at hqd
  simp only [hq.dvd_mul, Nat.dvd_prime prime_2, Nat.dvd_prime prime_53, Nat.dvd_prime prime_48557021, Nat.dvd_prime prime_63879670991, Nat.dvd_prime prime_7241729240142017205097, hq.ne_one, false_or] at hqd
  rcases hqd with ((((rfl | rfl) | rfl) | rfl) | rfl)
  · change (5 : ZMod 2381018959592823667713667654121769861082703) ^ 1190509479796411833856833827060884930541351 ≠ 1
    rw [h1190509479796411833856833827060884930541351]
    decide +kernel
  · change (5 : ZMod 2381018959592823667713667654121769861082703) ^ 44924886030053276749314484040033393605334 ≠ 1
    rw [h44924886030053276749314484040033393605334]
    decide +kernel
  · change (5 : ZMod 2381018959592823667713667654121769861082703) ^ 49035523814214707852725719193559462 ≠ 1
    rw [h49035523814214707852725719193559462]
    decide +kernel
  · change (5 : ZMod 2381018959592823667713667654121769861082703) ^ 37273500671728337075487171619922 ≠ 1
    rw [h37273500671728337075487171619922]
    decide +kernel
  · change (5 : ZMod 2381018959592823667713667654121769861082703) ^ 328791491733006247966 ≠ 1
    rw [h328791491733006247966]
    decide +kernel

#print axioms prime_2381018959592823667713667654121769861082703

open Erdos406SimpleRootValuation Erdos406DigitSumValuation

lemma monic_norm_eval_outside_gt_one (Q : ℂ[X]) (hQ : Q.Monic)
    (hdeg : 0 < Q.natDegree) (hroot : ∀ z ∈ Q.roots, ‖z‖ < 2)
    (a : ℂ) (ha : 3 ≤ ‖a‖) :
    1 < ‖Q.eval a‖ := by
  have hsplit := IsAlgClosed.splits Q
  rw [hsplit.eval_eq_prod_roots_of_monic hQ]
  apply one_lt_norm_multiset_prod
  · have hcard : 0 < (Q.roots.map (fun z => a - z)).card := by
      rw [Multiset.card_map, ← hsplit.natDegree_eq_card_roots]
      exact hdeg
    intro hh
    simp [hh] at hcard
  · intro z hz
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp hz
    have hh := norm_sub_norm_le a b
    have hr := hroot b hb
    linarith

/-- A prime absolute evaluation outside the root disk certifies irreducibility.
This is valid at negative as well as positive evaluation points. -/
lemma irreducible_of_natAbs_eval_prime (P : ℤ[X]) (p : ℕ) (a : ℤ)
    (hP : P.Monic) (hp : Nat.Prime p) (heval : (P.eval a).natAbs = p)
    (ha : 3 ≤ |a|)
    (hroots : ∀ z ∈ (P.map (Int.castRingHom ℂ)).roots, ‖z‖ < 2) :
    Irreducible P := by
  have hP1 : P ≠ 1 := by
    intro h
    have hh := heval
    rw [h] at hh
    simp only [eval_one, Int.natAbs_one] at hh
    exact hp.ne_one hh.symm
  have hfactor (Q : ℤ[X]) (hQ : Q.Monic) (hd : Q ∣ P) (hne : Q ≠ 1) :
      1 < (Q.eval a).natAbs := by
    have hQr : ∀ z ∈ (Q.map (Int.castRingHom ℂ)).roots, ‖z‖ < 2 := by
      intro z hz
      apply hroots z
      apply (mem_roots (hP.map _).ne_zero).mpr
      have hh := (mem_roots (hQ.map _).ne_zero).mp hz
      have hv := eval_dvd (x := z) (map_dvd (Int.castRingHom ℂ) hd)
      change (Q.map (Int.castRingHom ℂ)).eval z = 0 at hh
      rwa [hh, zero_dvd_iff] at hv
    have hdeg : 0 < Q.natDegree := hQ.natDegree_pos_of_not_isUnit (by simpa [hQ.isUnit_iff])
    have han : 3 ≤ ‖(a : ℂ)‖ := by
      rw [Complex.norm_intCast]
      exact_mod_cast ha
    have hh := monic_norm_eval_outside_gt_one (Q.map (Int.castRingHom ℂ)) (hQ.map _)
      (by rwa [hQ.natDegree_map]) hQr (a : ℂ) han
    have he : (Q.map (Int.castRingHom ℂ)).eval (a : ℂ) = ((Q.eval a : ℤ) : ℂ) := by
      rw [eval_map]
      exact eval₂_at_apply (Int.castRingHom ℂ) a
    rw [he, Complex.norm_intCast] at hh
    have hZ : (1 : ℤ) < |Q.eval a| := by exact_mod_cast hh
    rw [← Int.natCast_natAbs] at hZ
    exact_mod_cast hZ
  apply (irreducible_of_monic hP hP1).mpr
  intro Q R hQ hR he
  by_cases hQ1 : Q = 1
  · exact Or.inl hQ1
  by_cases hR1 : R = 1
  · exact Or.inr hR1
  have hq := hfactor Q hQ (by rw [← he]; exact dvd_mul_right _ _) hQ1
  have hr := hfactor R hR (by rw [← he]; exact dvd_mul_left _ _) hR1
  have hv := congrArg (fun F : ℤ[X] => (F.eval a).natAbs) he
  dsimp only at hv
  rw [eval_mul, Int.natAbs_mul, heval] at hv
  have hd : (Q.eval a).natAbs ∣ p := ⟨(R.eval a).natAbs, hv.symm⟩
  rcases (Nat.dvd_prime hp).mp hd with h1 | hpeq
  · omega
  · have hp0 := hp.pos
    nlinarith

lemma exampleP_monic : exampleP.Monic := by
  have hn : Nat.digits 3 exampleN ≠ [] := by decide +kernel
  have hl : (Nat.digits 3 exampleN).getLast hn = 1 := by decide +kernel +revert
  exact (digitPoly_isMonicOfDegree _ hn hl).monic

lemma exampleP_roots (z : ℂ) (hz : z ∈ (exampleP.map (Int.castRingHom ℂ)).roots) :
    ‖z‖ < 2 := by
  have hh := (mem_roots (exampleP_monic.map _).ne_zero).mp hz
  change (exampleP.map (Int.castRingHom ℂ)).eval z = 0 at hh
  rw [exampleP, eval_map_digitPoly_complex] at hh
  have he : Nat.digits 3 exampleN = (Nat.digits 3 exampleN).dropLast ++ [1] := by
    decide +kernel
  rw [he] at hh
  have hb := Erdos406Newman.upper_root_bound z (Nat.digits 3 exampleN).dropLast
    (by decide +kernel) hh
  have hn := norm_nonneg z
  nlinarith

lemma exampleP_eval_negative_fourteen :
    (exampleP.eval (-14)).natAbs = 2381018959592823667713667654121769861082703 := by
  rw [exampleP, eval_digitPoly]
  decide +kernel

lemma exampleP_irreducible : Irreducible exampleP :=
  irreducible_of_natAbs_eval_prime exampleP _ (-14) exampleP_monic
    prime_2381018959592823667713667654121769861082703 exampleP_eval_negative_fourteen
    (by norm_num) exampleP_roots

/-- Irreducibility does not rescue the tested general estimate. The pure-power
value hypothesis is absent and cannot be inferred for this example. -/
theorem irreducible_simple_root_degree_bound_false :
    ¬ (∀ n : ℕ, 0 < n → Nat.digits 3 n ⊆ [0, 1] →
      Irreducible (digitPoly (Nat.digits 3 n)) →
      SimpleOne (digitPoly (Nat.digits 3 n)) →
      padicValNat 2 n ≤ (digitPoly (Nat.digits 3 n)).natDegree + 9) := by
  intro h
  have hh := h exampleN (by decide) example_digits.1
    exampleP_irreducible exampleP_simple_one
  change padicValNat 2 exampleN ≤ exampleP.natDegree + 9 at hh
  rw [example_valuation, exampleP_degree] at hh
  omega

/-- The odd valuation also prevents this example from testing a square-value
version of the proposed estimate. -/
lemma exampleN_not_square : ¬ IsSquare exampleN := by
  rintro ⟨a, ha⟩
  have hane : a ≠ 0 := by
    intro hz
    rw [hz] at ha
    norm_num [exampleN] at ha
  have hh := example_valuation
  rw [ha, padicValNat.mul hane hane] at hh
  omega

#print axioms exampleN_not_square
#print axioms irreducible_of_natAbs_eval_prime
#print axioms exampleP_irreducible
#print axioms irreducible_simple_root_degree_bound_false

end Erdos406IrreducibleValuation

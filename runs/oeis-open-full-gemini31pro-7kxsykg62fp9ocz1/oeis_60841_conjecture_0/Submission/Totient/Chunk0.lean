import Submission.Totient.Base
open Nat Finset Rat

set_option maxHeartbeats 200000000
set_option maxRecDepth 20000000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

theorem tot_1 : totient 1 = 1 := rfl

theorem v3_phi_1 : v3_fast (totient 1) 100 = v3_phi_list.getD 1 0 := by
  rw [tot_1]
  rfl

theorem tot_2 : totient 2 = 1 := by
  have h : totient 2 = 2 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_2 : v3_fast (totient 2) 100 = v3_phi_list.getD 2 0 := by
  rw [tot_2]
  rfl

theorem tot_3 : totient 3 = 2 := by
  have h : totient 3 = 3 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_3 : v3_fast (totient 3) 100 = v3_phi_list.getD 3 0 := by
  rw [tot_3]
  rfl

theorem tot_4 : totient 4 = 2 := by
  have h : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (2^2 : ℕ) = 4 := by decide
  rw [← heq]
  rw [h]
  try omega

theorem v3_phi_4 : v3_fast (totient 4) 100 = v3_phi_list.getD 4 0 := by
  rw [tot_4]
  rfl

theorem tot_5 : totient 5 = 4 := by
  have h : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_5 : v3_fast (totient 5) 100 = v3_phi_list.getD 5 0 := by
  rw [tot_5]
  rfl

theorem tot_6 : totient 6 = 2 := by
  have heq : (2 * (3) : ℕ) = 6 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3]
  try omega

theorem v3_phi_6 : v3_fast (totient 6) 100 = v3_phi_list.getD 6 0 := by
  rw [tot_6]
  rfl

theorem tot_7 : totient 7 = 6 := by
  have h : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_7 : v3_fast (totient 7) 100 = v3_phi_list.getD 7 0 := by
  rw [tot_7]
  rfl

theorem tot_8 : totient 8 = 4 := by
  have h : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (2^3 : ℕ) = 8 := by decide
  rw [← heq]
  rw [h]
  try omega

theorem v3_phi_8 : v3_fast (totient 8) 100 = v3_phi_list.getD 8 0 := by
  rw [tot_8]
  rfl

theorem tot_9 : totient 9 = 6 := by
  have h : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (3^2 : ℕ) = 9 := by decide
  rw [← heq]
  rw [h]
  try omega

theorem v3_phi_9 : v3_fast (totient 9) 100 = v3_phi_list.getD 9 0 := by
  rw [tot_9]
  rfl

theorem tot_10 : totient 10 = 4 := by
  have heq : (2 * (5) : ℕ) = 10 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5]
  try omega

theorem v3_phi_10 : v3_fast (totient 10) 100 = v3_phi_list.getD 10 0 := by
  rw [tot_10]
  rfl

theorem tot_11 : totient 11 = 10 := by
  have h : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_11 : v3_fast (totient 11) 100 = v3_phi_list.getD 11 0 := by
  rw [tot_11]
  rfl

theorem tot_12 : totient 12 = 4 := by
  have heq : (2^2 * (3) : ℕ) = 12 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3]
  try omega

theorem v3_phi_12 : v3_fast (totient 12) 100 = v3_phi_list.getD 12 0 := by
  rw [tot_12]
  rfl

theorem tot_13 : totient 13 = 12 := by
  have h : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_13 : v3_fast (totient 13) 100 = v3_phi_list.getD 13 0 := by
  rw [tot_13]
  rfl

theorem tot_14 : totient 14 = 6 := by
  have heq : (2 * (7) : ℕ) = 14 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7]
  try omega

theorem v3_phi_14 : v3_fast (totient 14) 100 = v3_phi_list.getD 14 0 := by
  rw [tot_14]
  rfl

theorem tot_15 : totient 15 = 8 := by
  have heq : (3 * (5) : ℕ) = 15 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5]
  try omega

theorem v3_phi_15 : v3_fast (totient 15) 100 = v3_phi_list.getD 15 0 := by
  rw [tot_15]
  rfl

theorem tot_16 : totient 16 = 8 := by
  have h : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (2^4 : ℕ) = 16 := by decide
  rw [← heq]
  rw [h]
  try omega

theorem v3_phi_16 : v3_fast (totient 16) 100 = v3_phi_list.getD 16 0 := by
  rw [tot_16]
  rfl

theorem tot_17 : totient 17 = 16 := by
  have h : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_17 : v3_fast (totient 17) 100 = v3_phi_list.getD 17 0 := by
  rw [tot_17]
  rfl

theorem tot_18 : totient 18 = 6 := by
  have heq : (2 * (3^2) : ℕ) = 18 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3]
  try omega

theorem v3_phi_18 : v3_fast (totient 18) 100 = v3_phi_list.getD 18 0 := by
  rw [tot_18]
  rfl

theorem tot_19 : totient 19 = 18 := by
  have h : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_19 : v3_fast (totient 19) 100 = v3_phi_list.getD 19 0 := by
  rw [tot_19]
  rfl

theorem tot_20 : totient 20 = 8 := by
  have heq : (2^2 * (5) : ℕ) = 20 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5]
  try omega

theorem v3_phi_20 : v3_fast (totient 20) 100 = v3_phi_list.getD 20 0 := by
  rw [tot_20]
  rfl

theorem tot_21 : totient 21 = 12 := by
  have heq : (3 * (7) : ℕ) = 21 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7]
  try omega

theorem v3_phi_21 : v3_fast (totient 21) 100 = v3_phi_list.getD 21 0 := by
  rw [tot_21]
  rfl

theorem tot_22 : totient 22 = 10 := by
  have heq : (2 * (11) : ℕ) = 22 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11]
  try omega

theorem v3_phi_22 : v3_fast (totient 22) 100 = v3_phi_list.getD 22 0 := by
  rw [tot_22]
  rfl

theorem tot_23 : totient 23 = 22 := by
  have h : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_23 : v3_fast (totient 23) 100 = v3_phi_list.getD 23 0 := by
  rw [tot_23]
  rfl

theorem tot_24 : totient 24 = 8 := by
  have heq : (2^3 * (3) : ℕ) = 24 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3]
  try omega

theorem v3_phi_24 : v3_fast (totient 24) 100 = v3_phi_list.getD 24 0 := by
  rw [tot_24]
  rfl

theorem tot_25 : totient 25 = 20 := by
  have h : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (5^2 : ℕ) = 25 := by decide
  rw [← heq]
  rw [h]
  try omega

theorem v3_phi_25 : v3_fast (totient 25) 100 = v3_phi_list.getD 25 0 := by
  rw [tot_25]
  rfl

theorem tot_26 : totient 26 = 12 := by
  have heq : (2 * (13) : ℕ) = 26 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13]
  try omega

theorem v3_phi_26 : v3_fast (totient 26) 100 = v3_phi_list.getD 26 0 := by
  rw [tot_26]
  rfl

theorem tot_27 : totient 27 = 18 := by
  have h : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (3^3 : ℕ) = 27 := by decide
  rw [← heq]
  rw [h]
  try omega

theorem v3_phi_27 : v3_fast (totient 27) 100 = v3_phi_list.getD 27 0 := by
  rw [tot_27]
  rfl

theorem tot_28 : totient 28 = 12 := by
  have heq : (2^2 * (7) : ℕ) = 28 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7]
  try omega

theorem v3_phi_28 : v3_fast (totient 28) 100 = v3_phi_list.getD 28 0 := by
  rw [tot_28]
  rfl

theorem tot_29 : totient 29 = 28 := by
  have h : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_29 : v3_fast (totient 29) 100 = v3_phi_list.getD 29 0 := by
  rw [tot_29]
  rfl

theorem tot_30 : totient 30 = 8 := by
  have heq : (2 * (3 * (5)) : ℕ) = 30 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5]
  try omega

theorem v3_phi_30 : v3_fast (totient 30) 100 = v3_phi_list.getD 30 0 := by
  rw [tot_30]
  rfl

theorem tot_31 : totient 31 = 30 := by
  have h : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_31 : v3_fast (totient 31) 100 = v3_phi_list.getD 31 0 := by
  rw [tot_31]
  rfl

theorem tot_32 : totient 32 = 16 := by
  have h : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (2^5 : ℕ) = 32 := by decide
  rw [← heq]
  rw [h]
  try omega

theorem v3_phi_32 : v3_fast (totient 32) 100 = v3_phi_list.getD 32 0 := by
  rw [tot_32]
  rfl

theorem tot_33 : totient 33 = 20 := by
  have heq : (3 * (11) : ℕ) = 33 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11]
  try omega

theorem v3_phi_33 : v3_fast (totient 33) 100 = v3_phi_list.getD 33 0 := by
  rw [tot_33]
  rfl

theorem tot_34 : totient 34 = 16 := by
  have heq : (2 * (17) : ℕ) = 34 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17]
  try omega

theorem v3_phi_34 : v3_fast (totient 34) 100 = v3_phi_list.getD 34 0 := by
  rw [tot_34]
  rfl

theorem tot_35 : totient 35 = 24 := by
  have heq : (5 * (7) : ℕ) = 35 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_7]
  try omega

theorem v3_phi_35 : v3_fast (totient 35) 100 = v3_phi_list.getD 35 0 := by
  rw [tot_35]
  rfl

theorem tot_36 : totient 36 = 12 := by
  have heq : (2^2 * (3^2) : ℕ) = 36 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3]
  try omega

theorem v3_phi_36 : v3_fast (totient 36) 100 = v3_phi_list.getD 36 0 := by
  rw [tot_36]
  rfl

theorem tot_37 : totient 37 = 36 := by
  have h : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_37 : v3_fast (totient 37) 100 = v3_phi_list.getD 37 0 := by
  rw [tot_37]
  rfl

theorem tot_38 : totient 38 = 18 := by
  have heq : (2 * (19) : ℕ) = 38 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_19]
  try omega

theorem v3_phi_38 : v3_fast (totient 38) 100 = v3_phi_list.getD 38 0 := by
  rw [tot_38]
  rfl

theorem tot_39 : totient 39 = 24 := by
  have heq : (3 * (13) : ℕ) = 39 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_13]
  try omega

theorem v3_phi_39 : v3_fast (totient 39) 100 = v3_phi_list.getD 39 0 := by
  rw [tot_39]
  rfl

theorem tot_40 : totient 40 = 16 := by
  have heq : (2^3 * (5) : ℕ) = 40 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5]
  try omega

theorem v3_phi_40 : v3_fast (totient 40) 100 = v3_phi_list.getD 40 0 := by
  rw [tot_40]
  rfl

theorem tot_41 : totient 41 = 40 := by
  have h : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_41 : v3_fast (totient 41) 100 = v3_phi_list.getD 41 0 := by
  rw [tot_41]
  rfl

theorem tot_42 : totient 42 = 12 := by
  have heq : (2 * (3 * (7)) : ℕ) = 42 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7]
  try omega

theorem v3_phi_42 : v3_fast (totient 42) 100 = v3_phi_list.getD 42 0 := by
  rw [tot_42]
  rfl

theorem tot_43 : totient 43 = 42 := by
  have h : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_43 : v3_fast (totient 43) 100 = v3_phi_list.getD 43 0 := by
  rw [tot_43]
  rfl

theorem tot_44 : totient 44 = 20 := by
  have heq : (2^2 * (11) : ℕ) = 44 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11]
  try omega

theorem v3_phi_44 : v3_fast (totient 44) 100 = v3_phi_list.getD 44 0 := by
  rw [tot_44]
  rfl

theorem tot_45 : totient 45 = 24 := by
  have heq : (3^2 * (5) : ℕ) = 45 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5]
  try omega

theorem v3_phi_45 : v3_fast (totient 45) 100 = v3_phi_list.getD 45 0 := by
  rw [tot_45]
  rfl

theorem tot_46 : totient 46 = 22 := by
  have heq : (2 * (23) : ℕ) = 46 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_23]
  try omega

theorem v3_phi_46 : v3_fast (totient 46) 100 = v3_phi_list.getD 46 0 := by
  rw [tot_46]
  rfl

theorem tot_47 : totient 47 = 46 := by
  have h : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_47 : v3_fast (totient 47) 100 = v3_phi_list.getD 47 0 := by
  rw [tot_47]
  rfl

theorem tot_48 : totient 48 = 16 := by
  have heq : (2^4 * (3) : ℕ) = 48 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3]
  try omega

theorem v3_phi_48 : v3_fast (totient 48) 100 = v3_phi_list.getD 48 0 := by
  rw [tot_48]
  rfl

theorem tot_49 : totient 49 = 42 := by
  have h : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (7^2 : ℕ) = 49 := by decide
  rw [← heq]
  rw [h]
  try omega

theorem v3_phi_49 : v3_fast (totient 49) 100 = v3_phi_list.getD 49 0 := by
  rw [tot_49]
  rfl

theorem tot_50 : totient 50 = 20 := by
  have heq : (2 * (5^2) : ℕ) = 50 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_5]
  try omega

theorem v3_phi_50 : v3_fast (totient 50) 100 = v3_phi_list.getD 50 0 := by
  rw [tot_50]
  rfl

theorem tot_51 : totient 51 = 32 := by
  have heq : (3 * (17) : ℕ) = 51 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_17]
  try omega

theorem v3_phi_51 : v3_fast (totient 51) 100 = v3_phi_list.getD 51 0 := by
  rw [tot_51]
  rfl

theorem tot_52 : totient 52 = 24 := by
  have heq : (2^2 * (13) : ℕ) = 52 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13]
  try omega

theorem v3_phi_52 : v3_fast (totient 52) 100 = v3_phi_list.getD 52 0 := by
  rw [tot_52]
  rfl

theorem tot_53 : totient 53 = 52 := by
  have h : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_53 : v3_fast (totient 53) 100 = v3_phi_list.getD 53 0 := by
  rw [tot_53]
  rfl

theorem tot_54 : totient 54 = 18 := by
  have heq : (2 * (3^3) : ℕ) = 54 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3]
  try omega

theorem v3_phi_54 : v3_fast (totient 54) 100 = v3_phi_list.getD 54 0 := by
  rw [tot_54]
  rfl

theorem tot_55 : totient 55 = 40 := by
  have heq : (5 * (11) : ℕ) = 55 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_11]
  try omega

theorem v3_phi_55 : v3_fast (totient 55) 100 = v3_phi_list.getD 55 0 := by
  rw [tot_55]
  rfl

theorem tot_56 : totient 56 = 24 := by
  have heq : (2^3 * (7) : ℕ) = 56 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7]
  try omega

theorem v3_phi_56 : v3_fast (totient 56) 100 = v3_phi_list.getD 56 0 := by
  rw [tot_56]
  rfl

theorem tot_57 : totient 57 = 36 := by
  have heq : (3 * (19) : ℕ) = 57 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_19]
  try omega

theorem v3_phi_57 : v3_fast (totient 57) 100 = v3_phi_list.getD 57 0 := by
  rw [tot_57]
  rfl

theorem tot_58 : totient 58 = 28 := by
  have heq : (2 * (29) : ℕ) = 58 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_29]
  try omega

theorem v3_phi_58 : v3_fast (totient 58) 100 = v3_phi_list.getD 58 0 := by
  rw [tot_58]
  rfl

theorem tot_59 : totient 59 = 58 := by
  have h : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_59 : v3_fast (totient 59) 100 = v3_phi_list.getD 59 0 := by
  rw [tot_59]
  rfl

theorem tot_60 : totient 60 = 16 := by
  have heq : (2^2 * (3 * (5)) : ℕ) = 60 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5]
  try omega

theorem v3_phi_60 : v3_fast (totient 60) 100 = v3_phi_list.getD 60 0 := by
  rw [tot_60]
  rfl

theorem tot_61 : totient 61 = 60 := by
  have h : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_61 : v3_fast (totient 61) 100 = v3_phi_list.getD 61 0 := by
  rw [tot_61]
  rfl

theorem tot_62 : totient 62 = 30 := by
  have heq : (2 * (31) : ℕ) = 62 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_31]
  try omega

theorem v3_phi_62 : v3_fast (totient 62) 100 = v3_phi_list.getD 62 0 := by
  rw [tot_62]
  rfl

theorem tot_63 : totient 63 = 36 := by
  have heq : (3^2 * (7) : ℕ) = 63 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7]
  try omega

theorem v3_phi_63 : v3_fast (totient 63) 100 = v3_phi_list.getD 63 0 := by
  rw [tot_63]
  rfl

theorem tot_64 : totient 64 = 32 := by
  have h : totient (2^6) = 2^5 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (2^6 : ℕ) = 64 := by decide
  rw [← heq]
  rw [h]
  try omega

theorem v3_phi_64 : v3_fast (totient 64) 100 = v3_phi_list.getD 64 0 := by
  rw [tot_64]
  rfl

theorem tot_65 : totient 65 = 48 := by
  have heq : (5 * (13) : ℕ) = 65 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_13]
  try omega

theorem v3_phi_65 : v3_fast (totient 65) 100 = v3_phi_list.getD 65 0 := by
  rw [tot_65]
  rfl

theorem tot_66 : totient 66 = 20 := by
  have heq : (2 * (3 * (11)) : ℕ) = 66 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11]
  try omega

theorem v3_phi_66 : v3_fast (totient 66) 100 = v3_phi_list.getD 66 0 := by
  rw [tot_66]
  rfl

theorem tot_67 : totient 67 = 66 := by
  have h : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_67 : v3_fast (totient 67) 100 = v3_phi_list.getD 67 0 := by
  rw [tot_67]
  rfl

theorem tot_68 : totient 68 = 32 := by
  have heq : (2^2 * (17) : ℕ) = 68 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17]
  try omega

theorem v3_phi_68 : v3_fast (totient 68) 100 = v3_phi_list.getD 68 0 := by
  rw [tot_68]
  rfl

theorem tot_69 : totient 69 = 44 := by
  have heq : (3 * (23) : ℕ) = 69 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_23]
  try omega

theorem v3_phi_69 : v3_fast (totient 69) 100 = v3_phi_list.getD 69 0 := by
  rw [tot_69]
  rfl

theorem tot_70 : totient 70 = 24 := by
  have heq : (2 * (5 * (7)) : ℕ) = 70 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7]
  try omega

theorem v3_phi_70 : v3_fast (totient 70) 100 = v3_phi_list.getD 70 0 := by
  rw [tot_70]
  rfl

theorem tot_71 : totient 71 = 70 := by
  have h : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_71 : v3_fast (totient 71) 100 = v3_phi_list.getD 71 0 := by
  rw [tot_71]
  rfl

theorem tot_72 : totient 72 = 24 := by
  have heq : (2^3 * (3^2) : ℕ) = 72 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3]
  try omega

theorem v3_phi_72 : v3_fast (totient 72) 100 = v3_phi_list.getD 72 0 := by
  rw [tot_72]
  rfl

theorem tot_73 : totient 73 = 72 := by
  have h : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_73 : v3_fast (totient 73) 100 = v3_phi_list.getD 73 0 := by
  rw [tot_73]
  rfl

theorem tot_74 : totient 74 = 36 := by
  have heq : (2 * (37) : ℕ) = 74 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_37]
  try omega

theorem v3_phi_74 : v3_fast (totient 74) 100 = v3_phi_list.getD 74 0 := by
  rw [tot_74]
  rfl

theorem tot_75 : totient 75 = 40 := by
  have heq : (3 * (5^2) : ℕ) = 75 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_5]
  try omega

theorem v3_phi_75 : v3_fast (totient 75) 100 = v3_phi_list.getD 75 0 := by
  rw [tot_75]
  rfl

theorem tot_76 : totient 76 = 36 := by
  have heq : (2^2 * (19) : ℕ) = 76 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_19]
  try omega

theorem v3_phi_76 : v3_fast (totient 76) 100 = v3_phi_list.getD 76 0 := by
  rw [tot_76]
  rfl

theorem tot_77 : totient 77 = 60 := by
  have heq : (7 * (11) : ℕ) = 77 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_11]
  try omega

theorem v3_phi_77 : v3_fast (totient 77) 100 = v3_phi_list.getD 77 0 := by
  rw [tot_77]
  rfl

theorem tot_78 : totient 78 = 24 := by
  have heq : (2 * (3 * (13)) : ℕ) = 78 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_13]
  try omega

theorem v3_phi_78 : v3_fast (totient 78) 100 = v3_phi_list.getD 78 0 := by
  rw [tot_78]
  rfl

theorem tot_79 : totient 79 = 78 := by
  have h : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_79 : v3_fast (totient 79) 100 = v3_phi_list.getD 79 0 := by
  rw [tot_79]
  rfl

theorem tot_80 : totient 80 = 32 := by
  have heq : (2^4 * (5) : ℕ) = 80 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5]
  try omega

theorem v3_phi_80 : v3_fast (totient 80) 100 = v3_phi_list.getD 80 0 := by
  rw [tot_80]
  rfl

theorem tot_81 : totient 81 = 54 := by
  have h : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (3^4 : ℕ) = 81 := by decide
  rw [← heq]
  rw [h]
  try omega

theorem v3_phi_81 : v3_fast (totient 81) 100 = v3_phi_list.getD 81 0 := by
  rw [tot_81]
  rfl

theorem tot_82 : totient 82 = 40 := by
  have heq : (2 * (41) : ℕ) = 82 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_41]
  try omega

theorem v3_phi_82 : v3_fast (totient 82) 100 = v3_phi_list.getD 82 0 := by
  rw [tot_82]
  rfl

theorem tot_83 : totient 83 = 82 := by
  have h : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_83 : v3_fast (totient 83) 100 = v3_phi_list.getD 83 0 := by
  rw [tot_83]
  rfl

theorem tot_84 : totient 84 = 24 := by
  have heq : (2^2 * (3 * (7)) : ℕ) = 84 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7]
  try omega

theorem v3_phi_84 : v3_fast (totient 84) 100 = v3_phi_list.getD 84 0 := by
  rw [tot_84]
  rfl

theorem tot_85 : totient 85 = 64 := by
  have heq : (5 * (17) : ℕ) = 85 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_17]
  try omega

theorem v3_phi_85 : v3_fast (totient 85) 100 = v3_phi_list.getD 85 0 := by
  rw [tot_85]
  rfl

theorem tot_86 : totient 86 = 42 := by
  have heq : (2 * (43) : ℕ) = 86 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_43]
  try omega

theorem v3_phi_86 : v3_fast (totient 86) 100 = v3_phi_list.getD 86 0 := by
  rw [tot_86]
  rfl

theorem tot_87 : totient 87 = 56 := by
  have heq : (3 * (29) : ℕ) = 87 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_29]
  try omega

theorem v3_phi_87 : v3_fast (totient 87) 100 = v3_phi_list.getD 87 0 := by
  rw [tot_87]
  rfl

theorem tot_88 : totient 88 = 40 := by
  have heq : (2^3 * (11) : ℕ) = 88 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11]
  try omega

theorem v3_phi_88 : v3_fast (totient 88) 100 = v3_phi_list.getD 88 0 := by
  rw [tot_88]
  rfl

theorem tot_89 : totient 89 = 88 := by
  have h : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_89 : v3_fast (totient 89) 100 = v3_phi_list.getD 89 0 := by
  rw [tot_89]
  rfl

theorem tot_90 : totient 90 = 24 := by
  have heq : (2 * (3^2 * (5)) : ℕ) = 90 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5]
  try omega

theorem v3_phi_90 : v3_fast (totient 90) 100 = v3_phi_list.getD 90 0 := by
  rw [tot_90]
  rfl

theorem tot_91 : totient 91 = 72 := by
  have heq : (7 * (13) : ℕ) = 91 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_13]
  try omega

theorem v3_phi_91 : v3_fast (totient 91) 100 = v3_phi_list.getD 91 0 := by
  rw [tot_91]
  rfl

theorem tot_92 : totient 92 = 44 := by
  have heq : (2^2 * (23) : ℕ) = 92 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_23]
  try omega

theorem v3_phi_92 : v3_fast (totient 92) 100 = v3_phi_list.getD 92 0 := by
  rw [tot_92]
  rfl

theorem tot_93 : totient 93 = 60 := by
  have heq : (3 * (31) : ℕ) = 93 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_31]
  try omega

theorem v3_phi_93 : v3_fast (totient 93) 100 = v3_phi_list.getD 93 0 := by
  rw [tot_93]
  rfl

theorem tot_94 : totient 94 = 46 := by
  have heq : (2 * (47) : ℕ) = 94 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_47]
  try omega

theorem v3_phi_94 : v3_fast (totient 94) 100 = v3_phi_list.getD 94 0 := by
  rw [tot_94]
  rfl

theorem tot_95 : totient 95 = 72 := by
  have heq : (5 * (19) : ℕ) = 95 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_19]
  try omega

theorem v3_phi_95 : v3_fast (totient 95) 100 = v3_phi_list.getD 95 0 := by
  rw [tot_95]
  rfl

theorem tot_96 : totient 96 = 32 := by
  have heq : (2^5 * (3) : ℕ) = 96 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3]
  try omega

theorem v3_phi_96 : v3_fast (totient 96) 100 = v3_phi_list.getD 96 0 := by
  rw [tot_96]
  rfl

theorem tot_97 : totient 97 = 96 := by
  have h : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_97 : v3_fast (totient 97) 100 = v3_phi_list.getD 97 0 := by
  rw [tot_97]
  rfl

theorem tot_98 : totient 98 = 42 := by
  have heq : (2 * (7^2) : ℕ) = 98 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_7]
  try omega

theorem v3_phi_98 : v3_fast (totient 98) 100 = v3_phi_list.getD 98 0 := by
  rw [tot_98]
  rfl

theorem tot_99 : totient 99 = 60 := by
  have heq : (3^2 * (11) : ℕ) = 99 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11]
  try omega

theorem v3_phi_99 : v3_fast (totient 99) 100 = v3_phi_list.getD 99 0 := by
  rw [tot_99]
  rfl

theorem tot_100 : totient 100 = 40 := by
  have heq : (2^2 * (5^2) : ℕ) = 100 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_5]
  try omega

theorem v3_phi_100 : v3_fast (totient 100) 100 = v3_phi_list.getD 100 0 := by
  rw [tot_100]
  rfl

theorem tot_101 : totient 101 = 100 := by
  have h : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_101 : v3_fast (totient 101) 100 = v3_phi_list.getD 101 0 := by
  rw [tot_101]
  rfl

theorem tot_102 : totient 102 = 32 := by
  have heq : (2 * (3 * (17)) : ℕ) = 102 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_17]
  try omega

theorem v3_phi_102 : v3_fast (totient 102) 100 = v3_phi_list.getD 102 0 := by
  rw [tot_102]
  rfl

theorem tot_103 : totient 103 = 102 := by
  have h : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_103 : v3_fast (totient 103) 100 = v3_phi_list.getD 103 0 := by
  rw [tot_103]
  rfl

theorem tot_104 : totient 104 = 48 := by
  have heq : (2^3 * (13) : ℕ) = 104 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13]
  try omega

theorem v3_phi_104 : v3_fast (totient 104) 100 = v3_phi_list.getD 104 0 := by
  rw [tot_104]
  rfl

theorem tot_105 : totient 105 = 48 := by
  have heq : (3 * (5 * (7)) : ℕ) = 105 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_7]
  try omega

theorem v3_phi_105 : v3_fast (totient 105) 100 = v3_phi_list.getD 105 0 := by
  rw [tot_105]
  rfl

theorem tot_106 : totient 106 = 52 := by
  have heq : (2 * (53) : ℕ) = 106 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_53]
  try omega

theorem v3_phi_106 : v3_fast (totient 106) 100 = v3_phi_list.getD 106 0 := by
  rw [tot_106]
  rfl

theorem tot_107 : totient 107 = 106 := by
  have h : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_107 : v3_fast (totient 107) 100 = v3_phi_list.getD 107 0 := by
  rw [tot_107]
  rfl

theorem tot_108 : totient 108 = 36 := by
  have heq : (2^2 * (3^3) : ℕ) = 108 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3]
  try omega

theorem v3_phi_108 : v3_fast (totient 108) 100 = v3_phi_list.getD 108 0 := by
  rw [tot_108]
  rfl

theorem tot_109 : totient 109 = 108 := by
  have h : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_109 : v3_fast (totient 109) 100 = v3_phi_list.getD 109 0 := by
  rw [tot_109]
  rfl

theorem tot_110 : totient 110 = 40 := by
  have heq : (2 * (5 * (11)) : ℕ) = 110 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_11]
  try omega

theorem v3_phi_110 : v3_fast (totient 110) 100 = v3_phi_list.getD 110 0 := by
  rw [tot_110]
  rfl

theorem tot_111 : totient 111 = 72 := by
  have heq : (3 * (37) : ℕ) = 111 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_37]
  try omega

theorem v3_phi_111 : v3_fast (totient 111) 100 = v3_phi_list.getD 111 0 := by
  rw [tot_111]
  rfl

theorem tot_112 : totient 112 = 48 := by
  have heq : (2^4 * (7) : ℕ) = 112 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7]
  try omega

theorem v3_phi_112 : v3_fast (totient 112) 100 = v3_phi_list.getD 112 0 := by
  rw [tot_112]
  rfl

theorem tot_113 : totient 113 = 112 := by
  have h : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_113 : v3_fast (totient 113) 100 = v3_phi_list.getD 113 0 := by
  rw [tot_113]
  rfl

theorem tot_114 : totient 114 = 36 := by
  have heq : (2 * (3 * (19)) : ℕ) = 114 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_19]
  try omega

theorem v3_phi_114 : v3_fast (totient 114) 100 = v3_phi_list.getD 114 0 := by
  rw [tot_114]
  rfl

theorem tot_115 : totient 115 = 88 := by
  have heq : (5 * (23) : ℕ) = 115 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_23]
  try omega

theorem v3_phi_115 : v3_fast (totient 115) 100 = v3_phi_list.getD 115 0 := by
  rw [tot_115]
  rfl

theorem tot_116 : totient 116 = 56 := by
  have heq : (2^2 * (29) : ℕ) = 116 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_29]
  try omega

theorem v3_phi_116 : v3_fast (totient 116) 100 = v3_phi_list.getD 116 0 := by
  rw [tot_116]
  rfl

theorem tot_117 : totient 117 = 72 := by
  have heq : (3^2 * (13) : ℕ) = 117 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_13]
  try omega

theorem v3_phi_117 : v3_fast (totient 117) 100 = v3_phi_list.getD 117 0 := by
  rw [tot_117]
  rfl

theorem tot_118 : totient 118 = 58 := by
  have heq : (2 * (59) : ℕ) = 118 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_59]
  try omega

theorem v3_phi_118 : v3_fast (totient 118) 100 = v3_phi_list.getD 118 0 := by
  rw [tot_118]
  rfl

theorem tot_119 : totient 119 = 96 := by
  have heq : (7 * (17) : ℕ) = 119 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_17]
  try omega

theorem v3_phi_119 : v3_fast (totient 119) 100 = v3_phi_list.getD 119 0 := by
  rw [tot_119]
  rfl

theorem tot_120 : totient 120 = 32 := by
  have heq : (2^3 * (3 * (5)) : ℕ) = 120 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5]
  try omega

theorem v3_phi_120 : v3_fast (totient 120) 100 = v3_phi_list.getD 120 0 := by
  rw [tot_120]
  rfl

theorem tot_121 : totient 121 = 110 := by
  have h : totient (11^2) = 11^1 * (11 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (11^2 : ℕ) = 121 := by decide
  rw [← heq]
  rw [h]
  try omega

theorem v3_phi_121 : v3_fast (totient 121) 100 = v3_phi_list.getD 121 0 := by
  rw [tot_121]
  rfl

theorem tot_122 : totient 122 = 60 := by
  have heq : (2 * (61) : ℕ) = 122 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_61]
  try omega

theorem v3_phi_122 : v3_fast (totient 122) 100 = v3_phi_list.getD 122 0 := by
  rw [tot_122]
  rfl

theorem tot_123 : totient 123 = 80 := by
  have heq : (3 * (41) : ℕ) = 123 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_41]
  try omega

theorem v3_phi_123 : v3_fast (totient 123) 100 = v3_phi_list.getD 123 0 := by
  rw [tot_123]
  rfl

theorem tot_124 : totient 124 = 60 := by
  have heq : (2^2 * (31) : ℕ) = 124 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_31]
  try omega

theorem v3_phi_124 : v3_fast (totient 124) 100 = v3_phi_list.getD 124 0 := by
  rw [tot_124]
  rfl

theorem tot_125 : totient 125 = 100 := by
  have h : totient (5^3) = 5^2 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (5^3 : ℕ) = 125 := by decide
  rw [← heq]
  rw [h]
  try omega

theorem v3_phi_125 : v3_fast (totient 125) 100 = v3_phi_list.getD 125 0 := by
  rw [tot_125]
  rfl

theorem tot_126 : totient 126 = 36 := by
  have heq : (2 * (3^2 * (7)) : ℕ) = 126 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7]
  try omega

theorem v3_phi_126 : v3_fast (totient 126) 100 = v3_phi_list.getD 126 0 := by
  rw [tot_126]
  rfl

theorem tot_127 : totient 127 = 126 := by
  have h : totient 127 = 127 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_127 : v3_fast (totient 127) 100 = v3_phi_list.getD 127 0 := by
  rw [tot_127]
  rfl

theorem tot_128 : totient 128 = 64 := by
  have h : totient (2^7) = 2^6 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (2^7 : ℕ) = 128 := by decide
  rw [← heq]
  rw [h]
  try omega

theorem v3_phi_128 : v3_fast (totient 128) 100 = v3_phi_list.getD 128 0 := by
  rw [tot_128]
  rfl

theorem tot_129 : totient 129 = 84 := by
  have heq : (3 * (43) : ℕ) = 129 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_43]
  try omega

theorem v3_phi_129 : v3_fast (totient 129) 100 = v3_phi_list.getD 129 0 := by
  rw [tot_129]
  rfl

theorem tot_130 : totient 130 = 48 := by
  have heq : (2 * (5 * (13)) : ℕ) = 130 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_13]
  try omega

theorem v3_phi_130 : v3_fast (totient 130) 100 = v3_phi_list.getD 130 0 := by
  rw [tot_130]
  rfl

theorem tot_131 : totient 131 = 130 := by
  have h : totient 131 = 131 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_131 : v3_fast (totient 131) 100 = v3_phi_list.getD 131 0 := by
  rw [tot_131]
  rfl

theorem tot_132 : totient 132 = 40 := by
  have heq : (2^2 * (3 * (11)) : ℕ) = 132 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11]
  try omega

theorem v3_phi_132 : v3_fast (totient 132) 100 = v3_phi_list.getD 132 0 := by
  rw [tot_132]
  rfl

theorem tot_133 : totient 133 = 108 := by
  have heq : (7 * (19) : ℕ) = 133 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_19]
  try omega

theorem v3_phi_133 : v3_fast (totient 133) 100 = v3_phi_list.getD 133 0 := by
  rw [tot_133]
  rfl

theorem tot_134 : totient 134 = 66 := by
  have heq : (2 * (67) : ℕ) = 134 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_67]
  try omega

theorem v3_phi_134 : v3_fast (totient 134) 100 = v3_phi_list.getD 134 0 := by
  rw [tot_134]
  rfl

theorem tot_135 : totient 135 = 72 := by
  have heq : (3^3 * (5) : ℕ) = 135 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5]
  try omega

theorem v3_phi_135 : v3_fast (totient 135) 100 = v3_phi_list.getD 135 0 := by
  rw [tot_135]
  rfl

theorem tot_136 : totient 136 = 64 := by
  have heq : (2^3 * (17) : ℕ) = 136 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17]
  try omega

theorem v3_phi_136 : v3_fast (totient 136) 100 = v3_phi_list.getD 136 0 := by
  rw [tot_136]
  rfl

theorem tot_137 : totient 137 = 136 := by
  have h : totient 137 = 137 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_137 : v3_fast (totient 137) 100 = v3_phi_list.getD 137 0 := by
  rw [tot_137]
  rfl

theorem tot_138 : totient 138 = 44 := by
  have heq : (2 * (3 * (23)) : ℕ) = 138 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_23]
  try omega

theorem v3_phi_138 : v3_fast (totient 138) 100 = v3_phi_list.getD 138 0 := by
  rw [tot_138]
  rfl

theorem tot_139 : totient 139 = 138 := by
  have h : totient 139 = 139 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_139 : v3_fast (totient 139) 100 = v3_phi_list.getD 139 0 := by
  rw [tot_139]
  rfl

theorem tot_140 : totient 140 = 48 := by
  have heq : (2^2 * (5 * (7)) : ℕ) = 140 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7]
  try omega

theorem v3_phi_140 : v3_fast (totient 140) 100 = v3_phi_list.getD 140 0 := by
  rw [tot_140]
  rfl

theorem tot_141 : totient 141 = 92 := by
  have heq : (3 * (47) : ℕ) = 141 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_47]
  try omega

theorem v3_phi_141 : v3_fast (totient 141) 100 = v3_phi_list.getD 141 0 := by
  rw [tot_141]
  rfl

theorem tot_142 : totient 142 = 70 := by
  have heq : (2 * (71) : ℕ) = 142 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_71]
  try omega

theorem v3_phi_142 : v3_fast (totient 142) 100 = v3_phi_list.getD 142 0 := by
  rw [tot_142]
  rfl

theorem tot_143 : totient 143 = 120 := by
  have heq : (11 * (13) : ℕ) = 143 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_13]
  try omega

theorem v3_phi_143 : v3_fast (totient 143) 100 = v3_phi_list.getD 143 0 := by
  rw [tot_143]
  rfl

theorem tot_144 : totient 144 = 48 := by
  have heq : (2^4 * (3^2) : ℕ) = 144 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3]
  try omega

theorem v3_phi_144 : v3_fast (totient 144) 100 = v3_phi_list.getD 144 0 := by
  rw [tot_144]
  rfl

theorem tot_145 : totient 145 = 112 := by
  have heq : (5 * (29) : ℕ) = 145 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_29]
  try omega

theorem v3_phi_145 : v3_fast (totient 145) 100 = v3_phi_list.getD 145 0 := by
  rw [tot_145]
  rfl

theorem tot_146 : totient 146 = 72 := by
  have heq : (2 * (73) : ℕ) = 146 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_73]
  try omega

theorem v3_phi_146 : v3_fast (totient 146) 100 = v3_phi_list.getD 146 0 := by
  rw [tot_146]
  rfl

theorem tot_147 : totient 147 = 84 := by
  have heq : (3 * (7^2) : ℕ) = 147 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_7]
  try omega

theorem v3_phi_147 : v3_fast (totient 147) 100 = v3_phi_list.getD 147 0 := by
  rw [tot_147]
  rfl

theorem tot_148 : totient 148 = 72 := by
  have heq : (2^2 * (37) : ℕ) = 148 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_37]
  try omega

theorem v3_phi_148 : v3_fast (totient 148) 100 = v3_phi_list.getD 148 0 := by
  rw [tot_148]
  rfl

theorem tot_149 : totient 149 = 148 := by
  have h : totient 149 = 149 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_149 : v3_fast (totient 149) 100 = v3_phi_list.getD 149 0 := by
  rw [tot_149]
  rfl

theorem tot_150 : totient 150 = 40 := by
  have heq : (2 * (3 * (5^2)) : ℕ) = 150 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_5]
  try omega

theorem v3_phi_150 : v3_fast (totient 150) 100 = v3_phi_list.getD 150 0 := by
  rw [tot_150]
  rfl

theorem tot_151 : totient 151 = 150 := by
  have h : totient 151 = 151 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_151 : v3_fast (totient 151) 100 = v3_phi_list.getD 151 0 := by
  rw [tot_151]
  rfl

theorem tot_152 : totient 152 = 72 := by
  have heq : (2^3 * (19) : ℕ) = 152 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_19]
  try omega

theorem v3_phi_152 : v3_fast (totient 152) 100 = v3_phi_list.getD 152 0 := by
  rw [tot_152]
  rfl

theorem tot_153 : totient 153 = 96 := by
  have heq : (3^2 * (17) : ℕ) = 153 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_17]
  try omega

theorem v3_phi_153 : v3_fast (totient 153) 100 = v3_phi_list.getD 153 0 := by
  rw [tot_153]
  rfl

theorem tot_154 : totient 154 = 60 := by
  have heq : (2 * (7 * (11)) : ℕ) = 154 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_11]
  try omega

theorem v3_phi_154 : v3_fast (totient 154) 100 = v3_phi_list.getD 154 0 := by
  rw [tot_154]
  rfl

theorem tot_155 : totient 155 = 120 := by
  have heq : (5 * (31) : ℕ) = 155 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_31]
  try omega

theorem v3_phi_155 : v3_fast (totient 155) 100 = v3_phi_list.getD 155 0 := by
  rw [tot_155]
  rfl

theorem tot_156 : totient 156 = 48 := by
  have heq : (2^2 * (3 * (13)) : ℕ) = 156 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_13]
  try omega

theorem v3_phi_156 : v3_fast (totient 156) 100 = v3_phi_list.getD 156 0 := by
  rw [tot_156]
  rfl

theorem tot_157 : totient 157 = 156 := by
  have h : totient 157 = 157 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_157 : v3_fast (totient 157) 100 = v3_phi_list.getD 157 0 := by
  rw [tot_157]
  rfl

theorem tot_158 : totient 158 = 78 := by
  have heq : (2 * (79) : ℕ) = 158 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_79]
  try omega

theorem v3_phi_158 : v3_fast (totient 158) 100 = v3_phi_list.getD 158 0 := by
  rw [tot_158]
  rfl

theorem tot_159 : totient 159 = 104 := by
  have heq : (3 * (53) : ℕ) = 159 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_53]
  try omega

theorem v3_phi_159 : v3_fast (totient 159) 100 = v3_phi_list.getD 159 0 := by
  rw [tot_159]
  rfl

theorem tot_160 : totient 160 = 64 := by
  have heq : (2^5 * (5) : ℕ) = 160 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5]
  try omega

theorem v3_phi_160 : v3_fast (totient 160) 100 = v3_phi_list.getD 160 0 := by
  rw [tot_160]
  rfl

theorem tot_161 : totient 161 = 132 := by
  have heq : (7 * (23) : ℕ) = 161 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_23]
  try omega

theorem v3_phi_161 : v3_fast (totient 161) 100 = v3_phi_list.getD 161 0 := by
  rw [tot_161]
  rfl

theorem tot_162 : totient 162 = 54 := by
  have heq : (2 * (3^4) : ℕ) = 162 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3]
  try omega

theorem v3_phi_162 : v3_fast (totient 162) 100 = v3_phi_list.getD 162 0 := by
  rw [tot_162]
  rfl

theorem tot_163 : totient 163 = 162 := by
  have h : totient 163 = 163 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_163 : v3_fast (totient 163) 100 = v3_phi_list.getD 163 0 := by
  rw [tot_163]
  rfl

theorem tot_164 : totient 164 = 80 := by
  have heq : (2^2 * (41) : ℕ) = 164 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_41]
  try omega

theorem v3_phi_164 : v3_fast (totient 164) 100 = v3_phi_list.getD 164 0 := by
  rw [tot_164]
  rfl

theorem tot_165 : totient 165 = 80 := by
  have heq : (3 * (5 * (11)) : ℕ) = 165 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_11]
  try omega

theorem v3_phi_165 : v3_fast (totient 165) 100 = v3_phi_list.getD 165 0 := by
  rw [tot_165]
  rfl

theorem tot_166 : totient 166 = 82 := by
  have heq : (2 * (83) : ℕ) = 166 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_83]
  try omega

theorem v3_phi_166 : v3_fast (totient 166) 100 = v3_phi_list.getD 166 0 := by
  rw [tot_166]
  rfl

theorem tot_167 : totient 167 = 166 := by
  have h : totient 167 = 167 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_167 : v3_fast (totient 167) 100 = v3_phi_list.getD 167 0 := by
  rw [tot_167]
  rfl

theorem tot_168 : totient 168 = 48 := by
  have heq : (2^3 * (3 * (7)) : ℕ) = 168 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7]
  try omega

theorem v3_phi_168 : v3_fast (totient 168) 100 = v3_phi_list.getD 168 0 := by
  rw [tot_168]
  rfl

theorem tot_169 : totient 169 = 156 := by
  have h : totient (13^2) = 13^1 * (13 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (13^2 : ℕ) = 169 := by decide
  rw [← heq]
  rw [h]
  try omega

theorem v3_phi_169 : v3_fast (totient 169) 100 = v3_phi_list.getD 169 0 := by
  rw [tot_169]
  rfl

theorem tot_170 : totient 170 = 64 := by
  have heq : (2 * (5 * (17)) : ℕ) = 170 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_17]
  try omega

theorem v3_phi_170 : v3_fast (totient 170) 100 = v3_phi_list.getD 170 0 := by
  rw [tot_170]
  rfl

theorem tot_171 : totient 171 = 108 := by
  have heq : (3^2 * (19) : ℕ) = 171 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_19]
  try omega

theorem v3_phi_171 : v3_fast (totient 171) 100 = v3_phi_list.getD 171 0 := by
  rw [tot_171]
  rfl

theorem tot_172 : totient 172 = 84 := by
  have heq : (2^2 * (43) : ℕ) = 172 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_43]
  try omega

theorem v3_phi_172 : v3_fast (totient 172) 100 = v3_phi_list.getD 172 0 := by
  rw [tot_172]
  rfl

theorem tot_173 : totient 173 = 172 := by
  have h : totient 173 = 173 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_173 : v3_fast (totient 173) 100 = v3_phi_list.getD 173 0 := by
  rw [tot_173]
  rfl

theorem tot_174 : totient 174 = 56 := by
  have heq : (2 * (3 * (29)) : ℕ) = 174 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_29]
  try omega

theorem v3_phi_174 : v3_fast (totient 174) 100 = v3_phi_list.getD 174 0 := by
  rw [tot_174]
  rfl

theorem tot_175 : totient 175 = 120 := by
  have heq : (5^2 * (7) : ℕ) = 175 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_7]
  try omega

theorem v3_phi_175 : v3_fast (totient 175) 100 = v3_phi_list.getD 175 0 := by
  rw [tot_175]
  rfl

theorem tot_176 : totient 176 = 80 := by
  have heq : (2^4 * (11) : ℕ) = 176 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11]
  try omega

theorem v3_phi_176 : v3_fast (totient 176) 100 = v3_phi_list.getD 176 0 := by
  rw [tot_176]
  rfl

theorem tot_177 : totient 177 = 116 := by
  have heq : (3 * (59) : ℕ) = 177 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_59]
  try omega

theorem v3_phi_177 : v3_fast (totient 177) 100 = v3_phi_list.getD 177 0 := by
  rw [tot_177]
  rfl

theorem tot_178 : totient 178 = 88 := by
  have heq : (2 * (89) : ℕ) = 178 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_89]
  try omega

theorem v3_phi_178 : v3_fast (totient 178) 100 = v3_phi_list.getD 178 0 := by
  rw [tot_178]
  rfl

theorem tot_179 : totient 179 = 178 := by
  have h : totient 179 = 179 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_179 : v3_fast (totient 179) 100 = v3_phi_list.getD 179 0 := by
  rw [tot_179]
  rfl

theorem tot_180 : totient 180 = 48 := by
  have heq : (2^2 * (3^2 * (5)) : ℕ) = 180 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5]
  try omega

theorem v3_phi_180 : v3_fast (totient 180) 100 = v3_phi_list.getD 180 0 := by
  rw [tot_180]
  rfl

theorem tot_181 : totient 181 = 180 := by
  have h : totient 181 = 181 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_181 : v3_fast (totient 181) 100 = v3_phi_list.getD 181 0 := by
  rw [tot_181]
  rfl

theorem tot_182 : totient 182 = 72 := by
  have heq : (2 * (7 * (13)) : ℕ) = 182 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_13]
  try omega

theorem v3_phi_182 : v3_fast (totient 182) 100 = v3_phi_list.getD 182 0 := by
  rw [tot_182]
  rfl

theorem tot_183 : totient 183 = 120 := by
  have heq : (3 * (61) : ℕ) = 183 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_61]
  try omega

theorem v3_phi_183 : v3_fast (totient 183) 100 = v3_phi_list.getD 183 0 := by
  rw [tot_183]
  rfl

theorem tot_184 : totient 184 = 88 := by
  have heq : (2^3 * (23) : ℕ) = 184 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_23]
  try omega

theorem v3_phi_184 : v3_fast (totient 184) 100 = v3_phi_list.getD 184 0 := by
  rw [tot_184]
  rfl

theorem tot_185 : totient 185 = 144 := by
  have heq : (5 * (37) : ℕ) = 185 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_37]
  try omega

theorem v3_phi_185 : v3_fast (totient 185) 100 = v3_phi_list.getD 185 0 := by
  rw [tot_185]
  rfl

theorem tot_186 : totient 186 = 60 := by
  have heq : (2 * (3 * (31)) : ℕ) = 186 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_31]
  try omega

theorem v3_phi_186 : v3_fast (totient 186) 100 = v3_phi_list.getD 186 0 := by
  rw [tot_186]
  rfl

theorem tot_187 : totient 187 = 160 := by
  have heq : (11 * (17) : ℕ) = 187 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_17]
  try omega

theorem v3_phi_187 : v3_fast (totient 187) 100 = v3_phi_list.getD 187 0 := by
  rw [tot_187]
  rfl

theorem tot_188 : totient 188 = 92 := by
  have heq : (2^2 * (47) : ℕ) = 188 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_47]
  try omega

theorem v3_phi_188 : v3_fast (totient 188) 100 = v3_phi_list.getD 188 0 := by
  rw [tot_188]
  rfl

theorem tot_189 : totient 189 = 108 := by
  have heq : (3^3 * (7) : ℕ) = 189 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7]
  try omega

theorem v3_phi_189 : v3_fast (totient 189) 100 = v3_phi_list.getD 189 0 := by
  rw [tot_189]
  rfl

theorem tot_190 : totient 190 = 72 := by
  have heq : (2 * (5 * (19)) : ℕ) = 190 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_19]
  try omega

theorem v3_phi_190 : v3_fast (totient 190) 100 = v3_phi_list.getD 190 0 := by
  rw [tot_190]
  rfl

theorem tot_191 : totient 191 = 190 := by
  have h : totient 191 = 191 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_191 : v3_fast (totient 191) 100 = v3_phi_list.getD 191 0 := by
  rw [tot_191]
  rfl

theorem tot_192 : totient 192 = 64 := by
  have heq : (2^6 * (3) : ℕ) = 192 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^6) = 2^5 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3]
  try omega

theorem v3_phi_192 : v3_fast (totient 192) 100 = v3_phi_list.getD 192 0 := by
  rw [tot_192]
  rfl

theorem tot_193 : totient 193 = 192 := by
  have h : totient 193 = 193 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_193 : v3_fast (totient 193) 100 = v3_phi_list.getD 193 0 := by
  rw [tot_193]
  rfl

theorem tot_194 : totient 194 = 96 := by
  have heq : (2 * (97) : ℕ) = 194 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_97]
  try omega

theorem v3_phi_194 : v3_fast (totient 194) 100 = v3_phi_list.getD 194 0 := by
  rw [tot_194]
  rfl

theorem tot_195 : totient 195 = 96 := by
  have heq : (3 * (5 * (13)) : ℕ) = 195 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_13]
  try omega

theorem v3_phi_195 : v3_fast (totient 195) 100 = v3_phi_list.getD 195 0 := by
  rw [tot_195]
  rfl

theorem tot_196 : totient 196 = 84 := by
  have heq : (2^2 * (7^2) : ℕ) = 196 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_7]
  try omega

theorem v3_phi_196 : v3_fast (totient 196) 100 = v3_phi_list.getD 196 0 := by
  rw [tot_196]
  rfl

theorem tot_197 : totient 197 = 196 := by
  have h : totient 197 = 197 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_197 : v3_fast (totient 197) 100 = v3_phi_list.getD 197 0 := by
  rw [tot_197]
  rfl

theorem tot_198 : totient 198 = 60 := by
  have heq : (2 * (3^2 * (11)) : ℕ) = 198 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11]
  try omega

theorem v3_phi_198 : v3_fast (totient 198) 100 = v3_phi_list.getD 198 0 := by
  rw [tot_198]
  rfl

theorem tot_199 : totient 199 = 198 := by
  have h : totient 199 = 199 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_199 : v3_fast (totient 199) 100 = v3_phi_list.getD 199 0 := by
  rw [tot_199]
  rfl

theorem tot_200 : totient 200 = 80 := by
  have heq : (2^3 * (5^2) : ℕ) = 200 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_5]
  try omega

theorem v3_phi_200 : v3_fast (totient 200) 100 = v3_phi_list.getD 200 0 := by
  rw [tot_200]
  rfl

theorem tot_201 : totient 201 = 132 := by
  have heq : (3 * (67) : ℕ) = 201 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_67]
  try omega

theorem v3_phi_201 : v3_fast (totient 201) 100 = v3_phi_list.getD 201 0 := by
  rw [tot_201]
  rfl

theorem tot_202 : totient 202 = 100 := by
  have heq : (2 * (101) : ℕ) = 202 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_101]
  try omega

theorem v3_phi_202 : v3_fast (totient 202) 100 = v3_phi_list.getD 202 0 := by
  rw [tot_202]
  rfl

theorem tot_203 : totient 203 = 168 := by
  have heq : (7 * (29) : ℕ) = 203 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_29]
  try omega

theorem v3_phi_203 : v3_fast (totient 203) 100 = v3_phi_list.getD 203 0 := by
  rw [tot_203]
  rfl

theorem tot_204 : totient 204 = 64 := by
  have heq : (2^2 * (3 * (17)) : ℕ) = 204 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_17]
  try omega

theorem v3_phi_204 : v3_fast (totient 204) 100 = v3_phi_list.getD 204 0 := by
  rw [tot_204]
  rfl

theorem tot_205 : totient 205 = 160 := by
  have heq : (5 * (41) : ℕ) = 205 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_41]
  try omega

theorem v3_phi_205 : v3_fast (totient 205) 100 = v3_phi_list.getD 205 0 := by
  rw [tot_205]
  rfl

theorem tot_206 : totient 206 = 102 := by
  have heq : (2 * (103) : ℕ) = 206 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_103]
  try omega

theorem v3_phi_206 : v3_fast (totient 206) 100 = v3_phi_list.getD 206 0 := by
  rw [tot_206]
  rfl

theorem tot_207 : totient 207 = 132 := by
  have heq : (3^2 * (23) : ℕ) = 207 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_23]
  try omega

theorem v3_phi_207 : v3_fast (totient 207) 100 = v3_phi_list.getD 207 0 := by
  rw [tot_207]
  rfl

theorem tot_208 : totient 208 = 96 := by
  have heq : (2^4 * (13) : ℕ) = 208 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13]
  try omega

theorem v3_phi_208 : v3_fast (totient 208) 100 = v3_phi_list.getD 208 0 := by
  rw [tot_208]
  rfl

theorem tot_209 : totient 209 = 180 := by
  have heq : (11 * (19) : ℕ) = 209 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_19]
  try omega

theorem v3_phi_209 : v3_fast (totient 209) 100 = v3_phi_list.getD 209 0 := by
  rw [tot_209]
  rfl

theorem tot_210 : totient 210 = 48 := by
  have heq : (2 * (3 * (5 * (7))) : ℕ) = 210 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_7]
  try omega

theorem v3_phi_210 : v3_fast (totient 210) 100 = v3_phi_list.getD 210 0 := by
  rw [tot_210]
  rfl

theorem tot_211 : totient 211 = 210 := by
  have h : totient 211 = 211 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_211 : v3_fast (totient 211) 100 = v3_phi_list.getD 211 0 := by
  rw [tot_211]
  rfl

theorem tot_212 : totient 212 = 104 := by
  have heq : (2^2 * (53) : ℕ) = 212 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_53]
  try omega

theorem v3_phi_212 : v3_fast (totient 212) 100 = v3_phi_list.getD 212 0 := by
  rw [tot_212]
  rfl

theorem tot_213 : totient 213 = 140 := by
  have heq : (3 * (71) : ℕ) = 213 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_71]
  try omega

theorem v3_phi_213 : v3_fast (totient 213) 100 = v3_phi_list.getD 213 0 := by
  rw [tot_213]
  rfl

theorem tot_214 : totient 214 = 106 := by
  have heq : (2 * (107) : ℕ) = 214 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_107]
  try omega

theorem v3_phi_214 : v3_fast (totient 214) 100 = v3_phi_list.getD 214 0 := by
  rw [tot_214]
  rfl

theorem tot_215 : totient 215 = 168 := by
  have heq : (5 * (43) : ℕ) = 215 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_43]
  try omega

theorem v3_phi_215 : v3_fast (totient 215) 100 = v3_phi_list.getD 215 0 := by
  rw [tot_215]
  rfl

theorem tot_216 : totient 216 = 72 := by
  have heq : (2^3 * (3^3) : ℕ) = 216 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3]
  try omega

theorem v3_phi_216 : v3_fast (totient 216) 100 = v3_phi_list.getD 216 0 := by
  rw [tot_216]
  rfl

theorem tot_217 : totient 217 = 180 := by
  have heq : (7 * (31) : ℕ) = 217 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_31]
  try omega

theorem v3_phi_217 : v3_fast (totient 217) 100 = v3_phi_list.getD 217 0 := by
  rw [tot_217]
  rfl

theorem tot_218 : totient 218 = 108 := by
  have heq : (2 * (109) : ℕ) = 218 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_109]
  try omega

theorem v3_phi_218 : v3_fast (totient 218) 100 = v3_phi_list.getD 218 0 := by
  rw [tot_218]
  rfl

theorem tot_219 : totient 219 = 144 := by
  have heq : (3 * (73) : ℕ) = 219 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_73]
  try omega

theorem v3_phi_219 : v3_fast (totient 219) 100 = v3_phi_list.getD 219 0 := by
  rw [tot_219]
  rfl

theorem tot_220 : totient 220 = 80 := by
  have heq : (2^2 * (5 * (11)) : ℕ) = 220 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_11]
  try omega

theorem v3_phi_220 : v3_fast (totient 220) 100 = v3_phi_list.getD 220 0 := by
  rw [tot_220]
  rfl

theorem tot_221 : totient 221 = 192 := by
  have heq : (13 * (17) : ℕ) = 221 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_17]
  try omega

theorem v3_phi_221 : v3_fast (totient 221) 100 = v3_phi_list.getD 221 0 := by
  rw [tot_221]
  rfl

theorem tot_222 : totient 222 = 72 := by
  have heq : (2 * (3 * (37)) : ℕ) = 222 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_37]
  try omega

theorem v3_phi_222 : v3_fast (totient 222) 100 = v3_phi_list.getD 222 0 := by
  rw [tot_222]
  rfl

theorem tot_223 : totient 223 = 222 := by
  have h : totient 223 = 223 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_223 : v3_fast (totient 223) 100 = v3_phi_list.getD 223 0 := by
  rw [tot_223]
  rfl

theorem tot_224 : totient 224 = 96 := by
  have heq : (2^5 * (7) : ℕ) = 224 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7]
  try omega

theorem v3_phi_224 : v3_fast (totient 224) 100 = v3_phi_list.getD 224 0 := by
  rw [tot_224]
  rfl

theorem tot_225 : totient 225 = 120 := by
  have heq : (3^2 * (5^2) : ℕ) = 225 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_5]
  try omega

theorem v3_phi_225 : v3_fast (totient 225) 100 = v3_phi_list.getD 225 0 := by
  rw [tot_225]
  rfl

theorem tot_226 : totient 226 = 112 := by
  have heq : (2 * (113) : ℕ) = 226 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_113 : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_113]
  try omega

theorem v3_phi_226 : v3_fast (totient 226) 100 = v3_phi_list.getD 226 0 := by
  rw [tot_226]
  rfl

theorem tot_227 : totient 227 = 226 := by
  have h : totient 227 = 227 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_227 : v3_fast (totient 227) 100 = v3_phi_list.getD 227 0 := by
  rw [tot_227]
  rfl

theorem tot_228 : totient 228 = 72 := by
  have heq : (2^2 * (3 * (19)) : ℕ) = 228 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_19]
  try omega

theorem v3_phi_228 : v3_fast (totient 228) 100 = v3_phi_list.getD 228 0 := by
  rw [tot_228]
  rfl

theorem tot_229 : totient 229 = 228 := by
  have h : totient 229 = 229 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_229 : v3_fast (totient 229) 100 = v3_phi_list.getD 229 0 := by
  rw [tot_229]
  rfl

theorem tot_230 : totient 230 = 88 := by
  have heq : (2 * (5 * (23)) : ℕ) = 230 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_23]
  try omega

theorem v3_phi_230 : v3_fast (totient 230) 100 = v3_phi_list.getD 230 0 := by
  rw [tot_230]
  rfl

theorem tot_231 : totient 231 = 120 := by
  have heq : (3 * (7 * (11)) : ℕ) = 231 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_11]
  try omega

theorem v3_phi_231 : v3_fast (totient 231) 100 = v3_phi_list.getD 231 0 := by
  rw [tot_231]
  rfl

theorem tot_232 : totient 232 = 112 := by
  have heq : (2^3 * (29) : ℕ) = 232 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_29]
  try omega

theorem v3_phi_232 : v3_fast (totient 232) 100 = v3_phi_list.getD 232 0 := by
  rw [tot_232]
  rfl

theorem tot_233 : totient 233 = 232 := by
  have h : totient 233 = 233 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_233 : v3_fast (totient 233) 100 = v3_phi_list.getD 233 0 := by
  rw [tot_233]
  rfl

theorem tot_234 : totient 234 = 72 := by
  have heq : (2 * (3^2 * (13)) : ℕ) = 234 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_13]
  try omega

theorem v3_phi_234 : v3_fast (totient 234) 100 = v3_phi_list.getD 234 0 := by
  rw [tot_234]
  rfl

theorem tot_235 : totient 235 = 184 := by
  have heq : (5 * (47) : ℕ) = 235 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_47]
  try omega

theorem v3_phi_235 : v3_fast (totient 235) 100 = v3_phi_list.getD 235 0 := by
  rw [tot_235]
  rfl

theorem tot_236 : totient 236 = 116 := by
  have heq : (2^2 * (59) : ℕ) = 236 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_59]
  try omega

theorem v3_phi_236 : v3_fast (totient 236) 100 = v3_phi_list.getD 236 0 := by
  rw [tot_236]
  rfl

theorem tot_237 : totient 237 = 156 := by
  have heq : (3 * (79) : ℕ) = 237 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_79]
  try omega

theorem v3_phi_237 : v3_fast (totient 237) 100 = v3_phi_list.getD 237 0 := by
  rw [tot_237]
  rfl

theorem tot_238 : totient 238 = 96 := by
  have heq : (2 * (7 * (17)) : ℕ) = 238 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_17]
  try omega

theorem v3_phi_238 : v3_fast (totient 238) 100 = v3_phi_list.getD 238 0 := by
  rw [tot_238]
  rfl

theorem tot_239 : totient 239 = 238 := by
  have h : totient 239 = 239 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_239 : v3_fast (totient 239) 100 = v3_phi_list.getD 239 0 := by
  rw [tot_239]
  rfl

theorem tot_240 : totient 240 = 64 := by
  have heq : (2^4 * (3 * (5)) : ℕ) = 240 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5]
  try omega

theorem v3_phi_240 : v3_fast (totient 240) 100 = v3_phi_list.getD 240 0 := by
  rw [tot_240]
  rfl

theorem tot_241 : totient 241 = 240 := by
  have h : totient 241 = 241 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_241 : v3_fast (totient 241) 100 = v3_phi_list.getD 241 0 := by
  rw [tot_241]
  rfl

theorem tot_242 : totient 242 = 110 := by
  have heq : (2 * (11^2) : ℕ) = 242 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient (11^2) = 11^1 * (11 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_11]
  try omega

theorem v3_phi_242 : v3_fast (totient 242) 100 = v3_phi_list.getD 242 0 := by
  rw [tot_242]
  rfl

theorem tot_243 : totient 243 = 162 := by
  have h : totient (3^5) = 3^4 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (3^5 : ℕ) = 243 := by decide
  rw [← heq]
  rw [h]
  try omega

theorem v3_phi_243 : v3_fast (totient 243) 100 = v3_phi_list.getD 243 0 := by
  rw [tot_243]
  rfl

theorem tot_244 : totient 244 = 120 := by
  have heq : (2^2 * (61) : ℕ) = 244 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_61]
  try omega

theorem v3_phi_244 : v3_fast (totient 244) 100 = v3_phi_list.getD 244 0 := by
  rw [tot_244]
  rfl

theorem tot_245 : totient 245 = 168 := by
  have heq : (5 * (7^2) : ℕ) = 245 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_5, hp_7]
  try omega

theorem v3_phi_245 : v3_fast (totient 245) 100 = v3_phi_list.getD 245 0 := by
  rw [tot_245]
  rfl

theorem tot_246 : totient 246 = 80 := by
  have heq : (2 * (3 * (41)) : ℕ) = 246 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_41]
  try omega

theorem v3_phi_246 : v3_fast (totient 246) 100 = v3_phi_list.getD 246 0 := by
  rw [tot_246]
  rfl

theorem tot_247 : totient 247 = 216 := by
  have heq : (13 * (19) : ℕ) = 247 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_19]
  try omega

theorem v3_phi_247 : v3_fast (totient 247) 100 = v3_phi_list.getD 247 0 := by
  rw [tot_247]
  rfl

theorem tot_248 : totient 248 = 120 := by
  have heq : (2^3 * (31) : ℕ) = 248 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_31]
  try omega

theorem v3_phi_248 : v3_fast (totient 248) 100 = v3_phi_list.getD 248 0 := by
  rw [tot_248]
  rfl

theorem tot_249 : totient 249 = 164 := by
  have heq : (3 * (83) : ℕ) = 249 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_83]
  try omega

theorem v3_phi_249 : v3_fast (totient 249) 100 = v3_phi_list.getD 249 0 := by
  rw [tot_249]
  rfl

theorem tot_250 : totient 250 = 100 := by
  have heq : (2 * (5^3) : ℕ) = 250 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^3) = 5^2 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_5]
  try omega

theorem v3_phi_250 : v3_fast (totient 250) 100 = v3_phi_list.getD 250 0 := by
  rw [tot_250]
  rfl

theorem tot_251 : totient 251 = 250 := by
  have h : totient 251 = 251 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_251 : v3_fast (totient 251) 100 = v3_phi_list.getD 251 0 := by
  rw [tot_251]
  rfl

theorem tot_252 : totient 252 = 72 := by
  have heq : (2^2 * (3^2 * (7)) : ℕ) = 252 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7]
  try omega

theorem v3_phi_252 : v3_fast (totient 252) 100 = v3_phi_list.getD 252 0 := by
  rw [tot_252]
  rfl

theorem tot_253 : totient 253 = 220 := by
  have heq : (11 * (23) : ℕ) = 253 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_23]
  try omega

theorem v3_phi_253 : v3_fast (totient 253) 100 = v3_phi_list.getD 253 0 := by
  rw [tot_253]
  rfl

theorem tot_254 : totient 254 = 126 := by
  have heq : (2 * (127) : ℕ) = 254 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_127 : totient 127 = 127 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_127]
  try omega

theorem v3_phi_254 : v3_fast (totient 254) 100 = v3_phi_list.getD 254 0 := by
  rw [tot_254]
  rfl

theorem tot_255 : totient 255 = 128 := by
  have heq : (3 * (5 * (17)) : ℕ) = 255 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_17]
  try omega

theorem v3_phi_255 : v3_fast (totient 255) 100 = v3_phi_list.getD 255 0 := by
  rw [tot_255]
  rfl

theorem tot_256 : totient 256 = 128 := by
  have h : totient (2^8) = 2^7 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (2^8 : ℕ) = 256 := by decide
  rw [← heq]
  rw [h]
  try omega

theorem v3_phi_256 : v3_fast (totient 256) 100 = v3_phi_list.getD 256 0 := by
  rw [tot_256]
  rfl

theorem tot_257 : totient 257 = 256 := by
  have h : totient 257 = 257 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_257 : v3_fast (totient 257) 100 = v3_phi_list.getD 257 0 := by
  rw [tot_257]
  rfl

theorem tot_258 : totient 258 = 84 := by
  have heq : (2 * (3 * (43)) : ℕ) = 258 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_43]
  try omega

theorem v3_phi_258 : v3_fast (totient 258) 100 = v3_phi_list.getD 258 0 := by
  rw [tot_258]
  rfl

theorem tot_259 : totient 259 = 216 := by
  have heq : (7 * (37) : ℕ) = 259 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_37]
  try omega

theorem v3_phi_259 : v3_fast (totient 259) 100 = v3_phi_list.getD 259 0 := by
  rw [tot_259]
  rfl

theorem tot_260 : totient 260 = 96 := by
  have heq : (2^2 * (5 * (13)) : ℕ) = 260 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_13]
  try omega

theorem v3_phi_260 : v3_fast (totient 260) 100 = v3_phi_list.getD 260 0 := by
  rw [tot_260]
  rfl

theorem tot_261 : totient 261 = 168 := by
  have heq : (3^2 * (29) : ℕ) = 261 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_29]
  try omega

theorem v3_phi_261 : v3_fast (totient 261) 100 = v3_phi_list.getD 261 0 := by
  rw [tot_261]
  rfl

theorem tot_262 : totient 262 = 130 := by
  have heq : (2 * (131) : ℕ) = 262 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_131 : totient 131 = 131 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_131]
  try omega

theorem v3_phi_262 : v3_fast (totient 262) 100 = v3_phi_list.getD 262 0 := by
  rw [tot_262]
  rfl

theorem tot_263 : totient 263 = 262 := by
  have h : totient 263 = 263 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_263 : v3_fast (totient 263) 100 = v3_phi_list.getD 263 0 := by
  rw [tot_263]
  rfl

theorem tot_264 : totient 264 = 80 := by
  have heq : (2^3 * (3 * (11)) : ℕ) = 264 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11]
  try omega

theorem v3_phi_264 : v3_fast (totient 264) 100 = v3_phi_list.getD 264 0 := by
  rw [tot_264]
  rfl

theorem tot_265 : totient 265 = 208 := by
  have heq : (5 * (53) : ℕ) = 265 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_53]
  try omega

theorem v3_phi_265 : v3_fast (totient 265) 100 = v3_phi_list.getD 265 0 := by
  rw [tot_265]
  rfl

theorem tot_266 : totient 266 = 108 := by
  have heq : (2 * (7 * (19)) : ℕ) = 266 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_19]
  try omega

theorem v3_phi_266 : v3_fast (totient 266) 100 = v3_phi_list.getD 266 0 := by
  rw [tot_266]
  rfl

theorem tot_267 : totient 267 = 176 := by
  have heq : (3 * (89) : ℕ) = 267 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_89]
  try omega

theorem v3_phi_267 : v3_fast (totient 267) 100 = v3_phi_list.getD 267 0 := by
  rw [tot_267]
  rfl

theorem tot_268 : totient 268 = 132 := by
  have heq : (2^2 * (67) : ℕ) = 268 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_67]
  try omega

theorem v3_phi_268 : v3_fast (totient 268) 100 = v3_phi_list.getD 268 0 := by
  rw [tot_268]
  rfl

theorem tot_269 : totient 269 = 268 := by
  have h : totient 269 = 269 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_269 : v3_fast (totient 269) 100 = v3_phi_list.getD 269 0 := by
  rw [tot_269]
  rfl

theorem tot_270 : totient 270 = 72 := by
  have heq : (2 * (3^3 * (5)) : ℕ) = 270 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5]
  try omega

theorem v3_phi_270 : v3_fast (totient 270) 100 = v3_phi_list.getD 270 0 := by
  rw [tot_270]
  rfl

theorem tot_271 : totient 271 = 270 := by
  have h : totient 271 = 271 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_271 : v3_fast (totient 271) 100 = v3_phi_list.getD 271 0 := by
  rw [tot_271]
  rfl

theorem tot_272 : totient 272 = 128 := by
  have heq : (2^4 * (17) : ℕ) = 272 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17]
  try omega

theorem v3_phi_272 : v3_fast (totient 272) 100 = v3_phi_list.getD 272 0 := by
  rw [tot_272]
  rfl

theorem tot_273 : totient 273 = 144 := by
  have heq : (3 * (7 * (13)) : ℕ) = 273 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_13]
  try omega

theorem v3_phi_273 : v3_fast (totient 273) 100 = v3_phi_list.getD 273 0 := by
  rw [tot_273]
  rfl

theorem tot_274 : totient 274 = 136 := by
  have heq : (2 * (137) : ℕ) = 274 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_137 : totient 137 = 137 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_137]
  try omega

theorem v3_phi_274 : v3_fast (totient 274) 100 = v3_phi_list.getD 274 0 := by
  rw [tot_274]
  rfl

theorem tot_275 : totient 275 = 200 := by
  have heq : (5^2 * (11) : ℕ) = 275 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_11]
  try omega

theorem v3_phi_275 : v3_fast (totient 275) 100 = v3_phi_list.getD 275 0 := by
  rw [tot_275]
  rfl

theorem tot_276 : totient 276 = 88 := by
  have heq : (2^2 * (3 * (23)) : ℕ) = 276 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_23]
  try omega

theorem v3_phi_276 : v3_fast (totient 276) 100 = v3_phi_list.getD 276 0 := by
  rw [tot_276]
  rfl

theorem tot_277 : totient 277 = 276 := by
  have h : totient 277 = 277 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_277 : v3_fast (totient 277) 100 = v3_phi_list.getD 277 0 := by
  rw [tot_277]
  rfl

theorem tot_278 : totient 278 = 138 := by
  have heq : (2 * (139) : ℕ) = 278 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_139 : totient 139 = 139 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_139]
  try omega

theorem v3_phi_278 : v3_fast (totient 278) 100 = v3_phi_list.getD 278 0 := by
  rw [tot_278]
  rfl

theorem tot_279 : totient 279 = 180 := by
  have heq : (3^2 * (31) : ℕ) = 279 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_31]
  try omega

theorem v3_phi_279 : v3_fast (totient 279) 100 = v3_phi_list.getD 279 0 := by
  rw [tot_279]
  rfl

theorem tot_280 : totient 280 = 96 := by
  have heq : (2^3 * (5 * (7)) : ℕ) = 280 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7]
  try omega

theorem v3_phi_280 : v3_fast (totient 280) 100 = v3_phi_list.getD 280 0 := by
  rw [tot_280]
  rfl

theorem tot_281 : totient 281 = 280 := by
  have h : totient 281 = 281 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_281 : v3_fast (totient 281) 100 = v3_phi_list.getD 281 0 := by
  rw [tot_281]
  rfl

theorem tot_282 : totient 282 = 92 := by
  have heq : (2 * (3 * (47)) : ℕ) = 282 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_47]
  try omega

theorem v3_phi_282 : v3_fast (totient 282) 100 = v3_phi_list.getD 282 0 := by
  rw [tot_282]
  rfl

theorem tot_283 : totient 283 = 282 := by
  have h : totient 283 = 283 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_283 : v3_fast (totient 283) 100 = v3_phi_list.getD 283 0 := by
  rw [tot_283]
  rfl

theorem tot_284 : totient 284 = 140 := by
  have heq : (2^2 * (71) : ℕ) = 284 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_71]
  try omega

theorem v3_phi_284 : v3_fast (totient 284) 100 = v3_phi_list.getD 284 0 := by
  rw [tot_284]
  rfl

theorem tot_285 : totient 285 = 144 := by
  have heq : (3 * (5 * (19)) : ℕ) = 285 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_19]
  try omega

theorem v3_phi_285 : v3_fast (totient 285) 100 = v3_phi_list.getD 285 0 := by
  rw [tot_285]
  rfl

theorem tot_286 : totient 286 = 120 := by
  have heq : (2 * (11 * (13)) : ℕ) = 286 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_13]
  try omega

theorem v3_phi_286 : v3_fast (totient 286) 100 = v3_phi_list.getD 286 0 := by
  rw [tot_286]
  rfl

theorem tot_287 : totient 287 = 240 := by
  have heq : (7 * (41) : ℕ) = 287 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_41]
  try omega

theorem v3_phi_287 : v3_fast (totient 287) 100 = v3_phi_list.getD 287 0 := by
  rw [tot_287]
  rfl

theorem tot_288 : totient 288 = 96 := by
  have heq : (2^5 * (3^2) : ℕ) = 288 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3]
  try omega

theorem v3_phi_288 : v3_fast (totient 288) 100 = v3_phi_list.getD 288 0 := by
  rw [tot_288]
  rfl

theorem tot_289 : totient 289 = 272 := by
  have h : totient (17^2) = 17^1 * (17 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (17^2 : ℕ) = 289 := by decide
  rw [← heq]
  rw [h]
  try omega

theorem v3_phi_289 : v3_fast (totient 289) 100 = v3_phi_list.getD 289 0 := by
  rw [tot_289]
  rfl

theorem tot_290 : totient 290 = 112 := by
  have heq : (2 * (5 * (29)) : ℕ) = 290 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_29]
  try omega

theorem v3_phi_290 : v3_fast (totient 290) 100 = v3_phi_list.getD 290 0 := by
  rw [tot_290]
  rfl

theorem tot_291 : totient 291 = 192 := by
  have heq : (3 * (97) : ℕ) = 291 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_97]
  try omega

theorem v3_phi_291 : v3_fast (totient 291) 100 = v3_phi_list.getD 291 0 := by
  rw [tot_291]
  rfl

theorem tot_292 : totient 292 = 144 := by
  have heq : (2^2 * (73) : ℕ) = 292 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_73]
  try omega

theorem v3_phi_292 : v3_fast (totient 292) 100 = v3_phi_list.getD 292 0 := by
  rw [tot_292]
  rfl

theorem tot_293 : totient 293 = 292 := by
  have h : totient 293 = 293 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_293 : v3_fast (totient 293) 100 = v3_phi_list.getD 293 0 := by
  rw [tot_293]
  rfl

theorem tot_294 : totient 294 = 84 := by
  have heq : (2 * (3 * (7^2)) : ℕ) = 294 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_7]
  try omega

theorem v3_phi_294 : v3_fast (totient 294) 100 = v3_phi_list.getD 294 0 := by
  rw [tot_294]
  rfl

theorem tot_295 : totient 295 = 232 := by
  have heq : (5 * (59) : ℕ) = 295 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_59]
  try omega

theorem v3_phi_295 : v3_fast (totient 295) 100 = v3_phi_list.getD 295 0 := by
  rw [tot_295]
  rfl

theorem tot_296 : totient 296 = 144 := by
  have heq : (2^3 * (37) : ℕ) = 296 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_37]
  try omega

theorem v3_phi_296 : v3_fast (totient 296) 100 = v3_phi_list.getD 296 0 := by
  rw [tot_296]
  rfl

theorem tot_297 : totient 297 = 180 := by
  have heq : (3^3 * (11) : ℕ) = 297 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11]
  try omega

theorem v3_phi_297 : v3_fast (totient 297) 100 = v3_phi_list.getD 297 0 := by
  rw [tot_297]
  rfl

theorem tot_298 : totient 298 = 148 := by
  have heq : (2 * (149) : ℕ) = 298 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_149 : totient 149 = 149 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_149]
  try omega

theorem v3_phi_298 : v3_fast (totient 298) 100 = v3_phi_list.getD 298 0 := by
  rw [tot_298]
  rfl

theorem tot_299 : totient 299 = 264 := by
  have heq : (13 * (23) : ℕ) = 299 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_23]
  try omega

theorem v3_phi_299 : v3_fast (totient 299) 100 = v3_phi_list.getD 299 0 := by
  rw [tot_299]
  rfl

theorem tot_300 : totient 300 = 80 := by
  have heq : (2^2 * (3 * (5^2)) : ℕ) = 300 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_5]
  try omega

theorem v3_phi_300 : v3_fast (totient 300) 100 = v3_phi_list.getD 300 0 := by
  rw [tot_300]
  rfl

theorem tot_301 : totient 301 = 252 := by
  have heq : (7 * (43) : ℕ) = 301 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_43]
  try omega

theorem v3_phi_301 : v3_fast (totient 301) 100 = v3_phi_list.getD 301 0 := by
  rw [tot_301]
  rfl

theorem tot_302 : totient 302 = 150 := by
  have heq : (2 * (151) : ℕ) = 302 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_151 : totient 151 = 151 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_151]
  try omega

theorem v3_phi_302 : v3_fast (totient 302) 100 = v3_phi_list.getD 302 0 := by
  rw [tot_302]
  rfl

theorem tot_303 : totient 303 = 200 := by
  have heq : (3 * (101) : ℕ) = 303 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_101]
  try omega

theorem v3_phi_303 : v3_fast (totient 303) 100 = v3_phi_list.getD 303 0 := by
  rw [tot_303]
  rfl

theorem tot_304 : totient 304 = 144 := by
  have heq : (2^4 * (19) : ℕ) = 304 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_19]
  try omega

theorem v3_phi_304 : v3_fast (totient 304) 100 = v3_phi_list.getD 304 0 := by
  rw [tot_304]
  rfl

theorem tot_305 : totient 305 = 240 := by
  have heq : (5 * (61) : ℕ) = 305 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_61]
  try omega

theorem v3_phi_305 : v3_fast (totient 305) 100 = v3_phi_list.getD 305 0 := by
  rw [tot_305]
  rfl

theorem tot_306 : totient 306 = 96 := by
  have heq : (2 * (3^2 * (17)) : ℕ) = 306 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_17]
  try omega

theorem v3_phi_306 : v3_fast (totient 306) 100 = v3_phi_list.getD 306 0 := by
  rw [tot_306]
  rfl

theorem tot_307 : totient 307 = 306 := by
  have h : totient 307 = 307 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_307 : v3_fast (totient 307) 100 = v3_phi_list.getD 307 0 := by
  rw [tot_307]
  rfl

theorem tot_308 : totient 308 = 120 := by
  have heq : (2^2 * (7 * (11)) : ℕ) = 308 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_11]
  try omega

theorem v3_phi_308 : v3_fast (totient 308) 100 = v3_phi_list.getD 308 0 := by
  rw [tot_308]
  rfl

theorem tot_309 : totient 309 = 204 := by
  have heq : (3 * (103) : ℕ) = 309 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_103]
  try omega

theorem v3_phi_309 : v3_fast (totient 309) 100 = v3_phi_list.getD 309 0 := by
  rw [tot_309]
  rfl

theorem tot_310 : totient 310 = 120 := by
  have heq : (2 * (5 * (31)) : ℕ) = 310 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_31]
  try omega

theorem v3_phi_310 : v3_fast (totient 310) 100 = v3_phi_list.getD 310 0 := by
  rw [tot_310]
  rfl

theorem tot_311 : totient 311 = 310 := by
  have h : totient 311 = 311 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_311 : v3_fast (totient 311) 100 = v3_phi_list.getD 311 0 := by
  rw [tot_311]
  rfl

theorem tot_312 : totient 312 = 96 := by
  have heq : (2^3 * (3 * (13)) : ℕ) = 312 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_13]
  try omega

theorem v3_phi_312 : v3_fast (totient 312) 100 = v3_phi_list.getD 312 0 := by
  rw [tot_312]
  rfl

theorem tot_313 : totient 313 = 312 := by
  have h : totient 313 = 313 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_313 : v3_fast (totient 313) 100 = v3_phi_list.getD 313 0 := by
  rw [tot_313]
  rfl

theorem tot_314 : totient 314 = 156 := by
  have heq : (2 * (157) : ℕ) = 314 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_157 : totient 157 = 157 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_157]
  try omega

theorem v3_phi_314 : v3_fast (totient 314) 100 = v3_phi_list.getD 314 0 := by
  rw [tot_314]
  rfl

theorem tot_315 : totient 315 = 144 := by
  have heq : (3^2 * (5 * (7)) : ℕ) = 315 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_7]
  try omega

theorem v3_phi_315 : v3_fast (totient 315) 100 = v3_phi_list.getD 315 0 := by
  rw [tot_315]
  rfl

theorem tot_316 : totient 316 = 156 := by
  have heq : (2^2 * (79) : ℕ) = 316 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_79]
  try omega

theorem v3_phi_316 : v3_fast (totient 316) 100 = v3_phi_list.getD 316 0 := by
  rw [tot_316]
  rfl

theorem tot_317 : totient 317 = 316 := by
  have h : totient 317 = 317 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_317 : v3_fast (totient 317) 100 = v3_phi_list.getD 317 0 := by
  rw [tot_317]
  rfl

theorem tot_318 : totient 318 = 104 := by
  have heq : (2 * (3 * (53)) : ℕ) = 318 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_53]
  try omega

theorem v3_phi_318 : v3_fast (totient 318) 100 = v3_phi_list.getD 318 0 := by
  rw [tot_318]
  rfl

theorem tot_319 : totient 319 = 280 := by
  have heq : (11 * (29) : ℕ) = 319 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_29]
  try omega

theorem v3_phi_319 : v3_fast (totient 319) 100 = v3_phi_list.getD 319 0 := by
  rw [tot_319]
  rfl

theorem tot_320 : totient 320 = 128 := by
  have heq : (2^6 * (5) : ℕ) = 320 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^6) = 2^5 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5]
  try omega

theorem v3_phi_320 : v3_fast (totient 320) 100 = v3_phi_list.getD 320 0 := by
  rw [tot_320]
  rfl

theorem tot_321 : totient 321 = 212 := by
  have heq : (3 * (107) : ℕ) = 321 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_107]
  try omega

theorem v3_phi_321 : v3_fast (totient 321) 100 = v3_phi_list.getD 321 0 := by
  rw [tot_321]
  rfl

theorem tot_322 : totient 322 = 132 := by
  have heq : (2 * (7 * (23)) : ℕ) = 322 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_23]
  try omega

theorem v3_phi_322 : v3_fast (totient 322) 100 = v3_phi_list.getD 322 0 := by
  rw [tot_322]
  rfl

theorem tot_323 : totient 323 = 288 := by
  have heq : (17 * (19) : ℕ) = 323 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_19]
  try omega

theorem v3_phi_323 : v3_fast (totient 323) 100 = v3_phi_list.getD 323 0 := by
  rw [tot_323]
  rfl

theorem tot_324 : totient 324 = 108 := by
  have heq : (2^2 * (3^4) : ℕ) = 324 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3]
  try omega

theorem v3_phi_324 : v3_fast (totient 324) 100 = v3_phi_list.getD 324 0 := by
  rw [tot_324]
  rfl

theorem tot_325 : totient 325 = 240 := by
  have heq : (5^2 * (13) : ℕ) = 325 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_13]
  try omega

theorem v3_phi_325 : v3_fast (totient 325) 100 = v3_phi_list.getD 325 0 := by
  rw [tot_325]
  rfl

theorem tot_326 : totient 326 = 162 := by
  have heq : (2 * (163) : ℕ) = 326 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_163 : totient 163 = 163 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_163]
  try omega

theorem v3_phi_326 : v3_fast (totient 326) 100 = v3_phi_list.getD 326 0 := by
  rw [tot_326]
  rfl

theorem tot_327 : totient 327 = 216 := by
  have heq : (3 * (109) : ℕ) = 327 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_109]
  try omega

theorem v3_phi_327 : v3_fast (totient 327) 100 = v3_phi_list.getD 327 0 := by
  rw [tot_327]
  rfl

theorem tot_328 : totient 328 = 160 := by
  have heq : (2^3 * (41) : ℕ) = 328 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_41]
  try omega

theorem v3_phi_328 : v3_fast (totient 328) 100 = v3_phi_list.getD 328 0 := by
  rw [tot_328]
  rfl

theorem tot_329 : totient 329 = 276 := by
  have heq : (7 * (47) : ℕ) = 329 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_47]
  try omega

theorem v3_phi_329 : v3_fast (totient 329) 100 = v3_phi_list.getD 329 0 := by
  rw [tot_329]
  rfl

theorem tot_330 : totient 330 = 80 := by
  have heq : (2 * (3 * (5 * (11))) : ℕ) = 330 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_11]
  try omega

theorem v3_phi_330 : v3_fast (totient 330) 100 = v3_phi_list.getD 330 0 := by
  rw [tot_330]
  rfl

theorem tot_331 : totient 331 = 330 := by
  have h : totient 331 = 331 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_331 : v3_fast (totient 331) 100 = v3_phi_list.getD 331 0 := by
  rw [tot_331]
  rfl

theorem tot_332 : totient 332 = 164 := by
  have heq : (2^2 * (83) : ℕ) = 332 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_83]
  try omega

theorem v3_phi_332 : v3_fast (totient 332) 100 = v3_phi_list.getD 332 0 := by
  rw [tot_332]
  rfl

theorem tot_333 : totient 333 = 216 := by
  have heq : (3^2 * (37) : ℕ) = 333 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_37]
  try omega

theorem v3_phi_333 : v3_fast (totient 333) 100 = v3_phi_list.getD 333 0 := by
  rw [tot_333]
  rfl

theorem tot_334 : totient 334 = 166 := by
  have heq : (2 * (167) : ℕ) = 334 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_167 : totient 167 = 167 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_167]
  try omega

theorem v3_phi_334 : v3_fast (totient 334) 100 = v3_phi_list.getD 334 0 := by
  rw [tot_334]
  rfl

theorem tot_335 : totient 335 = 264 := by
  have heq : (5 * (67) : ℕ) = 335 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_67]
  try omega

theorem v3_phi_335 : v3_fast (totient 335) 100 = v3_phi_list.getD 335 0 := by
  rw [tot_335]
  rfl

theorem tot_336 : totient 336 = 96 := by
  have heq : (2^4 * (3 * (7)) : ℕ) = 336 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7]
  try omega

theorem v3_phi_336 : v3_fast (totient 336) 100 = v3_phi_list.getD 336 0 := by
  rw [tot_336]
  rfl

theorem tot_337 : totient 337 = 336 := by
  have h : totient 337 = 337 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_337 : v3_fast (totient 337) 100 = v3_phi_list.getD 337 0 := by
  rw [tot_337]
  rfl

theorem tot_338 : totient 338 = 156 := by
  have heq : (2 * (13^2) : ℕ) = 338 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient (13^2) = 13^1 * (13 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_13]
  try omega

theorem v3_phi_338 : v3_fast (totient 338) 100 = v3_phi_list.getD 338 0 := by
  rw [tot_338]
  rfl

theorem tot_339 : totient 339 = 224 := by
  have heq : (3 * (113) : ℕ) = 339 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_113 : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_113]
  try omega

theorem v3_phi_339 : v3_fast (totient 339) 100 = v3_phi_list.getD 339 0 := by
  rw [tot_339]
  rfl

theorem tot_340 : totient 340 = 128 := by
  have heq : (2^2 * (5 * (17)) : ℕ) = 340 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_17]
  try omega

theorem v3_phi_340 : v3_fast (totient 340) 100 = v3_phi_list.getD 340 0 := by
  rw [tot_340]
  rfl

theorem tot_341 : totient 341 = 300 := by
  have heq : (11 * (31) : ℕ) = 341 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_31]
  try omega

theorem v3_phi_341 : v3_fast (totient 341) 100 = v3_phi_list.getD 341 0 := by
  rw [tot_341]
  rfl

theorem tot_342 : totient 342 = 108 := by
  have heq : (2 * (3^2 * (19)) : ℕ) = 342 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_19]
  try omega

theorem v3_phi_342 : v3_fast (totient 342) 100 = v3_phi_list.getD 342 0 := by
  rw [tot_342]
  rfl

theorem tot_343 : totient 343 = 294 := by
  have h : totient (7^3) = 7^2 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (7^3 : ℕ) = 343 := by decide
  rw [← heq]
  rw [h]
  try omega

theorem v3_phi_343 : v3_fast (totient 343) 100 = v3_phi_list.getD 343 0 := by
  rw [tot_343]
  rfl

theorem tot_344 : totient 344 = 168 := by
  have heq : (2^3 * (43) : ℕ) = 344 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_43]
  try omega

theorem v3_phi_344 : v3_fast (totient 344) 100 = v3_phi_list.getD 344 0 := by
  rw [tot_344]
  rfl

theorem tot_345 : totient 345 = 176 := by
  have heq : (3 * (5 * (23)) : ℕ) = 345 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_23]
  try omega

theorem v3_phi_345 : v3_fast (totient 345) 100 = v3_phi_list.getD 345 0 := by
  rw [tot_345]
  rfl

theorem tot_346 : totient 346 = 172 := by
  have heq : (2 * (173) : ℕ) = 346 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_173 : totient 173 = 173 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_173]
  try omega

theorem v3_phi_346 : v3_fast (totient 346) 100 = v3_phi_list.getD 346 0 := by
  rw [tot_346]
  rfl

theorem tot_347 : totient 347 = 346 := by
  have h : totient 347 = 347 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_347 : v3_fast (totient 347) 100 = v3_phi_list.getD 347 0 := by
  rw [tot_347]
  rfl

theorem tot_348 : totient 348 = 112 := by
  have heq : (2^2 * (3 * (29)) : ℕ) = 348 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_29]
  try omega

theorem v3_phi_348 : v3_fast (totient 348) 100 = v3_phi_list.getD 348 0 := by
  rw [tot_348]
  rfl

theorem tot_349 : totient 349 = 348 := by
  have h : totient 349 = 349 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_349 : v3_fast (totient 349) 100 = v3_phi_list.getD 349 0 := by
  rw [tot_349]
  rfl

theorem tot_350 : totient 350 = 120 := by
  have heq : (2 * (5^2 * (7)) : ℕ) = 350 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7]
  try omega

theorem v3_phi_350 : v3_fast (totient 350) 100 = v3_phi_list.getD 350 0 := by
  rw [tot_350]
  rfl

theorem tot_351 : totient 351 = 216 := by
  have heq : (3^3 * (13) : ℕ) = 351 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_13]
  try omega

theorem v3_phi_351 : v3_fast (totient 351) 100 = v3_phi_list.getD 351 0 := by
  rw [tot_351]
  rfl

theorem tot_352 : totient 352 = 160 := by
  have heq : (2^5 * (11) : ℕ) = 352 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11]
  try omega

theorem v3_phi_352 : v3_fast (totient 352) 100 = v3_phi_list.getD 352 0 := by
  rw [tot_352]
  rfl

theorem tot_353 : totient 353 = 352 := by
  have h : totient 353 = 353 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_353 : v3_fast (totient 353) 100 = v3_phi_list.getD 353 0 := by
  rw [tot_353]
  rfl

theorem tot_354 : totient 354 = 116 := by
  have heq : (2 * (3 * (59)) : ℕ) = 354 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_59]
  try omega

theorem v3_phi_354 : v3_fast (totient 354) 100 = v3_phi_list.getD 354 0 := by
  rw [tot_354]
  rfl

theorem tot_355 : totient 355 = 280 := by
  have heq : (5 * (71) : ℕ) = 355 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_71]
  try omega

theorem v3_phi_355 : v3_fast (totient 355) 100 = v3_phi_list.getD 355 0 := by
  rw [tot_355]
  rfl

theorem tot_356 : totient 356 = 176 := by
  have heq : (2^2 * (89) : ℕ) = 356 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_89]
  try omega

theorem v3_phi_356 : v3_fast (totient 356) 100 = v3_phi_list.getD 356 0 := by
  rw [tot_356]
  rfl

theorem tot_357 : totient 357 = 192 := by
  have heq : (3 * (7 * (17)) : ℕ) = 357 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_17]
  try omega

theorem v3_phi_357 : v3_fast (totient 357) 100 = v3_phi_list.getD 357 0 := by
  rw [tot_357]
  rfl

theorem tot_358 : totient 358 = 178 := by
  have heq : (2 * (179) : ℕ) = 358 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_179 : totient 179 = 179 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_179]
  try omega

theorem v3_phi_358 : v3_fast (totient 358) 100 = v3_phi_list.getD 358 0 := by
  rw [tot_358]
  rfl

theorem tot_359 : totient 359 = 358 := by
  have h : totient 359 = 359 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_359 : v3_fast (totient 359) 100 = v3_phi_list.getD 359 0 := by
  rw [tot_359]
  rfl

theorem tot_360 : totient 360 = 96 := by
  have heq : (2^3 * (3^2 * (5)) : ℕ) = 360 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5]
  try omega

theorem v3_phi_360 : v3_fast (totient 360) 100 = v3_phi_list.getD 360 0 := by
  rw [tot_360]
  rfl

theorem tot_361 : totient 361 = 342 := by
  have h : totient (19^2) = 19^1 * (19 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (19^2 : ℕ) = 361 := by decide
  rw [← heq]
  rw [h]
  try omega

theorem v3_phi_361 : v3_fast (totient 361) 100 = v3_phi_list.getD 361 0 := by
  rw [tot_361]
  rfl

theorem tot_362 : totient 362 = 180 := by
  have heq : (2 * (181) : ℕ) = 362 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_181 : totient 181 = 181 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_181]
  try omega

theorem v3_phi_362 : v3_fast (totient 362) 100 = v3_phi_list.getD 362 0 := by
  rw [tot_362]
  rfl

theorem tot_363 : totient 363 = 220 := by
  have heq : (3 * (11^2) : ℕ) = 363 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient (11^2) = 11^1 * (11 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_11]
  try omega

theorem v3_phi_363 : v3_fast (totient 363) 100 = v3_phi_list.getD 363 0 := by
  rw [tot_363]
  rfl

theorem tot_364 : totient 364 = 144 := by
  have heq : (2^2 * (7 * (13)) : ℕ) = 364 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_13]
  try omega

theorem v3_phi_364 : v3_fast (totient 364) 100 = v3_phi_list.getD 364 0 := by
  rw [tot_364]
  rfl

theorem tot_365 : totient 365 = 288 := by
  have heq : (5 * (73) : ℕ) = 365 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_73]
  try omega

theorem v3_phi_365 : v3_fast (totient 365) 100 = v3_phi_list.getD 365 0 := by
  rw [tot_365]
  rfl

theorem tot_366 : totient 366 = 120 := by
  have heq : (2 * (3 * (61)) : ℕ) = 366 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_61]
  try omega

theorem v3_phi_366 : v3_fast (totient 366) 100 = v3_phi_list.getD 366 0 := by
  rw [tot_366]
  rfl

theorem tot_367 : totient 367 = 366 := by
  have h : totient 367 = 367 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_367 : v3_fast (totient 367) 100 = v3_phi_list.getD 367 0 := by
  rw [tot_367]
  rfl

theorem tot_368 : totient 368 = 176 := by
  have heq : (2^4 * (23) : ℕ) = 368 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_23]
  try omega

theorem v3_phi_368 : v3_fast (totient 368) 100 = v3_phi_list.getD 368 0 := by
  rw [tot_368]
  rfl

theorem tot_369 : totient 369 = 240 := by
  have heq : (3^2 * (41) : ℕ) = 369 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_41]
  try omega

theorem v3_phi_369 : v3_fast (totient 369) 100 = v3_phi_list.getD 369 0 := by
  rw [tot_369]
  rfl

theorem tot_370 : totient 370 = 144 := by
  have heq : (2 * (5 * (37)) : ℕ) = 370 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_37]
  try omega

theorem v3_phi_370 : v3_fast (totient 370) 100 = v3_phi_list.getD 370 0 := by
  rw [tot_370]
  rfl

theorem tot_371 : totient 371 = 312 := by
  have heq : (7 * (53) : ℕ) = 371 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_53]
  try omega

theorem v3_phi_371 : v3_fast (totient 371) 100 = v3_phi_list.getD 371 0 := by
  rw [tot_371]
  rfl

theorem tot_372 : totient 372 = 120 := by
  have heq : (2^2 * (3 * (31)) : ℕ) = 372 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_31]
  try omega

theorem v3_phi_372 : v3_fast (totient 372) 100 = v3_phi_list.getD 372 0 := by
  rw [tot_372]
  rfl

theorem tot_373 : totient 373 = 372 := by
  have h : totient 373 = 373 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_373 : v3_fast (totient 373) 100 = v3_phi_list.getD 373 0 := by
  rw [tot_373]
  rfl

theorem tot_374 : totient 374 = 160 := by
  have heq : (2 * (11 * (17)) : ℕ) = 374 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_17]
  try omega

theorem v3_phi_374 : v3_fast (totient 374) 100 = v3_phi_list.getD 374 0 := by
  rw [tot_374]
  rfl

theorem tot_375 : totient 375 = 200 := by
  have heq : (3 * (5^3) : ℕ) = 375 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^3) = 5^2 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_5]
  try omega

theorem v3_phi_375 : v3_fast (totient 375) 100 = v3_phi_list.getD 375 0 := by
  rw [tot_375]
  rfl

theorem tot_376 : totient 376 = 184 := by
  have heq : (2^3 * (47) : ℕ) = 376 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_47]
  try omega

theorem v3_phi_376 : v3_fast (totient 376) 100 = v3_phi_list.getD 376 0 := by
  rw [tot_376]
  rfl

theorem tot_377 : totient 377 = 336 := by
  have heq : (13 * (29) : ℕ) = 377 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_29]
  try omega

theorem v3_phi_377 : v3_fast (totient 377) 100 = v3_phi_list.getD 377 0 := by
  rw [tot_377]
  rfl

theorem tot_378 : totient 378 = 108 := by
  have heq : (2 * (3^3 * (7)) : ℕ) = 378 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7]
  try omega

theorem v3_phi_378 : v3_fast (totient 378) 100 = v3_phi_list.getD 378 0 := by
  rw [tot_378]
  rfl

theorem tot_379 : totient 379 = 378 := by
  have h : totient 379 = 379 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_379 : v3_fast (totient 379) 100 = v3_phi_list.getD 379 0 := by
  rw [tot_379]
  rfl

theorem tot_380 : totient 380 = 144 := by
  have heq : (2^2 * (5 * (19)) : ℕ) = 380 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_19]
  try omega

theorem v3_phi_380 : v3_fast (totient 380) 100 = v3_phi_list.getD 380 0 := by
  rw [tot_380]
  rfl

theorem tot_381 : totient 381 = 252 := by
  have heq : (3 * (127) : ℕ) = 381 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_127 : totient 127 = 127 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_127]
  try omega

theorem v3_phi_381 : v3_fast (totient 381) 100 = v3_phi_list.getD 381 0 := by
  rw [tot_381]
  rfl

theorem tot_382 : totient 382 = 190 := by
  have heq : (2 * (191) : ℕ) = 382 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_191 : totient 191 = 191 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_191]
  try omega

theorem v3_phi_382 : v3_fast (totient 382) 100 = v3_phi_list.getD 382 0 := by
  rw [tot_382]
  rfl

theorem tot_383 : totient 383 = 382 := by
  have h : totient 383 = 383 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_383 : v3_fast (totient 383) 100 = v3_phi_list.getD 383 0 := by
  rw [tot_383]
  rfl

theorem tot_384 : totient 384 = 128 := by
  have heq : (2^7 * (3) : ℕ) = 384 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^7) = 2^6 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3]
  try omega

theorem v3_phi_384 : v3_fast (totient 384) 100 = v3_phi_list.getD 384 0 := by
  rw [tot_384]
  rfl

theorem tot_385 : totient 385 = 240 := by
  have heq : (5 * (7 * (11)) : ℕ) = 385 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_7, hp_11]
  try omega

theorem v3_phi_385 : v3_fast (totient 385) 100 = v3_phi_list.getD 385 0 := by
  rw [tot_385]
  rfl

theorem tot_386 : totient 386 = 192 := by
  have heq : (2 * (193) : ℕ) = 386 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_193 : totient 193 = 193 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_193]
  try omega

theorem v3_phi_386 : v3_fast (totient 386) 100 = v3_phi_list.getD 386 0 := by
  rw [tot_386]
  rfl

theorem tot_387 : totient 387 = 252 := by
  have heq : (3^2 * (43) : ℕ) = 387 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_43]
  try omega

theorem v3_phi_387 : v3_fast (totient 387) 100 = v3_phi_list.getD 387 0 := by
  rw [tot_387]
  rfl

theorem tot_388 : totient 388 = 192 := by
  have heq : (2^2 * (97) : ℕ) = 388 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_97]
  try omega

theorem v3_phi_388 : v3_fast (totient 388) 100 = v3_phi_list.getD 388 0 := by
  rw [tot_388]
  rfl

theorem tot_389 : totient 389 = 388 := by
  have h : totient 389 = 389 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_389 : v3_fast (totient 389) 100 = v3_phi_list.getD 389 0 := by
  rw [tot_389]
  rfl

theorem tot_390 : totient 390 = 96 := by
  have heq : (2 * (3 * (5 * (13))) : ℕ) = 390 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_13]
  try omega

theorem v3_phi_390 : v3_fast (totient 390) 100 = v3_phi_list.getD 390 0 := by
  rw [tot_390]
  rfl

theorem tot_391 : totient 391 = 352 := by
  have heq : (17 * (23) : ℕ) = 391 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_23]
  try omega

theorem v3_phi_391 : v3_fast (totient 391) 100 = v3_phi_list.getD 391 0 := by
  rw [tot_391]
  rfl

theorem tot_392 : totient 392 = 168 := by
  have heq : (2^3 * (7^2) : ℕ) = 392 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_7]
  try omega

theorem v3_phi_392 : v3_fast (totient 392) 100 = v3_phi_list.getD 392 0 := by
  rw [tot_392]
  rfl

theorem tot_393 : totient 393 = 260 := by
  have heq : (3 * (131) : ℕ) = 393 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_131 : totient 131 = 131 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_131]
  try omega

theorem v3_phi_393 : v3_fast (totient 393) 100 = v3_phi_list.getD 393 0 := by
  rw [tot_393]
  rfl

theorem tot_394 : totient 394 = 196 := by
  have heq : (2 * (197) : ℕ) = 394 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_197 : totient 197 = 197 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_197]
  try omega

theorem v3_phi_394 : v3_fast (totient 394) 100 = v3_phi_list.getD 394 0 := by
  rw [tot_394]
  rfl

theorem tot_395 : totient 395 = 312 := by
  have heq : (5 * (79) : ℕ) = 395 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_79]
  try omega

theorem v3_phi_395 : v3_fast (totient 395) 100 = v3_phi_list.getD 395 0 := by
  rw [tot_395]
  rfl

theorem tot_396 : totient 396 = 120 := by
  have heq : (2^2 * (3^2 * (11)) : ℕ) = 396 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11]
  try omega

theorem v3_phi_396 : v3_fast (totient 396) 100 = v3_phi_list.getD 396 0 := by
  rw [tot_396]
  rfl

theorem tot_397 : totient 397 = 396 := by
  have h : totient 397 = 397 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_397 : v3_fast (totient 397) 100 = v3_phi_list.getD 397 0 := by
  rw [tot_397]
  rfl

theorem tot_398 : totient 398 = 198 := by
  have heq : (2 * (199) : ℕ) = 398 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_199 : totient 199 = 199 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_199]
  try omega

theorem v3_phi_398 : v3_fast (totient 398) 100 = v3_phi_list.getD 398 0 := by
  rw [tot_398]
  rfl

theorem tot_399 : totient 399 = 216 := by
  have heq : (3 * (7 * (19)) : ℕ) = 399 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_19]
  try omega

theorem v3_phi_399 : v3_fast (totient 399) 100 = v3_phi_list.getD 399 0 := by
  rw [tot_399]
  rfl

theorem tot_400 : totient 400 = 160 := by
  have heq : (2^4 * (5^2) : ℕ) = 400 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_5]
  try omega

theorem v3_phi_400 : v3_fast (totient 400) 100 = v3_phi_list.getD 400 0 := by
  rw [tot_400]
  rfl

theorem tot_401 : totient 401 = 400 := by
  have h : totient 401 = 401 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_401 : v3_fast (totient 401) 100 = v3_phi_list.getD 401 0 := by
  rw [tot_401]
  rfl

theorem tot_402 : totient 402 = 132 := by
  have heq : (2 * (3 * (67)) : ℕ) = 402 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_67]
  try omega

theorem v3_phi_402 : v3_fast (totient 402) 100 = v3_phi_list.getD 402 0 := by
  rw [tot_402]
  rfl

theorem tot_403 : totient 403 = 360 := by
  have heq : (13 * (31) : ℕ) = 403 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_31]
  try omega

theorem v3_phi_403 : v3_fast (totient 403) 100 = v3_phi_list.getD 403 0 := by
  rw [tot_403]
  rfl

theorem tot_404 : totient 404 = 200 := by
  have heq : (2^2 * (101) : ℕ) = 404 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_101]
  try omega

theorem v3_phi_404 : v3_fast (totient 404) 100 = v3_phi_list.getD 404 0 := by
  rw [tot_404]
  rfl

theorem tot_405 : totient 405 = 216 := by
  have heq : (3^4 * (5) : ℕ) = 405 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5]
  try omega

theorem v3_phi_405 : v3_fast (totient 405) 100 = v3_phi_list.getD 405 0 := by
  rw [tot_405]
  rfl

theorem tot_406 : totient 406 = 168 := by
  have heq : (2 * (7 * (29)) : ℕ) = 406 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_29]
  try omega

theorem v3_phi_406 : v3_fast (totient 406) 100 = v3_phi_list.getD 406 0 := by
  rw [tot_406]
  rfl

theorem tot_407 : totient 407 = 360 := by
  have heq : (11 * (37) : ℕ) = 407 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_37]
  try omega

theorem v3_phi_407 : v3_fast (totient 407) 100 = v3_phi_list.getD 407 0 := by
  rw [tot_407]
  rfl

theorem tot_408 : totient 408 = 128 := by
  have heq : (2^3 * (3 * (17)) : ℕ) = 408 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_17]
  try omega

theorem v3_phi_408 : v3_fast (totient 408) 100 = v3_phi_list.getD 408 0 := by
  rw [tot_408]
  rfl

theorem tot_409 : totient 409 = 408 := by
  have h : totient 409 = 409 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_409 : v3_fast (totient 409) 100 = v3_phi_list.getD 409 0 := by
  rw [tot_409]
  rfl

theorem tot_410 : totient 410 = 160 := by
  have heq : (2 * (5 * (41)) : ℕ) = 410 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_41]
  try omega

theorem v3_phi_410 : v3_fast (totient 410) 100 = v3_phi_list.getD 410 0 := by
  rw [tot_410]
  rfl

theorem tot_411 : totient 411 = 272 := by
  have heq : (3 * (137) : ℕ) = 411 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_137 : totient 137 = 137 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_137]
  try omega

theorem v3_phi_411 : v3_fast (totient 411) 100 = v3_phi_list.getD 411 0 := by
  rw [tot_411]
  rfl

theorem tot_412 : totient 412 = 204 := by
  have heq : (2^2 * (103) : ℕ) = 412 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_103]
  try omega

theorem v3_phi_412 : v3_fast (totient 412) 100 = v3_phi_list.getD 412 0 := by
  rw [tot_412]
  rfl

theorem tot_413 : totient 413 = 348 := by
  have heq : (7 * (59) : ℕ) = 413 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_59]
  try omega

theorem v3_phi_413 : v3_fast (totient 413) 100 = v3_phi_list.getD 413 0 := by
  rw [tot_413]
  rfl

theorem tot_414 : totient 414 = 132 := by
  have heq : (2 * (3^2 * (23)) : ℕ) = 414 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_23]
  try omega

theorem v3_phi_414 : v3_fast (totient 414) 100 = v3_phi_list.getD 414 0 := by
  rw [tot_414]
  rfl

theorem tot_415 : totient 415 = 328 := by
  have heq : (5 * (83) : ℕ) = 415 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_83]
  try omega

theorem v3_phi_415 : v3_fast (totient 415) 100 = v3_phi_list.getD 415 0 := by
  rw [tot_415]
  rfl

theorem tot_416 : totient 416 = 192 := by
  have heq : (2^5 * (13) : ℕ) = 416 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13]
  try omega

theorem v3_phi_416 : v3_fast (totient 416) 100 = v3_phi_list.getD 416 0 := by
  rw [tot_416]
  rfl

theorem tot_417 : totient 417 = 276 := by
  have heq : (3 * (139) : ℕ) = 417 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_139 : totient 139 = 139 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_139]
  try omega

theorem v3_phi_417 : v3_fast (totient 417) 100 = v3_phi_list.getD 417 0 := by
  rw [tot_417]
  rfl

theorem tot_418 : totient 418 = 180 := by
  have heq : (2 * (11 * (19)) : ℕ) = 418 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_19]
  try omega

theorem v3_phi_418 : v3_fast (totient 418) 100 = v3_phi_list.getD 418 0 := by
  rw [tot_418]
  rfl

theorem tot_419 : totient 419 = 418 := by
  have h : totient 419 = 419 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_419 : v3_fast (totient 419) 100 = v3_phi_list.getD 419 0 := by
  rw [tot_419]
  rfl

theorem tot_420 : totient 420 = 96 := by
  have heq : (2^2 * (3 * (5 * (7))) : ℕ) = 420 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_7]
  try omega

theorem v3_phi_420 : v3_fast (totient 420) 100 = v3_phi_list.getD 420 0 := by
  rw [tot_420]
  rfl

theorem tot_421 : totient 421 = 420 := by
  have h : totient 421 = 421 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_421 : v3_fast (totient 421) 100 = v3_phi_list.getD 421 0 := by
  rw [tot_421]
  rfl

theorem tot_422 : totient 422 = 210 := by
  have heq : (2 * (211) : ℕ) = 422 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_211 : totient 211 = 211 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_211]
  try omega

theorem v3_phi_422 : v3_fast (totient 422) 100 = v3_phi_list.getD 422 0 := by
  rw [tot_422]
  rfl

theorem tot_423 : totient 423 = 276 := by
  have heq : (3^2 * (47) : ℕ) = 423 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_47]
  try omega

theorem v3_phi_423 : v3_fast (totient 423) 100 = v3_phi_list.getD 423 0 := by
  rw [tot_423]
  rfl

theorem tot_424 : totient 424 = 208 := by
  have heq : (2^3 * (53) : ℕ) = 424 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_53]
  try omega

theorem v3_phi_424 : v3_fast (totient 424) 100 = v3_phi_list.getD 424 0 := by
  rw [tot_424]
  rfl

theorem tot_425 : totient 425 = 320 := by
  have heq : (5^2 * (17) : ℕ) = 425 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_17]
  try omega

theorem v3_phi_425 : v3_fast (totient 425) 100 = v3_phi_list.getD 425 0 := by
  rw [tot_425]
  rfl

theorem tot_426 : totient 426 = 140 := by
  have heq : (2 * (3 * (71)) : ℕ) = 426 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_71]
  try omega

theorem v3_phi_426 : v3_fast (totient 426) 100 = v3_phi_list.getD 426 0 := by
  rw [tot_426]
  rfl

theorem tot_427 : totient 427 = 360 := by
  have heq : (7 * (61) : ℕ) = 427 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_61]
  try omega

theorem v3_phi_427 : v3_fast (totient 427) 100 = v3_phi_list.getD 427 0 := by
  rw [tot_427]
  rfl

theorem tot_428 : totient 428 = 212 := by
  have heq : (2^2 * (107) : ℕ) = 428 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_107]
  try omega

theorem v3_phi_428 : v3_fast (totient 428) 100 = v3_phi_list.getD 428 0 := by
  rw [tot_428]
  rfl

theorem tot_429 : totient 429 = 240 := by
  have heq : (3 * (11 * (13)) : ℕ) = 429 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11, hp_13]
  try omega

theorem v3_phi_429 : v3_fast (totient 429) 100 = v3_phi_list.getD 429 0 := by
  rw [tot_429]
  rfl

theorem tot_430 : totient 430 = 168 := by
  have heq : (2 * (5 * (43)) : ℕ) = 430 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_43]
  try omega

theorem v3_phi_430 : v3_fast (totient 430) 100 = v3_phi_list.getD 430 0 := by
  rw [tot_430]
  rfl

theorem tot_431 : totient 431 = 430 := by
  have h : totient 431 = 431 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_431 : v3_fast (totient 431) 100 = v3_phi_list.getD 431 0 := by
  rw [tot_431]
  rfl

theorem tot_432 : totient 432 = 144 := by
  have heq : (2^4 * (3^3) : ℕ) = 432 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3]
  try omega

theorem v3_phi_432 : v3_fast (totient 432) 100 = v3_phi_list.getD 432 0 := by
  rw [tot_432]
  rfl

theorem tot_433 : totient 433 = 432 := by
  have h : totient 433 = 433 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_433 : v3_fast (totient 433) 100 = v3_phi_list.getD 433 0 := by
  rw [tot_433]
  rfl

theorem tot_434 : totient 434 = 180 := by
  have heq : (2 * (7 * (31)) : ℕ) = 434 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_31]
  try omega

theorem v3_phi_434 : v3_fast (totient 434) 100 = v3_phi_list.getD 434 0 := by
  rw [tot_434]
  rfl

theorem tot_435 : totient 435 = 224 := by
  have heq : (3 * (5 * (29)) : ℕ) = 435 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_29]
  try omega

theorem v3_phi_435 : v3_fast (totient 435) 100 = v3_phi_list.getD 435 0 := by
  rw [tot_435]
  rfl

theorem tot_436 : totient 436 = 216 := by
  have heq : (2^2 * (109) : ℕ) = 436 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_109]
  try omega

theorem v3_phi_436 : v3_fast (totient 436) 100 = v3_phi_list.getD 436 0 := by
  rw [tot_436]
  rfl

theorem tot_437 : totient 437 = 396 := by
  have heq : (19 * (23) : ℕ) = 437 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_23]
  try omega

theorem v3_phi_437 : v3_fast (totient 437) 100 = v3_phi_list.getD 437 0 := by
  rw [tot_437]
  rfl

theorem tot_438 : totient 438 = 144 := by
  have heq : (2 * (3 * (73)) : ℕ) = 438 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_73]
  try omega

theorem v3_phi_438 : v3_fast (totient 438) 100 = v3_phi_list.getD 438 0 := by
  rw [tot_438]
  rfl

theorem tot_439 : totient 439 = 438 := by
  have h : totient 439 = 439 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_439 : v3_fast (totient 439) 100 = v3_phi_list.getD 439 0 := by
  rw [tot_439]
  rfl

theorem tot_440 : totient 440 = 160 := by
  have heq : (2^3 * (5 * (11)) : ℕ) = 440 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_11]
  try omega

theorem v3_phi_440 : v3_fast (totient 440) 100 = v3_phi_list.getD 440 0 := by
  rw [tot_440]
  rfl

theorem tot_441 : totient 441 = 252 := by
  have heq : (3^2 * (7^2) : ℕ) = 441 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_7]
  try omega

theorem v3_phi_441 : v3_fast (totient 441) 100 = v3_phi_list.getD 441 0 := by
  rw [tot_441]
  rfl

theorem tot_442 : totient 442 = 192 := by
  have heq : (2 * (13 * (17)) : ℕ) = 442 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_17]
  try omega

theorem v3_phi_442 : v3_fast (totient 442) 100 = v3_phi_list.getD 442 0 := by
  rw [tot_442]
  rfl

theorem tot_443 : totient 443 = 442 := by
  have h : totient 443 = 443 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_443 : v3_fast (totient 443) 100 = v3_phi_list.getD 443 0 := by
  rw [tot_443]
  rfl

theorem tot_444 : totient 444 = 144 := by
  have heq : (2^2 * (3 * (37)) : ℕ) = 444 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_37]
  try omega

theorem v3_phi_444 : v3_fast (totient 444) 100 = v3_phi_list.getD 444 0 := by
  rw [tot_444]
  rfl

theorem tot_445 : totient 445 = 352 := by
  have heq : (5 * (89) : ℕ) = 445 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_89]
  try omega

theorem v3_phi_445 : v3_fast (totient 445) 100 = v3_phi_list.getD 445 0 := by
  rw [tot_445]
  rfl

theorem tot_446 : totient 446 = 222 := by
  have heq : (2 * (223) : ℕ) = 446 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_223 : totient 223 = 223 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_223]
  try omega

theorem v3_phi_446 : v3_fast (totient 446) 100 = v3_phi_list.getD 446 0 := by
  rw [tot_446]
  rfl

theorem tot_447 : totient 447 = 296 := by
  have heq : (3 * (149) : ℕ) = 447 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_149 : totient 149 = 149 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_149]
  try omega

theorem v3_phi_447 : v3_fast (totient 447) 100 = v3_phi_list.getD 447 0 := by
  rw [tot_447]
  rfl

theorem tot_448 : totient 448 = 192 := by
  have heq : (2^6 * (7) : ℕ) = 448 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^6) = 2^5 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7]
  try omega

theorem v3_phi_448 : v3_fast (totient 448) 100 = v3_phi_list.getD 448 0 := by
  rw [tot_448]
  rfl

theorem tot_449 : totient 449 = 448 := by
  have h : totient 449 = 449 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_449 : v3_fast (totient 449) 100 = v3_phi_list.getD 449 0 := by
  rw [tot_449]
  rfl

theorem tot_450 : totient 450 = 120 := by
  have heq : (2 * (3^2 * (5^2)) : ℕ) = 450 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_5]
  try omega

theorem v3_phi_450 : v3_fast (totient 450) 100 = v3_phi_list.getD 450 0 := by
  rw [tot_450]
  rfl

theorem tot_451 : totient 451 = 400 := by
  have heq : (11 * (41) : ℕ) = 451 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_41]
  try omega

theorem v3_phi_451 : v3_fast (totient 451) 100 = v3_phi_list.getD 451 0 := by
  rw [tot_451]
  rfl

theorem tot_452 : totient 452 = 224 := by
  have heq : (2^2 * (113) : ℕ) = 452 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_113 : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_113]
  try omega

theorem v3_phi_452 : v3_fast (totient 452) 100 = v3_phi_list.getD 452 0 := by
  rw [tot_452]
  rfl

theorem tot_453 : totient 453 = 300 := by
  have heq : (3 * (151) : ℕ) = 453 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_151 : totient 151 = 151 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_151]
  try omega

theorem v3_phi_453 : v3_fast (totient 453) 100 = v3_phi_list.getD 453 0 := by
  rw [tot_453]
  rfl

theorem tot_454 : totient 454 = 226 := by
  have heq : (2 * (227) : ℕ) = 454 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_227 : totient 227 = 227 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_227]
  try omega

theorem v3_phi_454 : v3_fast (totient 454) 100 = v3_phi_list.getD 454 0 := by
  rw [tot_454]
  rfl

theorem tot_455 : totient 455 = 288 := by
  have heq : (5 * (7 * (13)) : ℕ) = 455 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_7, hp_13]
  try omega

theorem v3_phi_455 : v3_fast (totient 455) 100 = v3_phi_list.getD 455 0 := by
  rw [tot_455]
  rfl

theorem tot_456 : totient 456 = 144 := by
  have heq : (2^3 * (3 * (19)) : ℕ) = 456 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_19]
  try omega

theorem v3_phi_456 : v3_fast (totient 456) 100 = v3_phi_list.getD 456 0 := by
  rw [tot_456]
  rfl

theorem tot_457 : totient 457 = 456 := by
  have h : totient 457 = 457 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_457 : v3_fast (totient 457) 100 = v3_phi_list.getD 457 0 := by
  rw [tot_457]
  rfl

theorem tot_458 : totient 458 = 228 := by
  have heq : (2 * (229) : ℕ) = 458 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_229 : totient 229 = 229 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_229]
  try omega

theorem v3_phi_458 : v3_fast (totient 458) 100 = v3_phi_list.getD 458 0 := by
  rw [tot_458]
  rfl

theorem tot_459 : totient 459 = 288 := by
  have heq : (3^3 * (17) : ℕ) = 459 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_17]
  try omega

theorem v3_phi_459 : v3_fast (totient 459) 100 = v3_phi_list.getD 459 0 := by
  rw [tot_459]
  rfl

theorem v3_phi_eq_list_0 (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 459) : v3_fast k.totient 100 = v3_phi_list.getD k 0 := by
  have heq : k = 1 + (k - 1) := by omega
  revert hk1 hk2
  rw [heq]
  match k - 1 with
  | 0 => intro _ _; exact v3_phi_1
  | 1 => intro _ _; exact v3_phi_2
  | 2 => intro _ _; exact v3_phi_3
  | 3 => intro _ _; exact v3_phi_4
  | 4 => intro _ _; exact v3_phi_5
  | 5 => intro _ _; exact v3_phi_6
  | 6 => intro _ _; exact v3_phi_7
  | 7 => intro _ _; exact v3_phi_8
  | 8 => intro _ _; exact v3_phi_9
  | 9 => intro _ _; exact v3_phi_10
  | 10 => intro _ _; exact v3_phi_11
  | 11 => intro _ _; exact v3_phi_12
  | 12 => intro _ _; exact v3_phi_13
  | 13 => intro _ _; exact v3_phi_14
  | 14 => intro _ _; exact v3_phi_15
  | 15 => intro _ _; exact v3_phi_16
  | 16 => intro _ _; exact v3_phi_17
  | 17 => intro _ _; exact v3_phi_18
  | 18 => intro _ _; exact v3_phi_19
  | 19 => intro _ _; exact v3_phi_20
  | 20 => intro _ _; exact v3_phi_21
  | 21 => intro _ _; exact v3_phi_22
  | 22 => intro _ _; exact v3_phi_23
  | 23 => intro _ _; exact v3_phi_24
  | 24 => intro _ _; exact v3_phi_25
  | 25 => intro _ _; exact v3_phi_26
  | 26 => intro _ _; exact v3_phi_27
  | 27 => intro _ _; exact v3_phi_28
  | 28 => intro _ _; exact v3_phi_29
  | 29 => intro _ _; exact v3_phi_30
  | 30 => intro _ _; exact v3_phi_31
  | 31 => intro _ _; exact v3_phi_32
  | 32 => intro _ _; exact v3_phi_33
  | 33 => intro _ _; exact v3_phi_34
  | 34 => intro _ _; exact v3_phi_35
  | 35 => intro _ _; exact v3_phi_36
  | 36 => intro _ _; exact v3_phi_37
  | 37 => intro _ _; exact v3_phi_38
  | 38 => intro _ _; exact v3_phi_39
  | 39 => intro _ _; exact v3_phi_40
  | 40 => intro _ _; exact v3_phi_41
  | 41 => intro _ _; exact v3_phi_42
  | 42 => intro _ _; exact v3_phi_43
  | 43 => intro _ _; exact v3_phi_44
  | 44 => intro _ _; exact v3_phi_45
  | 45 => intro _ _; exact v3_phi_46
  | 46 => intro _ _; exact v3_phi_47
  | 47 => intro _ _; exact v3_phi_48
  | 48 => intro _ _; exact v3_phi_49
  | 49 => intro _ _; exact v3_phi_50
  | 50 => intro _ _; exact v3_phi_51
  | 51 => intro _ _; exact v3_phi_52
  | 52 => intro _ _; exact v3_phi_53
  | 53 => intro _ _; exact v3_phi_54
  | 54 => intro _ _; exact v3_phi_55
  | 55 => intro _ _; exact v3_phi_56
  | 56 => intro _ _; exact v3_phi_57
  | 57 => intro _ _; exact v3_phi_58
  | 58 => intro _ _; exact v3_phi_59
  | 59 => intro _ _; exact v3_phi_60
  | 60 => intro _ _; exact v3_phi_61
  | 61 => intro _ _; exact v3_phi_62
  | 62 => intro _ _; exact v3_phi_63
  | 63 => intro _ _; exact v3_phi_64
  | 64 => intro _ _; exact v3_phi_65
  | 65 => intro _ _; exact v3_phi_66
  | 66 => intro _ _; exact v3_phi_67
  | 67 => intro _ _; exact v3_phi_68
  | 68 => intro _ _; exact v3_phi_69
  | 69 => intro _ _; exact v3_phi_70
  | 70 => intro _ _; exact v3_phi_71
  | 71 => intro _ _; exact v3_phi_72
  | 72 => intro _ _; exact v3_phi_73
  | 73 => intro _ _; exact v3_phi_74
  | 74 => intro _ _; exact v3_phi_75
  | 75 => intro _ _; exact v3_phi_76
  | 76 => intro _ _; exact v3_phi_77
  | 77 => intro _ _; exact v3_phi_78
  | 78 => intro _ _; exact v3_phi_79
  | 79 => intro _ _; exact v3_phi_80
  | 80 => intro _ _; exact v3_phi_81
  | 81 => intro _ _; exact v3_phi_82
  | 82 => intro _ _; exact v3_phi_83
  | 83 => intro _ _; exact v3_phi_84
  | 84 => intro _ _; exact v3_phi_85
  | 85 => intro _ _; exact v3_phi_86
  | 86 => intro _ _; exact v3_phi_87
  | 87 => intro _ _; exact v3_phi_88
  | 88 => intro _ _; exact v3_phi_89
  | 89 => intro _ _; exact v3_phi_90
  | 90 => intro _ _; exact v3_phi_91
  | 91 => intro _ _; exact v3_phi_92
  | 92 => intro _ _; exact v3_phi_93
  | 93 => intro _ _; exact v3_phi_94
  | 94 => intro _ _; exact v3_phi_95
  | 95 => intro _ _; exact v3_phi_96
  | 96 => intro _ _; exact v3_phi_97
  | 97 => intro _ _; exact v3_phi_98
  | 98 => intro _ _; exact v3_phi_99
  | 99 => intro _ _; exact v3_phi_100
  | 100 => intro _ _; exact v3_phi_101
  | 101 => intro _ _; exact v3_phi_102
  | 102 => intro _ _; exact v3_phi_103
  | 103 => intro _ _; exact v3_phi_104
  | 104 => intro _ _; exact v3_phi_105
  | 105 => intro _ _; exact v3_phi_106
  | 106 => intro _ _; exact v3_phi_107
  | 107 => intro _ _; exact v3_phi_108
  | 108 => intro _ _; exact v3_phi_109
  | 109 => intro _ _; exact v3_phi_110
  | 110 => intro _ _; exact v3_phi_111
  | 111 => intro _ _; exact v3_phi_112
  | 112 => intro _ _; exact v3_phi_113
  | 113 => intro _ _; exact v3_phi_114
  | 114 => intro _ _; exact v3_phi_115
  | 115 => intro _ _; exact v3_phi_116
  | 116 => intro _ _; exact v3_phi_117
  | 117 => intro _ _; exact v3_phi_118
  | 118 => intro _ _; exact v3_phi_119
  | 119 => intro _ _; exact v3_phi_120
  | 120 => intro _ _; exact v3_phi_121
  | 121 => intro _ _; exact v3_phi_122
  | 122 => intro _ _; exact v3_phi_123
  | 123 => intro _ _; exact v3_phi_124
  | 124 => intro _ _; exact v3_phi_125
  | 125 => intro _ _; exact v3_phi_126
  | 126 => intro _ _; exact v3_phi_127
  | 127 => intro _ _; exact v3_phi_128
  | 128 => intro _ _; exact v3_phi_129
  | 129 => intro _ _; exact v3_phi_130
  | 130 => intro _ _; exact v3_phi_131
  | 131 => intro _ _; exact v3_phi_132
  | 132 => intro _ _; exact v3_phi_133
  | 133 => intro _ _; exact v3_phi_134
  | 134 => intro _ _; exact v3_phi_135
  | 135 => intro _ _; exact v3_phi_136
  | 136 => intro _ _; exact v3_phi_137
  | 137 => intro _ _; exact v3_phi_138
  | 138 => intro _ _; exact v3_phi_139
  | 139 => intro _ _; exact v3_phi_140
  | 140 => intro _ _; exact v3_phi_141
  | 141 => intro _ _; exact v3_phi_142
  | 142 => intro _ _; exact v3_phi_143
  | 143 => intro _ _; exact v3_phi_144
  | 144 => intro _ _; exact v3_phi_145
  | 145 => intro _ _; exact v3_phi_146
  | 146 => intro _ _; exact v3_phi_147
  | 147 => intro _ _; exact v3_phi_148
  | 148 => intro _ _; exact v3_phi_149
  | 149 => intro _ _; exact v3_phi_150
  | 150 => intro _ _; exact v3_phi_151
  | 151 => intro _ _; exact v3_phi_152
  | 152 => intro _ _; exact v3_phi_153
  | 153 => intro _ _; exact v3_phi_154
  | 154 => intro _ _; exact v3_phi_155
  | 155 => intro _ _; exact v3_phi_156
  | 156 => intro _ _; exact v3_phi_157
  | 157 => intro _ _; exact v3_phi_158
  | 158 => intro _ _; exact v3_phi_159
  | 159 => intro _ _; exact v3_phi_160
  | 160 => intro _ _; exact v3_phi_161
  | 161 => intro _ _; exact v3_phi_162
  | 162 => intro _ _; exact v3_phi_163
  | 163 => intro _ _; exact v3_phi_164
  | 164 => intro _ _; exact v3_phi_165
  | 165 => intro _ _; exact v3_phi_166
  | 166 => intro _ _; exact v3_phi_167
  | 167 => intro _ _; exact v3_phi_168
  | 168 => intro _ _; exact v3_phi_169
  | 169 => intro _ _; exact v3_phi_170
  | 170 => intro _ _; exact v3_phi_171
  | 171 => intro _ _; exact v3_phi_172
  | 172 => intro _ _; exact v3_phi_173
  | 173 => intro _ _; exact v3_phi_174
  | 174 => intro _ _; exact v3_phi_175
  | 175 => intro _ _; exact v3_phi_176
  | 176 => intro _ _; exact v3_phi_177
  | 177 => intro _ _; exact v3_phi_178
  | 178 => intro _ _; exact v3_phi_179
  | 179 => intro _ _; exact v3_phi_180
  | 180 => intro _ _; exact v3_phi_181
  | 181 => intro _ _; exact v3_phi_182
  | 182 => intro _ _; exact v3_phi_183
  | 183 => intro _ _; exact v3_phi_184
  | 184 => intro _ _; exact v3_phi_185
  | 185 => intro _ _; exact v3_phi_186
  | 186 => intro _ _; exact v3_phi_187
  | 187 => intro _ _; exact v3_phi_188
  | 188 => intro _ _; exact v3_phi_189
  | 189 => intro _ _; exact v3_phi_190
  | 190 => intro _ _; exact v3_phi_191
  | 191 => intro _ _; exact v3_phi_192
  | 192 => intro _ _; exact v3_phi_193
  | 193 => intro _ _; exact v3_phi_194
  | 194 => intro _ _; exact v3_phi_195
  | 195 => intro _ _; exact v3_phi_196
  | 196 => intro _ _; exact v3_phi_197
  | 197 => intro _ _; exact v3_phi_198
  | 198 => intro _ _; exact v3_phi_199
  | 199 => intro _ _; exact v3_phi_200
  | 200 => intro _ _; exact v3_phi_201
  | 201 => intro _ _; exact v3_phi_202
  | 202 => intro _ _; exact v3_phi_203
  | 203 => intro _ _; exact v3_phi_204
  | 204 => intro _ _; exact v3_phi_205
  | 205 => intro _ _; exact v3_phi_206
  | 206 => intro _ _; exact v3_phi_207
  | 207 => intro _ _; exact v3_phi_208
  | 208 => intro _ _; exact v3_phi_209
  | 209 => intro _ _; exact v3_phi_210
  | 210 => intro _ _; exact v3_phi_211
  | 211 => intro _ _; exact v3_phi_212
  | 212 => intro _ _; exact v3_phi_213
  | 213 => intro _ _; exact v3_phi_214
  | 214 => intro _ _; exact v3_phi_215
  | 215 => intro _ _; exact v3_phi_216
  | 216 => intro _ _; exact v3_phi_217
  | 217 => intro _ _; exact v3_phi_218
  | 218 => intro _ _; exact v3_phi_219
  | 219 => intro _ _; exact v3_phi_220
  | 220 => intro _ _; exact v3_phi_221
  | 221 => intro _ _; exact v3_phi_222
  | 222 => intro _ _; exact v3_phi_223
  | 223 => intro _ _; exact v3_phi_224
  | 224 => intro _ _; exact v3_phi_225
  | 225 => intro _ _; exact v3_phi_226
  | 226 => intro _ _; exact v3_phi_227
  | 227 => intro _ _; exact v3_phi_228
  | 228 => intro _ _; exact v3_phi_229
  | 229 => intro _ _; exact v3_phi_230
  | 230 => intro _ _; exact v3_phi_231
  | 231 => intro _ _; exact v3_phi_232
  | 232 => intro _ _; exact v3_phi_233
  | 233 => intro _ _; exact v3_phi_234
  | 234 => intro _ _; exact v3_phi_235
  | 235 => intro _ _; exact v3_phi_236
  | 236 => intro _ _; exact v3_phi_237
  | 237 => intro _ _; exact v3_phi_238
  | 238 => intro _ _; exact v3_phi_239
  | 239 => intro _ _; exact v3_phi_240
  | 240 => intro _ _; exact v3_phi_241
  | 241 => intro _ _; exact v3_phi_242
  | 242 => intro _ _; exact v3_phi_243
  | 243 => intro _ _; exact v3_phi_244
  | 244 => intro _ _; exact v3_phi_245
  | 245 => intro _ _; exact v3_phi_246
  | 246 => intro _ _; exact v3_phi_247
  | 247 => intro _ _; exact v3_phi_248
  | 248 => intro _ _; exact v3_phi_249
  | 249 => intro _ _; exact v3_phi_250
  | 250 => intro _ _; exact v3_phi_251
  | 251 => intro _ _; exact v3_phi_252
  | 252 => intro _ _; exact v3_phi_253
  | 253 => intro _ _; exact v3_phi_254
  | 254 => intro _ _; exact v3_phi_255
  | 255 => intro _ _; exact v3_phi_256
  | 256 => intro _ _; exact v3_phi_257
  | 257 => intro _ _; exact v3_phi_258
  | 258 => intro _ _; exact v3_phi_259
  | 259 => intro _ _; exact v3_phi_260
  | 260 => intro _ _; exact v3_phi_261
  | 261 => intro _ _; exact v3_phi_262
  | 262 => intro _ _; exact v3_phi_263
  | 263 => intro _ _; exact v3_phi_264
  | 264 => intro _ _; exact v3_phi_265
  | 265 => intro _ _; exact v3_phi_266
  | 266 => intro _ _; exact v3_phi_267
  | 267 => intro _ _; exact v3_phi_268
  | 268 => intro _ _; exact v3_phi_269
  | 269 => intro _ _; exact v3_phi_270
  | 270 => intro _ _; exact v3_phi_271
  | 271 => intro _ _; exact v3_phi_272
  | 272 => intro _ _; exact v3_phi_273
  | 273 => intro _ _; exact v3_phi_274
  | 274 => intro _ _; exact v3_phi_275
  | 275 => intro _ _; exact v3_phi_276
  | 276 => intro _ _; exact v3_phi_277
  | 277 => intro _ _; exact v3_phi_278
  | 278 => intro _ _; exact v3_phi_279
  | 279 => intro _ _; exact v3_phi_280
  | 280 => intro _ _; exact v3_phi_281
  | 281 => intro _ _; exact v3_phi_282
  | 282 => intro _ _; exact v3_phi_283
  | 283 => intro _ _; exact v3_phi_284
  | 284 => intro _ _; exact v3_phi_285
  | 285 => intro _ _; exact v3_phi_286
  | 286 => intro _ _; exact v3_phi_287
  | 287 => intro _ _; exact v3_phi_288
  | 288 => intro _ _; exact v3_phi_289
  | 289 => intro _ _; exact v3_phi_290
  | 290 => intro _ _; exact v3_phi_291
  | 291 => intro _ _; exact v3_phi_292
  | 292 => intro _ _; exact v3_phi_293
  | 293 => intro _ _; exact v3_phi_294
  | 294 => intro _ _; exact v3_phi_295
  | 295 => intro _ _; exact v3_phi_296
  | 296 => intro _ _; exact v3_phi_297
  | 297 => intro _ _; exact v3_phi_298
  | 298 => intro _ _; exact v3_phi_299
  | 299 => intro _ _; exact v3_phi_300
  | 300 => intro _ _; exact v3_phi_301
  | 301 => intro _ _; exact v3_phi_302
  | 302 => intro _ _; exact v3_phi_303
  | 303 => intro _ _; exact v3_phi_304
  | 304 => intro _ _; exact v3_phi_305
  | 305 => intro _ _; exact v3_phi_306
  | 306 => intro _ _; exact v3_phi_307
  | 307 => intro _ _; exact v3_phi_308
  | 308 => intro _ _; exact v3_phi_309
  | 309 => intro _ _; exact v3_phi_310
  | 310 => intro _ _; exact v3_phi_311
  | 311 => intro _ _; exact v3_phi_312
  | 312 => intro _ _; exact v3_phi_313
  | 313 => intro _ _; exact v3_phi_314
  | 314 => intro _ _; exact v3_phi_315
  | 315 => intro _ _; exact v3_phi_316
  | 316 => intro _ _; exact v3_phi_317
  | 317 => intro _ _; exact v3_phi_318
  | 318 => intro _ _; exact v3_phi_319
  | 319 => intro _ _; exact v3_phi_320
  | 320 => intro _ _; exact v3_phi_321
  | 321 => intro _ _; exact v3_phi_322
  | 322 => intro _ _; exact v3_phi_323
  | 323 => intro _ _; exact v3_phi_324
  | 324 => intro _ _; exact v3_phi_325
  | 325 => intro _ _; exact v3_phi_326
  | 326 => intro _ _; exact v3_phi_327
  | 327 => intro _ _; exact v3_phi_328
  | 328 => intro _ _; exact v3_phi_329
  | 329 => intro _ _; exact v3_phi_330
  | 330 => intro _ _; exact v3_phi_331
  | 331 => intro _ _; exact v3_phi_332
  | 332 => intro _ _; exact v3_phi_333
  | 333 => intro _ _; exact v3_phi_334
  | 334 => intro _ _; exact v3_phi_335
  | 335 => intro _ _; exact v3_phi_336
  | 336 => intro _ _; exact v3_phi_337
  | 337 => intro _ _; exact v3_phi_338
  | 338 => intro _ _; exact v3_phi_339
  | 339 => intro _ _; exact v3_phi_340
  | 340 => intro _ _; exact v3_phi_341
  | 341 => intro _ _; exact v3_phi_342
  | 342 => intro _ _; exact v3_phi_343
  | 343 => intro _ _; exact v3_phi_344
  | 344 => intro _ _; exact v3_phi_345
  | 345 => intro _ _; exact v3_phi_346
  | 346 => intro _ _; exact v3_phi_347
  | 347 => intro _ _; exact v3_phi_348
  | 348 => intro _ _; exact v3_phi_349
  | 349 => intro _ _; exact v3_phi_350
  | 350 => intro _ _; exact v3_phi_351
  | 351 => intro _ _; exact v3_phi_352
  | 352 => intro _ _; exact v3_phi_353
  | 353 => intro _ _; exact v3_phi_354
  | 354 => intro _ _; exact v3_phi_355
  | 355 => intro _ _; exact v3_phi_356
  | 356 => intro _ _; exact v3_phi_357
  | 357 => intro _ _; exact v3_phi_358
  | 358 => intro _ _; exact v3_phi_359
  | 359 => intro _ _; exact v3_phi_360
  | 360 => intro _ _; exact v3_phi_361
  | 361 => intro _ _; exact v3_phi_362
  | 362 => intro _ _; exact v3_phi_363
  | 363 => intro _ _; exact v3_phi_364
  | 364 => intro _ _; exact v3_phi_365
  | 365 => intro _ _; exact v3_phi_366
  | 366 => intro _ _; exact v3_phi_367
  | 367 => intro _ _; exact v3_phi_368
  | 368 => intro _ _; exact v3_phi_369
  | 369 => intro _ _; exact v3_phi_370
  | 370 => intro _ _; exact v3_phi_371
  | 371 => intro _ _; exact v3_phi_372
  | 372 => intro _ _; exact v3_phi_373
  | 373 => intro _ _; exact v3_phi_374
  | 374 => intro _ _; exact v3_phi_375
  | 375 => intro _ _; exact v3_phi_376
  | 376 => intro _ _; exact v3_phi_377
  | 377 => intro _ _; exact v3_phi_378
  | 378 => intro _ _; exact v3_phi_379
  | 379 => intro _ _; exact v3_phi_380
  | 380 => intro _ _; exact v3_phi_381
  | 381 => intro _ _; exact v3_phi_382
  | 382 => intro _ _; exact v3_phi_383
  | 383 => intro _ _; exact v3_phi_384
  | 384 => intro _ _; exact v3_phi_385
  | 385 => intro _ _; exact v3_phi_386
  | 386 => intro _ _; exact v3_phi_387
  | 387 => intro _ _; exact v3_phi_388
  | 388 => intro _ _; exact v3_phi_389
  | 389 => intro _ _; exact v3_phi_390
  | 390 => intro _ _; exact v3_phi_391
  | 391 => intro _ _; exact v3_phi_392
  | 392 => intro _ _; exact v3_phi_393
  | 393 => intro _ _; exact v3_phi_394
  | 394 => intro _ _; exact v3_phi_395
  | 395 => intro _ _; exact v3_phi_396
  | 396 => intro _ _; exact v3_phi_397
  | 397 => intro _ _; exact v3_phi_398
  | 398 => intro _ _; exact v3_phi_399
  | 399 => intro _ _; exact v3_phi_400
  | 400 => intro _ _; exact v3_phi_401
  | 401 => intro _ _; exact v3_phi_402
  | 402 => intro _ _; exact v3_phi_403
  | 403 => intro _ _; exact v3_phi_404
  | 404 => intro _ _; exact v3_phi_405
  | 405 => intro _ _; exact v3_phi_406
  | 406 => intro _ _; exact v3_phi_407
  | 407 => intro _ _; exact v3_phi_408
  | 408 => intro _ _; exact v3_phi_409
  | 409 => intro _ _; exact v3_phi_410
  | 410 => intro _ _; exact v3_phi_411
  | 411 => intro _ _; exact v3_phi_412
  | 412 => intro _ _; exact v3_phi_413
  | 413 => intro _ _; exact v3_phi_414
  | 414 => intro _ _; exact v3_phi_415
  | 415 => intro _ _; exact v3_phi_416
  | 416 => intro _ _; exact v3_phi_417
  | 417 => intro _ _; exact v3_phi_418
  | 418 => intro _ _; exact v3_phi_419
  | 419 => intro _ _; exact v3_phi_420
  | 420 => intro _ _; exact v3_phi_421
  | 421 => intro _ _; exact v3_phi_422
  | 422 => intro _ _; exact v3_phi_423
  | 423 => intro _ _; exact v3_phi_424
  | 424 => intro _ _; exact v3_phi_425
  | 425 => intro _ _; exact v3_phi_426
  | 426 => intro _ _; exact v3_phi_427
  | 427 => intro _ _; exact v3_phi_428
  | 428 => intro _ _; exact v3_phi_429
  | 429 => intro _ _; exact v3_phi_430
  | 430 => intro _ _; exact v3_phi_431
  | 431 => intro _ _; exact v3_phi_432
  | 432 => intro _ _; exact v3_phi_433
  | 433 => intro _ _; exact v3_phi_434
  | 434 => intro _ _; exact v3_phi_435
  | 435 => intro _ _; exact v3_phi_436
  | 436 => intro _ _; exact v3_phi_437
  | 437 => intro _ _; exact v3_phi_438
  | 438 => intro _ _; exact v3_phi_439
  | 439 => intro _ _; exact v3_phi_440
  | 440 => intro _ _; exact v3_phi_441
  | 441 => intro _ _; exact v3_phi_442
  | 442 => intro _ _; exact v3_phi_443
  | 443 => intro _ _; exact v3_phi_444
  | 444 => intro _ _; exact v3_phi_445
  | 445 => intro _ _; exact v3_phi_446
  | 446 => intro _ _; exact v3_phi_447
  | 447 => intro _ _; exact v3_phi_448
  | 448 => intro _ _; exact v3_phi_449
  | 449 => intro _ _; exact v3_phi_450
  | 450 => intro _ _; exact v3_phi_451
  | 451 => intro _ _; exact v3_phi_452
  | 452 => intro _ _; exact v3_phi_453
  | 453 => intro _ _; exact v3_phi_454
  | 454 => intro _ _; exact v3_phi_455
  | 455 => intro _ _; exact v3_phi_456
  | 456 => intro _ _; exact v3_phi_457
  | 457 => intro _ _; exact v3_phi_458
  | 458 => intro _ _; exact v3_phi_459
  | x + 459 => intro h1 h2; omega


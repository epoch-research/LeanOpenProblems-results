import Submission.Spec
open Nat Finset Rat

set_option maxHeartbeats 200000000
set_option maxRecDepth 20000000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def v3_fast (n : ℕ) (fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | f + 1 =>
    if n = 0 then 0
    else if n % 3 = 0 then 1 + v3_fast (n / 3) f
    else 0

theorem tot_1 : totient 1 = 1 := rfl

theorem tot_2 : totient 2 = 1 := by
  have h : totient 2 = 2 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_3 : totient 3 = 2 := by
  have h : totient 3 = 3 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_4 : totient 4 = 2 := by
  have h : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (2^2 : ℕ) = 4 := by decide
  rw [← heq]
  rw [h] <;> decide

theorem tot_5 : totient 5 = 4 := by
  have h : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_6 : totient 6 = 2 := by
  have heq : (2 * (3) : ℕ) = 6 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3] <;> decide

theorem tot_7 : totient 7 = 6 := by
  have h : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_8 : totient 8 = 4 := by
  have h : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (2^3 : ℕ) = 8 := by decide
  rw [← heq]
  rw [h] <;> decide

theorem tot_9 : totient 9 = 6 := by
  have h : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (3^2 : ℕ) = 9 := by decide
  rw [← heq]
  rw [h] <;> decide

theorem tot_10 : totient 10 = 4 := by
  have heq : (2 * (5) : ℕ) = 10 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5] <;> decide

theorem tot_11 : totient 11 = 10 := by
  have h : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_12 : totient 12 = 4 := by
  have heq : (2^2 * (3) : ℕ) = 12 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3] <;> decide

theorem tot_13 : totient 13 = 12 := by
  have h : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_14 : totient 14 = 6 := by
  have heq : (2 * (7) : ℕ) = 14 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7] <;> decide

theorem tot_15 : totient 15 = 8 := by
  have heq : (3 * (5) : ℕ) = 15 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5] <;> decide

theorem tot_16 : totient 16 = 8 := by
  have h : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (2^4 : ℕ) = 16 := by decide
  rw [← heq]
  rw [h] <;> decide

theorem tot_17 : totient 17 = 16 := by
  have h : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_18 : totient 18 = 6 := by
  have heq : (2 * (3^2) : ℕ) = 18 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3] <;> decide

theorem tot_19 : totient 19 = 18 := by
  have h : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_20 : totient 20 = 8 := by
  have heq : (2^2 * (5) : ℕ) = 20 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5] <;> decide

theorem tot_21 : totient 21 = 12 := by
  have heq : (3 * (7) : ℕ) = 21 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7] <;> decide

theorem tot_22 : totient 22 = 10 := by
  have heq : (2 * (11) : ℕ) = 22 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11] <;> decide

theorem tot_23 : totient 23 = 22 := by
  have h : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_24 : totient 24 = 8 := by
  have heq : (2^3 * (3) : ℕ) = 24 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3] <;> decide

theorem tot_25 : totient 25 = 20 := by
  have h : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (5^2 : ℕ) = 25 := by decide
  rw [← heq]
  rw [h] <;> decide

theorem tot_26 : totient 26 = 12 := by
  have heq : (2 * (13) : ℕ) = 26 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13] <;> decide

theorem tot_27 : totient 27 = 18 := by
  have h : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (3^3 : ℕ) = 27 := by decide
  rw [← heq]
  rw [h] <;> decide

theorem tot_28 : totient 28 = 12 := by
  have heq : (2^2 * (7) : ℕ) = 28 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7] <;> decide

theorem tot_29 : totient 29 = 28 := by
  have h : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_30 : totient 30 = 8 := by
  have heq : (2 * (3 * (5)) : ℕ) = 30 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5] <;> decide

theorem tot_31 : totient 31 = 30 := by
  have h : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_32 : totient 32 = 16 := by
  have h : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (2^5 : ℕ) = 32 := by decide
  rw [← heq]
  rw [h] <;> decide

theorem tot_33 : totient 33 = 20 := by
  have heq : (3 * (11) : ℕ) = 33 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11] <;> decide

theorem tot_34 : totient 34 = 16 := by
  have heq : (2 * (17) : ℕ) = 34 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17] <;> decide

theorem tot_35 : totient 35 = 24 := by
  have heq : (5 * (7) : ℕ) = 35 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_7] <;> decide

theorem tot_36 : totient 36 = 12 := by
  have heq : (2^2 * (3^2) : ℕ) = 36 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3] <;> decide

theorem tot_37 : totient 37 = 36 := by
  have h : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_38 : totient 38 = 18 := by
  have heq : (2 * (19) : ℕ) = 38 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_19] <;> decide

theorem tot_39 : totient 39 = 24 := by
  have heq : (3 * (13) : ℕ) = 39 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_13] <;> decide

theorem tot_40 : totient 40 = 16 := by
  have heq : (2^3 * (5) : ℕ) = 40 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5] <;> decide

theorem tot_41 : totient 41 = 40 := by
  have h : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_42 : totient 42 = 12 := by
  have heq : (2 * (3 * (7)) : ℕ) = 42 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7] <;> decide

theorem tot_43 : totient 43 = 42 := by
  have h : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_44 : totient 44 = 20 := by
  have heq : (2^2 * (11) : ℕ) = 44 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11] <;> decide

theorem tot_45 : totient 45 = 24 := by
  have heq : (3^2 * (5) : ℕ) = 45 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5] <;> decide

theorem tot_46 : totient 46 = 22 := by
  have heq : (2 * (23) : ℕ) = 46 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_23] <;> decide

theorem tot_47 : totient 47 = 46 := by
  have h : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_48 : totient 48 = 16 := by
  have heq : (2^4 * (3) : ℕ) = 48 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3] <;> decide

theorem tot_49 : totient 49 = 42 := by
  have h : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (7^2 : ℕ) = 49 := by decide
  rw [← heq]
  rw [h] <;> decide

theorem tot_50 : totient 50 = 20 := by
  have heq : (2 * (5^2) : ℕ) = 50 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_5] <;> decide

theorem tot_51 : totient 51 = 32 := by
  have heq : (3 * (17) : ℕ) = 51 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_17] <;> decide

theorem tot_52 : totient 52 = 24 := by
  have heq : (2^2 * (13) : ℕ) = 52 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13] <;> decide

theorem tot_53 : totient 53 = 52 := by
  have h : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_54 : totient 54 = 18 := by
  have heq : (2 * (3^3) : ℕ) = 54 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3] <;> decide

theorem tot_55 : totient 55 = 40 := by
  have heq : (5 * (11) : ℕ) = 55 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_11] <;> decide

theorem tot_56 : totient 56 = 24 := by
  have heq : (2^3 * (7) : ℕ) = 56 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7] <;> decide

theorem tot_57 : totient 57 = 36 := by
  have heq : (3 * (19) : ℕ) = 57 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_19] <;> decide

theorem tot_58 : totient 58 = 28 := by
  have heq : (2 * (29) : ℕ) = 58 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_29] <;> decide

theorem tot_59 : totient 59 = 58 := by
  have h : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_60 : totient 60 = 16 := by
  have heq : (2^2 * (3 * (5)) : ℕ) = 60 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5] <;> decide

theorem tot_61 : totient 61 = 60 := by
  have h : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_62 : totient 62 = 30 := by
  have heq : (2 * (31) : ℕ) = 62 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_31] <;> decide

theorem tot_63 : totient 63 = 36 := by
  have heq : (3^2 * (7) : ℕ) = 63 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7] <;> decide

theorem tot_64 : totient 64 = 32 := by
  have h : totient (2^6) = 2^5 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (2^6 : ℕ) = 64 := by decide
  rw [← heq]
  rw [h] <;> decide

theorem tot_65 : totient 65 = 48 := by
  have heq : (5 * (13) : ℕ) = 65 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_13] <;> decide

theorem tot_66 : totient 66 = 20 := by
  have heq : (2 * (3 * (11)) : ℕ) = 66 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11] <;> decide

theorem tot_67 : totient 67 = 66 := by
  have h : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_68 : totient 68 = 32 := by
  have heq : (2^2 * (17) : ℕ) = 68 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17] <;> decide

theorem tot_69 : totient 69 = 44 := by
  have heq : (3 * (23) : ℕ) = 69 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_23] <;> decide

theorem tot_70 : totient 70 = 24 := by
  have heq : (2 * (5 * (7)) : ℕ) = 70 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7] <;> decide

theorem tot_71 : totient 71 = 70 := by
  have h : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_72 : totient 72 = 24 := by
  have heq : (2^3 * (3^2) : ℕ) = 72 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3] <;> decide

theorem tot_73 : totient 73 = 72 := by
  have h : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_74 : totient 74 = 36 := by
  have heq : (2 * (37) : ℕ) = 74 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_37] <;> decide

theorem tot_75 : totient 75 = 40 := by
  have heq : (3 * (5^2) : ℕ) = 75 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_5] <;> decide

theorem tot_76 : totient 76 = 36 := by
  have heq : (2^2 * (19) : ℕ) = 76 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_19] <;> decide

theorem tot_77 : totient 77 = 60 := by
  have heq : (7 * (11) : ℕ) = 77 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_11] <;> decide

theorem tot_78 : totient 78 = 24 := by
  have heq : (2 * (3 * (13)) : ℕ) = 78 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_13] <;> decide

theorem tot_79 : totient 79 = 78 := by
  have h : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_80 : totient 80 = 32 := by
  have heq : (2^4 * (5) : ℕ) = 80 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5] <;> decide

theorem tot_81 : totient 81 = 54 := by
  have h : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (3^4 : ℕ) = 81 := by decide
  rw [← heq]
  rw [h] <;> decide

theorem tot_82 : totient 82 = 40 := by
  have heq : (2 * (41) : ℕ) = 82 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_41] <;> decide

theorem tot_83 : totient 83 = 82 := by
  have h : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_84 : totient 84 = 24 := by
  have heq : (2^2 * (3 * (7)) : ℕ) = 84 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7] <;> decide

theorem tot_85 : totient 85 = 64 := by
  have heq : (5 * (17) : ℕ) = 85 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_17] <;> decide

theorem tot_86 : totient 86 = 42 := by
  have heq : (2 * (43) : ℕ) = 86 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_43] <;> decide

theorem tot_87 : totient 87 = 56 := by
  have heq : (3 * (29) : ℕ) = 87 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_29] <;> decide

theorem tot_88 : totient 88 = 40 := by
  have heq : (2^3 * (11) : ℕ) = 88 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11] <;> decide

theorem tot_89 : totient 89 = 88 := by
  have h : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_90 : totient 90 = 24 := by
  have heq : (2 * (3^2 * (5)) : ℕ) = 90 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5] <;> decide

theorem tot_91 : totient 91 = 72 := by
  have heq : (7 * (13) : ℕ) = 91 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_13] <;> decide

theorem tot_92 : totient 92 = 44 := by
  have heq : (2^2 * (23) : ℕ) = 92 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_23] <;> decide

theorem tot_93 : totient 93 = 60 := by
  have heq : (3 * (31) : ℕ) = 93 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_31] <;> decide

theorem tot_94 : totient 94 = 46 := by
  have heq : (2 * (47) : ℕ) = 94 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_47] <;> decide

theorem tot_95 : totient 95 = 72 := by
  have heq : (5 * (19) : ℕ) = 95 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_19] <;> decide

theorem tot_96 : totient 96 = 32 := by
  have heq : (2^5 * (3) : ℕ) = 96 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3] <;> decide

theorem tot_97 : totient 97 = 96 := by
  have h : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_98 : totient 98 = 42 := by
  have heq : (2 * (7^2) : ℕ) = 98 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_7] <;> decide

theorem tot_99 : totient 99 = 60 := by
  have heq : (3^2 * (11) : ℕ) = 99 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11] <;> decide

theorem tot_100 : totient 100 = 40 := by
  have heq : (2^2 * (5^2) : ℕ) = 100 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_5] <;> decide

theorem tot_101 : totient 101 = 100 := by
  have h : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_102 : totient 102 = 32 := by
  have heq : (2 * (3 * (17)) : ℕ) = 102 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_17] <;> decide

theorem tot_103 : totient 103 = 102 := by
  have h : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_104 : totient 104 = 48 := by
  have heq : (2^3 * (13) : ℕ) = 104 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13] <;> decide

theorem tot_105 : totient 105 = 48 := by
  have heq : (3 * (5 * (7)) : ℕ) = 105 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_7] <;> decide

theorem tot_106 : totient 106 = 52 := by
  have heq : (2 * (53) : ℕ) = 106 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_53] <;> decide

theorem tot_107 : totient 107 = 106 := by
  have h : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_108 : totient 108 = 36 := by
  have heq : (2^2 * (3^3) : ℕ) = 108 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3] <;> decide

theorem tot_109 : totient 109 = 108 := by
  have h : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_110 : totient 110 = 40 := by
  have heq : (2 * (5 * (11)) : ℕ) = 110 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_11] <;> decide

theorem tot_111 : totient 111 = 72 := by
  have heq : (3 * (37) : ℕ) = 111 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_37] <;> decide

theorem tot_112 : totient 112 = 48 := by
  have heq : (2^4 * (7) : ℕ) = 112 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7] <;> decide

theorem tot_113 : totient 113 = 112 := by
  have h : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_114 : totient 114 = 36 := by
  have heq : (2 * (3 * (19)) : ℕ) = 114 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_19] <;> decide

theorem tot_115 : totient 115 = 88 := by
  have heq : (5 * (23) : ℕ) = 115 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_23] <;> decide

theorem tot_116 : totient 116 = 56 := by
  have heq : (2^2 * (29) : ℕ) = 116 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_29] <;> decide

theorem tot_117 : totient 117 = 72 := by
  have heq : (3^2 * (13) : ℕ) = 117 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_13] <;> decide

theorem tot_118 : totient 118 = 58 := by
  have heq : (2 * (59) : ℕ) = 118 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_59] <;> decide

theorem tot_119 : totient 119 = 96 := by
  have heq : (7 * (17) : ℕ) = 119 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_17] <;> decide

theorem tot_120 : totient 120 = 32 := by
  have heq : (2^3 * (3 * (5)) : ℕ) = 120 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5] <;> decide

theorem tot_121 : totient 121 = 110 := by
  have h : totient (11^2) = 11^1 * (11 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (11^2 : ℕ) = 121 := by decide
  rw [← heq]
  rw [h] <;> decide

theorem tot_122 : totient 122 = 60 := by
  have heq : (2 * (61) : ℕ) = 122 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_61] <;> decide

theorem tot_123 : totient 123 = 80 := by
  have heq : (3 * (41) : ℕ) = 123 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_41] <;> decide

theorem tot_124 : totient 124 = 60 := by
  have heq : (2^2 * (31) : ℕ) = 124 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_31] <;> decide

theorem tot_125 : totient 125 = 100 := by
  have h : totient (5^3) = 5^2 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (5^3 : ℕ) = 125 := by decide
  rw [← heq]
  rw [h] <;> decide

theorem tot_126 : totient 126 = 36 := by
  have heq : (2 * (3^2 * (7)) : ℕ) = 126 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7] <;> decide

theorem tot_127 : totient 127 = 126 := by
  have h : totient 127 = 127 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_128 : totient 128 = 64 := by
  have h : totient (2^7) = 2^6 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (2^7 : ℕ) = 128 := by decide
  rw [← heq]
  rw [h] <;> decide

theorem tot_129 : totient 129 = 84 := by
  have heq : (3 * (43) : ℕ) = 129 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_43] <;> decide

theorem tot_130 : totient 130 = 48 := by
  have heq : (2 * (5 * (13)) : ℕ) = 130 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_13] <;> decide

theorem tot_131 : totient 131 = 130 := by
  have h : totient 131 = 131 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_132 : totient 132 = 40 := by
  have heq : (2^2 * (3 * (11)) : ℕ) = 132 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11] <;> decide

theorem tot_133 : totient 133 = 108 := by
  have heq : (7 * (19) : ℕ) = 133 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_19] <;> decide

theorem tot_134 : totient 134 = 66 := by
  have heq : (2 * (67) : ℕ) = 134 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_67] <;> decide

theorem tot_135 : totient 135 = 72 := by
  have heq : (3^3 * (5) : ℕ) = 135 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5] <;> decide

theorem tot_136 : totient 136 = 64 := by
  have heq : (2^3 * (17) : ℕ) = 136 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17] <;> decide

theorem tot_137 : totient 137 = 136 := by
  have h : totient 137 = 137 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_138 : totient 138 = 44 := by
  have heq : (2 * (3 * (23)) : ℕ) = 138 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_23] <;> decide

theorem tot_139 : totient 139 = 138 := by
  have h : totient 139 = 139 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_140 : totient 140 = 48 := by
  have heq : (2^2 * (5 * (7)) : ℕ) = 140 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7] <;> decide

theorem tot_141 : totient 141 = 92 := by
  have heq : (3 * (47) : ℕ) = 141 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_47] <;> decide

theorem tot_142 : totient 142 = 70 := by
  have heq : (2 * (71) : ℕ) = 142 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_71] <;> decide

theorem tot_143 : totient 143 = 120 := by
  have heq : (11 * (13) : ℕ) = 143 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_13] <;> decide

theorem tot_144 : totient 144 = 48 := by
  have heq : (2^4 * (3^2) : ℕ) = 144 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3] <;> decide

theorem tot_145 : totient 145 = 112 := by
  have heq : (5 * (29) : ℕ) = 145 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_29] <;> decide

theorem tot_146 : totient 146 = 72 := by
  have heq : (2 * (73) : ℕ) = 146 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_73] <;> decide

theorem tot_147 : totient 147 = 84 := by
  have heq : (3 * (7^2) : ℕ) = 147 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_7] <;> decide

theorem tot_148 : totient 148 = 72 := by
  have heq : (2^2 * (37) : ℕ) = 148 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_37] <;> decide

theorem tot_149 : totient 149 = 148 := by
  have h : totient 149 = 149 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_150 : totient 150 = 40 := by
  have heq : (2 * (3 * (5^2)) : ℕ) = 150 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_5] <;> decide

theorem tot_151 : totient 151 = 150 := by
  have h : totient 151 = 151 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_152 : totient 152 = 72 := by
  have heq : (2^3 * (19) : ℕ) = 152 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_19] <;> decide

theorem tot_153 : totient 153 = 96 := by
  have heq : (3^2 * (17) : ℕ) = 153 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_17] <;> decide

theorem tot_154 : totient 154 = 60 := by
  have heq : (2 * (7 * (11)) : ℕ) = 154 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_11] <;> decide

theorem tot_155 : totient 155 = 120 := by
  have heq : (5 * (31) : ℕ) = 155 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_31] <;> decide

theorem tot_156 : totient 156 = 48 := by
  have heq : (2^2 * (3 * (13)) : ℕ) = 156 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_13] <;> decide

theorem tot_157 : totient 157 = 156 := by
  have h : totient 157 = 157 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_158 : totient 158 = 78 := by
  have heq : (2 * (79) : ℕ) = 158 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_79] <;> decide

theorem tot_159 : totient 159 = 104 := by
  have heq : (3 * (53) : ℕ) = 159 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_53] <;> decide

theorem tot_160 : totient 160 = 64 := by
  have heq : (2^5 * (5) : ℕ) = 160 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5] <;> decide

theorem tot_161 : totient 161 = 132 := by
  have heq : (7 * (23) : ℕ) = 161 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_23] <;> decide

theorem tot_162 : totient 162 = 54 := by
  have heq : (2 * (3^4) : ℕ) = 162 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3] <;> decide

theorem tot_163 : totient 163 = 162 := by
  have h : totient 163 = 163 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_164 : totient 164 = 80 := by
  have heq : (2^2 * (41) : ℕ) = 164 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_41] <;> decide

theorem tot_165 : totient 165 = 80 := by
  have heq : (3 * (5 * (11)) : ℕ) = 165 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_11] <;> decide

theorem tot_166 : totient 166 = 82 := by
  have heq : (2 * (83) : ℕ) = 166 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_83] <;> decide

theorem tot_167 : totient 167 = 166 := by
  have h : totient 167 = 167 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_168 : totient 168 = 48 := by
  have heq : (2^3 * (3 * (7)) : ℕ) = 168 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7] <;> decide

theorem tot_169 : totient 169 = 156 := by
  have h : totient (13^2) = 13^1 * (13 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (13^2 : ℕ) = 169 := by decide
  rw [← heq]
  rw [h] <;> decide

theorem tot_170 : totient 170 = 64 := by
  have heq : (2 * (5 * (17)) : ℕ) = 170 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_17] <;> decide

theorem tot_171 : totient 171 = 108 := by
  have heq : (3^2 * (19) : ℕ) = 171 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_19] <;> decide

theorem tot_172 : totient 172 = 84 := by
  have heq : (2^2 * (43) : ℕ) = 172 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_43] <;> decide

theorem tot_173 : totient 173 = 172 := by
  have h : totient 173 = 173 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_174 : totient 174 = 56 := by
  have heq : (2 * (3 * (29)) : ℕ) = 174 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_29] <;> decide

theorem tot_175 : totient 175 = 120 := by
  have heq : (5^2 * (7) : ℕ) = 175 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_7] <;> decide

theorem tot_176 : totient 176 = 80 := by
  have heq : (2^4 * (11) : ℕ) = 176 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11] <;> decide

theorem tot_177 : totient 177 = 116 := by
  have heq : (3 * (59) : ℕ) = 177 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_59] <;> decide

theorem tot_178 : totient 178 = 88 := by
  have heq : (2 * (89) : ℕ) = 178 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_89] <;> decide

theorem tot_179 : totient 179 = 178 := by
  have h : totient 179 = 179 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_180 : totient 180 = 48 := by
  have heq : (2^2 * (3^2 * (5)) : ℕ) = 180 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5] <;> decide

theorem tot_181 : totient 181 = 180 := by
  have h : totient 181 = 181 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_182 : totient 182 = 72 := by
  have heq : (2 * (7 * (13)) : ℕ) = 182 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_13] <;> decide

theorem tot_183 : totient 183 = 120 := by
  have heq : (3 * (61) : ℕ) = 183 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_61] <;> decide

theorem tot_184 : totient 184 = 88 := by
  have heq : (2^3 * (23) : ℕ) = 184 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_23] <;> decide

theorem tot_185 : totient 185 = 144 := by
  have heq : (5 * (37) : ℕ) = 185 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_37] <;> decide

theorem tot_186 : totient 186 = 60 := by
  have heq : (2 * (3 * (31)) : ℕ) = 186 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_31] <;> decide

theorem tot_187 : totient 187 = 160 := by
  have heq : (11 * (17) : ℕ) = 187 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_17] <;> decide

theorem tot_188 : totient 188 = 92 := by
  have heq : (2^2 * (47) : ℕ) = 188 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_47] <;> decide

theorem tot_189 : totient 189 = 108 := by
  have heq : (3^3 * (7) : ℕ) = 189 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7] <;> decide

theorem tot_190 : totient 190 = 72 := by
  have heq : (2 * (5 * (19)) : ℕ) = 190 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_19] <;> decide

theorem tot_191 : totient 191 = 190 := by
  have h : totient 191 = 191 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_192 : totient 192 = 64 := by
  have heq : (2^6 * (3) : ℕ) = 192 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^6) = 2^5 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3] <;> decide

theorem tot_193 : totient 193 = 192 := by
  have h : totient 193 = 193 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_194 : totient 194 = 96 := by
  have heq : (2 * (97) : ℕ) = 194 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_97] <;> decide

theorem tot_195 : totient 195 = 96 := by
  have heq : (3 * (5 * (13)) : ℕ) = 195 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_13] <;> decide

theorem tot_196 : totient 196 = 84 := by
  have heq : (2^2 * (7^2) : ℕ) = 196 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_7] <;> decide

theorem tot_197 : totient 197 = 196 := by
  have h : totient 197 = 197 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_198 : totient 198 = 60 := by
  have heq : (2 * (3^2 * (11)) : ℕ) = 198 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11] <;> decide

theorem tot_199 : totient 199 = 198 := by
  have h : totient 199 = 199 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_200 : totient 200 = 80 := by
  have heq : (2^3 * (5^2) : ℕ) = 200 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_5] <;> decide

theorem tot_201 : totient 201 = 132 := by
  have heq : (3 * (67) : ℕ) = 201 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_67] <;> decide

theorem tot_202 : totient 202 = 100 := by
  have heq : (2 * (101) : ℕ) = 202 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_101] <;> decide

theorem tot_203 : totient 203 = 168 := by
  have heq : (7 * (29) : ℕ) = 203 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_29] <;> decide

theorem tot_204 : totient 204 = 64 := by
  have heq : (2^2 * (3 * (17)) : ℕ) = 204 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_17] <;> decide

theorem tot_205 : totient 205 = 160 := by
  have heq : (5 * (41) : ℕ) = 205 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_41] <;> decide

theorem tot_206 : totient 206 = 102 := by
  have heq : (2 * (103) : ℕ) = 206 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_103] <;> decide

theorem tot_207 : totient 207 = 132 := by
  have heq : (3^2 * (23) : ℕ) = 207 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_23] <;> decide

theorem tot_208 : totient 208 = 96 := by
  have heq : (2^4 * (13) : ℕ) = 208 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13] <;> decide

theorem tot_209 : totient 209 = 180 := by
  have heq : (11 * (19) : ℕ) = 209 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_19] <;> decide

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
  rw [hp_2, hp_3, hp_5, hp_7] <;> decide

theorem tot_211 : totient 211 = 210 := by
  have h : totient 211 = 211 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_212 : totient 212 = 104 := by
  have heq : (2^2 * (53) : ℕ) = 212 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_53] <;> decide

theorem tot_213 : totient 213 = 140 := by
  have heq : (3 * (71) : ℕ) = 213 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_71] <;> decide

theorem tot_214 : totient 214 = 106 := by
  have heq : (2 * (107) : ℕ) = 214 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_107] <;> decide

theorem tot_215 : totient 215 = 168 := by
  have heq : (5 * (43) : ℕ) = 215 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_43] <;> decide

theorem tot_216 : totient 216 = 72 := by
  have heq : (2^3 * (3^3) : ℕ) = 216 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3] <;> decide

theorem tot_217 : totient 217 = 180 := by
  have heq : (7 * (31) : ℕ) = 217 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_31] <;> decide

theorem tot_218 : totient 218 = 108 := by
  have heq : (2 * (109) : ℕ) = 218 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_109] <;> decide

theorem tot_219 : totient 219 = 144 := by
  have heq : (3 * (73) : ℕ) = 219 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_73] <;> decide

theorem tot_220 : totient 220 = 80 := by
  have heq : (2^2 * (5 * (11)) : ℕ) = 220 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_11] <;> decide

theorem tot_221 : totient 221 = 192 := by
  have heq : (13 * (17) : ℕ) = 221 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_17] <;> decide

theorem tot_222 : totient 222 = 72 := by
  have heq : (2 * (3 * (37)) : ℕ) = 222 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_37] <;> decide

theorem tot_223 : totient 223 = 222 := by
  have h : totient 223 = 223 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_224 : totient 224 = 96 := by
  have heq : (2^5 * (7) : ℕ) = 224 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7] <;> decide

theorem tot_225 : totient 225 = 120 := by
  have heq : (3^2 * (5^2) : ℕ) = 225 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_5] <;> decide

theorem tot_226 : totient 226 = 112 := by
  have heq : (2 * (113) : ℕ) = 226 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_113 : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_113] <;> decide

theorem tot_227 : totient 227 = 226 := by
  have h : totient 227 = 227 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_228 : totient 228 = 72 := by
  have heq : (2^2 * (3 * (19)) : ℕ) = 228 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_19] <;> decide

theorem tot_229 : totient 229 = 228 := by
  have h : totient 229 = 229 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_230 : totient 230 = 88 := by
  have heq : (2 * (5 * (23)) : ℕ) = 230 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_23] <;> decide

theorem tot_231 : totient 231 = 120 := by
  have heq : (3 * (7 * (11)) : ℕ) = 231 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_11] <;> decide

theorem tot_232 : totient 232 = 112 := by
  have heq : (2^3 * (29) : ℕ) = 232 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_29] <;> decide

theorem tot_233 : totient 233 = 232 := by
  have h : totient 233 = 233 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_234 : totient 234 = 72 := by
  have heq : (2 * (3^2 * (13)) : ℕ) = 234 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_13] <;> decide

theorem tot_235 : totient 235 = 184 := by
  have heq : (5 * (47) : ℕ) = 235 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_47] <;> decide

theorem tot_236 : totient 236 = 116 := by
  have heq : (2^2 * (59) : ℕ) = 236 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_59] <;> decide

theorem tot_237 : totient 237 = 156 := by
  have heq : (3 * (79) : ℕ) = 237 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_79] <;> decide

theorem tot_238 : totient 238 = 96 := by
  have heq : (2 * (7 * (17)) : ℕ) = 238 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_17] <;> decide

theorem tot_239 : totient 239 = 238 := by
  have h : totient 239 = 239 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_240 : totient 240 = 64 := by
  have heq : (2^4 * (3 * (5)) : ℕ) = 240 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5] <;> decide

theorem tot_241 : totient 241 = 240 := by
  have h : totient 241 = 241 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_242 : totient 242 = 110 := by
  have heq : (2 * (11^2) : ℕ) = 242 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient (11^2) = 11^1 * (11 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_11] <;> decide

theorem tot_243 : totient 243 = 162 := by
  have h : totient (3^5) = 3^4 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (3^5 : ℕ) = 243 := by decide
  rw [← heq]
  rw [h] <;> decide

theorem tot_244 : totient 244 = 120 := by
  have heq : (2^2 * (61) : ℕ) = 244 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_61] <;> decide

theorem tot_245 : totient 245 = 168 := by
  have heq : (5 * (7^2) : ℕ) = 245 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_5, hp_7] <;> decide

theorem tot_246 : totient 246 = 80 := by
  have heq : (2 * (3 * (41)) : ℕ) = 246 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_41] <;> decide

theorem tot_247 : totient 247 = 216 := by
  have heq : (13 * (19) : ℕ) = 247 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_19] <;> decide

theorem tot_248 : totient 248 = 120 := by
  have heq : (2^3 * (31) : ℕ) = 248 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_31] <;> decide

theorem tot_249 : totient 249 = 164 := by
  have heq : (3 * (83) : ℕ) = 249 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_83] <;> decide

theorem tot_250 : totient 250 = 100 := by
  have heq : (2 * (5^3) : ℕ) = 250 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^3) = 5^2 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_5] <;> decide

theorem tot_251 : totient 251 = 250 := by
  have h : totient 251 = 251 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_252 : totient 252 = 72 := by
  have heq : (2^2 * (3^2 * (7)) : ℕ) = 252 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7] <;> decide

theorem tot_253 : totient 253 = 220 := by
  have heq : (11 * (23) : ℕ) = 253 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_23] <;> decide

theorem tot_254 : totient 254 = 126 := by
  have heq : (2 * (127) : ℕ) = 254 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_127 : totient 127 = 127 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_127] <;> decide

theorem tot_255 : totient 255 = 128 := by
  have heq : (3 * (5 * (17)) : ℕ) = 255 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_17] <;> decide

theorem tot_256 : totient 256 = 128 := by
  have h : totient (2^8) = 2^7 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (2^8 : ℕ) = 256 := by decide
  rw [← heq]
  rw [h] <;> decide

theorem tot_257 : totient 257 = 256 := by
  have h : totient 257 = 257 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_258 : totient 258 = 84 := by
  have heq : (2 * (3 * (43)) : ℕ) = 258 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_43] <;> decide

theorem tot_259 : totient 259 = 216 := by
  have heq : (7 * (37) : ℕ) = 259 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_37] <;> decide

theorem tot_260 : totient 260 = 96 := by
  have heq : (2^2 * (5 * (13)) : ℕ) = 260 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_13] <;> decide

theorem tot_261 : totient 261 = 168 := by
  have heq : (3^2 * (29) : ℕ) = 261 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_29] <;> decide

theorem tot_262 : totient 262 = 130 := by
  have heq : (2 * (131) : ℕ) = 262 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_131 : totient 131 = 131 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_131] <;> decide

theorem tot_263 : totient 263 = 262 := by
  have h : totient 263 = 263 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_264 : totient 264 = 80 := by
  have heq : (2^3 * (3 * (11)) : ℕ) = 264 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11] <;> decide

theorem tot_265 : totient 265 = 208 := by
  have heq : (5 * (53) : ℕ) = 265 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_53] <;> decide

theorem tot_266 : totient 266 = 108 := by
  have heq : (2 * (7 * (19)) : ℕ) = 266 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_19] <;> decide

theorem tot_267 : totient 267 = 176 := by
  have heq : (3 * (89) : ℕ) = 267 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_89] <;> decide

theorem tot_268 : totient 268 = 132 := by
  have heq : (2^2 * (67) : ℕ) = 268 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_67] <;> decide

theorem tot_269 : totient 269 = 268 := by
  have h : totient 269 = 269 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_270 : totient 270 = 72 := by
  have heq : (2 * (3^3 * (5)) : ℕ) = 270 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5] <;> decide

theorem tot_271 : totient 271 = 270 := by
  have h : totient 271 = 271 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_272 : totient 272 = 128 := by
  have heq : (2^4 * (17) : ℕ) = 272 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17] <;> decide

theorem tot_273 : totient 273 = 144 := by
  have heq : (3 * (7 * (13)) : ℕ) = 273 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_13] <;> decide

theorem tot_274 : totient 274 = 136 := by
  have heq : (2 * (137) : ℕ) = 274 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_137 : totient 137 = 137 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_137] <;> decide

theorem tot_275 : totient 275 = 200 := by
  have heq : (5^2 * (11) : ℕ) = 275 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_11] <;> decide

theorem tot_276 : totient 276 = 88 := by
  have heq : (2^2 * (3 * (23)) : ℕ) = 276 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_23] <;> decide

theorem tot_277 : totient 277 = 276 := by
  have h : totient 277 = 277 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_278 : totient 278 = 138 := by
  have heq : (2 * (139) : ℕ) = 278 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_139 : totient 139 = 139 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_139] <;> decide

theorem tot_279 : totient 279 = 180 := by
  have heq : (3^2 * (31) : ℕ) = 279 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_31] <;> decide

theorem tot_280 : totient 280 = 96 := by
  have heq : (2^3 * (5 * (7)) : ℕ) = 280 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7] <;> decide

theorem tot_281 : totient 281 = 280 := by
  have h : totient 281 = 281 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_282 : totient 282 = 92 := by
  have heq : (2 * (3 * (47)) : ℕ) = 282 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_47] <;> decide

theorem tot_283 : totient 283 = 282 := by
  have h : totient 283 = 283 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_284 : totient 284 = 140 := by
  have heq : (2^2 * (71) : ℕ) = 284 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_71] <;> decide

theorem tot_285 : totient 285 = 144 := by
  have heq : (3 * (5 * (19)) : ℕ) = 285 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_19] <;> decide

theorem tot_286 : totient 286 = 120 := by
  have heq : (2 * (11 * (13)) : ℕ) = 286 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_13] <;> decide

theorem tot_287 : totient 287 = 240 := by
  have heq : (7 * (41) : ℕ) = 287 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_41] <;> decide

theorem tot_288 : totient 288 = 96 := by
  have heq : (2^5 * (3^2) : ℕ) = 288 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3] <;> decide

theorem tot_289 : totient 289 = 272 := by
  have h : totient (17^2) = 17^1 * (17 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (17^2 : ℕ) = 289 := by decide
  rw [← heq]
  rw [h] <;> decide

theorem tot_290 : totient 290 = 112 := by
  have heq : (2 * (5 * (29)) : ℕ) = 290 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_29] <;> decide

theorem tot_291 : totient 291 = 192 := by
  have heq : (3 * (97) : ℕ) = 291 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_97] <;> decide

theorem tot_292 : totient 292 = 144 := by
  have heq : (2^2 * (73) : ℕ) = 292 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_73] <;> decide

theorem tot_293 : totient 293 = 292 := by
  have h : totient 293 = 293 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_294 : totient 294 = 84 := by
  have heq : (2 * (3 * (7^2)) : ℕ) = 294 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_7] <;> decide

theorem tot_295 : totient 295 = 232 := by
  have heq : (5 * (59) : ℕ) = 295 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_59] <;> decide

theorem tot_296 : totient 296 = 144 := by
  have heq : (2^3 * (37) : ℕ) = 296 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_37] <;> decide

theorem tot_297 : totient 297 = 180 := by
  have heq : (3^3 * (11) : ℕ) = 297 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11] <;> decide

theorem tot_298 : totient 298 = 148 := by
  have heq : (2 * (149) : ℕ) = 298 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_149 : totient 149 = 149 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_149] <;> decide

theorem tot_299 : totient 299 = 264 := by
  have heq : (13 * (23) : ℕ) = 299 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_23] <;> decide

theorem tot_300 : totient 300 = 80 := by
  have heq : (2^2 * (3 * (5^2)) : ℕ) = 300 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_5] <;> decide

theorem tot_301 : totient 301 = 252 := by
  have heq : (7 * (43) : ℕ) = 301 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_43] <;> decide

theorem tot_302 : totient 302 = 150 := by
  have heq : (2 * (151) : ℕ) = 302 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_151 : totient 151 = 151 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_151] <;> decide

theorem tot_303 : totient 303 = 200 := by
  have heq : (3 * (101) : ℕ) = 303 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_101] <;> decide

theorem tot_304 : totient 304 = 144 := by
  have heq : (2^4 * (19) : ℕ) = 304 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_19] <;> decide

theorem tot_305 : totient 305 = 240 := by
  have heq : (5 * (61) : ℕ) = 305 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_61] <;> decide

theorem tot_306 : totient 306 = 96 := by
  have heq : (2 * (3^2 * (17)) : ℕ) = 306 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_17] <;> decide

theorem tot_307 : totient 307 = 306 := by
  have h : totient 307 = 307 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_308 : totient 308 = 120 := by
  have heq : (2^2 * (7 * (11)) : ℕ) = 308 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_11] <;> decide

theorem tot_309 : totient 309 = 204 := by
  have heq : (3 * (103) : ℕ) = 309 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_103] <;> decide

theorem tot_310 : totient 310 = 120 := by
  have heq : (2 * (5 * (31)) : ℕ) = 310 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_31] <;> decide

theorem tot_311 : totient 311 = 310 := by
  have h : totient 311 = 311 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_312 : totient 312 = 96 := by
  have heq : (2^3 * (3 * (13)) : ℕ) = 312 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_13] <;> decide

theorem tot_313 : totient 313 = 312 := by
  have h : totient 313 = 313 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_314 : totient 314 = 156 := by
  have heq : (2 * (157) : ℕ) = 314 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_157 : totient 157 = 157 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_157] <;> decide

theorem tot_315 : totient 315 = 144 := by
  have heq : (3^2 * (5 * (7)) : ℕ) = 315 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_7] <;> decide

theorem tot_316 : totient 316 = 156 := by
  have heq : (2^2 * (79) : ℕ) = 316 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_79] <;> decide

theorem tot_317 : totient 317 = 316 := by
  have h : totient 317 = 317 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_318 : totient 318 = 104 := by
  have heq : (2 * (3 * (53)) : ℕ) = 318 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_53] <;> decide

theorem tot_319 : totient 319 = 280 := by
  have heq : (11 * (29) : ℕ) = 319 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_29] <;> decide

theorem tot_320 : totient 320 = 128 := by
  have heq : (2^6 * (5) : ℕ) = 320 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^6) = 2^5 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5] <;> decide

theorem tot_321 : totient 321 = 212 := by
  have heq : (3 * (107) : ℕ) = 321 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_107] <;> decide

theorem tot_322 : totient 322 = 132 := by
  have heq : (2 * (7 * (23)) : ℕ) = 322 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_23] <;> decide

theorem tot_323 : totient 323 = 288 := by
  have heq : (17 * (19) : ℕ) = 323 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_19] <;> decide

theorem tot_324 : totient 324 = 108 := by
  have heq : (2^2 * (3^4) : ℕ) = 324 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3] <;> decide

theorem tot_325 : totient 325 = 240 := by
  have heq : (5^2 * (13) : ℕ) = 325 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_13] <;> decide

theorem tot_326 : totient 326 = 162 := by
  have heq : (2 * (163) : ℕ) = 326 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_163 : totient 163 = 163 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_163] <;> decide

theorem tot_327 : totient 327 = 216 := by
  have heq : (3 * (109) : ℕ) = 327 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_109] <;> decide

theorem tot_328 : totient 328 = 160 := by
  have heq : (2^3 * (41) : ℕ) = 328 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_41] <;> decide

theorem tot_329 : totient 329 = 276 := by
  have heq : (7 * (47) : ℕ) = 329 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_47] <;> decide

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
  rw [hp_2, hp_3, hp_5, hp_11] <;> decide

theorem tot_331 : totient 331 = 330 := by
  have h : totient 331 = 331 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_332 : totient 332 = 164 := by
  have heq : (2^2 * (83) : ℕ) = 332 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_83] <;> decide

theorem tot_333 : totient 333 = 216 := by
  have heq : (3^2 * (37) : ℕ) = 333 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_37] <;> decide

theorem tot_334 : totient 334 = 166 := by
  have heq : (2 * (167) : ℕ) = 334 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_167 : totient 167 = 167 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_167] <;> decide

theorem tot_335 : totient 335 = 264 := by
  have heq : (5 * (67) : ℕ) = 335 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_67] <;> decide

theorem tot_336 : totient 336 = 96 := by
  have heq : (2^4 * (3 * (7)) : ℕ) = 336 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7] <;> decide

theorem tot_337 : totient 337 = 336 := by
  have h : totient 337 = 337 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_338 : totient 338 = 156 := by
  have heq : (2 * (13^2) : ℕ) = 338 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient (13^2) = 13^1 * (13 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_13] <;> decide

theorem tot_339 : totient 339 = 224 := by
  have heq : (3 * (113) : ℕ) = 339 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_113 : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_113] <;> decide

theorem tot_340 : totient 340 = 128 := by
  have heq : (2^2 * (5 * (17)) : ℕ) = 340 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_17] <;> decide

theorem tot_341 : totient 341 = 300 := by
  have heq : (11 * (31) : ℕ) = 341 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_31] <;> decide

theorem tot_342 : totient 342 = 108 := by
  have heq : (2 * (3^2 * (19)) : ℕ) = 342 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_19] <;> decide

theorem tot_343 : totient 343 = 294 := by
  have h : totient (7^3) = 7^2 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (7^3 : ℕ) = 343 := by decide
  rw [← heq]
  rw [h] <;> decide

theorem tot_344 : totient 344 = 168 := by
  have heq : (2^3 * (43) : ℕ) = 344 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_43] <;> decide

theorem tot_345 : totient 345 = 176 := by
  have heq : (3 * (5 * (23)) : ℕ) = 345 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_23] <;> decide

theorem tot_346 : totient 346 = 172 := by
  have heq : (2 * (173) : ℕ) = 346 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_173 : totient 173 = 173 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_173] <;> decide

theorem tot_347 : totient 347 = 346 := by
  have h : totient 347 = 347 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_348 : totient 348 = 112 := by
  have heq : (2^2 * (3 * (29)) : ℕ) = 348 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_29] <;> decide

theorem tot_349 : totient 349 = 348 := by
  have h : totient 349 = 349 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_350 : totient 350 = 120 := by
  have heq : (2 * (5^2 * (7)) : ℕ) = 350 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7] <;> decide

theorem tot_351 : totient 351 = 216 := by
  have heq : (3^3 * (13) : ℕ) = 351 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_13] <;> decide

theorem tot_352 : totient 352 = 160 := by
  have heq : (2^5 * (11) : ℕ) = 352 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11] <;> decide

theorem tot_353 : totient 353 = 352 := by
  have h : totient 353 = 353 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_354 : totient 354 = 116 := by
  have heq : (2 * (3 * (59)) : ℕ) = 354 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_59] <;> decide

theorem tot_355 : totient 355 = 280 := by
  have heq : (5 * (71) : ℕ) = 355 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_71] <;> decide

theorem tot_356 : totient 356 = 176 := by
  have heq : (2^2 * (89) : ℕ) = 356 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_89] <;> decide

theorem tot_357 : totient 357 = 192 := by
  have heq : (3 * (7 * (17)) : ℕ) = 357 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_17] <;> decide

theorem tot_358 : totient 358 = 178 := by
  have heq : (2 * (179) : ℕ) = 358 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_179 : totient 179 = 179 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_179] <;> decide

theorem tot_359 : totient 359 = 358 := by
  have h : totient 359 = 359 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_360 : totient 360 = 96 := by
  have heq : (2^3 * (3^2 * (5)) : ℕ) = 360 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5] <;> decide

theorem tot_361 : totient 361 = 342 := by
  have h : totient (19^2) = 19^1 * (19 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (19^2 : ℕ) = 361 := by decide
  rw [← heq]
  rw [h] <;> decide

theorem tot_362 : totient 362 = 180 := by
  have heq : (2 * (181) : ℕ) = 362 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_181 : totient 181 = 181 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_181] <;> decide

theorem tot_363 : totient 363 = 220 := by
  have heq : (3 * (11^2) : ℕ) = 363 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient (11^2) = 11^1 * (11 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_11] <;> decide

theorem tot_364 : totient 364 = 144 := by
  have heq : (2^2 * (7 * (13)) : ℕ) = 364 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_13] <;> decide

theorem tot_365 : totient 365 = 288 := by
  have heq : (5 * (73) : ℕ) = 365 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_73] <;> decide

theorem tot_366 : totient 366 = 120 := by
  have heq : (2 * (3 * (61)) : ℕ) = 366 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_61] <;> decide

theorem tot_367 : totient 367 = 366 := by
  have h : totient 367 = 367 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_368 : totient 368 = 176 := by
  have heq : (2^4 * (23) : ℕ) = 368 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_23] <;> decide

theorem tot_369 : totient 369 = 240 := by
  have heq : (3^2 * (41) : ℕ) = 369 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_41] <;> decide

theorem tot_370 : totient 370 = 144 := by
  have heq : (2 * (5 * (37)) : ℕ) = 370 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_37] <;> decide

theorem tot_371 : totient 371 = 312 := by
  have heq : (7 * (53) : ℕ) = 371 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_53] <;> decide

theorem tot_372 : totient 372 = 120 := by
  have heq : (2^2 * (3 * (31)) : ℕ) = 372 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_31] <;> decide

theorem tot_373 : totient 373 = 372 := by
  have h : totient 373 = 373 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_374 : totient 374 = 160 := by
  have heq : (2 * (11 * (17)) : ℕ) = 374 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_17] <;> decide

theorem tot_375 : totient 375 = 200 := by
  have heq : (3 * (5^3) : ℕ) = 375 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^3) = 5^2 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_5] <;> decide

theorem tot_376 : totient 376 = 184 := by
  have heq : (2^3 * (47) : ℕ) = 376 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_47] <;> decide

theorem tot_377 : totient 377 = 336 := by
  have heq : (13 * (29) : ℕ) = 377 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_29] <;> decide

theorem tot_378 : totient 378 = 108 := by
  have heq : (2 * (3^3 * (7)) : ℕ) = 378 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7] <;> decide

theorem tot_379 : totient 379 = 378 := by
  have h : totient 379 = 379 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_380 : totient 380 = 144 := by
  have heq : (2^2 * (5 * (19)) : ℕ) = 380 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_19] <;> decide

theorem tot_381 : totient 381 = 252 := by
  have heq : (3 * (127) : ℕ) = 381 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_127 : totient 127 = 127 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_127] <;> decide

theorem tot_382 : totient 382 = 190 := by
  have heq : (2 * (191) : ℕ) = 382 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_191 : totient 191 = 191 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_191] <;> decide

theorem tot_383 : totient 383 = 382 := by
  have h : totient 383 = 383 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_384 : totient 384 = 128 := by
  have heq : (2^7 * (3) : ℕ) = 384 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^7) = 2^6 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3] <;> decide

theorem tot_385 : totient 385 = 240 := by
  have heq : (5 * (7 * (11)) : ℕ) = 385 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_7, hp_11] <;> decide

theorem tot_386 : totient 386 = 192 := by
  have heq : (2 * (193) : ℕ) = 386 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_193 : totient 193 = 193 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_193] <;> decide

theorem tot_387 : totient 387 = 252 := by
  have heq : (3^2 * (43) : ℕ) = 387 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_43] <;> decide

theorem tot_388 : totient 388 = 192 := by
  have heq : (2^2 * (97) : ℕ) = 388 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_97] <;> decide

theorem tot_389 : totient 389 = 388 := by
  have h : totient 389 = 389 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

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
  rw [hp_2, hp_3, hp_5, hp_13] <;> decide

theorem tot_391 : totient 391 = 352 := by
  have heq : (17 * (23) : ℕ) = 391 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_23] <;> decide

theorem tot_392 : totient 392 = 168 := by
  have heq : (2^3 * (7^2) : ℕ) = 392 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_7] <;> decide

theorem tot_393 : totient 393 = 260 := by
  have heq : (3 * (131) : ℕ) = 393 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_131 : totient 131 = 131 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_131] <;> decide

theorem tot_394 : totient 394 = 196 := by
  have heq : (2 * (197) : ℕ) = 394 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_197 : totient 197 = 197 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_197] <;> decide

theorem tot_395 : totient 395 = 312 := by
  have heq : (5 * (79) : ℕ) = 395 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_79] <;> decide

theorem tot_396 : totient 396 = 120 := by
  have heq : (2^2 * (3^2 * (11)) : ℕ) = 396 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11] <;> decide

theorem tot_397 : totient 397 = 396 := by
  have h : totient 397 = 397 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_398 : totient 398 = 198 := by
  have heq : (2 * (199) : ℕ) = 398 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_199 : totient 199 = 199 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_199] <;> decide

theorem tot_399 : totient 399 = 216 := by
  have heq : (3 * (7 * (19)) : ℕ) = 399 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_19] <;> decide

theorem tot_400 : totient 400 = 160 := by
  have heq : (2^4 * (5^2) : ℕ) = 400 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_5] <;> decide

theorem tot_401 : totient 401 = 400 := by
  have h : totient 401 = 401 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_402 : totient 402 = 132 := by
  have heq : (2 * (3 * (67)) : ℕ) = 402 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_67] <;> decide

theorem tot_403 : totient 403 = 360 := by
  have heq : (13 * (31) : ℕ) = 403 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_31] <;> decide

theorem tot_404 : totient 404 = 200 := by
  have heq : (2^2 * (101) : ℕ) = 404 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_101] <;> decide

theorem tot_405 : totient 405 = 216 := by
  have heq : (3^4 * (5) : ℕ) = 405 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5] <;> decide

theorem tot_406 : totient 406 = 168 := by
  have heq : (2 * (7 * (29)) : ℕ) = 406 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_29] <;> decide

theorem tot_407 : totient 407 = 360 := by
  have heq : (11 * (37) : ℕ) = 407 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_37] <;> decide

theorem tot_408 : totient 408 = 128 := by
  have heq : (2^3 * (3 * (17)) : ℕ) = 408 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_17] <;> decide

theorem tot_409 : totient 409 = 408 := by
  have h : totient 409 = 409 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_410 : totient 410 = 160 := by
  have heq : (2 * (5 * (41)) : ℕ) = 410 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_41] <;> decide

theorem tot_411 : totient 411 = 272 := by
  have heq : (3 * (137) : ℕ) = 411 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_137 : totient 137 = 137 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_137] <;> decide

theorem tot_412 : totient 412 = 204 := by
  have heq : (2^2 * (103) : ℕ) = 412 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_103] <;> decide

theorem tot_413 : totient 413 = 348 := by
  have heq : (7 * (59) : ℕ) = 413 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_59] <;> decide

theorem tot_414 : totient 414 = 132 := by
  have heq : (2 * (3^2 * (23)) : ℕ) = 414 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_23] <;> decide

theorem tot_415 : totient 415 = 328 := by
  have heq : (5 * (83) : ℕ) = 415 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_83] <;> decide

theorem tot_416 : totient 416 = 192 := by
  have heq : (2^5 * (13) : ℕ) = 416 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13] <;> decide

theorem tot_417 : totient 417 = 276 := by
  have heq : (3 * (139) : ℕ) = 417 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_139 : totient 139 = 139 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_139] <;> decide

theorem tot_418 : totient 418 = 180 := by
  have heq : (2 * (11 * (19)) : ℕ) = 418 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_19] <;> decide

theorem tot_419 : totient 419 = 418 := by
  have h : totient 419 = 419 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

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
  rw [hp_2, hp_3, hp_5, hp_7] <;> decide

theorem tot_421 : totient 421 = 420 := by
  have h : totient 421 = 421 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_422 : totient 422 = 210 := by
  have heq : (2 * (211) : ℕ) = 422 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_211 : totient 211 = 211 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_211] <;> decide

theorem tot_423 : totient 423 = 276 := by
  have heq : (3^2 * (47) : ℕ) = 423 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_47] <;> decide

theorem tot_424 : totient 424 = 208 := by
  have heq : (2^3 * (53) : ℕ) = 424 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_53] <;> decide

theorem tot_425 : totient 425 = 320 := by
  have heq : (5^2 * (17) : ℕ) = 425 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_17] <;> decide

theorem tot_426 : totient 426 = 140 := by
  have heq : (2 * (3 * (71)) : ℕ) = 426 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_71] <;> decide

theorem tot_427 : totient 427 = 360 := by
  have heq : (7 * (61) : ℕ) = 427 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_61] <;> decide

theorem tot_428 : totient 428 = 212 := by
  have heq : (2^2 * (107) : ℕ) = 428 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_107] <;> decide

theorem tot_429 : totient 429 = 240 := by
  have heq : (3 * (11 * (13)) : ℕ) = 429 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11, hp_13] <;> decide

theorem tot_430 : totient 430 = 168 := by
  have heq : (2 * (5 * (43)) : ℕ) = 430 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_43] <;> decide

theorem tot_431 : totient 431 = 430 := by
  have h : totient 431 = 431 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_432 : totient 432 = 144 := by
  have heq : (2^4 * (3^3) : ℕ) = 432 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3] <;> decide

theorem tot_433 : totient 433 = 432 := by
  have h : totient 433 = 433 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_434 : totient 434 = 180 := by
  have heq : (2 * (7 * (31)) : ℕ) = 434 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_31] <;> decide

theorem tot_435 : totient 435 = 224 := by
  have heq : (3 * (5 * (29)) : ℕ) = 435 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_29] <;> decide

theorem tot_436 : totient 436 = 216 := by
  have heq : (2^2 * (109) : ℕ) = 436 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_109] <;> decide

theorem tot_437 : totient 437 = 396 := by
  have heq : (19 * (23) : ℕ) = 437 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_23] <;> decide

theorem tot_438 : totient 438 = 144 := by
  have heq : (2 * (3 * (73)) : ℕ) = 438 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_73] <;> decide

theorem tot_439 : totient 439 = 438 := by
  have h : totient 439 = 439 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_440 : totient 440 = 160 := by
  have heq : (2^3 * (5 * (11)) : ℕ) = 440 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_11] <;> decide

theorem tot_441 : totient 441 = 252 := by
  have heq : (3^2 * (7^2) : ℕ) = 441 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_7] <;> decide

theorem tot_442 : totient 442 = 192 := by
  have heq : (2 * (13 * (17)) : ℕ) = 442 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_17] <;> decide

theorem tot_443 : totient 443 = 442 := by
  have h : totient 443 = 443 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_444 : totient 444 = 144 := by
  have heq : (2^2 * (3 * (37)) : ℕ) = 444 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_37] <;> decide

theorem tot_445 : totient 445 = 352 := by
  have heq : (5 * (89) : ℕ) = 445 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_89] <;> decide

theorem tot_446 : totient 446 = 222 := by
  have heq : (2 * (223) : ℕ) = 446 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_223 : totient 223 = 223 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_223] <;> decide

theorem tot_447 : totient 447 = 296 := by
  have heq : (3 * (149) : ℕ) = 447 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_149 : totient 149 = 149 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_149] <;> decide

theorem tot_448 : totient 448 = 192 := by
  have heq : (2^6 * (7) : ℕ) = 448 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^6) = 2^5 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7] <;> decide

theorem tot_449 : totient 449 = 448 := by
  have h : totient 449 = 449 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_450 : totient 450 = 120 := by
  have heq : (2 * (3^2 * (5^2)) : ℕ) = 450 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_5] <;> decide

theorem tot_451 : totient 451 = 400 := by
  have heq : (11 * (41) : ℕ) = 451 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_41] <;> decide

theorem tot_452 : totient 452 = 224 := by
  have heq : (2^2 * (113) : ℕ) = 452 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_113 : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_113] <;> decide

theorem tot_453 : totient 453 = 300 := by
  have heq : (3 * (151) : ℕ) = 453 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_151 : totient 151 = 151 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_151] <;> decide

theorem tot_454 : totient 454 = 226 := by
  have heq : (2 * (227) : ℕ) = 454 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_227 : totient 227 = 227 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_227] <;> decide

theorem tot_455 : totient 455 = 288 := by
  have heq : (5 * (7 * (13)) : ℕ) = 455 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_7, hp_13] <;> decide

theorem tot_456 : totient 456 = 144 := by
  have heq : (2^3 * (3 * (19)) : ℕ) = 456 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_19] <;> decide

theorem tot_457 : totient 457 = 456 := by
  have h : totient 457 = 457 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_458 : totient 458 = 228 := by
  have heq : (2 * (229) : ℕ) = 458 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_229 : totient 229 = 229 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_229] <;> decide

theorem tot_459 : totient 459 = 288 := by
  have heq : (3^3 * (17) : ℕ) = 459 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_17] <;> decide

theorem tot_460 : totient 460 = 176 := by
  have heq : (2^2 * (5 * (23)) : ℕ) = 460 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_23] <;> decide

theorem tot_461 : totient 461 = 460 := by
  have h : totient 461 = 461 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_462 : totient 462 = 120 := by
  have heq : (2 * (3 * (7 * (11))) : ℕ) = 462 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_11] <;> decide

theorem tot_463 : totient 463 = 462 := by
  have h : totient 463 = 463 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_464 : totient 464 = 224 := by
  have heq : (2^4 * (29) : ℕ) = 464 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_29] <;> decide

theorem tot_465 : totient 465 = 240 := by
  have heq : (3 * (5 * (31)) : ℕ) = 465 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_31] <;> decide

theorem tot_466 : totient 466 = 232 := by
  have heq : (2 * (233) : ℕ) = 466 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_233 : totient 233 = 233 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_233] <;> decide

theorem tot_467 : totient 467 = 466 := by
  have h : totient 467 = 467 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_468 : totient 468 = 144 := by
  have heq : (2^2 * (3^2 * (13)) : ℕ) = 468 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_13] <;> decide

theorem tot_469 : totient 469 = 396 := by
  have heq : (7 * (67) : ℕ) = 469 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_67] <;> decide

theorem tot_470 : totient 470 = 184 := by
  have heq : (2 * (5 * (47)) : ℕ) = 470 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_47] <;> decide

theorem tot_471 : totient 471 = 312 := by
  have heq : (3 * (157) : ℕ) = 471 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_157 : totient 157 = 157 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_157] <;> decide

theorem tot_472 : totient 472 = 232 := by
  have heq : (2^3 * (59) : ℕ) = 472 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_59] <;> decide

theorem tot_473 : totient 473 = 420 := by
  have heq : (11 * (43) : ℕ) = 473 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_43] <;> decide

theorem tot_474 : totient 474 = 156 := by
  have heq : (2 * (3 * (79)) : ℕ) = 474 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_79] <;> decide

theorem tot_475 : totient 475 = 360 := by
  have heq : (5^2 * (19) : ℕ) = 475 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_19] <;> decide

theorem tot_476 : totient 476 = 192 := by
  have heq : (2^2 * (7 * (17)) : ℕ) = 476 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_17] <;> decide

theorem tot_477 : totient 477 = 312 := by
  have heq : (3^2 * (53) : ℕ) = 477 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_53] <;> decide

theorem tot_478 : totient 478 = 238 := by
  have heq : (2 * (239) : ℕ) = 478 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_239 : totient 239 = 239 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_239] <;> decide

theorem tot_479 : totient 479 = 478 := by
  have h : totient 479 = 479 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_480 : totient 480 = 128 := by
  have heq : (2^5 * (3 * (5)) : ℕ) = 480 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5] <;> decide

theorem tot_481 : totient 481 = 432 := by
  have heq : (13 * (37) : ℕ) = 481 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_37] <;> decide

theorem tot_482 : totient 482 = 240 := by
  have heq : (2 * (241) : ℕ) = 482 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_241 : totient 241 = 241 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_241] <;> decide

theorem tot_483 : totient 483 = 264 := by
  have heq : (3 * (7 * (23)) : ℕ) = 483 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_23] <;> decide

theorem tot_484 : totient 484 = 220 := by
  have heq : (2^2 * (11^2) : ℕ) = 484 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient (11^2) = 11^1 * (11 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_11] <;> decide

theorem tot_485 : totient 485 = 384 := by
  have heq : (5 * (97) : ℕ) = 485 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_97] <;> decide

theorem tot_486 : totient 486 = 162 := by
  have heq : (2 * (3^5) : ℕ) = 486 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^5) = 3^4 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3] <;> decide

theorem tot_487 : totient 487 = 486 := by
  have h : totient 487 = 487 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_488 : totient 488 = 240 := by
  have heq : (2^3 * (61) : ℕ) = 488 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_61] <;> decide

theorem tot_489 : totient 489 = 324 := by
  have heq : (3 * (163) : ℕ) = 489 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_163 : totient 163 = 163 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_163] <;> decide

theorem tot_490 : totient 490 = 168 := by
  have heq : (2 * (5 * (7^2)) : ℕ) = 490 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_5, hp_7] <;> decide

theorem tot_491 : totient 491 = 490 := by
  have h : totient 491 = 491 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_492 : totient 492 = 160 := by
  have heq : (2^2 * (3 * (41)) : ℕ) = 492 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_41] <;> decide

theorem tot_493 : totient 493 = 448 := by
  have heq : (17 * (29) : ℕ) = 493 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_29] <;> decide

theorem tot_494 : totient 494 = 216 := by
  have heq : (2 * (13 * (19)) : ℕ) = 494 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_19] <;> decide

theorem tot_495 : totient 495 = 240 := by
  have heq : (3^2 * (5 * (11)) : ℕ) = 495 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_11] <;> decide

theorem tot_496 : totient 496 = 240 := by
  have heq : (2^4 * (31) : ℕ) = 496 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_31] <;> decide

theorem tot_497 : totient 497 = 420 := by
  have heq : (7 * (71) : ℕ) = 497 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_71] <;> decide

theorem tot_498 : totient 498 = 164 := by
  have heq : (2 * (3 * (83)) : ℕ) = 498 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_83] <;> decide

theorem tot_499 : totient 499 = 498 := by
  have h : totient 499 = 499 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_500 : totient 500 = 200 := by
  have heq : (2^2 * (5^3) : ℕ) = 500 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^3) = 5^2 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_5] <;> decide

theorem tot_501 : totient 501 = 332 := by
  have heq : (3 * (167) : ℕ) = 501 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_167 : totient 167 = 167 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_167] <;> decide

theorem tot_502 : totient 502 = 250 := by
  have heq : (2 * (251) : ℕ) = 502 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_251 : totient 251 = 251 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_251] <;> decide

theorem tot_503 : totient 503 = 502 := by
  have h : totient 503 = 503 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_504 : totient 504 = 144 := by
  have heq : (2^3 * (3^2 * (7)) : ℕ) = 504 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7] <;> decide

theorem tot_505 : totient 505 = 400 := by
  have heq : (5 * (101) : ℕ) = 505 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_101] <;> decide

theorem tot_506 : totient 506 = 220 := by
  have heq : (2 * (11 * (23)) : ℕ) = 506 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_23] <;> decide

theorem tot_507 : totient 507 = 312 := by
  have heq : (3 * (13^2) : ℕ) = 507 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient (13^2) = 13^1 * (13 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_13] <;> decide

theorem tot_508 : totient 508 = 252 := by
  have heq : (2^2 * (127) : ℕ) = 508 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_127 : totient 127 = 127 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_127] <;> decide

theorem tot_509 : totient 509 = 508 := by
  have h : totient 509 = 509 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_510 : totient 510 = 128 := by
  have heq : (2 * (3 * (5 * (17))) : ℕ) = 510 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_17] <;> decide

theorem tot_511 : totient 511 = 432 := by
  have heq : (7 * (73) : ℕ) = 511 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_73] <;> decide

theorem tot_512 : totient 512 = 256 := by
  have h : totient (2^9) = 2^8 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (2^9 : ℕ) = 512 := by decide
  rw [← heq]
  rw [h] <;> decide

theorem tot_513 : totient 513 = 324 := by
  have heq : (3^3 * (19) : ℕ) = 513 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_19] <;> decide

theorem tot_514 : totient 514 = 256 := by
  have heq : (2 * (257) : ℕ) = 514 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_257 : totient 257 = 257 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_257] <;> decide

theorem tot_515 : totient 515 = 408 := by
  have heq : (5 * (103) : ℕ) = 515 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_103] <;> decide

theorem tot_516 : totient 516 = 168 := by
  have heq : (2^2 * (3 * (43)) : ℕ) = 516 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_43] <;> decide

theorem tot_517 : totient 517 = 460 := by
  have heq : (11 * (47) : ℕ) = 517 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_47] <;> decide

theorem tot_518 : totient 518 = 216 := by
  have heq : (2 * (7 * (37)) : ℕ) = 518 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_37] <;> decide

theorem tot_519 : totient 519 = 344 := by
  have heq : (3 * (173) : ℕ) = 519 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_173 : totient 173 = 173 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_173] <;> decide

theorem tot_520 : totient 520 = 192 := by
  have heq : (2^3 * (5 * (13)) : ℕ) = 520 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_13] <;> decide

theorem tot_521 : totient 521 = 520 := by
  have h : totient 521 = 521 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_522 : totient 522 = 168 := by
  have heq : (2 * (3^2 * (29)) : ℕ) = 522 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_29] <;> decide

theorem tot_523 : totient 523 = 522 := by
  have h : totient 523 = 523 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_524 : totient 524 = 260 := by
  have heq : (2^2 * (131) : ℕ) = 524 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_131 : totient 131 = 131 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_131] <;> decide

theorem tot_525 : totient 525 = 240 := by
  have heq : (3 * (5^2 * (7)) : ℕ) = 525 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_7] <;> decide

theorem tot_526 : totient 526 = 262 := by
  have heq : (2 * (263) : ℕ) = 526 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_263 : totient 263 = 263 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_263] <;> decide

theorem tot_527 : totient 527 = 480 := by
  have heq : (17 * (31) : ℕ) = 527 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_31] <;> decide

theorem tot_528 : totient 528 = 160 := by
  have heq : (2^4 * (3 * (11)) : ℕ) = 528 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11] <;> decide

theorem tot_529 : totient 529 = 506 := by
  have h : totient (23^2) = 23^1 * (23 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (23^2 : ℕ) = 529 := by decide
  rw [← heq]
  rw [h] <;> decide

theorem tot_530 : totient 530 = 208 := by
  have heq : (2 * (5 * (53)) : ℕ) = 530 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_53] <;> decide

theorem tot_531 : totient 531 = 348 := by
  have heq : (3^2 * (59) : ℕ) = 531 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_59] <;> decide

theorem tot_532 : totient 532 = 216 := by
  have heq : (2^2 * (7 * (19)) : ℕ) = 532 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_19] <;> decide

theorem tot_533 : totient 533 = 480 := by
  have heq : (13 * (41) : ℕ) = 533 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_41] <;> decide

theorem tot_534 : totient 534 = 176 := by
  have heq : (2 * (3 * (89)) : ℕ) = 534 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_89] <;> decide

theorem tot_535 : totient 535 = 424 := by
  have heq : (5 * (107) : ℕ) = 535 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_107] <;> decide

theorem tot_536 : totient 536 = 264 := by
  have heq : (2^3 * (67) : ℕ) = 536 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_67] <;> decide

theorem tot_537 : totient 537 = 356 := by
  have heq : (3 * (179) : ℕ) = 537 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_179 : totient 179 = 179 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_179] <;> decide

theorem tot_538 : totient 538 = 268 := by
  have heq : (2 * (269) : ℕ) = 538 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_269 : totient 269 = 269 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_269] <;> decide

theorem tot_539 : totient 539 = 420 := by
  have heq : (7^2 * (11) : ℕ) = 539 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_11] <;> decide

theorem tot_540 : totient 540 = 144 := by
  have heq : (2^2 * (3^3 * (5)) : ℕ) = 540 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5] <;> decide

theorem tot_541 : totient 541 = 540 := by
  have h : totient 541 = 541 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_542 : totient 542 = 270 := by
  have heq : (2 * (271) : ℕ) = 542 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_271 : totient 271 = 271 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_271] <;> decide

theorem tot_543 : totient 543 = 360 := by
  have heq : (3 * (181) : ℕ) = 543 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_181 : totient 181 = 181 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_181] <;> decide

theorem tot_544 : totient 544 = 256 := by
  have heq : (2^5 * (17) : ℕ) = 544 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17] <;> decide

theorem tot_545 : totient 545 = 432 := by
  have heq : (5 * (109) : ℕ) = 545 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_109] <;> decide

theorem tot_546 : totient 546 = 144 := by
  have heq : (2 * (3 * (7 * (13))) : ℕ) = 546 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_13] <;> decide

theorem tot_547 : totient 547 = 546 := by
  have h : totient 547 = 547 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_548 : totient 548 = 272 := by
  have heq : (2^2 * (137) : ℕ) = 548 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_137 : totient 137 = 137 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_137] <;> decide

theorem tot_549 : totient 549 = 360 := by
  have heq : (3^2 * (61) : ℕ) = 549 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_61] <;> decide

theorem tot_550 : totient 550 = 200 := by
  have heq : (2 * (5^2 * (11)) : ℕ) = 550 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_11] <;> decide

theorem tot_551 : totient 551 = 504 := by
  have heq : (19 * (29) : ℕ) = 551 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_29] <;> decide

theorem tot_552 : totient 552 = 176 := by
  have heq : (2^3 * (3 * (23)) : ℕ) = 552 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_23] <;> decide

theorem tot_553 : totient 553 = 468 := by
  have heq : (7 * (79) : ℕ) = 553 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_79] <;> decide

theorem tot_554 : totient 554 = 276 := by
  have heq : (2 * (277) : ℕ) = 554 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_277 : totient 277 = 277 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_277] <;> decide

theorem tot_555 : totient 555 = 288 := by
  have heq : (3 * (5 * (37)) : ℕ) = 555 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_37] <;> decide

theorem tot_556 : totient 556 = 276 := by
  have heq : (2^2 * (139) : ℕ) = 556 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_139 : totient 139 = 139 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_139] <;> decide

theorem tot_557 : totient 557 = 556 := by
  have h : totient 557 = 557 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_558 : totient 558 = 180 := by
  have heq : (2 * (3^2 * (31)) : ℕ) = 558 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_31] <;> decide

theorem tot_559 : totient 559 = 504 := by
  have heq : (13 * (43) : ℕ) = 559 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_43] <;> decide

theorem tot_560 : totient 560 = 192 := by
  have heq : (2^4 * (5 * (7)) : ℕ) = 560 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7] <;> decide

theorem tot_561 : totient 561 = 320 := by
  have heq : (3 * (11 * (17)) : ℕ) = 561 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11, hp_17] <;> decide

theorem tot_562 : totient 562 = 280 := by
  have heq : (2 * (281) : ℕ) = 562 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_281 : totient 281 = 281 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_281] <;> decide

theorem tot_563 : totient 563 = 562 := by
  have h : totient 563 = 563 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_564 : totient 564 = 184 := by
  have heq : (2^2 * (3 * (47)) : ℕ) = 564 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_47] <;> decide

theorem tot_565 : totient 565 = 448 := by
  have heq : (5 * (113) : ℕ) = 565 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_113 : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_113] <;> decide

theorem tot_566 : totient 566 = 282 := by
  have heq : (2 * (283) : ℕ) = 566 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_283 : totient 283 = 283 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_283] <;> decide

theorem tot_567 : totient 567 = 324 := by
  have heq : (3^4 * (7) : ℕ) = 567 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7] <;> decide

theorem tot_568 : totient 568 = 280 := by
  have heq : (2^3 * (71) : ℕ) = 568 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_71] <;> decide

theorem tot_569 : totient 569 = 568 := by
  have h : totient 569 = 569 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_570 : totient 570 = 144 := by
  have heq : (2 * (3 * (5 * (19))) : ℕ) = 570 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_19] <;> decide

theorem tot_571 : totient 571 = 570 := by
  have h : totient 571 = 571 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_572 : totient 572 = 240 := by
  have heq : (2^2 * (11 * (13)) : ℕ) = 572 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_13] <;> decide

theorem tot_573 : totient 573 = 380 := by
  have heq : (3 * (191) : ℕ) = 573 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_191 : totient 191 = 191 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_191] <;> decide

theorem tot_574 : totient 574 = 240 := by
  have heq : (2 * (7 * (41)) : ℕ) = 574 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_41] <;> decide

theorem tot_575 : totient 575 = 440 := by
  have heq : (5^2 * (23) : ℕ) = 575 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_23] <;> decide

theorem tot_576 : totient 576 = 192 := by
  have heq : (2^6 * (3^2) : ℕ) = 576 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^6) = 2^5 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3] <;> decide

theorem tot_577 : totient 577 = 576 := by
  have h : totient 577 = 577 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_578 : totient 578 = 272 := by
  have heq : (2 * (17^2) : ℕ) = 578 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_17 : totient (17^2) = 17^1 * (17 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_17] <;> decide

theorem tot_579 : totient 579 = 384 := by
  have heq : (3 * (193) : ℕ) = 579 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_193 : totient 193 = 193 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_193] <;> decide

theorem tot_580 : totient 580 = 224 := by
  have heq : (2^2 * (5 * (29)) : ℕ) = 580 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_29] <;> decide

theorem tot_581 : totient 581 = 492 := by
  have heq : (7 * (83) : ℕ) = 581 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_83] <;> decide

theorem tot_582 : totient 582 = 192 := by
  have heq : (2 * (3 * (97)) : ℕ) = 582 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_97] <;> decide

theorem tot_583 : totient 583 = 520 := by
  have heq : (11 * (53) : ℕ) = 583 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_53] <;> decide

theorem tot_584 : totient 584 = 288 := by
  have heq : (2^3 * (73) : ℕ) = 584 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_73] <;> decide

theorem tot_585 : totient 585 = 288 := by
  have heq : (3^2 * (5 * (13)) : ℕ) = 585 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_13] <;> decide

theorem tot_586 : totient 586 = 292 := by
  have heq : (2 * (293) : ℕ) = 586 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_293 : totient 293 = 293 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_293] <;> decide

theorem tot_587 : totient 587 = 586 := by
  have h : totient 587 = 587 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_588 : totient 588 = 168 := by
  have heq : (2^2 * (3 * (7^2)) : ℕ) = 588 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_7] <;> decide

theorem tot_589 : totient 589 = 540 := by
  have heq : (19 * (31) : ℕ) = 589 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_31] <;> decide

theorem tot_590 : totient 590 = 232 := by
  have heq : (2 * (5 * (59)) : ℕ) = 590 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_59] <;> decide

theorem tot_591 : totient 591 = 392 := by
  have heq : (3 * (197) : ℕ) = 591 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_197 : totient 197 = 197 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_197] <;> decide

theorem tot_592 : totient 592 = 288 := by
  have heq : (2^4 * (37) : ℕ) = 592 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_37] <;> decide

theorem tot_593 : totient 593 = 592 := by
  have h : totient 593 = 593 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_594 : totient 594 = 180 := by
  have heq : (2 * (3^3 * (11)) : ℕ) = 594 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11] <;> decide

theorem tot_595 : totient 595 = 384 := by
  have heq : (5 * (7 * (17)) : ℕ) = 595 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_7, hp_17] <;> decide

theorem tot_596 : totient 596 = 296 := by
  have heq : (2^2 * (149) : ℕ) = 596 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_149 : totient 149 = 149 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_149] <;> decide

theorem tot_597 : totient 597 = 396 := by
  have heq : (3 * (199) : ℕ) = 597 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_199 : totient 199 = 199 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_199] <;> decide

theorem tot_598 : totient 598 = 264 := by
  have heq : (2 * (13 * (23)) : ℕ) = 598 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_23] <;> decide

theorem tot_599 : totient 599 = 598 := by
  have h : totient 599 = 599 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_600 : totient 600 = 160 := by
  have heq : (2^3 * (3 * (5^2)) : ℕ) = 600 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_5] <;> decide

theorem tot_601 : totient 601 = 600 := by
  have h : totient 601 = 601 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_602 : totient 602 = 252 := by
  have heq : (2 * (7 * (43)) : ℕ) = 602 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_43] <;> decide

theorem tot_603 : totient 603 = 396 := by
  have heq : (3^2 * (67) : ℕ) = 603 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_67] <;> decide

theorem tot_604 : totient 604 = 300 := by
  have heq : (2^2 * (151) : ℕ) = 604 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_151 : totient 151 = 151 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_151] <;> decide

theorem tot_605 : totient 605 = 440 := by
  have heq : (5 * (11^2) : ℕ) = 605 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient (11^2) = 11^1 * (11 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_5, hp_11] <;> decide

theorem tot_606 : totient 606 = 200 := by
  have heq : (2 * (3 * (101)) : ℕ) = 606 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_101] <;> decide

theorem tot_607 : totient 607 = 606 := by
  have h : totient 607 = 607 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_608 : totient 608 = 288 := by
  have heq : (2^5 * (19) : ℕ) = 608 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_19] <;> decide

theorem tot_609 : totient 609 = 336 := by
  have heq : (3 * (7 * (29)) : ℕ) = 609 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_29] <;> decide

theorem tot_610 : totient 610 = 240 := by
  have heq : (2 * (5 * (61)) : ℕ) = 610 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_61] <;> decide

theorem tot_611 : totient 611 = 552 := by
  have heq : (13 * (47) : ℕ) = 611 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_47] <;> decide

theorem tot_612 : totient 612 = 192 := by
  have heq : (2^2 * (3^2 * (17)) : ℕ) = 612 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_17] <;> decide

theorem tot_613 : totient 613 = 612 := by
  have h : totient 613 = 613 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_614 : totient 614 = 306 := by
  have heq : (2 * (307) : ℕ) = 614 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_307 : totient 307 = 307 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_307] <;> decide

theorem tot_615 : totient 615 = 320 := by
  have heq : (3 * (5 * (41)) : ℕ) = 615 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_41] <;> decide

theorem tot_616 : totient 616 = 240 := by
  have heq : (2^3 * (7 * (11)) : ℕ) = 616 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_11] <;> decide

theorem tot_617 : totient 617 = 616 := by
  have h : totient 617 = 617 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_618 : totient 618 = 204 := by
  have heq : (2 * (3 * (103)) : ℕ) = 618 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_103] <;> decide

theorem tot_619 : totient 619 = 618 := by
  have h : totient 619 = 619 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_620 : totient 620 = 240 := by
  have heq : (2^2 * (5 * (31)) : ℕ) = 620 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_31] <;> decide

theorem tot_621 : totient 621 = 396 := by
  have heq : (3^3 * (23) : ℕ) = 621 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_23] <;> decide

theorem tot_622 : totient 622 = 310 := by
  have heq : (2 * (311) : ℕ) = 622 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_311 : totient 311 = 311 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_311] <;> decide

theorem tot_623 : totient 623 = 528 := by
  have heq : (7 * (89) : ℕ) = 623 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_89] <;> decide

theorem tot_624 : totient 624 = 192 := by
  have heq : (2^4 * (3 * (13)) : ℕ) = 624 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_13] <;> decide

theorem tot_625 : totient 625 = 500 := by
  have h : totient (5^4) = 5^3 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (5^4 : ℕ) = 625 := by decide
  rw [← heq]
  rw [h] <;> decide

theorem tot_626 : totient 626 = 312 := by
  have heq : (2 * (313) : ℕ) = 626 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_313 : totient 313 = 313 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_313] <;> decide

theorem tot_627 : totient 627 = 360 := by
  have heq : (3 * (11 * (19)) : ℕ) = 627 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11, hp_19] <;> decide

theorem tot_628 : totient 628 = 312 := by
  have heq : (2^2 * (157) : ℕ) = 628 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_157 : totient 157 = 157 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_157] <;> decide

theorem tot_629 : totient 629 = 576 := by
  have heq : (17 * (37) : ℕ) = 629 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_37] <;> decide

theorem tot_630 : totient 630 = 144 := by
  have heq : (2 * (3^2 * (5 * (7))) : ℕ) = 630 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_7] <;> decide

theorem tot_631 : totient 631 = 630 := by
  have h : totient 631 = 631 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_632 : totient 632 = 312 := by
  have heq : (2^3 * (79) : ℕ) = 632 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_79] <;> decide

theorem tot_633 : totient 633 = 420 := by
  have heq : (3 * (211) : ℕ) = 633 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_211 : totient 211 = 211 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_211] <;> decide

theorem tot_634 : totient 634 = 316 := by
  have heq : (2 * (317) : ℕ) = 634 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_317 : totient 317 = 317 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_317] <;> decide

theorem tot_635 : totient 635 = 504 := by
  have heq : (5 * (127) : ℕ) = 635 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_127 : totient 127 = 127 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_127] <;> decide

theorem tot_636 : totient 636 = 208 := by
  have heq : (2^2 * (3 * (53)) : ℕ) = 636 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_53] <;> decide

theorem tot_637 : totient 637 = 504 := by
  have heq : (7^2 * (13) : ℕ) = 637 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_13] <;> decide

theorem tot_638 : totient 638 = 280 := by
  have heq : (2 * (11 * (29)) : ℕ) = 638 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_29] <;> decide

theorem tot_639 : totient 639 = 420 := by
  have heq : (3^2 * (71) : ℕ) = 639 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_71] <;> decide

theorem tot_640 : totient 640 = 256 := by
  have heq : (2^7 * (5) : ℕ) = 640 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^7) = 2^6 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5] <;> decide

theorem tot_641 : totient 641 = 640 := by
  have h : totient 641 = 641 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_642 : totient 642 = 212 := by
  have heq : (2 * (3 * (107)) : ℕ) = 642 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_107] <;> decide

theorem tot_643 : totient 643 = 642 := by
  have h : totient 643 = 643 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_644 : totient 644 = 264 := by
  have heq : (2^2 * (7 * (23)) : ℕ) = 644 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_23] <;> decide

theorem tot_645 : totient 645 = 336 := by
  have heq : (3 * (5 * (43)) : ℕ) = 645 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_43] <;> decide

theorem tot_646 : totient 646 = 288 := by
  have heq : (2 * (17 * (19)) : ℕ) = 646 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17, hp_19] <;> decide

theorem tot_647 : totient 647 = 646 := by
  have h : totient 647 = 647 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_648 : totient 648 = 216 := by
  have heq : (2^3 * (3^4) : ℕ) = 648 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3] <;> decide

theorem tot_649 : totient 649 = 580 := by
  have heq : (11 * (59) : ℕ) = 649 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_59] <;> decide

theorem tot_650 : totient 650 = 240 := by
  have heq : (2 * (5^2 * (13)) : ℕ) = 650 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_13] <;> decide

theorem tot_651 : totient 651 = 360 := by
  have heq : (3 * (7 * (31)) : ℕ) = 651 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_31] <;> decide

theorem tot_652 : totient 652 = 324 := by
  have heq : (2^2 * (163) : ℕ) = 652 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_163 : totient 163 = 163 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_163] <;> decide

theorem tot_653 : totient 653 = 652 := by
  have h : totient 653 = 653 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_654 : totient 654 = 216 := by
  have heq : (2 * (3 * (109)) : ℕ) = 654 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_109] <;> decide

theorem tot_655 : totient 655 = 520 := by
  have heq : (5 * (131) : ℕ) = 655 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_131 : totient 131 = 131 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_131] <;> decide

theorem tot_656 : totient 656 = 320 := by
  have heq : (2^4 * (41) : ℕ) = 656 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_41] <;> decide

theorem tot_657 : totient 657 = 432 := by
  have heq : (3^2 * (73) : ℕ) = 657 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_73] <;> decide

theorem tot_658 : totient 658 = 276 := by
  have heq : (2 * (7 * (47)) : ℕ) = 658 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_47] <;> decide

theorem tot_659 : totient 659 = 658 := by
  have h : totient 659 = 659 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_660 : totient 660 = 160 := by
  have heq : (2^2 * (3 * (5 * (11))) : ℕ) = 660 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_11] <;> decide

theorem tot_661 : totient 661 = 660 := by
  have h : totient 661 = 661 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_662 : totient 662 = 330 := by
  have heq : (2 * (331) : ℕ) = 662 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_331 : totient 331 = 331 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_331] <;> decide

theorem tot_663 : totient 663 = 384 := by
  have heq : (3 * (13 * (17)) : ℕ) = 663 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_13, hp_17] <;> decide

theorem tot_664 : totient 664 = 328 := by
  have heq : (2^3 * (83) : ℕ) = 664 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_83] <;> decide

theorem tot_665 : totient 665 = 432 := by
  have heq : (5 * (7 * (19)) : ℕ) = 665 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_7, hp_19] <;> decide

theorem tot_666 : totient 666 = 216 := by
  have heq : (2 * (3^2 * (37)) : ℕ) = 666 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_37] <;> decide

theorem tot_667 : totient 667 = 616 := by
  have heq : (23 * (29) : ℕ) = 667 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_23, hp_29] <;> decide

theorem tot_668 : totient 668 = 332 := by
  have heq : (2^2 * (167) : ℕ) = 668 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_167 : totient 167 = 167 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_167] <;> decide

theorem tot_669 : totient 669 = 444 := by
  have heq : (3 * (223) : ℕ) = 669 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_223 : totient 223 = 223 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_223] <;> decide

theorem tot_670 : totient 670 = 264 := by
  have heq : (2 * (5 * (67)) : ℕ) = 670 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_67] <;> decide

theorem tot_671 : totient 671 = 600 := by
  have heq : (11 * (61) : ℕ) = 671 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_61] <;> decide

theorem tot_672 : totient 672 = 192 := by
  have heq : (2^5 * (3 * (7)) : ℕ) = 672 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7] <;> decide

theorem tot_673 : totient 673 = 672 := by
  have h : totient 673 = 673 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_674 : totient 674 = 336 := by
  have heq : (2 * (337) : ℕ) = 674 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_337 : totient 337 = 337 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_337] <;> decide

theorem tot_675 : totient 675 = 360 := by
  have heq : (3^3 * (5^2) : ℕ) = 675 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_5] <;> decide

theorem tot_676 : totient 676 = 312 := by
  have heq : (2^2 * (13^2) : ℕ) = 676 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient (13^2) = 13^1 * (13 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_13] <;> decide

theorem tot_677 : totient 677 = 676 := by
  have h : totient 677 = 677 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_678 : totient 678 = 224 := by
  have heq : (2 * (3 * (113)) : ℕ) = 678 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_113 : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_113] <;> decide

theorem tot_679 : totient 679 = 576 := by
  have heq : (7 * (97) : ℕ) = 679 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_97] <;> decide

theorem tot_680 : totient 680 = 256 := by
  have heq : (2^3 * (5 * (17)) : ℕ) = 680 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_17] <;> decide

theorem tot_681 : totient 681 = 452 := by
  have heq : (3 * (227) : ℕ) = 681 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_227 : totient 227 = 227 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_227] <;> decide

theorem tot_682 : totient 682 = 300 := by
  have heq : (2 * (11 * (31)) : ℕ) = 682 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_31] <;> decide

theorem tot_683 : totient 683 = 682 := by
  have h : totient 683 = 683 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_684 : totient 684 = 216 := by
  have heq : (2^2 * (3^2 * (19)) : ℕ) = 684 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_19] <;> decide

theorem tot_685 : totient 685 = 544 := by
  have heq : (5 * (137) : ℕ) = 685 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_137 : totient 137 = 137 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_137] <;> decide

theorem tot_686 : totient 686 = 294 := by
  have heq : (2 * (7^3) : ℕ) = 686 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^3) = 7^2 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_7] <;> decide

theorem tot_687 : totient 687 = 456 := by
  have heq : (3 * (229) : ℕ) = 687 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_229 : totient 229 = 229 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_229] <;> decide

theorem tot_688 : totient 688 = 336 := by
  have heq : (2^4 * (43) : ℕ) = 688 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_43] <;> decide

theorem tot_689 : totient 689 = 624 := by
  have heq : (13 * (53) : ℕ) = 689 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_53] <;> decide

theorem tot_690 : totient 690 = 176 := by
  have heq : (2 * (3 * (5 * (23))) : ℕ) = 690 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_23] <;> decide

theorem tot_691 : totient 691 = 690 := by
  have h : totient 691 = 691 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_692 : totient 692 = 344 := by
  have heq : (2^2 * (173) : ℕ) = 692 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_173 : totient 173 = 173 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_173] <;> decide

theorem tot_693 : totient 693 = 360 := by
  have heq : (3^2 * (7 * (11)) : ℕ) = 693 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_11] <;> decide

theorem tot_694 : totient 694 = 346 := by
  have heq : (2 * (347) : ℕ) = 694 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_347 : totient 347 = 347 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_347] <;> decide

theorem tot_695 : totient 695 = 552 := by
  have heq : (5 * (139) : ℕ) = 695 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_139 : totient 139 = 139 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_139] <;> decide

theorem tot_696 : totient 696 = 224 := by
  have heq : (2^3 * (3 * (29)) : ℕ) = 696 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_29] <;> decide

theorem tot_697 : totient 697 = 640 := by
  have heq : (17 * (41) : ℕ) = 697 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_41] <;> decide

theorem tot_698 : totient 698 = 348 := by
  have heq : (2 * (349) : ℕ) = 698 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_349 : totient 349 = 349 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_349] <;> decide

theorem tot_699 : totient 699 = 464 := by
  have heq : (3 * (233) : ℕ) = 699 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_233 : totient 233 = 233 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_233] <;> decide

theorem tot_700 : totient 700 = 240 := by
  have heq : (2^2 * (5^2 * (7)) : ℕ) = 700 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7] <;> decide

theorem tot_701 : totient 701 = 700 := by
  have h : totient 701 = 701 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_702 : totient 702 = 216 := by
  have heq : (2 * (3^3 * (13)) : ℕ) = 702 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_13] <;> decide

theorem tot_703 : totient 703 = 648 := by
  have heq : (19 * (37) : ℕ) = 703 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_37] <;> decide

theorem tot_704 : totient 704 = 320 := by
  have heq : (2^6 * (11) : ℕ) = 704 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^6) = 2^5 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11] <;> decide

theorem tot_705 : totient 705 = 368 := by
  have heq : (3 * (5 * (47)) : ℕ) = 705 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_47] <;> decide

theorem tot_706 : totient 706 = 352 := by
  have heq : (2 * (353) : ℕ) = 706 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_353 : totient 353 = 353 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_353] <;> decide

theorem tot_707 : totient 707 = 600 := by
  have heq : (7 * (101) : ℕ) = 707 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_101] <;> decide

theorem tot_708 : totient 708 = 232 := by
  have heq : (2^2 * (3 * (59)) : ℕ) = 708 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_59] <;> decide

theorem tot_709 : totient 709 = 708 := by
  have h : totient 709 = 709 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_710 : totient 710 = 280 := by
  have heq : (2 * (5 * (71)) : ℕ) = 710 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_71] <;> decide

theorem tot_711 : totient 711 = 468 := by
  have heq : (3^2 * (79) : ℕ) = 711 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_79] <;> decide

theorem tot_712 : totient 712 = 352 := by
  have heq : (2^3 * (89) : ℕ) = 712 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_89] <;> decide

theorem tot_713 : totient 713 = 660 := by
  have heq : (23 * (31) : ℕ) = 713 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_23, hp_31] <;> decide

theorem tot_714 : totient 714 = 192 := by
  have heq : (2 * (3 * (7 * (17))) : ℕ) = 714 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_17] <;> decide

theorem tot_715 : totient 715 = 480 := by
  have heq : (5 * (11 * (13)) : ℕ) = 715 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_11, hp_13] <;> decide

theorem tot_716 : totient 716 = 356 := by
  have heq : (2^2 * (179) : ℕ) = 716 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_179 : totient 179 = 179 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_179] <;> decide

theorem tot_717 : totient 717 = 476 := by
  have heq : (3 * (239) : ℕ) = 717 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_239 : totient 239 = 239 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_239] <;> decide

theorem tot_718 : totient 718 = 358 := by
  have heq : (2 * (359) : ℕ) = 718 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_359 : totient 359 = 359 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_359] <;> decide

theorem tot_719 : totient 719 = 718 := by
  have h : totient 719 = 719 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_720 : totient 720 = 192 := by
  have heq : (2^4 * (3^2 * (5)) : ℕ) = 720 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5] <;> decide

theorem tot_721 : totient 721 = 612 := by
  have heq : (7 * (103) : ℕ) = 721 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_103] <;> decide

theorem tot_722 : totient 722 = 342 := by
  have heq : (2 * (19^2) : ℕ) = 722 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_19 : totient (19^2) = 19^1 * (19 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_19] <;> decide

theorem tot_723 : totient 723 = 480 := by
  have heq : (3 * (241) : ℕ) = 723 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_241 : totient 241 = 241 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_241] <;> decide

theorem tot_724 : totient 724 = 360 := by
  have heq : (2^2 * (181) : ℕ) = 724 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_181 : totient 181 = 181 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_181] <;> decide

theorem tot_725 : totient 725 = 560 := by
  have heq : (5^2 * (29) : ℕ) = 725 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_29] <;> decide

theorem tot_726 : totient 726 = 220 := by
  have heq : (2 * (3 * (11^2)) : ℕ) = 726 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient (11^2) = 11^1 * (11 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_11] <;> decide

theorem tot_727 : totient 727 = 726 := by
  have h : totient 727 = 727 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_728 : totient 728 = 288 := by
  have heq : (2^3 * (7 * (13)) : ℕ) = 728 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_13] <;> decide

theorem tot_729 : totient 729 = 486 := by
  have h : totient (3^6) = 3^5 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (3^6 : ℕ) = 729 := by decide
  rw [← heq]
  rw [h] <;> decide

theorem tot_730 : totient 730 = 288 := by
  have heq : (2 * (5 * (73)) : ℕ) = 730 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_73] <;> decide

theorem tot_731 : totient 731 = 672 := by
  have heq : (17 * (43) : ℕ) = 731 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_43] <;> decide

theorem tot_732 : totient 732 = 240 := by
  have heq : (2^2 * (3 * (61)) : ℕ) = 732 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_61] <;> decide

theorem tot_733 : totient 733 = 732 := by
  have h : totient 733 = 733 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_734 : totient 734 = 366 := by
  have heq : (2 * (367) : ℕ) = 734 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_367 : totient 367 = 367 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_367] <;> decide

theorem tot_735 : totient 735 = 336 := by
  have heq : (3 * (5 * (7^2)) : ℕ) = 735 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_5, hp_7] <;> decide

theorem tot_736 : totient 736 = 352 := by
  have heq : (2^5 * (23) : ℕ) = 736 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_23] <;> decide

theorem tot_737 : totient 737 = 660 := by
  have heq : (11 * (67) : ℕ) = 737 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_67] <;> decide

theorem tot_738 : totient 738 = 240 := by
  have heq : (2 * (3^2 * (41)) : ℕ) = 738 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_41] <;> decide

theorem tot_739 : totient 739 = 738 := by
  have h : totient 739 = 739 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_740 : totient 740 = 288 := by
  have heq : (2^2 * (5 * (37)) : ℕ) = 740 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_37] <;> decide

theorem tot_741 : totient 741 = 432 := by
  have heq : (3 * (13 * (19)) : ℕ) = 741 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_13, hp_19] <;> decide

theorem tot_742 : totient 742 = 312 := by
  have heq : (2 * (7 * (53)) : ℕ) = 742 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_53] <;> decide

theorem tot_743 : totient 743 = 742 := by
  have h : totient 743 = 743 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_744 : totient 744 = 240 := by
  have heq : (2^3 * (3 * (31)) : ℕ) = 744 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_31] <;> decide

theorem tot_745 : totient 745 = 592 := by
  have heq : (5 * (149) : ℕ) = 745 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_149 : totient 149 = 149 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_149] <;> decide

theorem tot_746 : totient 746 = 372 := by
  have heq : (2 * (373) : ℕ) = 746 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_373 : totient 373 = 373 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_373] <;> decide

theorem tot_747 : totient 747 = 492 := by
  have heq : (3^2 * (83) : ℕ) = 747 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_83] <;> decide

theorem tot_748 : totient 748 = 320 := by
  have heq : (2^2 * (11 * (17)) : ℕ) = 748 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_17] <;> decide

theorem tot_749 : totient 749 = 636 := by
  have heq : (7 * (107) : ℕ) = 749 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_107] <;> decide

theorem tot_750 : totient 750 = 200 := by
  have heq : (2 * (3 * (5^3)) : ℕ) = 750 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^3) = 5^2 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_5] <;> decide

theorem tot_751 : totient 751 = 750 := by
  have h : totient 751 = 751 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_752 : totient 752 = 368 := by
  have heq : (2^4 * (47) : ℕ) = 752 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_47] <;> decide

theorem tot_753 : totient 753 = 500 := by
  have heq : (3 * (251) : ℕ) = 753 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_251 : totient 251 = 251 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_251] <;> decide

theorem tot_754 : totient 754 = 336 := by
  have heq : (2 * (13 * (29)) : ℕ) = 754 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_29] <;> decide

theorem tot_755 : totient 755 = 600 := by
  have heq : (5 * (151) : ℕ) = 755 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_151 : totient 151 = 151 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_151] <;> decide

theorem tot_756 : totient 756 = 216 := by
  have heq : (2^2 * (3^3 * (7)) : ℕ) = 756 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7] <;> decide

theorem tot_757 : totient 757 = 756 := by
  have h : totient 757 = 757 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_758 : totient 758 = 378 := by
  have heq : (2 * (379) : ℕ) = 758 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_379 : totient 379 = 379 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_379] <;> decide

theorem tot_759 : totient 759 = 440 := by
  have heq : (3 * (11 * (23)) : ℕ) = 759 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11, hp_23] <;> decide

theorem tot_760 : totient 760 = 288 := by
  have heq : (2^3 * (5 * (19)) : ℕ) = 760 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_19] <;> decide

theorem tot_761 : totient 761 = 760 := by
  have h : totient 761 = 761 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_762 : totient 762 = 252 := by
  have heq : (2 * (3 * (127)) : ℕ) = 762 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_127 : totient 127 = 127 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_127] <;> decide

theorem tot_763 : totient 763 = 648 := by
  have heq : (7 * (109) : ℕ) = 763 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_109] <;> decide

theorem tot_764 : totient 764 = 380 := by
  have heq : (2^2 * (191) : ℕ) = 764 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_191 : totient 191 = 191 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_191] <;> decide

theorem tot_765 : totient 765 = 384 := by
  have heq : (3^2 * (5 * (17)) : ℕ) = 765 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_17] <;> decide

theorem tot_766 : totient 766 = 382 := by
  have heq : (2 * (383) : ℕ) = 766 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_383 : totient 383 = 383 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_383] <;> decide

theorem tot_767 : totient 767 = 696 := by
  have heq : (13 * (59) : ℕ) = 767 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_59] <;> decide

theorem tot_768 : totient 768 = 256 := by
  have heq : (2^8 * (3) : ℕ) = 768 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^8) = 2^7 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3] <;> decide

theorem tot_769 : totient 769 = 768 := by
  have h : totient 769 = 769 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_770 : totient 770 = 240 := by
  have heq : (2 * (5 * (7 * (11))) : ℕ) = 770 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7, hp_11] <;> decide

theorem tot_771 : totient 771 = 512 := by
  have heq : (3 * (257) : ℕ) = 771 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_257 : totient 257 = 257 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_257] <;> decide

theorem tot_772 : totient 772 = 384 := by
  have heq : (2^2 * (193) : ℕ) = 772 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_193 : totient 193 = 193 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_193] <;> decide

theorem tot_773 : totient 773 = 772 := by
  have h : totient 773 = 773 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_774 : totient 774 = 252 := by
  have heq : (2 * (3^2 * (43)) : ℕ) = 774 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_43] <;> decide

theorem tot_775 : totient 775 = 600 := by
  have heq : (5^2 * (31) : ℕ) = 775 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_31] <;> decide

theorem tot_776 : totient 776 = 384 := by
  have heq : (2^3 * (97) : ℕ) = 776 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_97] <;> decide

theorem tot_777 : totient 777 = 432 := by
  have heq : (3 * (7 * (37)) : ℕ) = 777 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_37] <;> decide

theorem tot_778 : totient 778 = 388 := by
  have heq : (2 * (389) : ℕ) = 778 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_389 : totient 389 = 389 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_389] <;> decide

theorem tot_779 : totient 779 = 720 := by
  have heq : (19 * (41) : ℕ) = 779 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_41] <;> decide

theorem tot_780 : totient 780 = 192 := by
  have heq : (2^2 * (3 * (5 * (13))) : ℕ) = 780 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_13] <;> decide

theorem tot_781 : totient 781 = 700 := by
  have heq : (11 * (71) : ℕ) = 781 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_71] <;> decide

theorem tot_782 : totient 782 = 352 := by
  have heq : (2 * (17 * (23)) : ℕ) = 782 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17, hp_23] <;> decide

theorem tot_783 : totient 783 = 504 := by
  have heq : (3^3 * (29) : ℕ) = 783 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_29] <;> decide

theorem tot_784 : totient 784 = 336 := by
  have heq : (2^4 * (7^2) : ℕ) = 784 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_7] <;> decide

theorem tot_785 : totient 785 = 624 := by
  have heq : (5 * (157) : ℕ) = 785 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_157 : totient 157 = 157 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_157] <;> decide

theorem tot_786 : totient 786 = 260 := by
  have heq : (2 * (3 * (131)) : ℕ) = 786 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_131 : totient 131 = 131 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_131] <;> decide

theorem tot_787 : totient 787 = 786 := by
  have h : totient 787 = 787 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_788 : totient 788 = 392 := by
  have heq : (2^2 * (197) : ℕ) = 788 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_197 : totient 197 = 197 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_197] <;> decide

theorem tot_789 : totient 789 = 524 := by
  have heq : (3 * (263) : ℕ) = 789 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_263 : totient 263 = 263 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_263] <;> decide

theorem tot_790 : totient 790 = 312 := by
  have heq : (2 * (5 * (79)) : ℕ) = 790 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_79] <;> decide

theorem tot_791 : totient 791 = 672 := by
  have heq : (7 * (113) : ℕ) = 791 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_113 : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_113] <;> decide

theorem tot_792 : totient 792 = 240 := by
  have heq : (2^3 * (3^2 * (11)) : ℕ) = 792 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11] <;> decide

theorem tot_793 : totient 793 = 720 := by
  have heq : (13 * (61) : ℕ) = 793 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_61] <;> decide

theorem tot_794 : totient 794 = 396 := by
  have heq : (2 * (397) : ℕ) = 794 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_397 : totient 397 = 397 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_397] <;> decide

theorem tot_795 : totient 795 = 416 := by
  have heq : (3 * (5 * (53)) : ℕ) = 795 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_53] <;> decide

theorem tot_796 : totient 796 = 396 := by
  have heq : (2^2 * (199) : ℕ) = 796 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_199 : totient 199 = 199 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_199] <;> decide

theorem tot_797 : totient 797 = 796 := by
  have h : totient 797 = 797 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_798 : totient 798 = 216 := by
  have heq : (2 * (3 * (7 * (19))) : ℕ) = 798 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_19] <;> decide

theorem tot_799 : totient 799 = 736 := by
  have heq : (17 * (47) : ℕ) = 799 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_47] <;> decide

theorem tot_800 : totient 800 = 320 := by
  have heq : (2^5 * (5^2) : ℕ) = 800 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_5] <;> decide

theorem tot_801 : totient 801 = 528 := by
  have heq : (3^2 * (89) : ℕ) = 801 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_89] <;> decide

theorem tot_802 : totient 802 = 400 := by
  have heq : (2 * (401) : ℕ) = 802 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_401 : totient 401 = 401 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_401] <;> decide

theorem tot_803 : totient 803 = 720 := by
  have heq : (11 * (73) : ℕ) = 803 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_73] <;> decide

theorem tot_804 : totient 804 = 264 := by
  have heq : (2^2 * (3 * (67)) : ℕ) = 804 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_67] <;> decide

theorem tot_805 : totient 805 = 528 := by
  have heq : (5 * (7 * (23)) : ℕ) = 805 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_7, hp_23] <;> decide

theorem tot_806 : totient 806 = 360 := by
  have heq : (2 * (13 * (31)) : ℕ) = 806 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_31] <;> decide

theorem tot_807 : totient 807 = 536 := by
  have heq : (3 * (269) : ℕ) = 807 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_269 : totient 269 = 269 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_269] <;> decide

theorem tot_808 : totient 808 = 400 := by
  have heq : (2^3 * (101) : ℕ) = 808 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_101] <;> decide

theorem tot_809 : totient 809 = 808 := by
  have h : totient 809 = 809 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_810 : totient 810 = 216 := by
  have heq : (2 * (3^4 * (5)) : ℕ) = 810 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5] <;> decide

theorem tot_811 : totient 811 = 810 := by
  have h : totient 811 = 811 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_812 : totient 812 = 336 := by
  have heq : (2^2 * (7 * (29)) : ℕ) = 812 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_29] <;> decide

theorem tot_813 : totient 813 = 540 := by
  have heq : (3 * (271) : ℕ) = 813 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_271 : totient 271 = 271 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_271] <;> decide

theorem tot_814 : totient 814 = 360 := by
  have heq : (2 * (11 * (37)) : ℕ) = 814 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_37] <;> decide

theorem tot_815 : totient 815 = 648 := by
  have heq : (5 * (163) : ℕ) = 815 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_163 : totient 163 = 163 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_163] <;> decide

theorem tot_816 : totient 816 = 256 := by
  have heq : (2^4 * (3 * (17)) : ℕ) = 816 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_17] <;> decide

theorem tot_817 : totient 817 = 756 := by
  have heq : (19 * (43) : ℕ) = 817 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_43] <;> decide

theorem tot_818 : totient 818 = 408 := by
  have heq : (2 * (409) : ℕ) = 818 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_409 : totient 409 = 409 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_409] <;> decide

theorem tot_819 : totient 819 = 432 := by
  have heq : (3^2 * (7 * (13)) : ℕ) = 819 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_13] <;> decide

theorem tot_820 : totient 820 = 320 := by
  have heq : (2^2 * (5 * (41)) : ℕ) = 820 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_41] <;> decide

theorem tot_821 : totient 821 = 820 := by
  have h : totient 821 = 821 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_822 : totient 822 = 272 := by
  have heq : (2 * (3 * (137)) : ℕ) = 822 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_137 : totient 137 = 137 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_137] <;> decide

theorem tot_823 : totient 823 = 822 := by
  have h : totient 823 = 823 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_824 : totient 824 = 408 := by
  have heq : (2^3 * (103) : ℕ) = 824 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_103] <;> decide

theorem tot_825 : totient 825 = 400 := by
  have heq : (3 * (5^2 * (11)) : ℕ) = 825 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_11] <;> decide

theorem tot_826 : totient 826 = 348 := by
  have heq : (2 * (7 * (59)) : ℕ) = 826 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_59] <;> decide

theorem tot_827 : totient 827 = 826 := by
  have h : totient 827 = 827 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_828 : totient 828 = 264 := by
  have heq : (2^2 * (3^2 * (23)) : ℕ) = 828 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_23] <;> decide

theorem tot_829 : totient 829 = 828 := by
  have h : totient 829 = 829 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_830 : totient 830 = 328 := by
  have heq : (2 * (5 * (83)) : ℕ) = 830 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_83] <;> decide

theorem tot_831 : totient 831 = 552 := by
  have heq : (3 * (277) : ℕ) = 831 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_277 : totient 277 = 277 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_277] <;> decide

theorem tot_832 : totient 832 = 384 := by
  have heq : (2^6 * (13) : ℕ) = 832 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^6) = 2^5 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13] <;> decide

theorem tot_833 : totient 833 = 672 := by
  have heq : (7^2 * (17) : ℕ) = 833 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_17] <;> decide

theorem tot_834 : totient 834 = 276 := by
  have heq : (2 * (3 * (139)) : ℕ) = 834 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_139 : totient 139 = 139 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_139] <;> decide

theorem tot_835 : totient 835 = 664 := by
  have heq : (5 * (167) : ℕ) = 835 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_167 : totient 167 = 167 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_167] <;> decide

theorem tot_836 : totient 836 = 360 := by
  have heq : (2^2 * (11 * (19)) : ℕ) = 836 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_19] <;> decide

theorem tot_837 : totient 837 = 540 := by
  have heq : (3^3 * (31) : ℕ) = 837 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_31] <;> decide

theorem tot_838 : totient 838 = 418 := by
  have heq : (2 * (419) : ℕ) = 838 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_419 : totient 419 = 419 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_419] <;> decide

theorem tot_839 : totient 839 = 838 := by
  have h : totient 839 = 839 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_840 : totient 840 = 192 := by
  have heq : (2^3 * (3 * (5 * (7))) : ℕ) = 840 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_7] <;> decide

theorem tot_841 : totient 841 = 812 := by
  have h : totient (29^2) = 29^1 * (29 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (29^2 : ℕ) = 841 := by decide
  rw [← heq]
  rw [h] <;> decide

theorem tot_842 : totient 842 = 420 := by
  have heq : (2 * (421) : ℕ) = 842 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_421 : totient 421 = 421 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_421] <;> decide

theorem tot_843 : totient 843 = 560 := by
  have heq : (3 * (281) : ℕ) = 843 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_281 : totient 281 = 281 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_281] <;> decide

theorem tot_844 : totient 844 = 420 := by
  have heq : (2^2 * (211) : ℕ) = 844 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_211 : totient 211 = 211 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_211] <;> decide

theorem tot_845 : totient 845 = 624 := by
  have heq : (5 * (13^2) : ℕ) = 845 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient (13^2) = 13^1 * (13 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_5, hp_13] <;> decide

theorem tot_846 : totient 846 = 276 := by
  have heq : (2 * (3^2 * (47)) : ℕ) = 846 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_47] <;> decide

theorem tot_847 : totient 847 = 660 := by
  have heq : (7 * (11^2) : ℕ) = 847 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient (11^2) = 11^1 * (11 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_7, hp_11] <;> decide

theorem tot_848 : totient 848 = 416 := by
  have heq : (2^4 * (53) : ℕ) = 848 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_53] <;> decide

theorem tot_849 : totient 849 = 564 := by
  have heq : (3 * (283) : ℕ) = 849 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_283 : totient 283 = 283 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_283] <;> decide

theorem tot_850 : totient 850 = 320 := by
  have heq : (2 * (5^2 * (17)) : ℕ) = 850 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_17] <;> decide

theorem tot_851 : totient 851 = 792 := by
  have heq : (23 * (37) : ℕ) = 851 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_23, hp_37] <;> decide

theorem tot_852 : totient 852 = 280 := by
  have heq : (2^2 * (3 * (71)) : ℕ) = 852 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_71] <;> decide

theorem tot_853 : totient 853 = 852 := by
  have h : totient 853 = 853 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_854 : totient 854 = 360 := by
  have heq : (2 * (7 * (61)) : ℕ) = 854 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_61] <;> decide

theorem tot_855 : totient 855 = 432 := by
  have heq : (3^2 * (5 * (19)) : ℕ) = 855 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_19] <;> decide

theorem tot_856 : totient 856 = 424 := by
  have heq : (2^3 * (107) : ℕ) = 856 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_107] <;> decide

theorem tot_857 : totient 857 = 856 := by
  have h : totient 857 = 857 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_858 : totient 858 = 240 := by
  have heq : (2 * (3 * (11 * (13))) : ℕ) = 858 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11, hp_13] <;> decide

theorem tot_859 : totient 859 = 858 := by
  have h : totient 859 = 859 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_860 : totient 860 = 336 := by
  have heq : (2^2 * (5 * (43)) : ℕ) = 860 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_43] <;> decide

theorem tot_861 : totient 861 = 480 := by
  have heq : (3 * (7 * (41)) : ℕ) = 861 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_41] <;> decide

theorem tot_862 : totient 862 = 430 := by
  have heq : (2 * (431) : ℕ) = 862 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_431 : totient 431 = 431 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_431] <;> decide

theorem tot_863 : totient 863 = 862 := by
  have h : totient 863 = 863 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_864 : totient 864 = 288 := by
  have heq : (2^5 * (3^3) : ℕ) = 864 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3] <;> decide

theorem tot_865 : totient 865 = 688 := by
  have heq : (5 * (173) : ℕ) = 865 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_173 : totient 173 = 173 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_173] <;> decide

theorem tot_866 : totient 866 = 432 := by
  have heq : (2 * (433) : ℕ) = 866 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_433 : totient 433 = 433 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_433] <;> decide

theorem tot_867 : totient 867 = 544 := by
  have heq : (3 * (17^2) : ℕ) = 867 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_17 : totient (17^2) = 17^1 * (17 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_17] <;> decide

theorem tot_868 : totient 868 = 360 := by
  have heq : (2^2 * (7 * (31)) : ℕ) = 868 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_31] <;> decide

theorem tot_869 : totient 869 = 780 := by
  have heq : (11 * (79) : ℕ) = 869 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_79] <;> decide

theorem tot_870 : totient 870 = 224 := by
  have heq : (2 * (3 * (5 * (29))) : ℕ) = 870 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_29] <;> decide

theorem tot_871 : totient 871 = 792 := by
  have heq : (13 * (67) : ℕ) = 871 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_67] <;> decide

theorem tot_872 : totient 872 = 432 := by
  have heq : (2^3 * (109) : ℕ) = 872 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_109] <;> decide

theorem tot_873 : totient 873 = 576 := by
  have heq : (3^2 * (97) : ℕ) = 873 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_97] <;> decide

theorem tot_874 : totient 874 = 396 := by
  have heq : (2 * (19 * (23)) : ℕ) = 874 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_19, hp_23] <;> decide

theorem tot_875 : totient 875 = 600 := by
  have heq : (5^3 * (7) : ℕ) = 875 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^3) = 5^2 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_7] <;> decide

theorem tot_876 : totient 876 = 288 := by
  have heq : (2^2 * (3 * (73)) : ℕ) = 876 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_73] <;> decide

theorem tot_877 : totient 877 = 876 := by
  have h : totient 877 = 877 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_878 : totient 878 = 438 := by
  have heq : (2 * (439) : ℕ) = 878 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_439 : totient 439 = 439 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_439] <;> decide

theorem tot_879 : totient 879 = 584 := by
  have heq : (3 * (293) : ℕ) = 879 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_293 : totient 293 = 293 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_293] <;> decide

theorem tot_880 : totient 880 = 320 := by
  have heq : (2^4 * (5 * (11)) : ℕ) = 880 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_11] <;> decide

theorem tot_881 : totient 881 = 880 := by
  have h : totient 881 = 881 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_882 : totient 882 = 252 := by
  have heq : (2 * (3^2 * (7^2)) : ℕ) = 882 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_7] <;> decide

theorem tot_883 : totient 883 = 882 := by
  have h : totient 883 = 883 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_884 : totient 884 = 384 := by
  have heq : (2^2 * (13 * (17)) : ℕ) = 884 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_17] <;> decide

theorem tot_885 : totient 885 = 464 := by
  have heq : (3 * (5 * (59)) : ℕ) = 885 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_59] <;> decide

theorem tot_886 : totient 886 = 442 := by
  have heq : (2 * (443) : ℕ) = 886 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_443 : totient 443 = 443 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_443] <;> decide

theorem tot_887 : totient 887 = 886 := by
  have h : totient 887 = 887 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_888 : totient 888 = 288 := by
  have heq : (2^3 * (3 * (37)) : ℕ) = 888 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_37] <;> decide

theorem tot_889 : totient 889 = 756 := by
  have heq : (7 * (127) : ℕ) = 889 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_127 : totient 127 = 127 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_127] <;> decide

theorem tot_890 : totient 890 = 352 := by
  have heq : (2 * (5 * (89)) : ℕ) = 890 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_89] <;> decide

theorem tot_891 : totient 891 = 540 := by
  have heq : (3^4 * (11) : ℕ) = 891 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11] <;> decide

theorem tot_892 : totient 892 = 444 := by
  have heq : (2^2 * (223) : ℕ) = 892 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_223 : totient 223 = 223 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_223] <;> decide

theorem tot_893 : totient 893 = 828 := by
  have heq : (19 * (47) : ℕ) = 893 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_47] <;> decide

theorem tot_894 : totient 894 = 296 := by
  have heq : (2 * (3 * (149)) : ℕ) = 894 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_149 : totient 149 = 149 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_149] <;> decide

theorem tot_895 : totient 895 = 712 := by
  have heq : (5 * (179) : ℕ) = 895 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_179 : totient 179 = 179 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_179] <;> decide

theorem tot_896 : totient 896 = 384 := by
  have heq : (2^7 * (7) : ℕ) = 896 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^7) = 2^6 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7] <;> decide

theorem tot_897 : totient 897 = 528 := by
  have heq : (3 * (13 * (23)) : ℕ) = 897 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_13, hp_23] <;> decide

theorem tot_898 : totient 898 = 448 := by
  have heq : (2 * (449) : ℕ) = 898 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_449 : totient 449 = 449 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_449] <;> decide

theorem tot_899 : totient 899 = 840 := by
  have heq : (29 * (31) : ℕ) = 899 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_29, hp_31] <;> decide

theorem tot_900 : totient 900 = 240 := by
  have heq : (2^2 * (3^2 * (5^2)) : ℕ) = 900 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_5] <;> decide

theorem tot_901 : totient 901 = 832 := by
  have heq : (17 * (53) : ℕ) = 901 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_53] <;> decide

theorem tot_902 : totient 902 = 400 := by
  have heq : (2 * (11 * (41)) : ℕ) = 902 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_41] <;> decide

theorem tot_903 : totient 903 = 504 := by
  have heq : (3 * (7 * (43)) : ℕ) = 903 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_43] <;> decide

theorem tot_904 : totient 904 = 448 := by
  have heq : (2^3 * (113) : ℕ) = 904 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_113 : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_113] <;> decide

theorem tot_905 : totient 905 = 720 := by
  have heq : (5 * (181) : ℕ) = 905 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_181 : totient 181 = 181 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_181] <;> decide

theorem tot_906 : totient 906 = 300 := by
  have heq : (2 * (3 * (151)) : ℕ) = 906 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_151 : totient 151 = 151 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_151] <;> decide

theorem tot_907 : totient 907 = 906 := by
  have h : totient 907 = 907 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_908 : totient 908 = 452 := by
  have heq : (2^2 * (227) : ℕ) = 908 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_227 : totient 227 = 227 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_227] <;> decide

theorem tot_909 : totient 909 = 600 := by
  have heq : (3^2 * (101) : ℕ) = 909 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_101] <;> decide

theorem tot_910 : totient 910 = 288 := by
  have heq : (2 * (5 * (7 * (13))) : ℕ) = 910 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7, hp_13] <;> decide

theorem tot_911 : totient 911 = 910 := by
  have h : totient 911 = 911 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_912 : totient 912 = 288 := by
  have heq : (2^4 * (3 * (19)) : ℕ) = 912 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_19] <;> decide

theorem tot_913 : totient 913 = 820 := by
  have heq : (11 * (83) : ℕ) = 913 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_83] <;> decide

theorem tot_914 : totient 914 = 456 := by
  have heq : (2 * (457) : ℕ) = 914 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_457 : totient 457 = 457 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_457] <;> decide

theorem tot_915 : totient 915 = 480 := by
  have heq : (3 * (5 * (61)) : ℕ) = 915 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_61] <;> decide

theorem tot_916 : totient 916 = 456 := by
  have heq : (2^2 * (229) : ℕ) = 916 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_229 : totient 229 = 229 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_229] <;> decide

theorem tot_917 : totient 917 = 780 := by
  have heq : (7 * (131) : ℕ) = 917 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_131 : totient 131 = 131 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_131] <;> decide

theorem tot_918 : totient 918 = 288 := by
  have heq : (2 * (3^3 * (17)) : ℕ) = 918 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_17] <;> decide

theorem tot_919 : totient 919 = 918 := by
  have h : totient 919 = 919 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_920 : totient 920 = 352 := by
  have heq : (2^3 * (5 * (23)) : ℕ) = 920 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_23] <;> decide

theorem tot_921 : totient 921 = 612 := by
  have heq : (3 * (307) : ℕ) = 921 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_307 : totient 307 = 307 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_307] <;> decide

theorem tot_922 : totient 922 = 460 := by
  have heq : (2 * (461) : ℕ) = 922 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_461 : totient 461 = 461 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_461] <;> decide

theorem tot_923 : totient 923 = 840 := by
  have heq : (13 * (71) : ℕ) = 923 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_71] <;> decide

theorem tot_924 : totient 924 = 240 := by
  have heq : (2^2 * (3 * (7 * (11))) : ℕ) = 924 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_11] <;> decide

theorem tot_925 : totient 925 = 720 := by
  have heq : (5^2 * (37) : ℕ) = 925 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_37] <;> decide

theorem tot_926 : totient 926 = 462 := by
  have heq : (2 * (463) : ℕ) = 926 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_463 : totient 463 = 463 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_463] <;> decide

theorem tot_927 : totient 927 = 612 := by
  have heq : (3^2 * (103) : ℕ) = 927 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_103] <;> decide

theorem tot_928 : totient 928 = 448 := by
  have heq : (2^5 * (29) : ℕ) = 928 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_29] <;> decide

theorem tot_929 : totient 929 = 928 := by
  have h : totient 929 = 929 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_930 : totient 930 = 240 := by
  have heq : (2 * (3 * (5 * (31))) : ℕ) = 930 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_31] <;> decide

theorem tot_931 : totient 931 = 756 := by
  have heq : (7^2 * (19) : ℕ) = 931 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_19] <;> decide

theorem tot_932 : totient 932 = 464 := by
  have heq : (2^2 * (233) : ℕ) = 932 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_233 : totient 233 = 233 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_233] <;> decide

theorem tot_933 : totient 933 = 620 := by
  have heq : (3 * (311) : ℕ) = 933 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_311 : totient 311 = 311 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_311] <;> decide

theorem tot_934 : totient 934 = 466 := by
  have heq : (2 * (467) : ℕ) = 934 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_467 : totient 467 = 467 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_467] <;> decide

theorem tot_935 : totient 935 = 640 := by
  have heq : (5 * (11 * (17)) : ℕ) = 935 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_11, hp_17] <;> decide

theorem tot_936 : totient 936 = 288 := by
  have heq : (2^3 * (3^2 * (13)) : ℕ) = 936 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_13] <;> decide

theorem tot_937 : totient 937 = 936 := by
  have h : totient 937 = 937 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_938 : totient 938 = 396 := by
  have heq : (2 * (7 * (67)) : ℕ) = 938 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_67] <;> decide

theorem tot_939 : totient 939 = 624 := by
  have heq : (3 * (313) : ℕ) = 939 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_313 : totient 313 = 313 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_313] <;> decide

theorem tot_940 : totient 940 = 368 := by
  have heq : (2^2 * (5 * (47)) : ℕ) = 940 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_47] <;> decide

theorem tot_941 : totient 941 = 940 := by
  have h : totient 941 = 941 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_942 : totient 942 = 312 := by
  have heq : (2 * (3 * (157)) : ℕ) = 942 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_157 : totient 157 = 157 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_157] <;> decide

theorem tot_943 : totient 943 = 880 := by
  have heq : (23 * (41) : ℕ) = 943 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_23, hp_41] <;> decide

theorem tot_944 : totient 944 = 464 := by
  have heq : (2^4 * (59) : ℕ) = 944 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_59] <;> decide

theorem tot_945 : totient 945 = 432 := by
  have heq : (3^3 * (5 * (7)) : ℕ) = 945 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_7] <;> decide

theorem tot_946 : totient 946 = 420 := by
  have heq : (2 * (11 * (43)) : ℕ) = 946 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_43] <;> decide

theorem tot_947 : totient 947 = 946 := by
  have h : totient 947 = 947 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_948 : totient 948 = 312 := by
  have heq : (2^2 * (3 * (79)) : ℕ) = 948 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_79] <;> decide

theorem tot_949 : totient 949 = 864 := by
  have heq : (13 * (73) : ℕ) = 949 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_73] <;> decide

theorem tot_950 : totient 950 = 360 := by
  have heq : (2 * (5^2 * (19)) : ℕ) = 950 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_19] <;> decide

theorem tot_951 : totient 951 = 632 := by
  have heq : (3 * (317) : ℕ) = 951 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_317 : totient 317 = 317 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_317] <;> decide

theorem tot_952 : totient 952 = 384 := by
  have heq : (2^3 * (7 * (17)) : ℕ) = 952 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_17] <;> decide

theorem tot_953 : totient 953 = 952 := by
  have h : totient 953 = 953 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_954 : totient 954 = 312 := by
  have heq : (2 * (3^2 * (53)) : ℕ) = 954 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_53] <;> decide

theorem tot_955 : totient 955 = 760 := by
  have heq : (5 * (191) : ℕ) = 955 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_191 : totient 191 = 191 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_191] <;> decide

theorem tot_956 : totient 956 = 476 := by
  have heq : (2^2 * (239) : ℕ) = 956 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_239 : totient 239 = 239 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_239] <;> decide

theorem tot_957 : totient 957 = 560 := by
  have heq : (3 * (11 * (29)) : ℕ) = 957 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11, hp_29] <;> decide

theorem tot_958 : totient 958 = 478 := by
  have heq : (2 * (479) : ℕ) = 958 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_479 : totient 479 = 479 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_479] <;> decide

theorem tot_959 : totient 959 = 816 := by
  have heq : (7 * (137) : ℕ) = 959 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_137 : totient 137 = 137 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_137] <;> decide

theorem tot_960 : totient 960 = 256 := by
  have heq : (2^6 * (3 * (5)) : ℕ) = 960 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^6) = 2^5 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5] <;> decide

theorem tot_961 : totient 961 = 930 := by
  have h : totient (31^2) = 31^1 * (31 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (31^2 : ℕ) = 961 := by decide
  rw [← heq]
  rw [h] <;> decide

theorem tot_962 : totient 962 = 432 := by
  have heq : (2 * (13 * (37)) : ℕ) = 962 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_37] <;> decide

theorem tot_963 : totient 963 = 636 := by
  have heq : (3^2 * (107) : ℕ) = 963 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_107] <;> decide

theorem tot_964 : totient 964 = 480 := by
  have heq : (2^2 * (241) : ℕ) = 964 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_241 : totient 241 = 241 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_241] <;> decide

theorem tot_965 : totient 965 = 768 := by
  have heq : (5 * (193) : ℕ) = 965 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_193 : totient 193 = 193 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_193] <;> decide

theorem tot_966 : totient 966 = 264 := by
  have heq : (2 * (3 * (7 * (23))) : ℕ) = 966 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_23] <;> decide

theorem tot_967 : totient 967 = 966 := by
  have h : totient 967 = 967 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_968 : totient 968 = 440 := by
  have heq : (2^3 * (11^2) : ℕ) = 968 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient (11^2) = 11^1 * (11 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_11] <;> decide

theorem tot_969 : totient 969 = 576 := by
  have heq : (3 * (17 * (19)) : ℕ) = 969 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_17, hp_19] <;> decide

theorem tot_970 : totient 970 = 384 := by
  have heq : (2 * (5 * (97)) : ℕ) = 970 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_97] <;> decide

theorem tot_971 : totient 971 = 970 := by
  have h : totient 971 = 971 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_972 : totient 972 = 324 := by
  have heq : (2^2 * (3^5) : ℕ) = 972 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^5) = 3^4 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3] <;> decide

theorem tot_973 : totient 973 = 828 := by
  have heq : (7 * (139) : ℕ) = 973 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_139 : totient 139 = 139 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_139] <;> decide

theorem tot_974 : totient 974 = 486 := by
  have heq : (2 * (487) : ℕ) = 974 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_487 : totient 487 = 487 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_487] <;> decide

theorem tot_975 : totient 975 = 480 := by
  have heq : (3 * (5^2 * (13)) : ℕ) = 975 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_13] <;> decide

theorem tot_976 : totient 976 = 480 := by
  have heq : (2^4 * (61) : ℕ) = 976 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_61] <;> decide

theorem tot_977 : totient 977 = 976 := by
  have h : totient 977 = 977 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_978 : totient 978 = 324 := by
  have heq : (2 * (3 * (163)) : ℕ) = 978 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_163 : totient 163 = 163 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_163] <;> decide

theorem tot_979 : totient 979 = 880 := by
  have heq : (11 * (89) : ℕ) = 979 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_89] <;> decide

theorem tot_980 : totient 980 = 336 := by
  have heq : (2^2 * (5 * (7^2)) : ℕ) = 980 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_5, hp_7] <;> decide

theorem tot_981 : totient 981 = 648 := by
  have heq : (3^2 * (109) : ℕ) = 981 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_109] <;> decide

theorem tot_982 : totient 982 = 490 := by
  have heq : (2 * (491) : ℕ) = 982 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_491 : totient 491 = 491 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_491] <;> decide

theorem tot_983 : totient 983 = 982 := by
  have h : totient 983 = 983 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_984 : totient 984 = 320 := by
  have heq : (2^3 * (3 * (41)) : ℕ) = 984 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_41] <;> decide

theorem tot_985 : totient 985 = 784 := by
  have heq : (5 * (197) : ℕ) = 985 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_197 : totient 197 = 197 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_197] <;> decide

theorem tot_986 : totient 986 = 448 := by
  have heq : (2 * (17 * (29)) : ℕ) = 986 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17, hp_29] <;> decide

theorem tot_987 : totient 987 = 552 := by
  have heq : (3 * (7 * (47)) : ℕ) = 987 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_47] <;> decide

theorem tot_988 : totient 988 = 432 := by
  have heq : (2^2 * (13 * (19)) : ℕ) = 988 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_19] <;> decide

theorem tot_989 : totient 989 = 924 := by
  have heq : (23 * (43) : ℕ) = 989 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_23, hp_43] <;> decide

theorem tot_990 : totient 990 = 240 := by
  have heq : (2 * (3^2 * (5 * (11))) : ℕ) = 990 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_11] <;> decide

theorem tot_991 : totient 991 = 990 := by
  have h : totient 991 = 991 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_992 : totient 992 = 480 := by
  have heq : (2^5 * (31) : ℕ) = 992 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_31] <;> decide

theorem tot_993 : totient 993 = 660 := by
  have heq : (3 * (331) : ℕ) = 993 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_331 : totient 331 = 331 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_331] <;> decide

theorem tot_994 : totient 994 = 420 := by
  have heq : (2 * (7 * (71)) : ℕ) = 994 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_71] <;> decide

theorem tot_995 : totient 995 = 792 := by
  have heq : (5 * (199) : ℕ) = 995 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_199 : totient 199 = 199 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_199] <;> decide

theorem tot_996 : totient 996 = 328 := by
  have heq : (2^2 * (3 * (83)) : ℕ) = 996 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_83] <;> decide

theorem tot_997 : totient 997 = 996 := by
  have h : totient 997 = 997 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_998 : totient 998 = 498 := by
  have heq : (2 * (499) : ℕ) = 998 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_499 : totient 499 = 499 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_499] <;> decide

theorem tot_999 : totient 999 = 648 := by
  have heq : (3^3 * (37) : ℕ) = 999 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_37] <;> decide

theorem tot_1000 : totient 1000 = 400 := by
  have heq : (2^3 * (5^3) : ℕ) = 1000 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^3) = 5^2 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_5] <;> decide

theorem tot_1001 : totient 1001 = 720 := by
  have heq : (7 * (11 * (13)) : ℕ) = 1001 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_11, hp_13] <;> decide

theorem tot_1002 : totient 1002 = 332 := by
  have heq : (2 * (3 * (167)) : ℕ) = 1002 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_167 : totient 167 = 167 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_167] <;> decide

theorem tot_1003 : totient 1003 = 928 := by
  have heq : (17 * (59) : ℕ) = 1003 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_59] <;> decide

theorem tot_1004 : totient 1004 = 500 := by
  have heq : (2^2 * (251) : ℕ) = 1004 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_251 : totient 251 = 251 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_251] <;> decide

theorem tot_1005 : totient 1005 = 528 := by
  have heq : (3 * (5 * (67)) : ℕ) = 1005 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_67] <;> decide

theorem tot_1006 : totient 1006 = 502 := by
  have heq : (2 * (503) : ℕ) = 1006 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_503 : totient 503 = 503 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_503] <;> decide

theorem tot_1007 : totient 1007 = 936 := by
  have heq : (19 * (53) : ℕ) = 1007 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_53] <;> decide

theorem tot_1008 : totient 1008 = 288 := by
  have heq : (2^4 * (3^2 * (7)) : ℕ) = 1008 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7] <;> decide

theorem tot_1009 : totient 1009 = 1008 := by
  have h : totient 1009 = 1009 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1010 : totient 1010 = 400 := by
  have heq : (2 * (5 * (101)) : ℕ) = 1010 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_101] <;> decide

theorem tot_1011 : totient 1011 = 672 := by
  have heq : (3 * (337) : ℕ) = 1011 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_337 : totient 337 = 337 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_337] <;> decide

theorem tot_1012 : totient 1012 = 440 := by
  have heq : (2^2 * (11 * (23)) : ℕ) = 1012 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_23] <;> decide

theorem tot_1013 : totient 1013 = 1012 := by
  have h : totient 1013 = 1013 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1014 : totient 1014 = 312 := by
  have heq : (2 * (3 * (13^2)) : ℕ) = 1014 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient (13^2) = 13^1 * (13 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_13] <;> decide

theorem tot_1015 : totient 1015 = 672 := by
  have heq : (5 * (7 * (29)) : ℕ) = 1015 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_7, hp_29] <;> decide

theorem tot_1016 : totient 1016 = 504 := by
  have heq : (2^3 * (127) : ℕ) = 1016 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_127 : totient 127 = 127 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_127] <;> decide

theorem tot_1017 : totient 1017 = 672 := by
  have heq : (3^2 * (113) : ℕ) = 1017 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_113 : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_113] <;> decide

theorem tot_1018 : totient 1018 = 508 := by
  have heq : (2 * (509) : ℕ) = 1018 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_509 : totient 509 = 509 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_509] <;> decide

theorem tot_1019 : totient 1019 = 1018 := by
  have h : totient 1019 = 1019 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1020 : totient 1020 = 256 := by
  have heq : (2^2 * (3 * (5 * (17))) : ℕ) = 1020 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_17] <;> decide

theorem tot_1021 : totient 1021 = 1020 := by
  have h : totient 1021 = 1021 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1022 : totient 1022 = 432 := by
  have heq : (2 * (7 * (73)) : ℕ) = 1022 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_73] <;> decide

theorem tot_1023 : totient 1023 = 600 := by
  have heq : (3 * (11 * (31)) : ℕ) = 1023 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11, hp_31] <;> decide

theorem tot_1024 : totient 1024 = 512 := by
  have h : totient (2^10) = 2^9 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (2^10 : ℕ) = 1024 := by decide
  rw [← heq]
  rw [h] <;> decide

theorem tot_1025 : totient 1025 = 800 := by
  have heq : (5^2 * (41) : ℕ) = 1025 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_41] <;> decide

theorem tot_1026 : totient 1026 = 324 := by
  have heq : (2 * (3^3 * (19)) : ℕ) = 1026 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_19] <;> decide

theorem tot_1027 : totient 1027 = 936 := by
  have heq : (13 * (79) : ℕ) = 1027 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_79] <;> decide

theorem tot_1028 : totient 1028 = 512 := by
  have heq : (2^2 * (257) : ℕ) = 1028 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_257 : totient 257 = 257 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_257] <;> decide

theorem tot_1029 : totient 1029 = 588 := by
  have heq : (3 * (7^3) : ℕ) = 1029 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^3) = 7^2 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_7] <;> decide

theorem tot_1030 : totient 1030 = 408 := by
  have heq : (2 * (5 * (103)) : ℕ) = 1030 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_103] <;> decide

theorem tot_1031 : totient 1031 = 1030 := by
  have h : totient 1031 = 1031 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1032 : totient 1032 = 336 := by
  have heq : (2^3 * (3 * (43)) : ℕ) = 1032 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_43] <;> decide

theorem tot_1033 : totient 1033 = 1032 := by
  have h : totient 1033 = 1033 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1034 : totient 1034 = 460 := by
  have heq : (2 * (11 * (47)) : ℕ) = 1034 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_47] <;> decide

theorem tot_1035 : totient 1035 = 528 := by
  have heq : (3^2 * (5 * (23)) : ℕ) = 1035 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_23] <;> decide

theorem tot_1036 : totient 1036 = 432 := by
  have heq : (2^2 * (7 * (37)) : ℕ) = 1036 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_37] <;> decide

theorem tot_1037 : totient 1037 = 960 := by
  have heq : (17 * (61) : ℕ) = 1037 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_61] <;> decide

theorem tot_1038 : totient 1038 = 344 := by
  have heq : (2 * (3 * (173)) : ℕ) = 1038 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_173 : totient 173 = 173 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_173] <;> decide

theorem tot_1039 : totient 1039 = 1038 := by
  have h : totient 1039 = 1039 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1040 : totient 1040 = 384 := by
  have heq : (2^4 * (5 * (13)) : ℕ) = 1040 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_13] <;> decide

theorem tot_1041 : totient 1041 = 692 := by
  have heq : (3 * (347) : ℕ) = 1041 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_347 : totient 347 = 347 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_347] <;> decide

theorem tot_1042 : totient 1042 = 520 := by
  have heq : (2 * (521) : ℕ) = 1042 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_521 : totient 521 = 521 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_521] <;> decide

theorem tot_1043 : totient 1043 = 888 := by
  have heq : (7 * (149) : ℕ) = 1043 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_149 : totient 149 = 149 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_149] <;> decide

theorem tot_1044 : totient 1044 = 336 := by
  have heq : (2^2 * (3^2 * (29)) : ℕ) = 1044 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_29] <;> decide

theorem tot_1045 : totient 1045 = 720 := by
  have heq : (5 * (11 * (19)) : ℕ) = 1045 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_11, hp_19] <;> decide

theorem tot_1046 : totient 1046 = 522 := by
  have heq : (2 * (523) : ℕ) = 1046 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_523 : totient 523 = 523 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_523] <;> decide

theorem tot_1047 : totient 1047 = 696 := by
  have heq : (3 * (349) : ℕ) = 1047 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_349 : totient 349 = 349 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_349] <;> decide

theorem tot_1048 : totient 1048 = 520 := by
  have heq : (2^3 * (131) : ℕ) = 1048 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_131 : totient 131 = 131 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_131] <;> decide

theorem tot_1049 : totient 1049 = 1048 := by
  have h : totient 1049 = 1049 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1050 : totient 1050 = 240 := by
  have heq : (2 * (3 * (5^2 * (7))) : ℕ) = 1050 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_7] <;> decide

theorem tot_1051 : totient 1051 = 1050 := by
  have h : totient 1051 = 1051 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1052 : totient 1052 = 524 := by
  have heq : (2^2 * (263) : ℕ) = 1052 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_263 : totient 263 = 263 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_263] <;> decide

theorem tot_1053 : totient 1053 = 648 := by
  have heq : (3^4 * (13) : ℕ) = 1053 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_13] <;> decide

theorem tot_1054 : totient 1054 = 480 := by
  have heq : (2 * (17 * (31)) : ℕ) = 1054 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17, hp_31] <;> decide

theorem tot_1055 : totient 1055 = 840 := by
  have heq : (5 * (211) : ℕ) = 1055 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_211 : totient 211 = 211 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_211] <;> decide

theorem tot_1056 : totient 1056 = 320 := by
  have heq : (2^5 * (3 * (11)) : ℕ) = 1056 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11] <;> decide

theorem tot_1057 : totient 1057 = 900 := by
  have heq : (7 * (151) : ℕ) = 1057 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_151 : totient 151 = 151 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_151] <;> decide

theorem tot_1058 : totient 1058 = 506 := by
  have heq : (2 * (23^2) : ℕ) = 1058 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_23 : totient (23^2) = 23^1 * (23 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_23] <;> decide

theorem tot_1059 : totient 1059 = 704 := by
  have heq : (3 * (353) : ℕ) = 1059 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_353 : totient 353 = 353 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_353] <;> decide

theorem tot_1060 : totient 1060 = 416 := by
  have heq : (2^2 * (5 * (53)) : ℕ) = 1060 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_53] <;> decide

theorem tot_1061 : totient 1061 = 1060 := by
  have h : totient 1061 = 1061 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1062 : totient 1062 = 348 := by
  have heq : (2 * (3^2 * (59)) : ℕ) = 1062 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_59] <;> decide

theorem tot_1063 : totient 1063 = 1062 := by
  have h : totient 1063 = 1063 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1064 : totient 1064 = 432 := by
  have heq : (2^3 * (7 * (19)) : ℕ) = 1064 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_19] <;> decide

theorem tot_1065 : totient 1065 = 560 := by
  have heq : (3 * (5 * (71)) : ℕ) = 1065 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_71] <;> decide

theorem tot_1066 : totient 1066 = 480 := by
  have heq : (2 * (13 * (41)) : ℕ) = 1066 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_41] <;> decide

theorem tot_1067 : totient 1067 = 960 := by
  have heq : (11 * (97) : ℕ) = 1067 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_97] <;> decide

theorem tot_1068 : totient 1068 = 352 := by
  have heq : (2^2 * (3 * (89)) : ℕ) = 1068 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_89] <;> decide

theorem tot_1069 : totient 1069 = 1068 := by
  have h : totient 1069 = 1069 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1070 : totient 1070 = 424 := by
  have heq : (2 * (5 * (107)) : ℕ) = 1070 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_107] <;> decide

theorem tot_1071 : totient 1071 = 576 := by
  have heq : (3^2 * (7 * (17)) : ℕ) = 1071 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_17] <;> decide

theorem tot_1072 : totient 1072 = 528 := by
  have heq : (2^4 * (67) : ℕ) = 1072 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_67] <;> decide

theorem tot_1073 : totient 1073 = 1008 := by
  have heq : (29 * (37) : ℕ) = 1073 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_29, hp_37] <;> decide

theorem tot_1074 : totient 1074 = 356 := by
  have heq : (2 * (3 * (179)) : ℕ) = 1074 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_179 : totient 179 = 179 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_179] <;> decide

theorem tot_1075 : totient 1075 = 840 := by
  have heq : (5^2 * (43) : ℕ) = 1075 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_43] <;> decide

theorem tot_1076 : totient 1076 = 536 := by
  have heq : (2^2 * (269) : ℕ) = 1076 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_269 : totient 269 = 269 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_269] <;> decide

theorem tot_1077 : totient 1077 = 716 := by
  have heq : (3 * (359) : ℕ) = 1077 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_359 : totient 359 = 359 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_359] <;> decide

theorem tot_1078 : totient 1078 = 420 := by
  have heq : (2 * (7^2 * (11)) : ℕ) = 1078 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_11] <;> decide

theorem tot_1079 : totient 1079 = 984 := by
  have heq : (13 * (83) : ℕ) = 1079 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_83] <;> decide

theorem tot_1080 : totient 1080 = 288 := by
  have heq : (2^3 * (3^3 * (5)) : ℕ) = 1080 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5] <;> decide

theorem tot_1081 : totient 1081 = 1012 := by
  have heq : (23 * (47) : ℕ) = 1081 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_23, hp_47] <;> decide

theorem tot_1082 : totient 1082 = 540 := by
  have heq : (2 * (541) : ℕ) = 1082 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_541 : totient 541 = 541 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_541] <;> decide

theorem tot_1083 : totient 1083 = 684 := by
  have heq : (3 * (19^2) : ℕ) = 1083 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_19 : totient (19^2) = 19^1 * (19 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_19] <;> decide

theorem tot_1084 : totient 1084 = 540 := by
  have heq : (2^2 * (271) : ℕ) = 1084 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_271 : totient 271 = 271 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_271] <;> decide

theorem tot_1085 : totient 1085 = 720 := by
  have heq : (5 * (7 * (31)) : ℕ) = 1085 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_7, hp_31] <;> decide

theorem tot_1086 : totient 1086 = 360 := by
  have heq : (2 * (3 * (181)) : ℕ) = 1086 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_181 : totient 181 = 181 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_181] <;> decide

theorem tot_1087 : totient 1087 = 1086 := by
  have h : totient 1087 = 1087 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1088 : totient 1088 = 512 := by
  have heq : (2^6 * (17) : ℕ) = 1088 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^6) = 2^5 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17] <;> decide

theorem tot_1089 : totient 1089 = 660 := by
  have heq : (3^2 * (11^2) : ℕ) = 1089 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient (11^2) = 11^1 * (11 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_11] <;> decide

theorem tot_1090 : totient 1090 = 432 := by
  have heq : (2 * (5 * (109)) : ℕ) = 1090 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_109] <;> decide

theorem tot_1091 : totient 1091 = 1090 := by
  have h : totient 1091 = 1091 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1092 : totient 1092 = 288 := by
  have heq : (2^2 * (3 * (7 * (13))) : ℕ) = 1092 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_13] <;> decide

theorem tot_1093 : totient 1093 = 1092 := by
  have h : totient 1093 = 1093 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1094 : totient 1094 = 546 := by
  have heq : (2 * (547) : ℕ) = 1094 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_547 : totient 547 = 547 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_547] <;> decide

theorem tot_1095 : totient 1095 = 576 := by
  have heq : (3 * (5 * (73)) : ℕ) = 1095 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_73] <;> decide

theorem tot_1096 : totient 1096 = 544 := by
  have heq : (2^3 * (137) : ℕ) = 1096 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_137 : totient 137 = 137 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_137] <;> decide

theorem tot_1097 : totient 1097 = 1096 := by
  have h : totient 1097 = 1097 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1098 : totient 1098 = 360 := by
  have heq : (2 * (3^2 * (61)) : ℕ) = 1098 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_61] <;> decide

theorem tot_1099 : totient 1099 = 936 := by
  have heq : (7 * (157) : ℕ) = 1099 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_157 : totient 157 = 157 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_157] <;> decide

theorem tot_1100 : totient 1100 = 400 := by
  have heq : (2^2 * (5^2 * (11)) : ℕ) = 1100 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_11] <;> decide

theorem tot_1101 : totient 1101 = 732 := by
  have heq : (3 * (367) : ℕ) = 1101 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_367 : totient 367 = 367 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_367] <;> decide

theorem tot_1102 : totient 1102 = 504 := by
  have heq : (2 * (19 * (29)) : ℕ) = 1102 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_19, hp_29] <;> decide

theorem tot_1103 : totient 1103 = 1102 := by
  have h : totient 1103 = 1103 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1104 : totient 1104 = 352 := by
  have heq : (2^4 * (3 * (23)) : ℕ) = 1104 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_23] <;> decide

theorem tot_1105 : totient 1105 = 768 := by
  have heq : (5 * (13 * (17)) : ℕ) = 1105 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_13, hp_17] <;> decide

theorem tot_1106 : totient 1106 = 468 := by
  have heq : (2 * (7 * (79)) : ℕ) = 1106 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_79] <;> decide

theorem tot_1107 : totient 1107 = 720 := by
  have heq : (3^3 * (41) : ℕ) = 1107 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_41] <;> decide

theorem tot_1108 : totient 1108 = 552 := by
  have heq : (2^2 * (277) : ℕ) = 1108 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_277 : totient 277 = 277 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_277] <;> decide

theorem tot_1109 : totient 1109 = 1108 := by
  have h : totient 1109 = 1109 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1110 : totient 1110 = 288 := by
  have heq : (2 * (3 * (5 * (37))) : ℕ) = 1110 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_37] <;> decide

theorem tot_1111 : totient 1111 = 1000 := by
  have heq : (11 * (101) : ℕ) = 1111 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_101] <;> decide

theorem tot_1112 : totient 1112 = 552 := by
  have heq : (2^3 * (139) : ℕ) = 1112 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_139 : totient 139 = 139 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_139] <;> decide

theorem tot_1113 : totient 1113 = 624 := by
  have heq : (3 * (7 * (53)) : ℕ) = 1113 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_53] <;> decide

theorem tot_1114 : totient 1114 = 556 := by
  have heq : (2 * (557) : ℕ) = 1114 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_557 : totient 557 = 557 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_557] <;> decide

theorem tot_1115 : totient 1115 = 888 := by
  have heq : (5 * (223) : ℕ) = 1115 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_223 : totient 223 = 223 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_223] <;> decide

theorem tot_1116 : totient 1116 = 360 := by
  have heq : (2^2 * (3^2 * (31)) : ℕ) = 1116 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_31] <;> decide

theorem tot_1117 : totient 1117 = 1116 := by
  have h : totient 1117 = 1117 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1118 : totient 1118 = 504 := by
  have heq : (2 * (13 * (43)) : ℕ) = 1118 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_43] <;> decide

theorem tot_1119 : totient 1119 = 744 := by
  have heq : (3 * (373) : ℕ) = 1119 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_373 : totient 373 = 373 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_373] <;> decide

theorem tot_1120 : totient 1120 = 384 := by
  have heq : (2^5 * (5 * (7)) : ℕ) = 1120 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7] <;> decide

theorem tot_1121 : totient 1121 = 1044 := by
  have heq : (19 * (59) : ℕ) = 1121 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_59] <;> decide

theorem tot_1122 : totient 1122 = 320 := by
  have heq : (2 * (3 * (11 * (17))) : ℕ) = 1122 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11, hp_17] <;> decide

theorem tot_1123 : totient 1123 = 1122 := by
  have h : totient 1123 = 1123 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1124 : totient 1124 = 560 := by
  have heq : (2^2 * (281) : ℕ) = 1124 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_281 : totient 281 = 281 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_281] <;> decide

theorem tot_1125 : totient 1125 = 600 := by
  have heq : (3^2 * (5^3) : ℕ) = 1125 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^3) = 5^2 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_5] <;> decide

theorem tot_1126 : totient 1126 = 562 := by
  have heq : (2 * (563) : ℕ) = 1126 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_563 : totient 563 = 563 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_563] <;> decide

theorem tot_1127 : totient 1127 = 924 := by
  have heq : (7^2 * (23) : ℕ) = 1127 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_23] <;> decide

theorem tot_1128 : totient 1128 = 368 := by
  have heq : (2^3 * (3 * (47)) : ℕ) = 1128 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_47] <;> decide

theorem tot_1129 : totient 1129 = 1128 := by
  have h : totient 1129 = 1129 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1130 : totient 1130 = 448 := by
  have heq : (2 * (5 * (113)) : ℕ) = 1130 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_113 : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_113] <;> decide

theorem tot_1131 : totient 1131 = 672 := by
  have heq : (3 * (13 * (29)) : ℕ) = 1131 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_13, hp_29] <;> decide

theorem tot_1132 : totient 1132 = 564 := by
  have heq : (2^2 * (283) : ℕ) = 1132 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_283 : totient 283 = 283 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_283] <;> decide

theorem tot_1133 : totient 1133 = 1020 := by
  have heq : (11 * (103) : ℕ) = 1133 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_103] <;> decide

theorem tot_1134 : totient 1134 = 324 := by
  have heq : (2 * (3^4 * (7)) : ℕ) = 1134 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7] <;> decide

theorem tot_1135 : totient 1135 = 904 := by
  have heq : (5 * (227) : ℕ) = 1135 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_227 : totient 227 = 227 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_227] <;> decide

theorem tot_1136 : totient 1136 = 560 := by
  have heq : (2^4 * (71) : ℕ) = 1136 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_71] <;> decide

theorem tot_1137 : totient 1137 = 756 := by
  have heq : (3 * (379) : ℕ) = 1137 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_379 : totient 379 = 379 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_379] <;> decide

theorem tot_1138 : totient 1138 = 568 := by
  have heq : (2 * (569) : ℕ) = 1138 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_569 : totient 569 = 569 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_569] <;> decide

theorem tot_1139 : totient 1139 = 1056 := by
  have heq : (17 * (67) : ℕ) = 1139 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_67] <;> decide

theorem tot_1140 : totient 1140 = 288 := by
  have heq : (2^2 * (3 * (5 * (19))) : ℕ) = 1140 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_19] <;> decide

theorem tot_1141 : totient 1141 = 972 := by
  have heq : (7 * (163) : ℕ) = 1141 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_163 : totient 163 = 163 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_163] <;> decide

theorem tot_1142 : totient 1142 = 570 := by
  have heq : (2 * (571) : ℕ) = 1142 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_571 : totient 571 = 571 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_571] <;> decide

theorem tot_1143 : totient 1143 = 756 := by
  have heq : (3^2 * (127) : ℕ) = 1143 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_127 : totient 127 = 127 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_127] <;> decide

theorem tot_1144 : totient 1144 = 480 := by
  have heq : (2^3 * (11 * (13)) : ℕ) = 1144 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_13] <;> decide

theorem tot_1145 : totient 1145 = 912 := by
  have heq : (5 * (229) : ℕ) = 1145 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_229 : totient 229 = 229 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_229] <;> decide

theorem tot_1146 : totient 1146 = 380 := by
  have heq : (2 * (3 * (191)) : ℕ) = 1146 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_191 : totient 191 = 191 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_191] <;> decide

theorem tot_1147 : totient 1147 = 1080 := by
  have heq : (31 * (37) : ℕ) = 1147 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_31, hp_37] <;> decide

theorem tot_1148 : totient 1148 = 480 := by
  have heq : (2^2 * (7 * (41)) : ℕ) = 1148 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_41] <;> decide

theorem tot_1149 : totient 1149 = 764 := by
  have heq : (3 * (383) : ℕ) = 1149 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_383 : totient 383 = 383 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_383] <;> decide

theorem tot_1150 : totient 1150 = 440 := by
  have heq : (2 * (5^2 * (23)) : ℕ) = 1150 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_23] <;> decide

theorem tot_1151 : totient 1151 = 1150 := by
  have h : totient 1151 = 1151 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1152 : totient 1152 = 384 := by
  have heq : (2^7 * (3^2) : ℕ) = 1152 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^7) = 2^6 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3] <;> decide

theorem tot_1153 : totient 1153 = 1152 := by
  have h : totient 1153 = 1153 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1154 : totient 1154 = 576 := by
  have heq : (2 * (577) : ℕ) = 1154 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_577 : totient 577 = 577 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_577] <;> decide

theorem tot_1155 : totient 1155 = 480 := by
  have heq : (3 * (5 * (7 * (11))) : ℕ) = 1155 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_7, hp_11] <;> decide

theorem tot_1156 : totient 1156 = 544 := by
  have heq : (2^2 * (17^2) : ℕ) = 1156 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient (17^2) = 17^1 * (17 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_17] <;> decide

theorem tot_1157 : totient 1157 = 1056 := by
  have heq : (13 * (89) : ℕ) = 1157 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_89] <;> decide

theorem tot_1158 : totient 1158 = 384 := by
  have heq : (2 * (3 * (193)) : ℕ) = 1158 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_193 : totient 193 = 193 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_193] <;> decide

theorem tot_1159 : totient 1159 = 1080 := by
  have heq : (19 * (61) : ℕ) = 1159 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_61] <;> decide

theorem tot_1160 : totient 1160 = 448 := by
  have heq : (2^3 * (5 * (29)) : ℕ) = 1160 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_29] <;> decide

theorem tot_1161 : totient 1161 = 756 := by
  have heq : (3^3 * (43) : ℕ) = 1161 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_43] <;> decide

theorem tot_1162 : totient 1162 = 492 := by
  have heq : (2 * (7 * (83)) : ℕ) = 1162 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_83] <;> decide

theorem tot_1163 : totient 1163 = 1162 := by
  have h : totient 1163 = 1163 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1164 : totient 1164 = 384 := by
  have heq : (2^2 * (3 * (97)) : ℕ) = 1164 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_97] <;> decide

theorem tot_1165 : totient 1165 = 928 := by
  have heq : (5 * (233) : ℕ) = 1165 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_233 : totient 233 = 233 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_233] <;> decide

theorem tot_1166 : totient 1166 = 520 := by
  have heq : (2 * (11 * (53)) : ℕ) = 1166 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_53] <;> decide

theorem tot_1167 : totient 1167 = 776 := by
  have heq : (3 * (389) : ℕ) = 1167 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_389 : totient 389 = 389 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_389] <;> decide

theorem tot_1168 : totient 1168 = 576 := by
  have heq : (2^4 * (73) : ℕ) = 1168 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_73] <;> decide

theorem tot_1169 : totient 1169 = 996 := by
  have heq : (7 * (167) : ℕ) = 1169 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_167 : totient 167 = 167 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_167] <;> decide

theorem tot_1170 : totient 1170 = 288 := by
  have heq : (2 * (3^2 * (5 * (13))) : ℕ) = 1170 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_13] <;> decide

theorem tot_1171 : totient 1171 = 1170 := by
  have h : totient 1171 = 1171 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1172 : totient 1172 = 584 := by
  have heq : (2^2 * (293) : ℕ) = 1172 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_293 : totient 293 = 293 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_293] <;> decide

theorem tot_1173 : totient 1173 = 704 := by
  have heq : (3 * (17 * (23)) : ℕ) = 1173 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_17, hp_23] <;> decide

theorem tot_1174 : totient 1174 = 586 := by
  have heq : (2 * (587) : ℕ) = 1174 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_587 : totient 587 = 587 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_587] <;> decide

theorem tot_1175 : totient 1175 = 920 := by
  have heq : (5^2 * (47) : ℕ) = 1175 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_47] <;> decide

theorem tot_1176 : totient 1176 = 336 := by
  have heq : (2^3 * (3 * (7^2)) : ℕ) = 1176 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_7] <;> decide

theorem tot_1177 : totient 1177 = 1060 := by
  have heq : (11 * (107) : ℕ) = 1177 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_107] <;> decide

theorem tot_1178 : totient 1178 = 540 := by
  have heq : (2 * (19 * (31)) : ℕ) = 1178 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_19, hp_31] <;> decide

theorem tot_1179 : totient 1179 = 780 := by
  have heq : (3^2 * (131) : ℕ) = 1179 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_131 : totient 131 = 131 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_131] <;> decide

theorem tot_1180 : totient 1180 = 464 := by
  have heq : (2^2 * (5 * (59)) : ℕ) = 1180 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_59] <;> decide

theorem tot_1181 : totient 1181 = 1180 := by
  have h : totient 1181 = 1181 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1182 : totient 1182 = 392 := by
  have heq : (2 * (3 * (197)) : ℕ) = 1182 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_197 : totient 197 = 197 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_197] <;> decide

theorem tot_1183 : totient 1183 = 936 := by
  have heq : (7 * (13^2) : ℕ) = 1183 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient (13^2) = 13^1 * (13 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_7, hp_13] <;> decide

theorem tot_1184 : totient 1184 = 576 := by
  have heq : (2^5 * (37) : ℕ) = 1184 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_37] <;> decide

theorem tot_1185 : totient 1185 = 624 := by
  have heq : (3 * (5 * (79)) : ℕ) = 1185 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_79] <;> decide

theorem tot_1186 : totient 1186 = 592 := by
  have heq : (2 * (593) : ℕ) = 1186 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_593 : totient 593 = 593 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_593] <;> decide

theorem tot_1187 : totient 1187 = 1186 := by
  have h : totient 1187 = 1187 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1188 : totient 1188 = 360 := by
  have heq : (2^2 * (3^3 * (11)) : ℕ) = 1188 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11] <;> decide

theorem tot_1189 : totient 1189 = 1120 := by
  have heq : (29 * (41) : ℕ) = 1189 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_29, hp_41] <;> decide

theorem tot_1190 : totient 1190 = 384 := by
  have heq : (2 * (5 * (7 * (17))) : ℕ) = 1190 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7, hp_17] <;> decide

theorem tot_1191 : totient 1191 = 792 := by
  have heq : (3 * (397) : ℕ) = 1191 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_397 : totient 397 = 397 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_397] <;> decide

theorem tot_1192 : totient 1192 = 592 := by
  have heq : (2^3 * (149) : ℕ) = 1192 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_149 : totient 149 = 149 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_149] <;> decide

theorem tot_1193 : totient 1193 = 1192 := by
  have h : totient 1193 = 1193 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1194 : totient 1194 = 396 := by
  have heq : (2 * (3 * (199)) : ℕ) = 1194 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_199 : totient 199 = 199 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_199] <;> decide

theorem tot_1195 : totient 1195 = 952 := by
  have heq : (5 * (239) : ℕ) = 1195 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_239 : totient 239 = 239 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_239] <;> decide

theorem tot_1196 : totient 1196 = 528 := by
  have heq : (2^2 * (13 * (23)) : ℕ) = 1196 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_23] <;> decide

theorem tot_1197 : totient 1197 = 648 := by
  have heq : (3^2 * (7 * (19)) : ℕ) = 1197 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_19] <;> decide

theorem tot_1198 : totient 1198 = 598 := by
  have heq : (2 * (599) : ℕ) = 1198 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_599 : totient 599 = 599 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_599] <;> decide

theorem tot_1199 : totient 1199 = 1080 := by
  have heq : (11 * (109) : ℕ) = 1199 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_109] <;> decide

theorem tot_1200 : totient 1200 = 320 := by
  have heq : (2^4 * (3 * (5^2)) : ℕ) = 1200 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_5] <;> decide

theorem tot_1201 : totient 1201 = 1200 := by
  have h : totient 1201 = 1201 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1202 : totient 1202 = 600 := by
  have heq : (2 * (601) : ℕ) = 1202 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_601 : totient 601 = 601 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_601] <;> decide

theorem tot_1203 : totient 1203 = 800 := by
  have heq : (3 * (401) : ℕ) = 1203 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_401 : totient 401 = 401 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_401] <;> decide

theorem tot_1204 : totient 1204 = 504 := by
  have heq : (2^2 * (7 * (43)) : ℕ) = 1204 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_43] <;> decide

theorem tot_1205 : totient 1205 = 960 := by
  have heq : (5 * (241) : ℕ) = 1205 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_241 : totient 241 = 241 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_241] <;> decide

theorem tot_1206 : totient 1206 = 396 := by
  have heq : (2 * (3^2 * (67)) : ℕ) = 1206 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_67] <;> decide

theorem tot_1207 : totient 1207 = 1120 := by
  have heq : (17 * (71) : ℕ) = 1207 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_71] <;> decide

theorem tot_1208 : totient 1208 = 600 := by
  have heq : (2^3 * (151) : ℕ) = 1208 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_151 : totient 151 = 151 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_151] <;> decide

theorem tot_1209 : totient 1209 = 720 := by
  have heq : (3 * (13 * (31)) : ℕ) = 1209 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_13, hp_31] <;> decide

theorem tot_1210 : totient 1210 = 440 := by
  have heq : (2 * (5 * (11^2)) : ℕ) = 1210 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient (11^2) = 11^1 * (11 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_5, hp_11] <;> decide

theorem tot_1211 : totient 1211 = 1032 := by
  have heq : (7 * (173) : ℕ) = 1211 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_173 : totient 173 = 173 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_173] <;> decide

theorem tot_1212 : totient 1212 = 400 := by
  have heq : (2^2 * (3 * (101)) : ℕ) = 1212 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_101] <;> decide

theorem tot_1213 : totient 1213 = 1212 := by
  have h : totient 1213 = 1213 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1214 : totient 1214 = 606 := by
  have heq : (2 * (607) : ℕ) = 1214 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_607 : totient 607 = 607 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_607] <;> decide

theorem tot_1215 : totient 1215 = 648 := by
  have heq : (3^5 * (5) : ℕ) = 1215 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^5) = 3^4 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5] <;> decide

theorem tot_1216 : totient 1216 = 576 := by
  have heq : (2^6 * (19) : ℕ) = 1216 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^6) = 2^5 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_19] <;> decide

theorem tot_1217 : totient 1217 = 1216 := by
  have h : totient 1217 = 1217 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1218 : totient 1218 = 336 := by
  have heq : (2 * (3 * (7 * (29))) : ℕ) = 1218 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_29] <;> decide

theorem tot_1219 : totient 1219 = 1144 := by
  have heq : (23 * (53) : ℕ) = 1219 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_23, hp_53] <;> decide

theorem tot_1220 : totient 1220 = 480 := by
  have heq : (2^2 * (5 * (61)) : ℕ) = 1220 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_61] <;> decide

theorem tot_1221 : totient 1221 = 720 := by
  have heq : (3 * (11 * (37)) : ℕ) = 1221 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11, hp_37] <;> decide

theorem tot_1222 : totient 1222 = 552 := by
  have heq : (2 * (13 * (47)) : ℕ) = 1222 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_47] <;> decide

theorem tot_1223 : totient 1223 = 1222 := by
  have h : totient 1223 = 1223 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1224 : totient 1224 = 384 := by
  have heq : (2^3 * (3^2 * (17)) : ℕ) = 1224 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_17] <;> decide

theorem tot_1225 : totient 1225 = 840 := by
  have heq : (5^2 * (7^2) : ℕ) = 1225 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_5, hp_7] <;> decide

theorem tot_1226 : totient 1226 = 612 := by
  have heq : (2 * (613) : ℕ) = 1226 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_613 : totient 613 = 613 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_613] <;> decide

theorem tot_1227 : totient 1227 = 816 := by
  have heq : (3 * (409) : ℕ) = 1227 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_409 : totient 409 = 409 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_409] <;> decide

theorem tot_1228 : totient 1228 = 612 := by
  have heq : (2^2 * (307) : ℕ) = 1228 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_307 : totient 307 = 307 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_307] <;> decide

theorem tot_1229 : totient 1229 = 1228 := by
  have h : totient 1229 = 1229 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1230 : totient 1230 = 320 := by
  have heq : (2 * (3 * (5 * (41))) : ℕ) = 1230 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_41] <;> decide

theorem tot_1231 : totient 1231 = 1230 := by
  have h : totient 1231 = 1231 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1232 : totient 1232 = 480 := by
  have heq : (2^4 * (7 * (11)) : ℕ) = 1232 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_11] <;> decide

theorem tot_1233 : totient 1233 = 816 := by
  have heq : (3^2 * (137) : ℕ) = 1233 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_137 : totient 137 = 137 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_137] <;> decide

theorem tot_1234 : totient 1234 = 616 := by
  have heq : (2 * (617) : ℕ) = 1234 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_617 : totient 617 = 617 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_617] <;> decide

theorem tot_1235 : totient 1235 = 864 := by
  have heq : (5 * (13 * (19)) : ℕ) = 1235 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_13, hp_19] <;> decide

theorem tot_1236 : totient 1236 = 408 := by
  have heq : (2^2 * (3 * (103)) : ℕ) = 1236 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_103] <;> decide

theorem tot_1237 : totient 1237 = 1236 := by
  have h : totient 1237 = 1237 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1238 : totient 1238 = 618 := by
  have heq : (2 * (619) : ℕ) = 1238 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_619 : totient 619 = 619 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_619] <;> decide

theorem tot_1239 : totient 1239 = 696 := by
  have heq : (3 * (7 * (59)) : ℕ) = 1239 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_59] <;> decide

theorem tot_1240 : totient 1240 = 480 := by
  have heq : (2^3 * (5 * (31)) : ℕ) = 1240 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_31] <;> decide

theorem tot_1241 : totient 1241 = 1152 := by
  have heq : (17 * (73) : ℕ) = 1241 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_73] <;> decide

theorem tot_1242 : totient 1242 = 396 := by
  have heq : (2 * (3^3 * (23)) : ℕ) = 1242 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_23] <;> decide

theorem tot_1243 : totient 1243 = 1120 := by
  have heq : (11 * (113) : ℕ) = 1243 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_113 : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_113] <;> decide

theorem tot_1244 : totient 1244 = 620 := by
  have heq : (2^2 * (311) : ℕ) = 1244 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_311 : totient 311 = 311 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_311] <;> decide

theorem tot_1245 : totient 1245 = 656 := by
  have heq : (3 * (5 * (83)) : ℕ) = 1245 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_83] <;> decide

theorem tot_1246 : totient 1246 = 528 := by
  have heq : (2 * (7 * (89)) : ℕ) = 1246 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_89] <;> decide

theorem tot_1247 : totient 1247 = 1176 := by
  have heq : (29 * (43) : ℕ) = 1247 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_29, hp_43] <;> decide

theorem tot_1248 : totient 1248 = 384 := by
  have heq : (2^5 * (3 * (13)) : ℕ) = 1248 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_13] <;> decide

theorem tot_1249 : totient 1249 = 1248 := by
  have h : totient 1249 = 1249 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1250 : totient 1250 = 500 := by
  have heq : (2 * (5^4) : ℕ) = 1250 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^4) = 5^3 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_5] <;> decide

theorem tot_1251 : totient 1251 = 828 := by
  have heq : (3^2 * (139) : ℕ) = 1251 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_139 : totient 139 = 139 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_139] <;> decide

theorem tot_1252 : totient 1252 = 624 := by
  have heq : (2^2 * (313) : ℕ) = 1252 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_313 : totient 313 = 313 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_313] <;> decide

theorem tot_1253 : totient 1253 = 1068 := by
  have heq : (7 * (179) : ℕ) = 1253 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_179 : totient 179 = 179 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_179] <;> decide

theorem tot_1254 : totient 1254 = 360 := by
  have heq : (2 * (3 * (11 * (19))) : ℕ) = 1254 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11, hp_19] <;> decide

theorem tot_1255 : totient 1255 = 1000 := by
  have heq : (5 * (251) : ℕ) = 1255 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_251 : totient 251 = 251 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_251] <;> decide

theorem tot_1256 : totient 1256 = 624 := by
  have heq : (2^3 * (157) : ℕ) = 1256 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_157 : totient 157 = 157 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_157] <;> decide

theorem tot_1257 : totient 1257 = 836 := by
  have heq : (3 * (419) : ℕ) = 1257 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_419 : totient 419 = 419 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_419] <;> decide

theorem tot_1258 : totient 1258 = 576 := by
  have heq : (2 * (17 * (37)) : ℕ) = 1258 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17, hp_37] <;> decide

theorem tot_1259 : totient 1259 = 1258 := by
  have h : totient 1259 = 1259 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1260 : totient 1260 = 288 := by
  have heq : (2^2 * (3^2 * (5 * (7))) : ℕ) = 1260 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_7] <;> decide

theorem tot_1261 : totient 1261 = 1152 := by
  have heq : (13 * (97) : ℕ) = 1261 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_97] <;> decide

theorem tot_1262 : totient 1262 = 630 := by
  have heq : (2 * (631) : ℕ) = 1262 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_631 : totient 631 = 631 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_631] <;> decide

theorem tot_1263 : totient 1263 = 840 := by
  have heq : (3 * (421) : ℕ) = 1263 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_421 : totient 421 = 421 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_421] <;> decide

theorem tot_1264 : totient 1264 = 624 := by
  have heq : (2^4 * (79) : ℕ) = 1264 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_79] <;> decide

theorem tot_1265 : totient 1265 = 880 := by
  have heq : (5 * (11 * (23)) : ℕ) = 1265 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_11, hp_23] <;> decide

theorem tot_1266 : totient 1266 = 420 := by
  have heq : (2 * (3 * (211)) : ℕ) = 1266 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_211 : totient 211 = 211 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_211] <;> decide

theorem tot_1267 : totient 1267 = 1080 := by
  have heq : (7 * (181) : ℕ) = 1267 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_181 : totient 181 = 181 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_181] <;> decide

theorem tot_1268 : totient 1268 = 632 := by
  have heq : (2^2 * (317) : ℕ) = 1268 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_317 : totient 317 = 317 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_317] <;> decide

theorem tot_1269 : totient 1269 = 828 := by
  have heq : (3^3 * (47) : ℕ) = 1269 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_47] <;> decide

theorem tot_1270 : totient 1270 = 504 := by
  have heq : (2 * (5 * (127)) : ℕ) = 1270 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_127 : totient 127 = 127 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_127] <;> decide

theorem tot_1271 : totient 1271 = 1200 := by
  have heq : (31 * (41) : ℕ) = 1271 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_31, hp_41] <;> decide

theorem tot_1272 : totient 1272 = 416 := by
  have heq : (2^3 * (3 * (53)) : ℕ) = 1272 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_53] <;> decide

theorem tot_1273 : totient 1273 = 1188 := by
  have heq : (19 * (67) : ℕ) = 1273 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_67] <;> decide

theorem tot_1274 : totient 1274 = 504 := by
  have heq : (2 * (7^2 * (13)) : ℕ) = 1274 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_13] <;> decide

theorem tot_1275 : totient 1275 = 640 := by
  have heq : (3 * (5^2 * (17)) : ℕ) = 1275 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_17] <;> decide

theorem tot_1276 : totient 1276 = 560 := by
  have heq : (2^2 * (11 * (29)) : ℕ) = 1276 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_29] <;> decide

theorem tot_1277 : totient 1277 = 1276 := by
  have h : totient 1277 = 1277 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1278 : totient 1278 = 420 := by
  have heq : (2 * (3^2 * (71)) : ℕ) = 1278 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_71] <;> decide

theorem tot_1279 : totient 1279 = 1278 := by
  have h : totient 1279 = 1279 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1280 : totient 1280 = 512 := by
  have heq : (2^8 * (5) : ℕ) = 1280 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^8) = 2^7 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5] <;> decide

theorem tot_1281 : totient 1281 = 720 := by
  have heq : (3 * (7 * (61)) : ℕ) = 1281 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_61] <;> decide

theorem tot_1282 : totient 1282 = 640 := by
  have heq : (2 * (641) : ℕ) = 1282 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_641 : totient 641 = 641 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_641] <;> decide

theorem tot_1283 : totient 1283 = 1282 := by
  have h : totient 1283 = 1283 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1284 : totient 1284 = 424 := by
  have heq : (2^2 * (3 * (107)) : ℕ) = 1284 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_107] <;> decide

theorem tot_1285 : totient 1285 = 1024 := by
  have heq : (5 * (257) : ℕ) = 1285 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_257 : totient 257 = 257 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_257] <;> decide

theorem tot_1286 : totient 1286 = 642 := by
  have heq : (2 * (643) : ℕ) = 1286 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_643 : totient 643 = 643 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_643] <;> decide

theorem tot_1287 : totient 1287 = 720 := by
  have heq : (3^2 * (11 * (13)) : ℕ) = 1287 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11, hp_13] <;> decide

theorem tot_1288 : totient 1288 = 528 := by
  have heq : (2^3 * (7 * (23)) : ℕ) = 1288 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_23] <;> decide

theorem tot_1289 : totient 1289 = 1288 := by
  have h : totient 1289 = 1289 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1290 : totient 1290 = 336 := by
  have heq : (2 * (3 * (5 * (43))) : ℕ) = 1290 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_43] <;> decide

theorem tot_1291 : totient 1291 = 1290 := by
  have h : totient 1291 = 1291 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1292 : totient 1292 = 576 := by
  have heq : (2^2 * (17 * (19)) : ℕ) = 1292 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17, hp_19] <;> decide

theorem tot_1293 : totient 1293 = 860 := by
  have heq : (3 * (431) : ℕ) = 1293 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_431 : totient 431 = 431 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_431] <;> decide

theorem tot_1294 : totient 1294 = 646 := by
  have heq : (2 * (647) : ℕ) = 1294 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_647 : totient 647 = 647 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_647] <;> decide

theorem tot_1295 : totient 1295 = 864 := by
  have heq : (5 * (7 * (37)) : ℕ) = 1295 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_7, hp_37] <;> decide

theorem tot_1296 : totient 1296 = 432 := by
  have heq : (2^4 * (3^4) : ℕ) = 1296 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3] <;> decide

theorem tot_1297 : totient 1297 = 1296 := by
  have h : totient 1297 = 1297 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1298 : totient 1298 = 580 := by
  have heq : (2 * (11 * (59)) : ℕ) = 1298 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_59] <;> decide

theorem tot_1299 : totient 1299 = 864 := by
  have heq : (3 * (433) : ℕ) = 1299 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_433 : totient 433 = 433 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_433] <;> decide

theorem tot_1300 : totient 1300 = 480 := by
  have heq : (2^2 * (5^2 * (13)) : ℕ) = 1300 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_13] <;> decide

theorem tot_1301 : totient 1301 = 1300 := by
  have h : totient 1301 = 1301 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1302 : totient 1302 = 360 := by
  have heq : (2 * (3 * (7 * (31))) : ℕ) = 1302 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_31] <;> decide

theorem tot_1303 : totient 1303 = 1302 := by
  have h : totient 1303 = 1303 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1304 : totient 1304 = 648 := by
  have heq : (2^3 * (163) : ℕ) = 1304 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_163 : totient 163 = 163 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_163] <;> decide

theorem tot_1305 : totient 1305 = 672 := by
  have heq : (3^2 * (5 * (29)) : ℕ) = 1305 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_29] <;> decide

theorem tot_1306 : totient 1306 = 652 := by
  have heq : (2 * (653) : ℕ) = 1306 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_653 : totient 653 = 653 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_653] <;> decide

theorem tot_1307 : totient 1307 = 1306 := by
  have h : totient 1307 = 1307 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1308 : totient 1308 = 432 := by
  have heq : (2^2 * (3 * (109)) : ℕ) = 1308 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_109] <;> decide

theorem tot_1309 : totient 1309 = 960 := by
  have heq : (7 * (11 * (17)) : ℕ) = 1309 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_11, hp_17] <;> decide

theorem tot_1310 : totient 1310 = 520 := by
  have heq : (2 * (5 * (131)) : ℕ) = 1310 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_131 : totient 131 = 131 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_131] <;> decide

theorem tot_1311 : totient 1311 = 792 := by
  have heq : (3 * (19 * (23)) : ℕ) = 1311 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_19, hp_23] <;> decide

theorem tot_1312 : totient 1312 = 640 := by
  have heq : (2^5 * (41) : ℕ) = 1312 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_41] <;> decide

theorem tot_1313 : totient 1313 = 1200 := by
  have heq : (13 * (101) : ℕ) = 1313 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_101] <;> decide

theorem tot_1314 : totient 1314 = 432 := by
  have heq : (2 * (3^2 * (73)) : ℕ) = 1314 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_73] <;> decide

theorem tot_1315 : totient 1315 = 1048 := by
  have heq : (5 * (263) : ℕ) = 1315 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_263 : totient 263 = 263 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_263] <;> decide

theorem tot_1316 : totient 1316 = 552 := by
  have heq : (2^2 * (7 * (47)) : ℕ) = 1316 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_47] <;> decide

theorem tot_1317 : totient 1317 = 876 := by
  have heq : (3 * (439) : ℕ) = 1317 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_439 : totient 439 = 439 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_439] <;> decide

theorem tot_1318 : totient 1318 = 658 := by
  have heq : (2 * (659) : ℕ) = 1318 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_659 : totient 659 = 659 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_659] <;> decide

theorem tot_1319 : totient 1319 = 1318 := by
  have h : totient 1319 = 1319 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1320 : totient 1320 = 320 := by
  have heq : (2^3 * (3 * (5 * (11))) : ℕ) = 1320 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_11] <;> decide

theorem tot_1321 : totient 1321 = 1320 := by
  have h : totient 1321 = 1321 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1322 : totient 1322 = 660 := by
  have heq : (2 * (661) : ℕ) = 1322 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_661 : totient 661 = 661 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_661] <;> decide

theorem tot_1323 : totient 1323 = 756 := by
  have heq : (3^3 * (7^2) : ℕ) = 1323 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_7] <;> decide

theorem tot_1324 : totient 1324 = 660 := by
  have heq : (2^2 * (331) : ℕ) = 1324 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_331 : totient 331 = 331 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_331] <;> decide

theorem tot_1325 : totient 1325 = 1040 := by
  have heq : (5^2 * (53) : ℕ) = 1325 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_53] <;> decide

theorem tot_1326 : totient 1326 = 384 := by
  have heq : (2 * (3 * (13 * (17))) : ℕ) = 1326 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_13, hp_17] <;> decide

theorem tot_1327 : totient 1327 = 1326 := by
  have h : totient 1327 = 1327 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1328 : totient 1328 = 656 := by
  have heq : (2^4 * (83) : ℕ) = 1328 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_83] <;> decide

theorem tot_1329 : totient 1329 = 884 := by
  have heq : (3 * (443) : ℕ) = 1329 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_443 : totient 443 = 443 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_443] <;> decide

theorem tot_1330 : totient 1330 = 432 := by
  have heq : (2 * (5 * (7 * (19))) : ℕ) = 1330 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7, hp_19] <;> decide

theorem tot_1331 : totient 1331 = 1210 := by
  have h : totient (11^3) = 11^2 * (11 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (11^3 : ℕ) = 1331 := by decide
  rw [← heq]
  rw [h] <;> decide

theorem tot_1332 : totient 1332 = 432 := by
  have heq : (2^2 * (3^2 * (37)) : ℕ) = 1332 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_37] <;> decide

theorem tot_1333 : totient 1333 = 1260 := by
  have heq : (31 * (43) : ℕ) = 1333 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_31, hp_43] <;> decide

theorem tot_1334 : totient 1334 = 616 := by
  have heq : (2 * (23 * (29)) : ℕ) = 1334 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_23, hp_29] <;> decide

theorem tot_1335 : totient 1335 = 704 := by
  have heq : (3 * (5 * (89)) : ℕ) = 1335 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_89] <;> decide

theorem tot_1336 : totient 1336 = 664 := by
  have heq : (2^3 * (167) : ℕ) = 1336 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_167 : totient 167 = 167 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_167] <;> decide

theorem tot_1337 : totient 1337 = 1140 := by
  have heq : (7 * (191) : ℕ) = 1337 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_191 : totient 191 = 191 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_191] <;> decide

theorem tot_1338 : totient 1338 = 444 := by
  have heq : (2 * (3 * (223)) : ℕ) = 1338 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_223 : totient 223 = 223 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_223] <;> decide

theorem tot_1339 : totient 1339 = 1224 := by
  have heq : (13 * (103) : ℕ) = 1339 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_103] <;> decide

theorem tot_1340 : totient 1340 = 528 := by
  have heq : (2^2 * (5 * (67)) : ℕ) = 1340 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_67] <;> decide

theorem tot_1341 : totient 1341 = 888 := by
  have heq : (3^2 * (149) : ℕ) = 1341 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_149 : totient 149 = 149 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_149] <;> decide

theorem tot_1342 : totient 1342 = 600 := by
  have heq : (2 * (11 * (61)) : ℕ) = 1342 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_61] <;> decide

theorem tot_1343 : totient 1343 = 1248 := by
  have heq : (17 * (79) : ℕ) = 1343 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_79] <;> decide

theorem tot_1344 : totient 1344 = 384 := by
  have heq : (2^6 * (3 * (7)) : ℕ) = 1344 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^6) = 2^5 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7] <;> decide

theorem tot_1345 : totient 1345 = 1072 := by
  have heq : (5 * (269) : ℕ) = 1345 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_269 : totient 269 = 269 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_269] <;> decide

theorem tot_1346 : totient 1346 = 672 := by
  have heq : (2 * (673) : ℕ) = 1346 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_673 : totient 673 = 673 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_673] <;> decide

theorem tot_1347 : totient 1347 = 896 := by
  have heq : (3 * (449) : ℕ) = 1347 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_449 : totient 449 = 449 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_449] <;> decide

theorem tot_1348 : totient 1348 = 672 := by
  have heq : (2^2 * (337) : ℕ) = 1348 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_337 : totient 337 = 337 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_337] <;> decide

theorem tot_1349 : totient 1349 = 1260 := by
  have heq : (19 * (71) : ℕ) = 1349 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_71] <;> decide

theorem tot_1350 : totient 1350 = 360 := by
  have heq : (2 * (3^3 * (5^2)) : ℕ) = 1350 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_5] <;> decide

theorem tot_1351 : totient 1351 = 1152 := by
  have heq : (7 * (193) : ℕ) = 1351 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_193 : totient 193 = 193 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_193] <;> decide

theorem tot_1352 : totient 1352 = 624 := by
  have heq : (2^3 * (13^2) : ℕ) = 1352 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient (13^2) = 13^1 * (13 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_13] <;> decide

theorem tot_1353 : totient 1353 = 800 := by
  have heq : (3 * (11 * (41)) : ℕ) = 1353 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11, hp_41] <;> decide

theorem tot_1354 : totient 1354 = 676 := by
  have heq : (2 * (677) : ℕ) = 1354 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_677 : totient 677 = 677 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_677] <;> decide

theorem tot_1355 : totient 1355 = 1080 := by
  have heq : (5 * (271) : ℕ) = 1355 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_271 : totient 271 = 271 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_271] <;> decide

theorem tot_1356 : totient 1356 = 448 := by
  have heq : (2^2 * (3 * (113)) : ℕ) = 1356 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_113 : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_113] <;> decide

theorem tot_1357 : totient 1357 = 1276 := by
  have heq : (23 * (59) : ℕ) = 1357 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_23, hp_59] <;> decide

theorem tot_1358 : totient 1358 = 576 := by
  have heq : (2 * (7 * (97)) : ℕ) = 1358 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_97] <;> decide

theorem tot_1359 : totient 1359 = 900 := by
  have heq : (3^2 * (151) : ℕ) = 1359 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_151 : totient 151 = 151 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_151] <;> decide

theorem tot_1360 : totient 1360 = 512 := by
  have heq : (2^4 * (5 * (17)) : ℕ) = 1360 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_17] <;> decide

theorem tot_1361 : totient 1361 = 1360 := by
  have h : totient 1361 = 1361 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1362 : totient 1362 = 452 := by
  have heq : (2 * (3 * (227)) : ℕ) = 1362 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_227 : totient 227 = 227 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_227] <;> decide

theorem tot_1363 : totient 1363 = 1288 := by
  have heq : (29 * (47) : ℕ) = 1363 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_29, hp_47] <;> decide

theorem tot_1364 : totient 1364 = 600 := by
  have heq : (2^2 * (11 * (31)) : ℕ) = 1364 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_31] <;> decide

theorem tot_1365 : totient 1365 = 576 := by
  have heq : (3 * (5 * (7 * (13))) : ℕ) = 1365 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_7, hp_13] <;> decide

theorem tot_1366 : totient 1366 = 682 := by
  have heq : (2 * (683) : ℕ) = 1366 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_683 : totient 683 = 683 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_683] <;> decide

theorem tot_1367 : totient 1367 = 1366 := by
  have h : totient 1367 = 1367 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1368 : totient 1368 = 432 := by
  have heq : (2^3 * (3^2 * (19)) : ℕ) = 1368 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_19] <;> decide

theorem tot_1369 : totient 1369 = 1332 := by
  have h : totient (37^2) = 37^1 * (37 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (37^2 : ℕ) = 1369 := by decide
  rw [← heq]
  rw [h] <;> decide

theorem tot_1370 : totient 1370 = 544 := by
  have heq : (2 * (5 * (137)) : ℕ) = 1370 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_137 : totient 137 = 137 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_137] <;> decide

theorem tot_1371 : totient 1371 = 912 := by
  have heq : (3 * (457) : ℕ) = 1371 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_457 : totient 457 = 457 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_457] <;> decide

theorem tot_1372 : totient 1372 = 588 := by
  have heq : (2^2 * (7^3) : ℕ) = 1372 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient (7^3) = 7^2 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_7] <;> decide

theorem tot_1373 : totient 1373 = 1372 := by
  have h : totient 1373 = 1373 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1374 : totient 1374 = 456 := by
  have heq : (2 * (3 * (229)) : ℕ) = 1374 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_229 : totient 229 = 229 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_229] <;> decide

theorem tot_1375 : totient 1375 = 1000 := by
  have heq : (5^3 * (11) : ℕ) = 1375 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^3) = 5^2 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_11] <;> decide

theorem tot_1376 : totient 1376 = 672 := by
  have heq : (2^5 * (43) : ℕ) = 1376 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_43] <;> decide

theorem tot_1377 : totient 1377 = 864 := by
  have heq : (3^4 * (17) : ℕ) = 1377 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_17] <;> decide

theorem tot_1378 : totient 1378 = 624 := by
  have heq : (2 * (13 * (53)) : ℕ) = 1378 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_53] <;> decide

theorem tot_1379 : totient 1379 = 1176 := by
  have heq : (7 * (197) : ℕ) = 1379 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_197 : totient 197 = 197 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_197] <;> decide

theorem tot_1380 : totient 1380 = 352 := by
  have heq : (2^2 * (3 * (5 * (23))) : ℕ) = 1380 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_23] <;> decide

theorem tot_1381 : totient 1381 = 1380 := by
  have h : totient 1381 = 1381 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1382 : totient 1382 = 690 := by
  have heq : (2 * (691) : ℕ) = 1382 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_691 : totient 691 = 691 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_691] <;> decide

theorem tot_1383 : totient 1383 = 920 := by
  have heq : (3 * (461) : ℕ) = 1383 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_461 : totient 461 = 461 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_461] <;> decide

theorem tot_1384 : totient 1384 = 688 := by
  have heq : (2^3 * (173) : ℕ) = 1384 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_173 : totient 173 = 173 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_173] <;> decide

theorem tot_1385 : totient 1385 = 1104 := by
  have heq : (5 * (277) : ℕ) = 1385 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_277 : totient 277 = 277 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_277] <;> decide

theorem tot_1386 : totient 1386 = 360 := by
  have heq : (2 * (3^2 * (7 * (11))) : ℕ) = 1386 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_11] <;> decide

theorem tot_1387 : totient 1387 = 1296 := by
  have heq : (19 * (73) : ℕ) = 1387 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_73] <;> decide

theorem tot_1388 : totient 1388 = 692 := by
  have heq : (2^2 * (347) : ℕ) = 1388 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_347 : totient 347 = 347 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_347] <;> decide

theorem tot_1389 : totient 1389 = 924 := by
  have heq : (3 * (463) : ℕ) = 1389 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_463 : totient 463 = 463 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_463] <;> decide

theorem tot_1390 : totient 1390 = 552 := by
  have heq : (2 * (5 * (139)) : ℕ) = 1390 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_139 : totient 139 = 139 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_139] <;> decide

theorem tot_1391 : totient 1391 = 1272 := by
  have heq : (13 * (107) : ℕ) = 1391 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_107] <;> decide

theorem tot_1392 : totient 1392 = 448 := by
  have heq : (2^4 * (3 * (29)) : ℕ) = 1392 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_29] <;> decide

theorem tot_1393 : totient 1393 = 1188 := by
  have heq : (7 * (199) : ℕ) = 1393 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_199 : totient 199 = 199 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_199] <;> decide

theorem tot_1394 : totient 1394 = 640 := by
  have heq : (2 * (17 * (41)) : ℕ) = 1394 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17, hp_41] <;> decide

theorem tot_1395 : totient 1395 = 720 := by
  have heq : (3^2 * (5 * (31)) : ℕ) = 1395 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_31] <;> decide

theorem tot_1396 : totient 1396 = 696 := by
  have heq : (2^2 * (349) : ℕ) = 1396 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_349 : totient 349 = 349 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_349] <;> decide

theorem tot_1397 : totient 1397 = 1260 := by
  have heq : (11 * (127) : ℕ) = 1397 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_127 : totient 127 = 127 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_127] <;> decide

theorem tot_1398 : totient 1398 = 464 := by
  have heq : (2 * (3 * (233)) : ℕ) = 1398 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_233 : totient 233 = 233 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_233] <;> decide

theorem tot_1399 : totient 1399 = 1398 := by
  have h : totient 1399 = 1399 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1400 : totient 1400 = 480 := by
  have heq : (2^3 * (5^2 * (7)) : ℕ) = 1400 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7] <;> decide

theorem tot_1401 : totient 1401 = 932 := by
  have heq : (3 * (467) : ℕ) = 1401 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_467 : totient 467 = 467 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_467] <;> decide

theorem tot_1402 : totient 1402 = 700 := by
  have heq : (2 * (701) : ℕ) = 1402 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_701 : totient 701 = 701 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_701] <;> decide

theorem tot_1403 : totient 1403 = 1320 := by
  have heq : (23 * (61) : ℕ) = 1403 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_23, hp_61] <;> decide

theorem tot_1404 : totient 1404 = 432 := by
  have heq : (2^2 * (3^3 * (13)) : ℕ) = 1404 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_13] <;> decide

theorem tot_1405 : totient 1405 = 1120 := by
  have heq : (5 * (281) : ℕ) = 1405 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_281 : totient 281 = 281 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_281] <;> decide

theorem tot_1406 : totient 1406 = 648 := by
  have heq : (2 * (19 * (37)) : ℕ) = 1406 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_19, hp_37] <;> decide

theorem tot_1407 : totient 1407 = 792 := by
  have heq : (3 * (7 * (67)) : ℕ) = 1407 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_67] <;> decide

theorem tot_1408 : totient 1408 = 640 := by
  have heq : (2^7 * (11) : ℕ) = 1408 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^7) = 2^6 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11] <;> decide

theorem tot_1409 : totient 1409 = 1408 := by
  have h : totient 1409 = 1409 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1410 : totient 1410 = 368 := by
  have heq : (2 * (3 * (5 * (47))) : ℕ) = 1410 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_47] <;> decide

theorem tot_1411 : totient 1411 = 1312 := by
  have heq : (17 * (83) : ℕ) = 1411 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_83] <;> decide

theorem tot_1412 : totient 1412 = 704 := by
  have heq : (2^2 * (353) : ℕ) = 1412 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_353 : totient 353 = 353 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_353] <;> decide

theorem tot_1413 : totient 1413 = 936 := by
  have heq : (3^2 * (157) : ℕ) = 1413 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_157 : totient 157 = 157 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_157] <;> decide

theorem tot_1414 : totient 1414 = 600 := by
  have heq : (2 * (7 * (101)) : ℕ) = 1414 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_101] <;> decide

theorem tot_1415 : totient 1415 = 1128 := by
  have heq : (5 * (283) : ℕ) = 1415 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_283 : totient 283 = 283 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_283] <;> decide

theorem tot_1416 : totient 1416 = 464 := by
  have heq : (2^3 * (3 * (59)) : ℕ) = 1416 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_59] <;> decide

theorem tot_1417 : totient 1417 = 1296 := by
  have heq : (13 * (109) : ℕ) = 1417 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_109] <;> decide

theorem tot_1418 : totient 1418 = 708 := by
  have heq : (2 * (709) : ℕ) = 1418 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_709 : totient 709 = 709 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_709] <;> decide

theorem tot_1419 : totient 1419 = 840 := by
  have heq : (3 * (11 * (43)) : ℕ) = 1419 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11, hp_43] <;> decide

theorem tot_1420 : totient 1420 = 560 := by
  have heq : (2^2 * (5 * (71)) : ℕ) = 1420 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_71] <;> decide

theorem tot_1421 : totient 1421 = 1176 := by
  have heq : (7^2 * (29) : ℕ) = 1421 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_29] <;> decide

theorem tot_1422 : totient 1422 = 468 := by
  have heq : (2 * (3^2 * (79)) : ℕ) = 1422 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_79] <;> decide

theorem tot_1423 : totient 1423 = 1422 := by
  have h : totient 1423 = 1423 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1424 : totient 1424 = 704 := by
  have heq : (2^4 * (89) : ℕ) = 1424 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_89] <;> decide

theorem tot_1425 : totient 1425 = 720 := by
  have heq : (3 * (5^2 * (19)) : ℕ) = 1425 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_19] <;> decide

theorem tot_1426 : totient 1426 = 660 := by
  have heq : (2 * (23 * (31)) : ℕ) = 1426 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_23, hp_31] <;> decide

theorem tot_1427 : totient 1427 = 1426 := by
  have h : totient 1427 = 1427 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1428 : totient 1428 = 384 := by
  have heq : (2^2 * (3 * (7 * (17))) : ℕ) = 1428 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_17] <;> decide

theorem tot_1429 : totient 1429 = 1428 := by
  have h : totient 1429 = 1429 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1430 : totient 1430 = 480 := by
  have heq : (2 * (5 * (11 * (13))) : ℕ) = 1430 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_11, hp_13] <;> decide

theorem tot_1431 : totient 1431 = 936 := by
  have heq : (3^3 * (53) : ℕ) = 1431 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_53] <;> decide

theorem tot_1432 : totient 1432 = 712 := by
  have heq : (2^3 * (179) : ℕ) = 1432 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_179 : totient 179 = 179 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_179] <;> decide

theorem tot_1433 : totient 1433 = 1432 := by
  have h : totient 1433 = 1433 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1434 : totient 1434 = 476 := by
  have heq : (2 * (3 * (239)) : ℕ) = 1434 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_239 : totient 239 = 239 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_239] <;> decide

theorem tot_1435 : totient 1435 = 960 := by
  have heq : (5 * (7 * (41)) : ℕ) = 1435 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_7, hp_41] <;> decide

theorem tot_1436 : totient 1436 = 716 := by
  have heq : (2^2 * (359) : ℕ) = 1436 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_359 : totient 359 = 359 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_359] <;> decide

theorem tot_1437 : totient 1437 = 956 := by
  have heq : (3 * (479) : ℕ) = 1437 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_479 : totient 479 = 479 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_479] <;> decide

theorem tot_1438 : totient 1438 = 718 := by
  have heq : (2 * (719) : ℕ) = 1438 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_719 : totient 719 = 719 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_719] <;> decide

theorem tot_1439 : totient 1439 = 1438 := by
  have h : totient 1439 = 1439 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1440 : totient 1440 = 384 := by
  have heq : (2^5 * (3^2 * (5)) : ℕ) = 1440 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5] <;> decide

theorem tot_1441 : totient 1441 = 1300 := by
  have heq : (11 * (131) : ℕ) = 1441 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_131 : totient 131 = 131 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_131] <;> decide

theorem tot_1442 : totient 1442 = 612 := by
  have heq : (2 * (7 * (103)) : ℕ) = 1442 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_103] <;> decide

theorem tot_1443 : totient 1443 = 864 := by
  have heq : (3 * (13 * (37)) : ℕ) = 1443 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_13, hp_37] <;> decide

theorem tot_1444 : totient 1444 = 684 := by
  have heq : (2^2 * (19^2) : ℕ) = 1444 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient (19^2) = 19^1 * (19 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_19] <;> decide

theorem tot_1445 : totient 1445 = 1088 := by
  have heq : (5 * (17^2) : ℕ) = 1445 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_17 : totient (17^2) = 17^1 * (17 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_5, hp_17] <;> decide

theorem tot_1446 : totient 1446 = 480 := by
  have heq : (2 * (3 * (241)) : ℕ) = 1446 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_241 : totient 241 = 241 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_241] <;> decide

theorem tot_1447 : totient 1447 = 1446 := by
  have h : totient 1447 = 1447 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1448 : totient 1448 = 720 := by
  have heq : (2^3 * (181) : ℕ) = 1448 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_181 : totient 181 = 181 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_181] <;> decide

theorem tot_1449 : totient 1449 = 792 := by
  have heq : (3^2 * (7 * (23)) : ℕ) = 1449 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_23] <;> decide

theorem tot_1450 : totient 1450 = 560 := by
  have heq : (2 * (5^2 * (29)) : ℕ) = 1450 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_29] <;> decide

theorem tot_1451 : totient 1451 = 1450 := by
  have h : totient 1451 = 1451 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1452 : totient 1452 = 440 := by
  have heq : (2^2 * (3 * (11^2)) : ℕ) = 1452 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient (11^2) = 11^1 * (11 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_11] <;> decide

theorem tot_1453 : totient 1453 = 1452 := by
  have h : totient 1453 = 1453 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1454 : totient 1454 = 726 := by
  have heq : (2 * (727) : ℕ) = 1454 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_727 : totient 727 = 727 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_727] <;> decide

theorem tot_1455 : totient 1455 = 768 := by
  have heq : (3 * (5 * (97)) : ℕ) = 1455 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_97] <;> decide

theorem tot_1456 : totient 1456 = 576 := by
  have heq : (2^4 * (7 * (13)) : ℕ) = 1456 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_13] <;> decide

theorem tot_1457 : totient 1457 = 1380 := by
  have heq : (31 * (47) : ℕ) = 1457 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_31, hp_47] <;> decide

theorem tot_1458 : totient 1458 = 486 := by
  have heq : (2 * (3^6) : ℕ) = 1458 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^6) = 3^5 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3] <;> decide

theorem tot_1459 : totient 1459 = 1458 := by
  have h : totient 1459 = 1459 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1460 : totient 1460 = 576 := by
  have heq : (2^2 * (5 * (73)) : ℕ) = 1460 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_73] <;> decide

theorem tot_1461 : totient 1461 = 972 := by
  have heq : (3 * (487) : ℕ) = 1461 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_487 : totient 487 = 487 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_487] <;> decide

theorem tot_1462 : totient 1462 = 672 := by
  have heq : (2 * (17 * (43)) : ℕ) = 1462 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17, hp_43] <;> decide

theorem tot_1463 : totient 1463 = 1080 := by
  have heq : (7 * (11 * (19)) : ℕ) = 1463 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_11, hp_19] <;> decide

theorem tot_1464 : totient 1464 = 480 := by
  have heq : (2^3 * (3 * (61)) : ℕ) = 1464 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_61] <;> decide

theorem tot_1465 : totient 1465 = 1168 := by
  have heq : (5 * (293) : ℕ) = 1465 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_293 : totient 293 = 293 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_293] <;> decide

theorem tot_1466 : totient 1466 = 732 := by
  have heq : (2 * (733) : ℕ) = 1466 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_733 : totient 733 = 733 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_733] <;> decide

theorem tot_1467 : totient 1467 = 972 := by
  have heq : (3^2 * (163) : ℕ) = 1467 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_163 : totient 163 = 163 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_163] <;> decide

theorem tot_1468 : totient 1468 = 732 := by
  have heq : (2^2 * (367) : ℕ) = 1468 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_367 : totient 367 = 367 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_367] <;> decide

theorem tot_1469 : totient 1469 = 1344 := by
  have heq : (13 * (113) : ℕ) = 1469 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_113 : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_113] <;> decide

theorem tot_1470 : totient 1470 = 336 := by
  have heq : (2 * (3 * (5 * (7^2))) : ℕ) = 1470 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_5, hp_7] <;> decide

theorem tot_1471 : totient 1471 = 1470 := by
  have h : totient 1471 = 1471 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1472 : totient 1472 = 704 := by
  have heq : (2^6 * (23) : ℕ) = 1472 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^6) = 2^5 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_23] <;> decide

theorem tot_1473 : totient 1473 = 980 := by
  have heq : (3 * (491) : ℕ) = 1473 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_491 : totient 491 = 491 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_491] <;> decide

theorem tot_1474 : totient 1474 = 660 := by
  have heq : (2 * (11 * (67)) : ℕ) = 1474 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_67] <;> decide

theorem tot_1475 : totient 1475 = 1160 := by
  have heq : (5^2 * (59) : ℕ) = 1475 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_59] <;> decide

theorem tot_1476 : totient 1476 = 480 := by
  have heq : (2^2 * (3^2 * (41)) : ℕ) = 1476 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_41] <;> decide

theorem tot_1477 : totient 1477 = 1260 := by
  have heq : (7 * (211) : ℕ) = 1477 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_211 : totient 211 = 211 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_211] <;> decide

theorem tot_1478 : totient 1478 = 738 := by
  have heq : (2 * (739) : ℕ) = 1478 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_739 : totient 739 = 739 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_739] <;> decide

theorem tot_1479 : totient 1479 = 896 := by
  have heq : (3 * (17 * (29)) : ℕ) = 1479 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_17, hp_29] <;> decide

theorem tot_1480 : totient 1480 = 576 := by
  have heq : (2^3 * (5 * (37)) : ℕ) = 1480 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_37] <;> decide

theorem tot_1481 : totient 1481 = 1480 := by
  have h : totient 1481 = 1481 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1482 : totient 1482 = 432 := by
  have heq : (2 * (3 * (13 * (19))) : ℕ) = 1482 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_13, hp_19] <;> decide

theorem tot_1483 : totient 1483 = 1482 := by
  have h : totient 1483 = 1483 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1484 : totient 1484 = 624 := by
  have heq : (2^2 * (7 * (53)) : ℕ) = 1484 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_53] <;> decide

theorem tot_1485 : totient 1485 = 720 := by
  have heq : (3^3 * (5 * (11)) : ℕ) = 1485 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_11] <;> decide

theorem tot_1486 : totient 1486 = 742 := by
  have heq : (2 * (743) : ℕ) = 1486 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_743 : totient 743 = 743 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_743] <;> decide

theorem tot_1487 : totient 1487 = 1486 := by
  have h : totient 1487 = 1487 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1488 : totient 1488 = 480 := by
  have heq : (2^4 * (3 * (31)) : ℕ) = 1488 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_31] <;> decide

theorem tot_1489 : totient 1489 = 1488 := by
  have h : totient 1489 = 1489 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1490 : totient 1490 = 592 := by
  have heq : (2 * (5 * (149)) : ℕ) = 1490 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_149 : totient 149 = 149 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_149] <;> decide

theorem tot_1491 : totient 1491 = 840 := by
  have heq : (3 * (7 * (71)) : ℕ) = 1491 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_71] <;> decide

theorem tot_1492 : totient 1492 = 744 := by
  have heq : (2^2 * (373) : ℕ) = 1492 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_373 : totient 373 = 373 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_373] <;> decide

theorem tot_1493 : totient 1493 = 1492 := by
  have h : totient 1493 = 1493 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1494 : totient 1494 = 492 := by
  have heq : (2 * (3^2 * (83)) : ℕ) = 1494 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_83] <;> decide

theorem tot_1495 : totient 1495 = 1056 := by
  have heq : (5 * (13 * (23)) : ℕ) = 1495 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_13, hp_23] <;> decide

theorem tot_1496 : totient 1496 = 640 := by
  have heq : (2^3 * (11 * (17)) : ℕ) = 1496 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_17] <;> decide

theorem tot_1497 : totient 1497 = 996 := by
  have heq : (3 * (499) : ℕ) = 1497 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_499 : totient 499 = 499 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_499] <;> decide

theorem tot_1498 : totient 1498 = 636 := by
  have heq : (2 * (7 * (107)) : ℕ) = 1498 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_107] <;> decide

theorem tot_1499 : totient 1499 = 1498 := by
  have h : totient 1499 = 1499 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1500 : totient 1500 = 400 := by
  have heq : (2^2 * (3 * (5^3)) : ℕ) = 1500 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^3) = 5^2 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_5] <;> decide

theorem tot_1501 : totient 1501 = 1404 := by
  have heq : (19 * (79) : ℕ) = 1501 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_79] <;> decide

theorem tot_1502 : totient 1502 = 750 := by
  have heq : (2 * (751) : ℕ) = 1502 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_751 : totient 751 = 751 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_751] <;> decide

theorem tot_1503 : totient 1503 = 996 := by
  have heq : (3^2 * (167) : ℕ) = 1503 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_167 : totient 167 = 167 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_167] <;> decide

theorem tot_1504 : totient 1504 = 736 := by
  have heq : (2^5 * (47) : ℕ) = 1504 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_47] <;> decide

theorem tot_1505 : totient 1505 = 1008 := by
  have heq : (5 * (7 * (43)) : ℕ) = 1505 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_7, hp_43] <;> decide

theorem tot_1506 : totient 1506 = 500 := by
  have heq : (2 * (3 * (251)) : ℕ) = 1506 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_251 : totient 251 = 251 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_251] <;> decide

theorem tot_1507 : totient 1507 = 1360 := by
  have heq : (11 * (137) : ℕ) = 1507 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_137 : totient 137 = 137 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_137] <;> decide

theorem tot_1508 : totient 1508 = 672 := by
  have heq : (2^2 * (13 * (29)) : ℕ) = 1508 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_29] <;> decide

theorem tot_1509 : totient 1509 = 1004 := by
  have heq : (3 * (503) : ℕ) = 1509 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_503 : totient 503 = 503 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_503] <;> decide

theorem tot_1510 : totient 1510 = 600 := by
  have heq : (2 * (5 * (151)) : ℕ) = 1510 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_151 : totient 151 = 151 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_151] <;> decide

theorem tot_1511 : totient 1511 = 1510 := by
  have h : totient 1511 = 1511 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1512 : totient 1512 = 432 := by
  have heq : (2^3 * (3^3 * (7)) : ℕ) = 1512 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7] <;> decide

theorem tot_1513 : totient 1513 = 1408 := by
  have heq : (17 * (89) : ℕ) = 1513 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_89] <;> decide

theorem tot_1514 : totient 1514 = 756 := by
  have heq : (2 * (757) : ℕ) = 1514 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_757 : totient 757 = 757 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_757] <;> decide

theorem tot_1515 : totient 1515 = 800 := by
  have heq : (3 * (5 * (101)) : ℕ) = 1515 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_101] <;> decide

theorem tot_1516 : totient 1516 = 756 := by
  have heq : (2^2 * (379) : ℕ) = 1516 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_379 : totient 379 = 379 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_379] <;> decide

theorem tot_1517 : totient 1517 = 1440 := by
  have heq : (37 * (41) : ℕ) = 1517 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_37, hp_41] <;> decide

theorem tot_1518 : totient 1518 = 440 := by
  have heq : (2 * (3 * (11 * (23))) : ℕ) = 1518 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11, hp_23] <;> decide

theorem tot_1519 : totient 1519 = 1260 := by
  have heq : (7^2 * (31) : ℕ) = 1519 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_31] <;> decide

theorem tot_1520 : totient 1520 = 576 := by
  have heq : (2^4 * (5 * (19)) : ℕ) = 1520 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_19] <;> decide

theorem tot_1521 : totient 1521 = 936 := by
  have heq : (3^2 * (13^2) : ℕ) = 1521 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient (13^2) = 13^1 * (13 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_13] <;> decide

theorem tot_1522 : totient 1522 = 760 := by
  have heq : (2 * (761) : ℕ) = 1522 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_761 : totient 761 = 761 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_761] <;> decide

theorem tot_1523 : totient 1523 = 1522 := by
  have h : totient 1523 = 1523 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1524 : totient 1524 = 504 := by
  have heq : (2^2 * (3 * (127)) : ℕ) = 1524 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_127 : totient 127 = 127 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_127] <;> decide

theorem tot_1525 : totient 1525 = 1200 := by
  have heq : (5^2 * (61) : ℕ) = 1525 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_61] <;> decide

theorem tot_1526 : totient 1526 = 648 := by
  have heq : (2 * (7 * (109)) : ℕ) = 1526 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_109] <;> decide

theorem tot_1527 : totient 1527 = 1016 := by
  have heq : (3 * (509) : ℕ) = 1527 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_509 : totient 509 = 509 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_509] <;> decide

theorem tot_1528 : totient 1528 = 760 := by
  have heq : (2^3 * (191) : ℕ) = 1528 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_191 : totient 191 = 191 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_191] <;> decide

theorem tot_1529 : totient 1529 = 1380 := by
  have heq : (11 * (139) : ℕ) = 1529 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_139 : totient 139 = 139 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_139] <;> decide

theorem tot_1530 : totient 1530 = 384 := by
  have heq : (2 * (3^2 * (5 * (17))) : ℕ) = 1530 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_17] <;> decide

theorem tot_1531 : totient 1531 = 1530 := by
  have h : totient 1531 = 1531 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1532 : totient 1532 = 764 := by
  have heq : (2^2 * (383) : ℕ) = 1532 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_383 : totient 383 = 383 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_383] <;> decide

theorem tot_1533 : totient 1533 = 864 := by
  have heq : (3 * (7 * (73)) : ℕ) = 1533 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_73] <;> decide

theorem tot_1534 : totient 1534 = 696 := by
  have heq : (2 * (13 * (59)) : ℕ) = 1534 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_59] <;> decide

theorem tot_1535 : totient 1535 = 1224 := by
  have heq : (5 * (307) : ℕ) = 1535 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_307 : totient 307 = 307 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_307] <;> decide

theorem tot_1536 : totient 1536 = 512 := by
  have heq : (2^9 * (3) : ℕ) = 1536 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^9) = 2^8 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3] <;> decide

theorem tot_1537 : totient 1537 = 1456 := by
  have heq : (29 * (53) : ℕ) = 1537 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_29, hp_53] <;> decide

theorem tot_1538 : totient 1538 = 768 := by
  have heq : (2 * (769) : ℕ) = 1538 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_769 : totient 769 = 769 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_769] <;> decide

theorem tot_1539 : totient 1539 = 972 := by
  have heq : (3^4 * (19) : ℕ) = 1539 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_19] <;> decide

theorem tot_1540 : totient 1540 = 480 := by
  have heq : (2^2 * (5 * (7 * (11))) : ℕ) = 1540 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7, hp_11] <;> decide

theorem tot_1541 : totient 1541 = 1452 := by
  have heq : (23 * (67) : ℕ) = 1541 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_23, hp_67] <;> decide

theorem tot_1542 : totient 1542 = 512 := by
  have heq : (2 * (3 * (257)) : ℕ) = 1542 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_257 : totient 257 = 257 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_257] <;> decide

theorem tot_1543 : totient 1543 = 1542 := by
  have h : totient 1543 = 1543 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1544 : totient 1544 = 768 := by
  have heq : (2^3 * (193) : ℕ) = 1544 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_193 : totient 193 = 193 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_193] <;> decide

theorem tot_1545 : totient 1545 = 816 := by
  have heq : (3 * (5 * (103)) : ℕ) = 1545 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_103] <;> decide

theorem tot_1546 : totient 1546 = 772 := by
  have heq : (2 * (773) : ℕ) = 1546 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_773 : totient 773 = 773 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_773] <;> decide

theorem tot_1547 : totient 1547 = 1152 := by
  have heq : (7 * (13 * (17)) : ℕ) = 1547 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_13, hp_17] <;> decide

theorem tot_1548 : totient 1548 = 504 := by
  have heq : (2^2 * (3^2 * (43)) : ℕ) = 1548 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_43] <;> decide

theorem tot_1549 : totient 1549 = 1548 := by
  have h : totient 1549 = 1549 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1550 : totient 1550 = 600 := by
  have heq : (2 * (5^2 * (31)) : ℕ) = 1550 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_31] <;> decide

theorem tot_1551 : totient 1551 = 920 := by
  have heq : (3 * (11 * (47)) : ℕ) = 1551 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11, hp_47] <;> decide

theorem tot_1552 : totient 1552 = 768 := by
  have heq : (2^4 * (97) : ℕ) = 1552 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_97] <;> decide

theorem tot_1553 : totient 1553 = 1552 := by
  have h : totient 1553 = 1553 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1554 : totient 1554 = 432 := by
  have heq : (2 * (3 * (7 * (37))) : ℕ) = 1554 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_37] <;> decide

theorem tot_1555 : totient 1555 = 1240 := by
  have heq : (5 * (311) : ℕ) = 1555 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_311 : totient 311 = 311 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_311] <;> decide

theorem tot_1556 : totient 1556 = 776 := by
  have heq : (2^2 * (389) : ℕ) = 1556 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_389 : totient 389 = 389 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_389] <;> decide

theorem tot_1557 : totient 1557 = 1032 := by
  have heq : (3^2 * (173) : ℕ) = 1557 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_173 : totient 173 = 173 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_173] <;> decide

theorem tot_1558 : totient 1558 = 720 := by
  have heq : (2 * (19 * (41)) : ℕ) = 1558 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_19, hp_41] <;> decide

theorem tot_1559 : totient 1559 = 1558 := by
  have h : totient 1559 = 1559 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1560 : totient 1560 = 384 := by
  have heq : (2^3 * (3 * (5 * (13))) : ℕ) = 1560 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_13] <;> decide

theorem tot_1561 : totient 1561 = 1332 := by
  have heq : (7 * (223) : ℕ) = 1561 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_223 : totient 223 = 223 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_223] <;> decide

theorem tot_1562 : totient 1562 = 700 := by
  have heq : (2 * (11 * (71)) : ℕ) = 1562 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_71] <;> decide

theorem tot_1563 : totient 1563 = 1040 := by
  have heq : (3 * (521) : ℕ) = 1563 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_521 : totient 521 = 521 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_521] <;> decide

theorem tot_1564 : totient 1564 = 704 := by
  have heq : (2^2 * (17 * (23)) : ℕ) = 1564 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17, hp_23] <;> decide

theorem tot_1565 : totient 1565 = 1248 := by
  have heq : (5 * (313) : ℕ) = 1565 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_313 : totient 313 = 313 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_313] <;> decide

theorem tot_1566 : totient 1566 = 504 := by
  have heq : (2 * (3^3 * (29)) : ℕ) = 1566 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_29] <;> decide

theorem tot_1567 : totient 1567 = 1566 := by
  have h : totient 1567 = 1567 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1568 : totient 1568 = 672 := by
  have heq : (2^5 * (7^2) : ℕ) = 1568 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_7] <;> decide

theorem tot_1569 : totient 1569 = 1044 := by
  have heq : (3 * (523) : ℕ) = 1569 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_523 : totient 523 = 523 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_523] <;> decide

theorem tot_1570 : totient 1570 = 624 := by
  have heq : (2 * (5 * (157)) : ℕ) = 1570 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_157 : totient 157 = 157 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_157] <;> decide

theorem tot_1571 : totient 1571 = 1570 := by
  have h : totient 1571 = 1571 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1572 : totient 1572 = 520 := by
  have heq : (2^2 * (3 * (131)) : ℕ) = 1572 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_131 : totient 131 = 131 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_131] <;> decide

theorem tot_1573 : totient 1573 = 1320 := by
  have heq : (11^2 * (13) : ℕ) = 1573 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient (11^2) = 11^1 * (11 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_13] <;> decide

theorem tot_1574 : totient 1574 = 786 := by
  have heq : (2 * (787) : ℕ) = 1574 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_787 : totient 787 = 787 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_787] <;> decide

theorem tot_1575 : totient 1575 = 720 := by
  have heq : (3^2 * (5^2 * (7)) : ℕ) = 1575 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_7] <;> decide

theorem tot_1576 : totient 1576 = 784 := by
  have heq : (2^3 * (197) : ℕ) = 1576 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_197 : totient 197 = 197 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_197] <;> decide

theorem tot_1577 : totient 1577 = 1476 := by
  have heq : (19 * (83) : ℕ) = 1577 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_83] <;> decide

theorem tot_1578 : totient 1578 = 524 := by
  have heq : (2 * (3 * (263)) : ℕ) = 1578 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_263 : totient 263 = 263 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_263] <;> decide

theorem tot_1579 : totient 1579 = 1578 := by
  have h : totient 1579 = 1579 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1580 : totient 1580 = 624 := by
  have heq : (2^2 * (5 * (79)) : ℕ) = 1580 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_79] <;> decide

theorem tot_1581 : totient 1581 = 960 := by
  have heq : (3 * (17 * (31)) : ℕ) = 1581 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_17, hp_31] <;> decide

theorem tot_1582 : totient 1582 = 672 := by
  have heq : (2 * (7 * (113)) : ℕ) = 1582 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_113 : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_113] <;> decide

theorem tot_1583 : totient 1583 = 1582 := by
  have h : totient 1583 = 1583 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1584 : totient 1584 = 480 := by
  have heq : (2^4 * (3^2 * (11)) : ℕ) = 1584 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11] <;> decide

theorem tot_1585 : totient 1585 = 1264 := by
  have heq : (5 * (317) : ℕ) = 1585 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_317 : totient 317 = 317 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_317] <;> decide

theorem tot_1586 : totient 1586 = 720 := by
  have heq : (2 * (13 * (61)) : ℕ) = 1586 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_61] <;> decide

theorem tot_1587 : totient 1587 = 1012 := by
  have heq : (3 * (23^2) : ℕ) = 1587 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_23 : totient (23^2) = 23^1 * (23 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_23] <;> decide

theorem tot_1588 : totient 1588 = 792 := by
  have heq : (2^2 * (397) : ℕ) = 1588 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_397 : totient 397 = 397 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_397] <;> decide

theorem tot_1589 : totient 1589 = 1356 := by
  have heq : (7 * (227) : ℕ) = 1589 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_227 : totient 227 = 227 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_227] <;> decide

theorem tot_1590 : totient 1590 = 416 := by
  have heq : (2 * (3 * (5 * (53))) : ℕ) = 1590 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_53] <;> decide

theorem tot_1591 : totient 1591 = 1512 := by
  have heq : (37 * (43) : ℕ) = 1591 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_37, hp_43] <;> decide

theorem tot_1592 : totient 1592 = 792 := by
  have heq : (2^3 * (199) : ℕ) = 1592 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_199 : totient 199 = 199 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_199] <;> decide

theorem tot_1593 : totient 1593 = 1044 := by
  have heq : (3^3 * (59) : ℕ) = 1593 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_59] <;> decide

theorem tot_1594 : totient 1594 = 796 := by
  have heq : (2 * (797) : ℕ) = 1594 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_797 : totient 797 = 797 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_797] <;> decide

theorem tot_1595 : totient 1595 = 1120 := by
  have heq : (5 * (11 * (29)) : ℕ) = 1595 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_11, hp_29] <;> decide

theorem tot_1596 : totient 1596 = 432 := by
  have heq : (2^2 * (3 * (7 * (19))) : ℕ) = 1596 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_19] <;> decide

theorem tot_1597 : totient 1597 = 1596 := by
  have h : totient 1597 = 1597 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1598 : totient 1598 = 736 := by
  have heq : (2 * (17 * (47)) : ℕ) = 1598 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17, hp_47] <;> decide

theorem tot_1599 : totient 1599 = 960 := by
  have heq : (3 * (13 * (41)) : ℕ) = 1599 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_13, hp_41] <;> decide

theorem tot_1600 : totient 1600 = 640 := by
  have heq : (2^6 * (5^2) : ℕ) = 1600 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^6) = 2^5 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_5] <;> decide

theorem tot_1601 : totient 1601 = 1600 := by
  have h : totient 1601 = 1601 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1602 : totient 1602 = 528 := by
  have heq : (2 * (3^2 * (89)) : ℕ) = 1602 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_89] <;> decide

theorem tot_1603 : totient 1603 = 1368 := by
  have heq : (7 * (229) : ℕ) = 1603 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_229 : totient 229 = 229 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_229] <;> decide

theorem tot_1604 : totient 1604 = 800 := by
  have heq : (2^2 * (401) : ℕ) = 1604 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_401 : totient 401 = 401 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_401] <;> decide

theorem tot_1605 : totient 1605 = 848 := by
  have heq : (3 * (5 * (107)) : ℕ) = 1605 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_107] <;> decide

theorem tot_1606 : totient 1606 = 720 := by
  have heq : (2 * (11 * (73)) : ℕ) = 1606 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_73] <;> decide

theorem tot_1607 : totient 1607 = 1606 := by
  have h : totient 1607 = 1607 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1608 : totient 1608 = 528 := by
  have heq : (2^3 * (3 * (67)) : ℕ) = 1608 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_67] <;> decide

theorem tot_1609 : totient 1609 = 1608 := by
  have h : totient 1609 = 1609 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1610 : totient 1610 = 528 := by
  have heq : (2 * (5 * (7 * (23))) : ℕ) = 1610 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7, hp_23] <;> decide

theorem tot_1611 : totient 1611 = 1068 := by
  have heq : (3^2 * (179) : ℕ) = 1611 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_179 : totient 179 = 179 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_179] <;> decide

theorem tot_1612 : totient 1612 = 720 := by
  have heq : (2^2 * (13 * (31)) : ℕ) = 1612 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_31] <;> decide

theorem tot_1613 : totient 1613 = 1612 := by
  have h : totient 1613 = 1613 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1614 : totient 1614 = 536 := by
  have heq : (2 * (3 * (269)) : ℕ) = 1614 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_269 : totient 269 = 269 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_269] <;> decide

theorem tot_1615 : totient 1615 = 1152 := by
  have heq : (5 * (17 * (19)) : ℕ) = 1615 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_17, hp_19] <;> decide

theorem tot_1616 : totient 1616 = 800 := by
  have heq : (2^4 * (101) : ℕ) = 1616 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_101] <;> decide

theorem tot_1617 : totient 1617 = 840 := by
  have heq : (3 * (7^2 * (11)) : ℕ) = 1617 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_11] <;> decide

theorem tot_1618 : totient 1618 = 808 := by
  have heq : (2 * (809) : ℕ) = 1618 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_809 : totient 809 = 809 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_809] <;> decide

theorem tot_1619 : totient 1619 = 1618 := by
  have h : totient 1619 = 1619 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1620 : totient 1620 = 432 := by
  have heq : (2^2 * (3^4 * (5)) : ℕ) = 1620 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5] <;> decide

theorem tot_1621 : totient 1621 = 1620 := by
  have h : totient 1621 = 1621 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1622 : totient 1622 = 810 := by
  have heq : (2 * (811) : ℕ) = 1622 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_811 : totient 811 = 811 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_811] <;> decide

theorem tot_1623 : totient 1623 = 1080 := by
  have heq : (3 * (541) : ℕ) = 1623 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_541 : totient 541 = 541 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_541] <;> decide

theorem tot_1624 : totient 1624 = 672 := by
  have heq : (2^3 * (7 * (29)) : ℕ) = 1624 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_29] <;> decide

theorem tot_1625 : totient 1625 = 1200 := by
  have heq : (5^3 * (13) : ℕ) = 1625 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^3) = 5^2 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_13] <;> decide

theorem tot_1626 : totient 1626 = 540 := by
  have heq : (2 * (3 * (271)) : ℕ) = 1626 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_271 : totient 271 = 271 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_271] <;> decide

theorem tot_1627 : totient 1627 = 1626 := by
  have h : totient 1627 = 1627 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1628 : totient 1628 = 720 := by
  have heq : (2^2 * (11 * (37)) : ℕ) = 1628 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_37] <;> decide

theorem tot_1629 : totient 1629 = 1080 := by
  have heq : (3^2 * (181) : ℕ) = 1629 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_181 : totient 181 = 181 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_181] <;> decide

theorem tot_1630 : totient 1630 = 648 := by
  have heq : (2 * (5 * (163)) : ℕ) = 1630 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_163 : totient 163 = 163 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_163] <;> decide

theorem tot_1631 : totient 1631 = 1392 := by
  have heq : (7 * (233) : ℕ) = 1631 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_233 : totient 233 = 233 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_233] <;> decide

theorem tot_1632 : totient 1632 = 512 := by
  have heq : (2^5 * (3 * (17)) : ℕ) = 1632 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_17] <;> decide

theorem tot_1633 : totient 1633 = 1540 := by
  have heq : (23 * (71) : ℕ) = 1633 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_23, hp_71] <;> decide

theorem tot_1634 : totient 1634 = 756 := by
  have heq : (2 * (19 * (43)) : ℕ) = 1634 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_19, hp_43] <;> decide

theorem tot_1635 : totient 1635 = 864 := by
  have heq : (3 * (5 * (109)) : ℕ) = 1635 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_109] <;> decide

theorem tot_1636 : totient 1636 = 816 := by
  have heq : (2^2 * (409) : ℕ) = 1636 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_409 : totient 409 = 409 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_409] <;> decide

theorem tot_1637 : totient 1637 = 1636 := by
  have h : totient 1637 = 1637 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1638 : totient 1638 = 432 := by
  have heq : (2 * (3^2 * (7 * (13))) : ℕ) = 1638 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_13] <;> decide

theorem tot_1639 : totient 1639 = 1480 := by
  have heq : (11 * (149) : ℕ) = 1639 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_149 : totient 149 = 149 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_149] <;> decide

theorem tot_1640 : totient 1640 = 640 := by
  have heq : (2^3 * (5 * (41)) : ℕ) = 1640 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_41] <;> decide

theorem tot_1641 : totient 1641 = 1092 := by
  have heq : (3 * (547) : ℕ) = 1641 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_547 : totient 547 = 547 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_547] <;> decide

theorem tot_1642 : totient 1642 = 820 := by
  have heq : (2 * (821) : ℕ) = 1642 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_821 : totient 821 = 821 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_821] <;> decide

theorem tot_1643 : totient 1643 = 1560 := by
  have heq : (31 * (53) : ℕ) = 1643 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_31, hp_53] <;> decide

theorem tot_1644 : totient 1644 = 544 := by
  have heq : (2^2 * (3 * (137)) : ℕ) = 1644 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_137 : totient 137 = 137 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_137] <;> decide

theorem tot_1645 : totient 1645 = 1104 := by
  have heq : (5 * (7 * (47)) : ℕ) = 1645 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_7, hp_47] <;> decide

theorem tot_1646 : totient 1646 = 822 := by
  have heq : (2 * (823) : ℕ) = 1646 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_823 : totient 823 = 823 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_823] <;> decide

theorem tot_1647 : totient 1647 = 1080 := by
  have heq : (3^3 * (61) : ℕ) = 1647 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_61] <;> decide

theorem tot_1648 : totient 1648 = 816 := by
  have heq : (2^4 * (103) : ℕ) = 1648 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_103] <;> decide

theorem tot_1649 : totient 1649 = 1536 := by
  have heq : (17 * (97) : ℕ) = 1649 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_97] <;> decide

theorem tot_1650 : totient 1650 = 400 := by
  have heq : (2 * (3 * (5^2 * (11))) : ℕ) = 1650 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_11] <;> decide

theorem tot_1651 : totient 1651 = 1512 := by
  have heq : (13 * (127) : ℕ) = 1651 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_127 : totient 127 = 127 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_127] <;> decide

theorem tot_1652 : totient 1652 = 696 := by
  have heq : (2^2 * (7 * (59)) : ℕ) = 1652 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_59] <;> decide

theorem tot_1653 : totient 1653 = 1008 := by
  have heq : (3 * (19 * (29)) : ℕ) = 1653 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_19, hp_29] <;> decide

theorem tot_1654 : totient 1654 = 826 := by
  have heq : (2 * (827) : ℕ) = 1654 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_827 : totient 827 = 827 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_827] <;> decide

theorem tot_1655 : totient 1655 = 1320 := by
  have heq : (5 * (331) : ℕ) = 1655 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_331 : totient 331 = 331 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_331] <;> decide

theorem tot_1656 : totient 1656 = 528 := by
  have heq : (2^3 * (3^2 * (23)) : ℕ) = 1656 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_23] <;> decide

theorem tot_1657 : totient 1657 = 1656 := by
  have h : totient 1657 = 1657 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1658 : totient 1658 = 828 := by
  have heq : (2 * (829) : ℕ) = 1658 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_829 : totient 829 = 829 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_829] <;> decide

theorem tot_1659 : totient 1659 = 936 := by
  have heq : (3 * (7 * (79)) : ℕ) = 1659 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_79] <;> decide

theorem tot_1660 : totient 1660 = 656 := by
  have heq : (2^2 * (5 * (83)) : ℕ) = 1660 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_83] <;> decide

theorem tot_1661 : totient 1661 = 1500 := by
  have heq : (11 * (151) : ℕ) = 1661 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_151 : totient 151 = 151 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_151] <;> decide

theorem tot_1662 : totient 1662 = 552 := by
  have heq : (2 * (3 * (277)) : ℕ) = 1662 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_277 : totient 277 = 277 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_277] <;> decide

theorem tot_1663 : totient 1663 = 1662 := by
  have h : totient 1663 = 1663 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1664 : totient 1664 = 768 := by
  have heq : (2^7 * (13) : ℕ) = 1664 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^7) = 2^6 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13] <;> decide

theorem tot_1665 : totient 1665 = 864 := by
  have heq : (3^2 * (5 * (37)) : ℕ) = 1665 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_37] <;> decide

theorem tot_1666 : totient 1666 = 672 := by
  have heq : (2 * (7^2 * (17)) : ℕ) = 1666 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_17] <;> decide

theorem tot_1667 : totient 1667 = 1666 := by
  have h : totient 1667 = 1667 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1668 : totient 1668 = 552 := by
  have heq : (2^2 * (3 * (139)) : ℕ) = 1668 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_139 : totient 139 = 139 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_139] <;> decide

theorem tot_1669 : totient 1669 = 1668 := by
  have h : totient 1669 = 1669 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1670 : totient 1670 = 664 := by
  have heq : (2 * (5 * (167)) : ℕ) = 1670 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_167 : totient 167 = 167 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_167] <;> decide

theorem tot_1671 : totient 1671 = 1112 := by
  have heq : (3 * (557) : ℕ) = 1671 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_557 : totient 557 = 557 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_557] <;> decide

theorem tot_1672 : totient 1672 = 720 := by
  have heq : (2^3 * (11 * (19)) : ℕ) = 1672 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_19] <;> decide

theorem tot_1673 : totient 1673 = 1428 := by
  have heq : (7 * (239) : ℕ) = 1673 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_239 : totient 239 = 239 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_239] <;> decide

theorem tot_1674 : totient 1674 = 540 := by
  have heq : (2 * (3^3 * (31)) : ℕ) = 1674 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_31] <;> decide

theorem tot_1675 : totient 1675 = 1320 := by
  have heq : (5^2 * (67) : ℕ) = 1675 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_67] <;> decide

theorem tot_1676 : totient 1676 = 836 := by
  have heq : (2^2 * (419) : ℕ) = 1676 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_419 : totient 419 = 419 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_419] <;> decide

theorem tot_1677 : totient 1677 = 1008 := by
  have heq : (3 * (13 * (43)) : ℕ) = 1677 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_13, hp_43] <;> decide

theorem tot_1678 : totient 1678 = 838 := by
  have heq : (2 * (839) : ℕ) = 1678 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_839 : totient 839 = 839 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_839] <;> decide

theorem tot_1679 : totient 1679 = 1584 := by
  have heq : (23 * (73) : ℕ) = 1679 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_23, hp_73] <;> decide

theorem tot_1680 : totient 1680 = 384 := by
  have heq : (2^4 * (3 * (5 * (7))) : ℕ) = 1680 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_7] <;> decide

theorem tot_1681 : totient 1681 = 1640 := by
  have h : totient (41^2) = 41^1 * (41 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (41^2 : ℕ) = 1681 := by decide
  rw [← heq]
  rw [h] <;> decide

theorem tot_1682 : totient 1682 = 812 := by
  have heq : (2 * (29^2) : ℕ) = 1682 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_29 : totient (29^2) = 29^1 * (29 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_29] <;> decide

theorem tot_1683 : totient 1683 = 960 := by
  have heq : (3^2 * (11 * (17)) : ℕ) = 1683 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11, hp_17] <;> decide

theorem tot_1684 : totient 1684 = 840 := by
  have heq : (2^2 * (421) : ℕ) = 1684 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_421 : totient 421 = 421 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_421] <;> decide

theorem tot_1685 : totient 1685 = 1344 := by
  have heq : (5 * (337) : ℕ) = 1685 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_337 : totient 337 = 337 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_337] <;> decide

theorem tot_1686 : totient 1686 = 560 := by
  have heq : (2 * (3 * (281)) : ℕ) = 1686 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_281 : totient 281 = 281 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_281] <;> decide

theorem tot_1687 : totient 1687 = 1440 := by
  have heq : (7 * (241) : ℕ) = 1687 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_241 : totient 241 = 241 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_241] <;> decide

theorem tot_1688 : totient 1688 = 840 := by
  have heq : (2^3 * (211) : ℕ) = 1688 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_211 : totient 211 = 211 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_211] <;> decide

theorem tot_1689 : totient 1689 = 1124 := by
  have heq : (3 * (563) : ℕ) = 1689 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_563 : totient 563 = 563 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_563] <;> decide

theorem tot_1690 : totient 1690 = 624 := by
  have heq : (2 * (5 * (13^2)) : ℕ) = 1690 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient (13^2) = 13^1 * (13 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_5, hp_13] <;> decide

theorem tot_1691 : totient 1691 = 1584 := by
  have heq : (19 * (89) : ℕ) = 1691 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_89] <;> decide

theorem tot_1692 : totient 1692 = 552 := by
  have heq : (2^2 * (3^2 * (47)) : ℕ) = 1692 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_47] <;> decide

theorem tot_1693 : totient 1693 = 1692 := by
  have h : totient 1693 = 1693 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1694 : totient 1694 = 660 := by
  have heq : (2 * (7 * (11^2)) : ℕ) = 1694 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient (11^2) = 11^1 * (11 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_7, hp_11] <;> decide

theorem tot_1695 : totient 1695 = 896 := by
  have heq : (3 * (5 * (113)) : ℕ) = 1695 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_113 : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_113] <;> decide

theorem tot_1696 : totient 1696 = 832 := by
  have heq : (2^5 * (53) : ℕ) = 1696 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_53] <;> decide

theorem tot_1697 : totient 1697 = 1696 := by
  have h : totient 1697 = 1697 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1698 : totient 1698 = 564 := by
  have heq : (2 * (3 * (283)) : ℕ) = 1698 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_283 : totient 283 = 283 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_283] <;> decide

theorem tot_1699 : totient 1699 = 1698 := by
  have h : totient 1699 = 1699 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1700 : totient 1700 = 640 := by
  have heq : (2^2 * (5^2 * (17)) : ℕ) = 1700 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_17] <;> decide

theorem tot_1701 : totient 1701 = 972 := by
  have heq : (3^5 * (7) : ℕ) = 1701 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^5) = 3^4 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7] <;> decide

theorem tot_1702 : totient 1702 = 792 := by
  have heq : (2 * (23 * (37)) : ℕ) = 1702 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_23, hp_37] <;> decide

theorem tot_1703 : totient 1703 = 1560 := by
  have heq : (13 * (131) : ℕ) = 1703 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_131 : totient 131 = 131 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_131] <;> decide

theorem tot_1704 : totient 1704 = 560 := by
  have heq : (2^3 * (3 * (71)) : ℕ) = 1704 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_71] <;> decide

theorem tot_1705 : totient 1705 = 1200 := by
  have heq : (5 * (11 * (31)) : ℕ) = 1705 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_11, hp_31] <;> decide

theorem tot_1706 : totient 1706 = 852 := by
  have heq : (2 * (853) : ℕ) = 1706 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_853 : totient 853 = 853 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_853] <;> decide

theorem tot_1707 : totient 1707 = 1136 := by
  have heq : (3 * (569) : ℕ) = 1707 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_569 : totient 569 = 569 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_569] <;> decide

theorem tot_1708 : totient 1708 = 720 := by
  have heq : (2^2 * (7 * (61)) : ℕ) = 1708 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_61] <;> decide

theorem tot_1709 : totient 1709 = 1708 := by
  have h : totient 1709 = 1709 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1710 : totient 1710 = 432 := by
  have heq : (2 * (3^2 * (5 * (19))) : ℕ) = 1710 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_19] <;> decide

theorem tot_1711 : totient 1711 = 1624 := by
  have heq : (29 * (59) : ℕ) = 1711 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_29, hp_59] <;> decide

theorem tot_1712 : totient 1712 = 848 := by
  have heq : (2^4 * (107) : ℕ) = 1712 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_107] <;> decide

theorem tot_1713 : totient 1713 = 1140 := by
  have heq : (3 * (571) : ℕ) = 1713 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_571 : totient 571 = 571 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_571] <;> decide

theorem tot_1714 : totient 1714 = 856 := by
  have heq : (2 * (857) : ℕ) = 1714 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_857 : totient 857 = 857 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_857] <;> decide

theorem tot_1715 : totient 1715 = 1176 := by
  have heq : (5 * (7^3) : ℕ) = 1715 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^3) = 7^2 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_5, hp_7] <;> decide

theorem tot_1716 : totient 1716 = 480 := by
  have heq : (2^2 * (3 * (11 * (13))) : ℕ) = 1716 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11, hp_13] <;> decide

theorem tot_1717 : totient 1717 = 1600 := by
  have heq : (17 * (101) : ℕ) = 1717 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_101] <;> decide

theorem tot_1718 : totient 1718 = 858 := by
  have heq : (2 * (859) : ℕ) = 1718 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_859 : totient 859 = 859 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_859] <;> decide

theorem tot_1719 : totient 1719 = 1140 := by
  have heq : (3^2 * (191) : ℕ) = 1719 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_191 : totient 191 = 191 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_191] <;> decide

theorem tot_1720 : totient 1720 = 672 := by
  have heq : (2^3 * (5 * (43)) : ℕ) = 1720 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_43] <;> decide

theorem tot_1721 : totient 1721 = 1720 := by
  have h : totient 1721 = 1721 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1722 : totient 1722 = 480 := by
  have heq : (2 * (3 * (7 * (41))) : ℕ) = 1722 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_41] <;> decide

theorem tot_1723 : totient 1723 = 1722 := by
  have h : totient 1723 = 1723 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1724 : totient 1724 = 860 := by
  have heq : (2^2 * (431) : ℕ) = 1724 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_431 : totient 431 = 431 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_431] <;> decide

theorem tot_1725 : totient 1725 = 880 := by
  have heq : (3 * (5^2 * (23)) : ℕ) = 1725 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_23] <;> decide

theorem tot_1726 : totient 1726 = 862 := by
  have heq : (2 * (863) : ℕ) = 1726 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_863 : totient 863 = 863 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_863] <;> decide

theorem tot_1727 : totient 1727 = 1560 := by
  have heq : (11 * (157) : ℕ) = 1727 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_157 : totient 157 = 157 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_157] <;> decide

theorem tot_1728 : totient 1728 = 576 := by
  have heq : (2^6 * (3^3) : ℕ) = 1728 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^6) = 2^5 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3] <;> decide

theorem tot_1729 : totient 1729 = 1296 := by
  have heq : (7 * (13 * (19)) : ℕ) = 1729 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_13, hp_19] <;> decide

theorem tot_1730 : totient 1730 = 688 := by
  have heq : (2 * (5 * (173)) : ℕ) = 1730 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_173 : totient 173 = 173 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_173] <;> decide

theorem tot_1731 : totient 1731 = 1152 := by
  have heq : (3 * (577) : ℕ) = 1731 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_577 : totient 577 = 577 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_577] <;> decide

theorem tot_1732 : totient 1732 = 864 := by
  have heq : (2^2 * (433) : ℕ) = 1732 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_433 : totient 433 = 433 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_433] <;> decide

theorem tot_1733 : totient 1733 = 1732 := by
  have h : totient 1733 = 1733 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1734 : totient 1734 = 544 := by
  have heq : (2 * (3 * (17^2)) : ℕ) = 1734 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_17 : totient (17^2) = 17^1 * (17 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_17] <;> decide

theorem tot_1735 : totient 1735 = 1384 := by
  have heq : (5 * (347) : ℕ) = 1735 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_347 : totient 347 = 347 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_347] <;> decide

theorem tot_1736 : totient 1736 = 720 := by
  have heq : (2^3 * (7 * (31)) : ℕ) = 1736 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_31] <;> decide

theorem tot_1737 : totient 1737 = 1152 := by
  have heq : (3^2 * (193) : ℕ) = 1737 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_193 : totient 193 = 193 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_193] <;> decide

theorem tot_1738 : totient 1738 = 780 := by
  have heq : (2 * (11 * (79)) : ℕ) = 1738 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_79] <;> decide

theorem tot_1739 : totient 1739 = 1656 := by
  have heq : (37 * (47) : ℕ) = 1739 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_37, hp_47] <;> decide

theorem tot_1740 : totient 1740 = 448 := by
  have heq : (2^2 * (3 * (5 * (29))) : ℕ) = 1740 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_29] <;> decide

theorem tot_1741 : totient 1741 = 1740 := by
  have h : totient 1741 = 1741 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1742 : totient 1742 = 792 := by
  have heq : (2 * (13 * (67)) : ℕ) = 1742 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_67] <;> decide

theorem tot_1743 : totient 1743 = 984 := by
  have heq : (3 * (7 * (83)) : ℕ) = 1743 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_83] <;> decide

theorem tot_1744 : totient 1744 = 864 := by
  have heq : (2^4 * (109) : ℕ) = 1744 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_109] <;> decide

theorem tot_1745 : totient 1745 = 1392 := by
  have heq : (5 * (349) : ℕ) = 1745 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_349 : totient 349 = 349 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_349] <;> decide

theorem tot_1746 : totient 1746 = 576 := by
  have heq : (2 * (3^2 * (97)) : ℕ) = 1746 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_97] <;> decide

theorem tot_1747 : totient 1747 = 1746 := by
  have h : totient 1747 = 1747 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1748 : totient 1748 = 792 := by
  have heq : (2^2 * (19 * (23)) : ℕ) = 1748 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_19, hp_23] <;> decide

theorem tot_1749 : totient 1749 = 1040 := by
  have heq : (3 * (11 * (53)) : ℕ) = 1749 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11, hp_53] <;> decide

theorem tot_1750 : totient 1750 = 600 := by
  have heq : (2 * (5^3 * (7)) : ℕ) = 1750 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^3) = 5^2 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7] <;> decide

theorem tot_1751 : totient 1751 = 1632 := by
  have heq : (17 * (103) : ℕ) = 1751 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_103] <;> decide

theorem tot_1752 : totient 1752 = 576 := by
  have heq : (2^3 * (3 * (73)) : ℕ) = 1752 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_73] <;> decide

theorem tot_1753 : totient 1753 = 1752 := by
  have h : totient 1753 = 1753 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1754 : totient 1754 = 876 := by
  have heq : (2 * (877) : ℕ) = 1754 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_877 : totient 877 = 877 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_877] <;> decide

theorem tot_1755 : totient 1755 = 864 := by
  have heq : (3^3 * (5 * (13)) : ℕ) = 1755 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_13] <;> decide

theorem tot_1756 : totient 1756 = 876 := by
  have heq : (2^2 * (439) : ℕ) = 1756 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_439 : totient 439 = 439 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_439] <;> decide

theorem tot_1757 : totient 1757 = 1500 := by
  have heq : (7 * (251) : ℕ) = 1757 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_251 : totient 251 = 251 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_251] <;> decide

theorem tot_1758 : totient 1758 = 584 := by
  have heq : (2 * (3 * (293)) : ℕ) = 1758 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_293 : totient 293 = 293 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_293] <;> decide

theorem tot_1759 : totient 1759 = 1758 := by
  have h : totient 1759 = 1759 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1760 : totient 1760 = 640 := by
  have heq : (2^5 * (5 * (11)) : ℕ) = 1760 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_11] <;> decide

theorem tot_1761 : totient 1761 = 1172 := by
  have heq : (3 * (587) : ℕ) = 1761 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_587 : totient 587 = 587 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_587] <;> decide

theorem tot_1762 : totient 1762 = 880 := by
  have heq : (2 * (881) : ℕ) = 1762 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_881 : totient 881 = 881 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_881] <;> decide

theorem tot_1763 : totient 1763 = 1680 := by
  have heq : (41 * (43) : ℕ) = 1763 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_41, hp_43] <;> decide

theorem tot_1764 : totient 1764 = 504 := by
  have heq : (2^2 * (3^2 * (7^2)) : ℕ) = 1764 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_7] <;> decide

theorem tot_1765 : totient 1765 = 1408 := by
  have heq : (5 * (353) : ℕ) = 1765 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_353 : totient 353 = 353 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_353] <;> decide

theorem tot_1766 : totient 1766 = 882 := by
  have heq : (2 * (883) : ℕ) = 1766 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_883 : totient 883 = 883 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_883] <;> decide

theorem tot_1767 : totient 1767 = 1080 := by
  have heq : (3 * (19 * (31)) : ℕ) = 1767 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_19, hp_31] <;> decide

theorem tot_1768 : totient 1768 = 768 := by
  have heq : (2^3 * (13 * (17)) : ℕ) = 1768 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_17] <;> decide

theorem tot_1769 : totient 1769 = 1680 := by
  have heq : (29 * (61) : ℕ) = 1769 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_29, hp_61] <;> decide

theorem tot_1770 : totient 1770 = 464 := by
  have heq : (2 * (3 * (5 * (59))) : ℕ) = 1770 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_59] <;> decide

theorem tot_1771 : totient 1771 = 1320 := by
  have heq : (7 * (11 * (23)) : ℕ) = 1771 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_11, hp_23] <;> decide

theorem tot_1772 : totient 1772 = 884 := by
  have heq : (2^2 * (443) : ℕ) = 1772 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_443 : totient 443 = 443 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_443] <;> decide

theorem tot_1773 : totient 1773 = 1176 := by
  have heq : (3^2 * (197) : ℕ) = 1773 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_197 : totient 197 = 197 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_197] <;> decide

theorem tot_1774 : totient 1774 = 886 := by
  have heq : (2 * (887) : ℕ) = 1774 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_887 : totient 887 = 887 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_887] <;> decide

theorem tot_1775 : totient 1775 = 1400 := by
  have heq : (5^2 * (71) : ℕ) = 1775 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_71] <;> decide

theorem tot_1776 : totient 1776 = 576 := by
  have heq : (2^4 * (3 * (37)) : ℕ) = 1776 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_37] <;> decide

theorem tot_1777 : totient 1777 = 1776 := by
  have h : totient 1777 = 1777 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1778 : totient 1778 = 756 := by
  have heq : (2 * (7 * (127)) : ℕ) = 1778 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_127 : totient 127 = 127 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_127] <;> decide

theorem tot_1779 : totient 1779 = 1184 := by
  have heq : (3 * (593) : ℕ) = 1779 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_593 : totient 593 = 593 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_593] <;> decide

theorem tot_1780 : totient 1780 = 704 := by
  have heq : (2^2 * (5 * (89)) : ℕ) = 1780 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_89] <;> decide

theorem tot_1781 : totient 1781 = 1632 := by
  have heq : (13 * (137) : ℕ) = 1781 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_137 : totient 137 = 137 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_137] <;> decide

theorem tot_1782 : totient 1782 = 540 := by
  have heq : (2 * (3^4 * (11)) : ℕ) = 1782 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11] <;> decide

theorem tot_1783 : totient 1783 = 1782 := by
  have h : totient 1783 = 1783 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1784 : totient 1784 = 888 := by
  have heq : (2^3 * (223) : ℕ) = 1784 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_223 : totient 223 = 223 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_223] <;> decide

theorem tot_1785 : totient 1785 = 768 := by
  have heq : (3 * (5 * (7 * (17))) : ℕ) = 1785 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_7, hp_17] <;> decide

theorem tot_1786 : totient 1786 = 828 := by
  have heq : (2 * (19 * (47)) : ℕ) = 1786 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_19, hp_47] <;> decide

theorem tot_1787 : totient 1787 = 1786 := by
  have h : totient 1787 = 1787 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1788 : totient 1788 = 592 := by
  have heq : (2^2 * (3 * (149)) : ℕ) = 1788 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_149 : totient 149 = 149 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_149] <;> decide

theorem tot_1789 : totient 1789 = 1788 := by
  have h : totient 1789 = 1789 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1790 : totient 1790 = 712 := by
  have heq : (2 * (5 * (179)) : ℕ) = 1790 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_179 : totient 179 = 179 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_179] <;> decide

theorem tot_1791 : totient 1791 = 1188 := by
  have heq : (3^2 * (199) : ℕ) = 1791 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_199 : totient 199 = 199 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_199] <;> decide

theorem tot_1792 : totient 1792 = 768 := by
  have heq : (2^8 * (7) : ℕ) = 1792 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^8) = 2^7 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7] <;> decide

theorem tot_1793 : totient 1793 = 1620 := by
  have heq : (11 * (163) : ℕ) = 1793 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_163 : totient 163 = 163 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_163] <;> decide

theorem tot_1794 : totient 1794 = 528 := by
  have heq : (2 * (3 * (13 * (23))) : ℕ) = 1794 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_13, hp_23] <;> decide

theorem tot_1795 : totient 1795 = 1432 := by
  have heq : (5 * (359) : ℕ) = 1795 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_359 : totient 359 = 359 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_359] <;> decide

theorem tot_1796 : totient 1796 = 896 := by
  have heq : (2^2 * (449) : ℕ) = 1796 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_449 : totient 449 = 449 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_449] <;> decide

theorem tot_1797 : totient 1797 = 1196 := by
  have heq : (3 * (599) : ℕ) = 1797 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_599 : totient 599 = 599 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_599] <;> decide

theorem tot_1798 : totient 1798 = 840 := by
  have heq : (2 * (29 * (31)) : ℕ) = 1798 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_29, hp_31] <;> decide

theorem tot_1799 : totient 1799 = 1536 := by
  have heq : (7 * (257) : ℕ) = 1799 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_257 : totient 257 = 257 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_257] <;> decide

theorem tot_1800 : totient 1800 = 480 := by
  have heq : (2^3 * (3^2 * (5^2)) : ℕ) = 1800 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_5] <;> decide

theorem tot_1801 : totient 1801 = 1800 := by
  have h : totient 1801 = 1801 - 1 := totient_prime (by norm_num)
  rw [h] <;> decide

theorem tot_1802 : totient 1802 = 832 := by
  have heq : (2 * (17 * (53)) : ℕ) = 1802 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17, hp_53] <;> decide

theorem tot_1803 : totient 1803 = 1200 := by
  have heq : (3 * (601) : ℕ) = 1803 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_601 : totient 601 = 601 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_601] <;> decide

theorem tot_1804 : totient 1804 = 800 := by
  have heq : (2^2 * (11 * (41)) : ℕ) = 1804 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_41] <;> decide

theorem tot_1805 : totient 1805 = 1368 := by
  have heq : (5 * (19^2) : ℕ) = 1805 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_19 : totient (19^2) = 19^1 * (19 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_5, hp_19] <;> decide

theorem tot_1806 : totient 1806 = 504 := by
  have heq : (2 * (3 * (7 * (43))) : ℕ) = 1806 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_43] <;> decide

theorem tot_1807 : totient 1807 = 1656 := by
  have heq : (13 * (139) : ℕ) = 1807 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_139 : totient 139 = 139 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_139] <;> decide

theorem Icc_succ_sum (n : ℕ) (g : ℕ → ℕ) :
  (Icc 1 (n + 1)).sum g = (Icc 1 n).sum g + g (n + 1) := by
  exact sum_Icc_succ_top (by omega) g

def my_sum (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | k + 1 => my_sum k + v3_fast (totient (k + 1)) 100

theorem my_sum_0 : my_sum 0 = 0 := rfl
theorem my_sum_1 : my_sum 1 = 0 := by
  rw [my_sum, my_sum_0, tot_1]
  have h : v3_fast 1 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_2 : my_sum 2 = 0 := by
  rw [my_sum, my_sum_1, tot_2]
  have h : v3_fast 1 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_3 : my_sum 3 = 0 := by
  rw [my_sum, my_sum_2, tot_3]
  have h : v3_fast 2 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_4 : my_sum 4 = 0 := by
  rw [my_sum, my_sum_3, tot_4]
  have h : v3_fast 2 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_5 : my_sum 5 = 0 := by
  rw [my_sum, my_sum_4, tot_5]
  have h : v3_fast 4 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_6 : my_sum 6 = 0 := by
  rw [my_sum, my_sum_5, tot_6]
  have h : v3_fast 2 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_7 : my_sum 7 = 1 := by
  rw [my_sum, my_sum_6, tot_7]
  have h : v3_fast 6 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_8 : my_sum 8 = 1 := by
  rw [my_sum, my_sum_7, tot_8]
  have h : v3_fast 4 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_9 : my_sum 9 = 2 := by
  rw [my_sum, my_sum_8, tot_9]
  have h : v3_fast 6 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_10 : my_sum 10 = 2 := by
  rw [my_sum, my_sum_9, tot_10]
  have h : v3_fast 4 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_11 : my_sum 11 = 2 := by
  rw [my_sum, my_sum_10, tot_11]
  have h : v3_fast 10 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_12 : my_sum 12 = 2 := by
  rw [my_sum, my_sum_11, tot_12]
  have h : v3_fast 4 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_13 : my_sum 13 = 3 := by
  rw [my_sum, my_sum_12, tot_13]
  have h : v3_fast 12 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_14 : my_sum 14 = 4 := by
  rw [my_sum, my_sum_13, tot_14]
  have h : v3_fast 6 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_15 : my_sum 15 = 4 := by
  rw [my_sum, my_sum_14, tot_15]
  have h : v3_fast 8 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_16 : my_sum 16 = 4 := by
  rw [my_sum, my_sum_15, tot_16]
  have h : v3_fast 8 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_17 : my_sum 17 = 4 := by
  rw [my_sum, my_sum_16, tot_17]
  have h : v3_fast 16 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_18 : my_sum 18 = 5 := by
  rw [my_sum, my_sum_17, tot_18]
  have h : v3_fast 6 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_19 : my_sum 19 = 7 := by
  rw [my_sum, my_sum_18, tot_19]
  have h : v3_fast 18 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_20 : my_sum 20 = 7 := by
  rw [my_sum, my_sum_19, tot_20]
  have h : v3_fast 8 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_21 : my_sum 21 = 8 := by
  rw [my_sum, my_sum_20, tot_21]
  have h : v3_fast 12 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_22 : my_sum 22 = 8 := by
  rw [my_sum, my_sum_21, tot_22]
  have h : v3_fast 10 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_23 : my_sum 23 = 8 := by
  rw [my_sum, my_sum_22, tot_23]
  have h : v3_fast 22 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_24 : my_sum 24 = 8 := by
  rw [my_sum, my_sum_23, tot_24]
  have h : v3_fast 8 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_25 : my_sum 25 = 8 := by
  rw [my_sum, my_sum_24, tot_25]
  have h : v3_fast 20 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_26 : my_sum 26 = 9 := by
  rw [my_sum, my_sum_25, tot_26]
  have h : v3_fast 12 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_27 : my_sum 27 = 11 := by
  rw [my_sum, my_sum_26, tot_27]
  have h : v3_fast 18 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_28 : my_sum 28 = 12 := by
  rw [my_sum, my_sum_27, tot_28]
  have h : v3_fast 12 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_29 : my_sum 29 = 12 := by
  rw [my_sum, my_sum_28, tot_29]
  have h : v3_fast 28 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_30 : my_sum 30 = 12 := by
  rw [my_sum, my_sum_29, tot_30]
  have h : v3_fast 8 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_31 : my_sum 31 = 13 := by
  rw [my_sum, my_sum_30, tot_31]
  have h : v3_fast 30 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_32 : my_sum 32 = 13 := by
  rw [my_sum, my_sum_31, tot_32]
  have h : v3_fast 16 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_33 : my_sum 33 = 13 := by
  rw [my_sum, my_sum_32, tot_33]
  have h : v3_fast 20 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_34 : my_sum 34 = 13 := by
  rw [my_sum, my_sum_33, tot_34]
  have h : v3_fast 16 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_35 : my_sum 35 = 14 := by
  rw [my_sum, my_sum_34, tot_35]
  have h : v3_fast 24 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_36 : my_sum 36 = 15 := by
  rw [my_sum, my_sum_35, tot_36]
  have h : v3_fast 12 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_37 : my_sum 37 = 17 := by
  rw [my_sum, my_sum_36, tot_37]
  have h : v3_fast 36 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_38 : my_sum 38 = 19 := by
  rw [my_sum, my_sum_37, tot_38]
  have h : v3_fast 18 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_39 : my_sum 39 = 20 := by
  rw [my_sum, my_sum_38, tot_39]
  have h : v3_fast 24 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_40 : my_sum 40 = 20 := by
  rw [my_sum, my_sum_39, tot_40]
  have h : v3_fast 16 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_41 : my_sum 41 = 20 := by
  rw [my_sum, my_sum_40, tot_41]
  have h : v3_fast 40 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_42 : my_sum 42 = 21 := by
  rw [my_sum, my_sum_41, tot_42]
  have h : v3_fast 12 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_43 : my_sum 43 = 22 := by
  rw [my_sum, my_sum_42, tot_43]
  have h : v3_fast 42 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_44 : my_sum 44 = 22 := by
  rw [my_sum, my_sum_43, tot_44]
  have h : v3_fast 20 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_45 : my_sum 45 = 23 := by
  rw [my_sum, my_sum_44, tot_45]
  have h : v3_fast 24 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_46 : my_sum 46 = 23 := by
  rw [my_sum, my_sum_45, tot_46]
  have h : v3_fast 22 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_47 : my_sum 47 = 23 := by
  rw [my_sum, my_sum_46, tot_47]
  have h : v3_fast 46 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_48 : my_sum 48 = 23 := by
  rw [my_sum, my_sum_47, tot_48]
  have h : v3_fast 16 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_49 : my_sum 49 = 24 := by
  rw [my_sum, my_sum_48, tot_49]
  have h : v3_fast 42 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_50 : my_sum 50 = 24 := by
  rw [my_sum, my_sum_49, tot_50]
  have h : v3_fast 20 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_51 : my_sum 51 = 24 := by
  rw [my_sum, my_sum_50, tot_51]
  have h : v3_fast 32 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_52 : my_sum 52 = 25 := by
  rw [my_sum, my_sum_51, tot_52]
  have h : v3_fast 24 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_53 : my_sum 53 = 25 := by
  rw [my_sum, my_sum_52, tot_53]
  have h : v3_fast 52 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_54 : my_sum 54 = 27 := by
  rw [my_sum, my_sum_53, tot_54]
  have h : v3_fast 18 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_55 : my_sum 55 = 27 := by
  rw [my_sum, my_sum_54, tot_55]
  have h : v3_fast 40 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_56 : my_sum 56 = 28 := by
  rw [my_sum, my_sum_55, tot_56]
  have h : v3_fast 24 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_57 : my_sum 57 = 30 := by
  rw [my_sum, my_sum_56, tot_57]
  have h : v3_fast 36 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_58 : my_sum 58 = 30 := by
  rw [my_sum, my_sum_57, tot_58]
  have h : v3_fast 28 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_59 : my_sum 59 = 30 := by
  rw [my_sum, my_sum_58, tot_59]
  have h : v3_fast 58 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_60 : my_sum 60 = 30 := by
  rw [my_sum, my_sum_59, tot_60]
  have h : v3_fast 16 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_61 : my_sum 61 = 31 := by
  rw [my_sum, my_sum_60, tot_61]
  have h : v3_fast 60 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_62 : my_sum 62 = 32 := by
  rw [my_sum, my_sum_61, tot_62]
  have h : v3_fast 30 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_63 : my_sum 63 = 34 := by
  rw [my_sum, my_sum_62, tot_63]
  have h : v3_fast 36 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_64 : my_sum 64 = 34 := by
  rw [my_sum, my_sum_63, tot_64]
  have h : v3_fast 32 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_65 : my_sum 65 = 35 := by
  rw [my_sum, my_sum_64, tot_65]
  have h : v3_fast 48 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_66 : my_sum 66 = 35 := by
  rw [my_sum, my_sum_65, tot_66]
  have h : v3_fast 20 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_67 : my_sum 67 = 36 := by
  rw [my_sum, my_sum_66, tot_67]
  have h : v3_fast 66 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_68 : my_sum 68 = 36 := by
  rw [my_sum, my_sum_67, tot_68]
  have h : v3_fast 32 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_69 : my_sum 69 = 36 := by
  rw [my_sum, my_sum_68, tot_69]
  have h : v3_fast 44 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_70 : my_sum 70 = 37 := by
  rw [my_sum, my_sum_69, tot_70]
  have h : v3_fast 24 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_71 : my_sum 71 = 37 := by
  rw [my_sum, my_sum_70, tot_71]
  have h : v3_fast 70 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_72 : my_sum 72 = 38 := by
  rw [my_sum, my_sum_71, tot_72]
  have h : v3_fast 24 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_73 : my_sum 73 = 40 := by
  rw [my_sum, my_sum_72, tot_73]
  have h : v3_fast 72 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_74 : my_sum 74 = 42 := by
  rw [my_sum, my_sum_73, tot_74]
  have h : v3_fast 36 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_75 : my_sum 75 = 42 := by
  rw [my_sum, my_sum_74, tot_75]
  have h : v3_fast 40 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_76 : my_sum 76 = 44 := by
  rw [my_sum, my_sum_75, tot_76]
  have h : v3_fast 36 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_77 : my_sum 77 = 45 := by
  rw [my_sum, my_sum_76, tot_77]
  have h : v3_fast 60 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_78 : my_sum 78 = 46 := by
  rw [my_sum, my_sum_77, tot_78]
  have h : v3_fast 24 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_79 : my_sum 79 = 47 := by
  rw [my_sum, my_sum_78, tot_79]
  have h : v3_fast 78 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_80 : my_sum 80 = 47 := by
  rw [my_sum, my_sum_79, tot_80]
  have h : v3_fast 32 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_81 : my_sum 81 = 50 := by
  rw [my_sum, my_sum_80, tot_81]
  have h : v3_fast 54 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_82 : my_sum 82 = 50 := by
  rw [my_sum, my_sum_81, tot_82]
  have h : v3_fast 40 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_83 : my_sum 83 = 50 := by
  rw [my_sum, my_sum_82, tot_83]
  have h : v3_fast 82 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_84 : my_sum 84 = 51 := by
  rw [my_sum, my_sum_83, tot_84]
  have h : v3_fast 24 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_85 : my_sum 85 = 51 := by
  rw [my_sum, my_sum_84, tot_85]
  have h : v3_fast 64 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_86 : my_sum 86 = 52 := by
  rw [my_sum, my_sum_85, tot_86]
  have h : v3_fast 42 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_87 : my_sum 87 = 52 := by
  rw [my_sum, my_sum_86, tot_87]
  have h : v3_fast 56 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_88 : my_sum 88 = 52 := by
  rw [my_sum, my_sum_87, tot_88]
  have h : v3_fast 40 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_89 : my_sum 89 = 52 := by
  rw [my_sum, my_sum_88, tot_89]
  have h : v3_fast 88 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_90 : my_sum 90 = 53 := by
  rw [my_sum, my_sum_89, tot_90]
  have h : v3_fast 24 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_91 : my_sum 91 = 55 := by
  rw [my_sum, my_sum_90, tot_91]
  have h : v3_fast 72 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_92 : my_sum 92 = 55 := by
  rw [my_sum, my_sum_91, tot_92]
  have h : v3_fast 44 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_93 : my_sum 93 = 56 := by
  rw [my_sum, my_sum_92, tot_93]
  have h : v3_fast 60 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_94 : my_sum 94 = 56 := by
  rw [my_sum, my_sum_93, tot_94]
  have h : v3_fast 46 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_95 : my_sum 95 = 58 := by
  rw [my_sum, my_sum_94, tot_95]
  have h : v3_fast 72 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_96 : my_sum 96 = 58 := by
  rw [my_sum, my_sum_95, tot_96]
  have h : v3_fast 32 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_97 : my_sum 97 = 59 := by
  rw [my_sum, my_sum_96, tot_97]
  have h : v3_fast 96 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_98 : my_sum 98 = 60 := by
  rw [my_sum, my_sum_97, tot_98]
  have h : v3_fast 42 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_99 : my_sum 99 = 61 := by
  rw [my_sum, my_sum_98, tot_99]
  have h : v3_fast 60 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_100 : my_sum 100 = 61 := by
  rw [my_sum, my_sum_99, tot_100]
  have h : v3_fast 40 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_101 : my_sum 101 = 61 := by
  rw [my_sum, my_sum_100, tot_101]
  have h : v3_fast 100 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_102 : my_sum 102 = 61 := by
  rw [my_sum, my_sum_101, tot_102]
  have h : v3_fast 32 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_103 : my_sum 103 = 62 := by
  rw [my_sum, my_sum_102, tot_103]
  have h : v3_fast 102 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_104 : my_sum 104 = 63 := by
  rw [my_sum, my_sum_103, tot_104]
  have h : v3_fast 48 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_105 : my_sum 105 = 64 := by
  rw [my_sum, my_sum_104, tot_105]
  have h : v3_fast 48 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_106 : my_sum 106 = 64 := by
  rw [my_sum, my_sum_105, tot_106]
  have h : v3_fast 52 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_107 : my_sum 107 = 64 := by
  rw [my_sum, my_sum_106, tot_107]
  have h : v3_fast 106 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_108 : my_sum 108 = 66 := by
  rw [my_sum, my_sum_107, tot_108]
  have h : v3_fast 36 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_109 : my_sum 109 = 69 := by
  rw [my_sum, my_sum_108, tot_109]
  have h : v3_fast 108 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_110 : my_sum 110 = 69 := by
  rw [my_sum, my_sum_109, tot_110]
  have h : v3_fast 40 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_111 : my_sum 111 = 71 := by
  rw [my_sum, my_sum_110, tot_111]
  have h : v3_fast 72 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_112 : my_sum 112 = 72 := by
  rw [my_sum, my_sum_111, tot_112]
  have h : v3_fast 48 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_113 : my_sum 113 = 72 := by
  rw [my_sum, my_sum_112, tot_113]
  have h : v3_fast 112 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_114 : my_sum 114 = 74 := by
  rw [my_sum, my_sum_113, tot_114]
  have h : v3_fast 36 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_115 : my_sum 115 = 74 := by
  rw [my_sum, my_sum_114, tot_115]
  have h : v3_fast 88 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_116 : my_sum 116 = 74 := by
  rw [my_sum, my_sum_115, tot_116]
  have h : v3_fast 56 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_117 : my_sum 117 = 76 := by
  rw [my_sum, my_sum_116, tot_117]
  have h : v3_fast 72 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_118 : my_sum 118 = 76 := by
  rw [my_sum, my_sum_117, tot_118]
  have h : v3_fast 58 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_119 : my_sum 119 = 77 := by
  rw [my_sum, my_sum_118, tot_119]
  have h : v3_fast 96 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_120 : my_sum 120 = 77 := by
  rw [my_sum, my_sum_119, tot_120]
  have h : v3_fast 32 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_121 : my_sum 121 = 77 := by
  rw [my_sum, my_sum_120, tot_121]
  have h : v3_fast 110 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_122 : my_sum 122 = 78 := by
  rw [my_sum, my_sum_121, tot_122]
  have h : v3_fast 60 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_123 : my_sum 123 = 78 := by
  rw [my_sum, my_sum_122, tot_123]
  have h : v3_fast 80 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_124 : my_sum 124 = 79 := by
  rw [my_sum, my_sum_123, tot_124]
  have h : v3_fast 60 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_125 : my_sum 125 = 79 := by
  rw [my_sum, my_sum_124, tot_125]
  have h : v3_fast 100 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_126 : my_sum 126 = 81 := by
  rw [my_sum, my_sum_125, tot_126]
  have h : v3_fast 36 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_127 : my_sum 127 = 83 := by
  rw [my_sum, my_sum_126, tot_127]
  have h : v3_fast 126 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_128 : my_sum 128 = 83 := by
  rw [my_sum, my_sum_127, tot_128]
  have h : v3_fast 64 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_129 : my_sum 129 = 84 := by
  rw [my_sum, my_sum_128, tot_129]
  have h : v3_fast 84 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_130 : my_sum 130 = 85 := by
  rw [my_sum, my_sum_129, tot_130]
  have h : v3_fast 48 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_131 : my_sum 131 = 85 := by
  rw [my_sum, my_sum_130, tot_131]
  have h : v3_fast 130 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_132 : my_sum 132 = 85 := by
  rw [my_sum, my_sum_131, tot_132]
  have h : v3_fast 40 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_133 : my_sum 133 = 88 := by
  rw [my_sum, my_sum_132, tot_133]
  have h : v3_fast 108 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_134 : my_sum 134 = 89 := by
  rw [my_sum, my_sum_133, tot_134]
  have h : v3_fast 66 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_135 : my_sum 135 = 91 := by
  rw [my_sum, my_sum_134, tot_135]
  have h : v3_fast 72 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_136 : my_sum 136 = 91 := by
  rw [my_sum, my_sum_135, tot_136]
  have h : v3_fast 64 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_137 : my_sum 137 = 91 := by
  rw [my_sum, my_sum_136, tot_137]
  have h : v3_fast 136 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_138 : my_sum 138 = 91 := by
  rw [my_sum, my_sum_137, tot_138]
  have h : v3_fast 44 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_139 : my_sum 139 = 92 := by
  rw [my_sum, my_sum_138, tot_139]
  have h : v3_fast 138 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_140 : my_sum 140 = 93 := by
  rw [my_sum, my_sum_139, tot_140]
  have h : v3_fast 48 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_141 : my_sum 141 = 93 := by
  rw [my_sum, my_sum_140, tot_141]
  have h : v3_fast 92 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_142 : my_sum 142 = 93 := by
  rw [my_sum, my_sum_141, tot_142]
  have h : v3_fast 70 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_143 : my_sum 143 = 94 := by
  rw [my_sum, my_sum_142, tot_143]
  have h : v3_fast 120 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_144 : my_sum 144 = 95 := by
  rw [my_sum, my_sum_143, tot_144]
  have h : v3_fast 48 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_145 : my_sum 145 = 95 := by
  rw [my_sum, my_sum_144, tot_145]
  have h : v3_fast 112 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_146 : my_sum 146 = 97 := by
  rw [my_sum, my_sum_145, tot_146]
  have h : v3_fast 72 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_147 : my_sum 147 = 98 := by
  rw [my_sum, my_sum_146, tot_147]
  have h : v3_fast 84 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_148 : my_sum 148 = 100 := by
  rw [my_sum, my_sum_147, tot_148]
  have h : v3_fast 72 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_149 : my_sum 149 = 100 := by
  rw [my_sum, my_sum_148, tot_149]
  have h : v3_fast 148 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_150 : my_sum 150 = 100 := by
  rw [my_sum, my_sum_149, tot_150]
  have h : v3_fast 40 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_151 : my_sum 151 = 101 := by
  rw [my_sum, my_sum_150, tot_151]
  have h : v3_fast 150 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_152 : my_sum 152 = 103 := by
  rw [my_sum, my_sum_151, tot_152]
  have h : v3_fast 72 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_153 : my_sum 153 = 104 := by
  rw [my_sum, my_sum_152, tot_153]
  have h : v3_fast 96 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_154 : my_sum 154 = 105 := by
  rw [my_sum, my_sum_153, tot_154]
  have h : v3_fast 60 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_155 : my_sum 155 = 106 := by
  rw [my_sum, my_sum_154, tot_155]
  have h : v3_fast 120 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_156 : my_sum 156 = 107 := by
  rw [my_sum, my_sum_155, tot_156]
  have h : v3_fast 48 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_157 : my_sum 157 = 108 := by
  rw [my_sum, my_sum_156, tot_157]
  have h : v3_fast 156 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_158 : my_sum 158 = 109 := by
  rw [my_sum, my_sum_157, tot_158]
  have h : v3_fast 78 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_159 : my_sum 159 = 109 := by
  rw [my_sum, my_sum_158, tot_159]
  have h : v3_fast 104 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_160 : my_sum 160 = 109 := by
  rw [my_sum, my_sum_159, tot_160]
  have h : v3_fast 64 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_161 : my_sum 161 = 110 := by
  rw [my_sum, my_sum_160, tot_161]
  have h : v3_fast 132 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_162 : my_sum 162 = 113 := by
  rw [my_sum, my_sum_161, tot_162]
  have h : v3_fast 54 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_163 : my_sum 163 = 117 := by
  rw [my_sum, my_sum_162, tot_163]
  have h : v3_fast 162 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_164 : my_sum 164 = 117 := by
  rw [my_sum, my_sum_163, tot_164]
  have h : v3_fast 80 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_165 : my_sum 165 = 117 := by
  rw [my_sum, my_sum_164, tot_165]
  have h : v3_fast 80 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_166 : my_sum 166 = 117 := by
  rw [my_sum, my_sum_165, tot_166]
  have h : v3_fast 82 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_167 : my_sum 167 = 117 := by
  rw [my_sum, my_sum_166, tot_167]
  have h : v3_fast 166 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_168 : my_sum 168 = 118 := by
  rw [my_sum, my_sum_167, tot_168]
  have h : v3_fast 48 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_169 : my_sum 169 = 119 := by
  rw [my_sum, my_sum_168, tot_169]
  have h : v3_fast 156 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_170 : my_sum 170 = 119 := by
  rw [my_sum, my_sum_169, tot_170]
  have h : v3_fast 64 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_171 : my_sum 171 = 122 := by
  rw [my_sum, my_sum_170, tot_171]
  have h : v3_fast 108 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_172 : my_sum 172 = 123 := by
  rw [my_sum, my_sum_171, tot_172]
  have h : v3_fast 84 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_173 : my_sum 173 = 123 := by
  rw [my_sum, my_sum_172, tot_173]
  have h : v3_fast 172 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_174 : my_sum 174 = 123 := by
  rw [my_sum, my_sum_173, tot_174]
  have h : v3_fast 56 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_175 : my_sum 175 = 124 := by
  rw [my_sum, my_sum_174, tot_175]
  have h : v3_fast 120 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_176 : my_sum 176 = 124 := by
  rw [my_sum, my_sum_175, tot_176]
  have h : v3_fast 80 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_177 : my_sum 177 = 124 := by
  rw [my_sum, my_sum_176, tot_177]
  have h : v3_fast 116 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_178 : my_sum 178 = 124 := by
  rw [my_sum, my_sum_177, tot_178]
  have h : v3_fast 88 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_179 : my_sum 179 = 124 := by
  rw [my_sum, my_sum_178, tot_179]
  have h : v3_fast 178 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_180 : my_sum 180 = 125 := by
  rw [my_sum, my_sum_179, tot_180]
  have h : v3_fast 48 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_181 : my_sum 181 = 127 := by
  rw [my_sum, my_sum_180, tot_181]
  have h : v3_fast 180 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_182 : my_sum 182 = 129 := by
  rw [my_sum, my_sum_181, tot_182]
  have h : v3_fast 72 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_183 : my_sum 183 = 130 := by
  rw [my_sum, my_sum_182, tot_183]
  have h : v3_fast 120 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_184 : my_sum 184 = 130 := by
  rw [my_sum, my_sum_183, tot_184]
  have h : v3_fast 88 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_185 : my_sum 185 = 132 := by
  rw [my_sum, my_sum_184, tot_185]
  have h : v3_fast 144 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_186 : my_sum 186 = 133 := by
  rw [my_sum, my_sum_185, tot_186]
  have h : v3_fast 60 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_187 : my_sum 187 = 133 := by
  rw [my_sum, my_sum_186, tot_187]
  have h : v3_fast 160 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_188 : my_sum 188 = 133 := by
  rw [my_sum, my_sum_187, tot_188]
  have h : v3_fast 92 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_189 : my_sum 189 = 136 := by
  rw [my_sum, my_sum_188, tot_189]
  have h : v3_fast 108 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_190 : my_sum 190 = 138 := by
  rw [my_sum, my_sum_189, tot_190]
  have h : v3_fast 72 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_191 : my_sum 191 = 138 := by
  rw [my_sum, my_sum_190, tot_191]
  have h : v3_fast 190 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_192 : my_sum 192 = 138 := by
  rw [my_sum, my_sum_191, tot_192]
  have h : v3_fast 64 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_193 : my_sum 193 = 139 := by
  rw [my_sum, my_sum_192, tot_193]
  have h : v3_fast 192 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_194 : my_sum 194 = 140 := by
  rw [my_sum, my_sum_193, tot_194]
  have h : v3_fast 96 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_195 : my_sum 195 = 141 := by
  rw [my_sum, my_sum_194, tot_195]
  have h : v3_fast 96 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_196 : my_sum 196 = 142 := by
  rw [my_sum, my_sum_195, tot_196]
  have h : v3_fast 84 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_197 : my_sum 197 = 142 := by
  rw [my_sum, my_sum_196, tot_197]
  have h : v3_fast 196 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_198 : my_sum 198 = 143 := by
  rw [my_sum, my_sum_197, tot_198]
  have h : v3_fast 60 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_199 : my_sum 199 = 145 := by
  rw [my_sum, my_sum_198, tot_199]
  have h : v3_fast 198 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_200 : my_sum 200 = 145 := by
  rw [my_sum, my_sum_199, tot_200]
  have h : v3_fast 80 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_201 : my_sum 201 = 146 := by
  rw [my_sum, my_sum_200, tot_201]
  have h : v3_fast 132 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_202 : my_sum 202 = 146 := by
  rw [my_sum, my_sum_201, tot_202]
  have h : v3_fast 100 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_203 : my_sum 203 = 147 := by
  rw [my_sum, my_sum_202, tot_203]
  have h : v3_fast 168 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_204 : my_sum 204 = 147 := by
  rw [my_sum, my_sum_203, tot_204]
  have h : v3_fast 64 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_205 : my_sum 205 = 147 := by
  rw [my_sum, my_sum_204, tot_205]
  have h : v3_fast 160 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_206 : my_sum 206 = 148 := by
  rw [my_sum, my_sum_205, tot_206]
  have h : v3_fast 102 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_207 : my_sum 207 = 149 := by
  rw [my_sum, my_sum_206, tot_207]
  have h : v3_fast 132 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_208 : my_sum 208 = 150 := by
  rw [my_sum, my_sum_207, tot_208]
  have h : v3_fast 96 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_209 : my_sum 209 = 152 := by
  rw [my_sum, my_sum_208, tot_209]
  have h : v3_fast 180 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_210 : my_sum 210 = 153 := by
  rw [my_sum, my_sum_209, tot_210]
  have h : v3_fast 48 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_211 : my_sum 211 = 154 := by
  rw [my_sum, my_sum_210, tot_211]
  have h : v3_fast 210 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_212 : my_sum 212 = 154 := by
  rw [my_sum, my_sum_211, tot_212]
  have h : v3_fast 104 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_213 : my_sum 213 = 154 := by
  rw [my_sum, my_sum_212, tot_213]
  have h : v3_fast 140 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_214 : my_sum 214 = 154 := by
  rw [my_sum, my_sum_213, tot_214]
  have h : v3_fast 106 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_215 : my_sum 215 = 155 := by
  rw [my_sum, my_sum_214, tot_215]
  have h : v3_fast 168 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_216 : my_sum 216 = 157 := by
  rw [my_sum, my_sum_215, tot_216]
  have h : v3_fast 72 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_217 : my_sum 217 = 159 := by
  rw [my_sum, my_sum_216, tot_217]
  have h : v3_fast 180 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_218 : my_sum 218 = 162 := by
  rw [my_sum, my_sum_217, tot_218]
  have h : v3_fast 108 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_219 : my_sum 219 = 164 := by
  rw [my_sum, my_sum_218, tot_219]
  have h : v3_fast 144 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_220 : my_sum 220 = 164 := by
  rw [my_sum, my_sum_219, tot_220]
  have h : v3_fast 80 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_221 : my_sum 221 = 165 := by
  rw [my_sum, my_sum_220, tot_221]
  have h : v3_fast 192 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_222 : my_sum 222 = 167 := by
  rw [my_sum, my_sum_221, tot_222]
  have h : v3_fast 72 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_223 : my_sum 223 = 168 := by
  rw [my_sum, my_sum_222, tot_223]
  have h : v3_fast 222 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_224 : my_sum 224 = 169 := by
  rw [my_sum, my_sum_223, tot_224]
  have h : v3_fast 96 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_225 : my_sum 225 = 170 := by
  rw [my_sum, my_sum_224, tot_225]
  have h : v3_fast 120 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_226 : my_sum 226 = 170 := by
  rw [my_sum, my_sum_225, tot_226]
  have h : v3_fast 112 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_227 : my_sum 227 = 170 := by
  rw [my_sum, my_sum_226, tot_227]
  have h : v3_fast 226 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_228 : my_sum 228 = 172 := by
  rw [my_sum, my_sum_227, tot_228]
  have h : v3_fast 72 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_229 : my_sum 229 = 173 := by
  rw [my_sum, my_sum_228, tot_229]
  have h : v3_fast 228 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_230 : my_sum 230 = 173 := by
  rw [my_sum, my_sum_229, tot_230]
  have h : v3_fast 88 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_231 : my_sum 231 = 174 := by
  rw [my_sum, my_sum_230, tot_231]
  have h : v3_fast 120 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_232 : my_sum 232 = 174 := by
  rw [my_sum, my_sum_231, tot_232]
  have h : v3_fast 112 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_233 : my_sum 233 = 174 := by
  rw [my_sum, my_sum_232, tot_233]
  have h : v3_fast 232 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_234 : my_sum 234 = 176 := by
  rw [my_sum, my_sum_233, tot_234]
  have h : v3_fast 72 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_235 : my_sum 235 = 176 := by
  rw [my_sum, my_sum_234, tot_235]
  have h : v3_fast 184 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_236 : my_sum 236 = 176 := by
  rw [my_sum, my_sum_235, tot_236]
  have h : v3_fast 116 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_237 : my_sum 237 = 177 := by
  rw [my_sum, my_sum_236, tot_237]
  have h : v3_fast 156 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_238 : my_sum 238 = 178 := by
  rw [my_sum, my_sum_237, tot_238]
  have h : v3_fast 96 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_239 : my_sum 239 = 178 := by
  rw [my_sum, my_sum_238, tot_239]
  have h : v3_fast 238 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_240 : my_sum 240 = 178 := by
  rw [my_sum, my_sum_239, tot_240]
  have h : v3_fast 64 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_241 : my_sum 241 = 179 := by
  rw [my_sum, my_sum_240, tot_241]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_242 : my_sum 242 = 179 := by
  rw [my_sum, my_sum_241, tot_242]
  have h : v3_fast 110 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_243 : my_sum 243 = 183 := by
  rw [my_sum, my_sum_242, tot_243]
  have h : v3_fast 162 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_244 : my_sum 244 = 184 := by
  rw [my_sum, my_sum_243, tot_244]
  have h : v3_fast 120 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_245 : my_sum 245 = 185 := by
  rw [my_sum, my_sum_244, tot_245]
  have h : v3_fast 168 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_246 : my_sum 246 = 185 := by
  rw [my_sum, my_sum_245, tot_246]
  have h : v3_fast 80 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_247 : my_sum 247 = 188 := by
  rw [my_sum, my_sum_246, tot_247]
  have h : v3_fast 216 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_248 : my_sum 248 = 189 := by
  rw [my_sum, my_sum_247, tot_248]
  have h : v3_fast 120 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_249 : my_sum 249 = 189 := by
  rw [my_sum, my_sum_248, tot_249]
  have h : v3_fast 164 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_250 : my_sum 250 = 189 := by
  rw [my_sum, my_sum_249, tot_250]
  have h : v3_fast 100 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_251 : my_sum 251 = 189 := by
  rw [my_sum, my_sum_250, tot_251]
  have h : v3_fast 250 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_252 : my_sum 252 = 191 := by
  rw [my_sum, my_sum_251, tot_252]
  have h : v3_fast 72 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_253 : my_sum 253 = 191 := by
  rw [my_sum, my_sum_252, tot_253]
  have h : v3_fast 220 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_254 : my_sum 254 = 193 := by
  rw [my_sum, my_sum_253, tot_254]
  have h : v3_fast 126 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_255 : my_sum 255 = 193 := by
  rw [my_sum, my_sum_254, tot_255]
  have h : v3_fast 128 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_256 : my_sum 256 = 193 := by
  rw [my_sum, my_sum_255, tot_256]
  have h : v3_fast 128 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_257 : my_sum 257 = 193 := by
  rw [my_sum, my_sum_256, tot_257]
  have h : v3_fast 256 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_258 : my_sum 258 = 194 := by
  rw [my_sum, my_sum_257, tot_258]
  have h : v3_fast 84 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_259 : my_sum 259 = 197 := by
  rw [my_sum, my_sum_258, tot_259]
  have h : v3_fast 216 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_260 : my_sum 260 = 198 := by
  rw [my_sum, my_sum_259, tot_260]
  have h : v3_fast 96 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_261 : my_sum 261 = 199 := by
  rw [my_sum, my_sum_260, tot_261]
  have h : v3_fast 168 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_262 : my_sum 262 = 199 := by
  rw [my_sum, my_sum_261, tot_262]
  have h : v3_fast 130 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_263 : my_sum 263 = 199 := by
  rw [my_sum, my_sum_262, tot_263]
  have h : v3_fast 262 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_264 : my_sum 264 = 199 := by
  rw [my_sum, my_sum_263, tot_264]
  have h : v3_fast 80 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_265 : my_sum 265 = 199 := by
  rw [my_sum, my_sum_264, tot_265]
  have h : v3_fast 208 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_266 : my_sum 266 = 202 := by
  rw [my_sum, my_sum_265, tot_266]
  have h : v3_fast 108 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_267 : my_sum 267 = 202 := by
  rw [my_sum, my_sum_266, tot_267]
  have h : v3_fast 176 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_268 : my_sum 268 = 203 := by
  rw [my_sum, my_sum_267, tot_268]
  have h : v3_fast 132 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_269 : my_sum 269 = 203 := by
  rw [my_sum, my_sum_268, tot_269]
  have h : v3_fast 268 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_270 : my_sum 270 = 205 := by
  rw [my_sum, my_sum_269, tot_270]
  have h : v3_fast 72 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_271 : my_sum 271 = 208 := by
  rw [my_sum, my_sum_270, tot_271]
  have h : v3_fast 270 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_272 : my_sum 272 = 208 := by
  rw [my_sum, my_sum_271, tot_272]
  have h : v3_fast 128 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_273 : my_sum 273 = 210 := by
  rw [my_sum, my_sum_272, tot_273]
  have h : v3_fast 144 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_274 : my_sum 274 = 210 := by
  rw [my_sum, my_sum_273, tot_274]
  have h : v3_fast 136 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_275 : my_sum 275 = 210 := by
  rw [my_sum, my_sum_274, tot_275]
  have h : v3_fast 200 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_276 : my_sum 276 = 210 := by
  rw [my_sum, my_sum_275, tot_276]
  have h : v3_fast 88 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_277 : my_sum 277 = 211 := by
  rw [my_sum, my_sum_276, tot_277]
  have h : v3_fast 276 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_278 : my_sum 278 = 212 := by
  rw [my_sum, my_sum_277, tot_278]
  have h : v3_fast 138 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_279 : my_sum 279 = 214 := by
  rw [my_sum, my_sum_278, tot_279]
  have h : v3_fast 180 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_280 : my_sum 280 = 215 := by
  rw [my_sum, my_sum_279, tot_280]
  have h : v3_fast 96 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_281 : my_sum 281 = 215 := by
  rw [my_sum, my_sum_280, tot_281]
  have h : v3_fast 280 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_282 : my_sum 282 = 215 := by
  rw [my_sum, my_sum_281, tot_282]
  have h : v3_fast 92 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_283 : my_sum 283 = 216 := by
  rw [my_sum, my_sum_282, tot_283]
  have h : v3_fast 282 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_284 : my_sum 284 = 216 := by
  rw [my_sum, my_sum_283, tot_284]
  have h : v3_fast 140 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_285 : my_sum 285 = 218 := by
  rw [my_sum, my_sum_284, tot_285]
  have h : v3_fast 144 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_286 : my_sum 286 = 219 := by
  rw [my_sum, my_sum_285, tot_286]
  have h : v3_fast 120 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_287 : my_sum 287 = 220 := by
  rw [my_sum, my_sum_286, tot_287]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_288 : my_sum 288 = 221 := by
  rw [my_sum, my_sum_287, tot_288]
  have h : v3_fast 96 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_289 : my_sum 289 = 221 := by
  rw [my_sum, my_sum_288, tot_289]
  have h : v3_fast 272 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_290 : my_sum 290 = 221 := by
  rw [my_sum, my_sum_289, tot_290]
  have h : v3_fast 112 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_291 : my_sum 291 = 222 := by
  rw [my_sum, my_sum_290, tot_291]
  have h : v3_fast 192 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_292 : my_sum 292 = 224 := by
  rw [my_sum, my_sum_291, tot_292]
  have h : v3_fast 144 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_293 : my_sum 293 = 224 := by
  rw [my_sum, my_sum_292, tot_293]
  have h : v3_fast 292 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_294 : my_sum 294 = 225 := by
  rw [my_sum, my_sum_293, tot_294]
  have h : v3_fast 84 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_295 : my_sum 295 = 225 := by
  rw [my_sum, my_sum_294, tot_295]
  have h : v3_fast 232 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_296 : my_sum 296 = 227 := by
  rw [my_sum, my_sum_295, tot_296]
  have h : v3_fast 144 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_297 : my_sum 297 = 229 := by
  rw [my_sum, my_sum_296, tot_297]
  have h : v3_fast 180 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_298 : my_sum 298 = 229 := by
  rw [my_sum, my_sum_297, tot_298]
  have h : v3_fast 148 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_299 : my_sum 299 = 230 := by
  rw [my_sum, my_sum_298, tot_299]
  have h : v3_fast 264 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_300 : my_sum 300 = 230 := by
  rw [my_sum, my_sum_299, tot_300]
  have h : v3_fast 80 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_301 : my_sum 301 = 232 := by
  rw [my_sum, my_sum_300, tot_301]
  have h : v3_fast 252 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_302 : my_sum 302 = 233 := by
  rw [my_sum, my_sum_301, tot_302]
  have h : v3_fast 150 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_303 : my_sum 303 = 233 := by
  rw [my_sum, my_sum_302, tot_303]
  have h : v3_fast 200 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_304 : my_sum 304 = 235 := by
  rw [my_sum, my_sum_303, tot_304]
  have h : v3_fast 144 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_305 : my_sum 305 = 236 := by
  rw [my_sum, my_sum_304, tot_305]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_306 : my_sum 306 = 237 := by
  rw [my_sum, my_sum_305, tot_306]
  have h : v3_fast 96 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_307 : my_sum 307 = 239 := by
  rw [my_sum, my_sum_306, tot_307]
  have h : v3_fast 306 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_308 : my_sum 308 = 240 := by
  rw [my_sum, my_sum_307, tot_308]
  have h : v3_fast 120 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_309 : my_sum 309 = 241 := by
  rw [my_sum, my_sum_308, tot_309]
  have h : v3_fast 204 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_310 : my_sum 310 = 242 := by
  rw [my_sum, my_sum_309, tot_310]
  have h : v3_fast 120 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_311 : my_sum 311 = 242 := by
  rw [my_sum, my_sum_310, tot_311]
  have h : v3_fast 310 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_312 : my_sum 312 = 243 := by
  rw [my_sum, my_sum_311, tot_312]
  have h : v3_fast 96 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_313 : my_sum 313 = 244 := by
  rw [my_sum, my_sum_312, tot_313]
  have h : v3_fast 312 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_314 : my_sum 314 = 245 := by
  rw [my_sum, my_sum_313, tot_314]
  have h : v3_fast 156 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_315 : my_sum 315 = 247 := by
  rw [my_sum, my_sum_314, tot_315]
  have h : v3_fast 144 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_316 : my_sum 316 = 248 := by
  rw [my_sum, my_sum_315, tot_316]
  have h : v3_fast 156 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_317 : my_sum 317 = 248 := by
  rw [my_sum, my_sum_316, tot_317]
  have h : v3_fast 316 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_318 : my_sum 318 = 248 := by
  rw [my_sum, my_sum_317, tot_318]
  have h : v3_fast 104 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_319 : my_sum 319 = 248 := by
  rw [my_sum, my_sum_318, tot_319]
  have h : v3_fast 280 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_320 : my_sum 320 = 248 := by
  rw [my_sum, my_sum_319, tot_320]
  have h : v3_fast 128 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_321 : my_sum 321 = 248 := by
  rw [my_sum, my_sum_320, tot_321]
  have h : v3_fast 212 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_322 : my_sum 322 = 249 := by
  rw [my_sum, my_sum_321, tot_322]
  have h : v3_fast 132 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_323 : my_sum 323 = 251 := by
  rw [my_sum, my_sum_322, tot_323]
  have h : v3_fast 288 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_324 : my_sum 324 = 254 := by
  rw [my_sum, my_sum_323, tot_324]
  have h : v3_fast 108 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_325 : my_sum 325 = 255 := by
  rw [my_sum, my_sum_324, tot_325]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_326 : my_sum 326 = 259 := by
  rw [my_sum, my_sum_325, tot_326]
  have h : v3_fast 162 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_327 : my_sum 327 = 262 := by
  rw [my_sum, my_sum_326, tot_327]
  have h : v3_fast 216 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_328 : my_sum 328 = 262 := by
  rw [my_sum, my_sum_327, tot_328]
  have h : v3_fast 160 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_329 : my_sum 329 = 263 := by
  rw [my_sum, my_sum_328, tot_329]
  have h : v3_fast 276 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_330 : my_sum 330 = 263 := by
  rw [my_sum, my_sum_329, tot_330]
  have h : v3_fast 80 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_331 : my_sum 331 = 264 := by
  rw [my_sum, my_sum_330, tot_331]
  have h : v3_fast 330 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_332 : my_sum 332 = 264 := by
  rw [my_sum, my_sum_331, tot_332]
  have h : v3_fast 164 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_333 : my_sum 333 = 267 := by
  rw [my_sum, my_sum_332, tot_333]
  have h : v3_fast 216 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_334 : my_sum 334 = 267 := by
  rw [my_sum, my_sum_333, tot_334]
  have h : v3_fast 166 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_335 : my_sum 335 = 268 := by
  rw [my_sum, my_sum_334, tot_335]
  have h : v3_fast 264 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_336 : my_sum 336 = 269 := by
  rw [my_sum, my_sum_335, tot_336]
  have h : v3_fast 96 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_337 : my_sum 337 = 270 := by
  rw [my_sum, my_sum_336, tot_337]
  have h : v3_fast 336 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_338 : my_sum 338 = 271 := by
  rw [my_sum, my_sum_337, tot_338]
  have h : v3_fast 156 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_339 : my_sum 339 = 271 := by
  rw [my_sum, my_sum_338, tot_339]
  have h : v3_fast 224 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_340 : my_sum 340 = 271 := by
  rw [my_sum, my_sum_339, tot_340]
  have h : v3_fast 128 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_341 : my_sum 341 = 272 := by
  rw [my_sum, my_sum_340, tot_341]
  have h : v3_fast 300 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_342 : my_sum 342 = 275 := by
  rw [my_sum, my_sum_341, tot_342]
  have h : v3_fast 108 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_343 : my_sum 343 = 276 := by
  rw [my_sum, my_sum_342, tot_343]
  have h : v3_fast 294 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_344 : my_sum 344 = 277 := by
  rw [my_sum, my_sum_343, tot_344]
  have h : v3_fast 168 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_345 : my_sum 345 = 277 := by
  rw [my_sum, my_sum_344, tot_345]
  have h : v3_fast 176 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_346 : my_sum 346 = 277 := by
  rw [my_sum, my_sum_345, tot_346]
  have h : v3_fast 172 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_347 : my_sum 347 = 277 := by
  rw [my_sum, my_sum_346, tot_347]
  have h : v3_fast 346 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_348 : my_sum 348 = 277 := by
  rw [my_sum, my_sum_347, tot_348]
  have h : v3_fast 112 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_349 : my_sum 349 = 278 := by
  rw [my_sum, my_sum_348, tot_349]
  have h : v3_fast 348 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_350 : my_sum 350 = 279 := by
  rw [my_sum, my_sum_349, tot_350]
  have h : v3_fast 120 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_351 : my_sum 351 = 282 := by
  rw [my_sum, my_sum_350, tot_351]
  have h : v3_fast 216 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_352 : my_sum 352 = 282 := by
  rw [my_sum, my_sum_351, tot_352]
  have h : v3_fast 160 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_353 : my_sum 353 = 282 := by
  rw [my_sum, my_sum_352, tot_353]
  have h : v3_fast 352 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_354 : my_sum 354 = 282 := by
  rw [my_sum, my_sum_353, tot_354]
  have h : v3_fast 116 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_355 : my_sum 355 = 282 := by
  rw [my_sum, my_sum_354, tot_355]
  have h : v3_fast 280 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_356 : my_sum 356 = 282 := by
  rw [my_sum, my_sum_355, tot_356]
  have h : v3_fast 176 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_357 : my_sum 357 = 283 := by
  rw [my_sum, my_sum_356, tot_357]
  have h : v3_fast 192 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_358 : my_sum 358 = 283 := by
  rw [my_sum, my_sum_357, tot_358]
  have h : v3_fast 178 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_359 : my_sum 359 = 283 := by
  rw [my_sum, my_sum_358, tot_359]
  have h : v3_fast 358 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_360 : my_sum 360 = 284 := by
  rw [my_sum, my_sum_359, tot_360]
  have h : v3_fast 96 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_361 : my_sum 361 = 286 := by
  rw [my_sum, my_sum_360, tot_361]
  have h : v3_fast 342 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_362 : my_sum 362 = 288 := by
  rw [my_sum, my_sum_361, tot_362]
  have h : v3_fast 180 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_363 : my_sum 363 = 288 := by
  rw [my_sum, my_sum_362, tot_363]
  have h : v3_fast 220 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_364 : my_sum 364 = 290 := by
  rw [my_sum, my_sum_363, tot_364]
  have h : v3_fast 144 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_365 : my_sum 365 = 292 := by
  rw [my_sum, my_sum_364, tot_365]
  have h : v3_fast 288 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_366 : my_sum 366 = 293 := by
  rw [my_sum, my_sum_365, tot_366]
  have h : v3_fast 120 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_367 : my_sum 367 = 294 := by
  rw [my_sum, my_sum_366, tot_367]
  have h : v3_fast 366 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_368 : my_sum 368 = 294 := by
  rw [my_sum, my_sum_367, tot_368]
  have h : v3_fast 176 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_369 : my_sum 369 = 295 := by
  rw [my_sum, my_sum_368, tot_369]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_370 : my_sum 370 = 297 := by
  rw [my_sum, my_sum_369, tot_370]
  have h : v3_fast 144 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_371 : my_sum 371 = 298 := by
  rw [my_sum, my_sum_370, tot_371]
  have h : v3_fast 312 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_372 : my_sum 372 = 299 := by
  rw [my_sum, my_sum_371, tot_372]
  have h : v3_fast 120 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_373 : my_sum 373 = 300 := by
  rw [my_sum, my_sum_372, tot_373]
  have h : v3_fast 372 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_374 : my_sum 374 = 300 := by
  rw [my_sum, my_sum_373, tot_374]
  have h : v3_fast 160 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_375 : my_sum 375 = 300 := by
  rw [my_sum, my_sum_374, tot_375]
  have h : v3_fast 200 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_376 : my_sum 376 = 300 := by
  rw [my_sum, my_sum_375, tot_376]
  have h : v3_fast 184 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_377 : my_sum 377 = 301 := by
  rw [my_sum, my_sum_376, tot_377]
  have h : v3_fast 336 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_378 : my_sum 378 = 304 := by
  rw [my_sum, my_sum_377, tot_378]
  have h : v3_fast 108 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_379 : my_sum 379 = 307 := by
  rw [my_sum, my_sum_378, tot_379]
  have h : v3_fast 378 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_380 : my_sum 380 = 309 := by
  rw [my_sum, my_sum_379, tot_380]
  have h : v3_fast 144 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_381 : my_sum 381 = 311 := by
  rw [my_sum, my_sum_380, tot_381]
  have h : v3_fast 252 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_382 : my_sum 382 = 311 := by
  rw [my_sum, my_sum_381, tot_382]
  have h : v3_fast 190 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_383 : my_sum 383 = 311 := by
  rw [my_sum, my_sum_382, tot_383]
  have h : v3_fast 382 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_384 : my_sum 384 = 311 := by
  rw [my_sum, my_sum_383, tot_384]
  have h : v3_fast 128 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_385 : my_sum 385 = 312 := by
  rw [my_sum, my_sum_384, tot_385]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_386 : my_sum 386 = 313 := by
  rw [my_sum, my_sum_385, tot_386]
  have h : v3_fast 192 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_387 : my_sum 387 = 315 := by
  rw [my_sum, my_sum_386, tot_387]
  have h : v3_fast 252 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_388 : my_sum 388 = 316 := by
  rw [my_sum, my_sum_387, tot_388]
  have h : v3_fast 192 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_389 : my_sum 389 = 316 := by
  rw [my_sum, my_sum_388, tot_389]
  have h : v3_fast 388 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_390 : my_sum 390 = 317 := by
  rw [my_sum, my_sum_389, tot_390]
  have h : v3_fast 96 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_391 : my_sum 391 = 317 := by
  rw [my_sum, my_sum_390, tot_391]
  have h : v3_fast 352 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_392 : my_sum 392 = 318 := by
  rw [my_sum, my_sum_391, tot_392]
  have h : v3_fast 168 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_393 : my_sum 393 = 318 := by
  rw [my_sum, my_sum_392, tot_393]
  have h : v3_fast 260 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_394 : my_sum 394 = 318 := by
  rw [my_sum, my_sum_393, tot_394]
  have h : v3_fast 196 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_395 : my_sum 395 = 319 := by
  rw [my_sum, my_sum_394, tot_395]
  have h : v3_fast 312 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_396 : my_sum 396 = 320 := by
  rw [my_sum, my_sum_395, tot_396]
  have h : v3_fast 120 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_397 : my_sum 397 = 322 := by
  rw [my_sum, my_sum_396, tot_397]
  have h : v3_fast 396 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_398 : my_sum 398 = 324 := by
  rw [my_sum, my_sum_397, tot_398]
  have h : v3_fast 198 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_399 : my_sum 399 = 327 := by
  rw [my_sum, my_sum_398, tot_399]
  have h : v3_fast 216 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_400 : my_sum 400 = 327 := by
  rw [my_sum, my_sum_399, tot_400]
  have h : v3_fast 160 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_401 : my_sum 401 = 327 := by
  rw [my_sum, my_sum_400, tot_401]
  have h : v3_fast 400 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_402 : my_sum 402 = 328 := by
  rw [my_sum, my_sum_401, tot_402]
  have h : v3_fast 132 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_403 : my_sum 403 = 330 := by
  rw [my_sum, my_sum_402, tot_403]
  have h : v3_fast 360 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_404 : my_sum 404 = 330 := by
  rw [my_sum, my_sum_403, tot_404]
  have h : v3_fast 200 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_405 : my_sum 405 = 333 := by
  rw [my_sum, my_sum_404, tot_405]
  have h : v3_fast 216 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_406 : my_sum 406 = 334 := by
  rw [my_sum, my_sum_405, tot_406]
  have h : v3_fast 168 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_407 : my_sum 407 = 336 := by
  rw [my_sum, my_sum_406, tot_407]
  have h : v3_fast 360 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_408 : my_sum 408 = 336 := by
  rw [my_sum, my_sum_407, tot_408]
  have h : v3_fast 128 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_409 : my_sum 409 = 337 := by
  rw [my_sum, my_sum_408, tot_409]
  have h : v3_fast 408 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_410 : my_sum 410 = 337 := by
  rw [my_sum, my_sum_409, tot_410]
  have h : v3_fast 160 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_411 : my_sum 411 = 337 := by
  rw [my_sum, my_sum_410, tot_411]
  have h : v3_fast 272 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_412 : my_sum 412 = 338 := by
  rw [my_sum, my_sum_411, tot_412]
  have h : v3_fast 204 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_413 : my_sum 413 = 339 := by
  rw [my_sum, my_sum_412, tot_413]
  have h : v3_fast 348 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_414 : my_sum 414 = 340 := by
  rw [my_sum, my_sum_413, tot_414]
  have h : v3_fast 132 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_415 : my_sum 415 = 340 := by
  rw [my_sum, my_sum_414, tot_415]
  have h : v3_fast 328 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_416 : my_sum 416 = 341 := by
  rw [my_sum, my_sum_415, tot_416]
  have h : v3_fast 192 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_417 : my_sum 417 = 342 := by
  rw [my_sum, my_sum_416, tot_417]
  have h : v3_fast 276 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_418 : my_sum 418 = 344 := by
  rw [my_sum, my_sum_417, tot_418]
  have h : v3_fast 180 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_419 : my_sum 419 = 344 := by
  rw [my_sum, my_sum_418, tot_419]
  have h : v3_fast 418 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_420 : my_sum 420 = 345 := by
  rw [my_sum, my_sum_419, tot_420]
  have h : v3_fast 96 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_421 : my_sum 421 = 346 := by
  rw [my_sum, my_sum_420, tot_421]
  have h : v3_fast 420 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_422 : my_sum 422 = 347 := by
  rw [my_sum, my_sum_421, tot_422]
  have h : v3_fast 210 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_423 : my_sum 423 = 348 := by
  rw [my_sum, my_sum_422, tot_423]
  have h : v3_fast 276 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_424 : my_sum 424 = 348 := by
  rw [my_sum, my_sum_423, tot_424]
  have h : v3_fast 208 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_425 : my_sum 425 = 348 := by
  rw [my_sum, my_sum_424, tot_425]
  have h : v3_fast 320 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_426 : my_sum 426 = 348 := by
  rw [my_sum, my_sum_425, tot_426]
  have h : v3_fast 140 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_427 : my_sum 427 = 350 := by
  rw [my_sum, my_sum_426, tot_427]
  have h : v3_fast 360 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_428 : my_sum 428 = 350 := by
  rw [my_sum, my_sum_427, tot_428]
  have h : v3_fast 212 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_429 : my_sum 429 = 351 := by
  rw [my_sum, my_sum_428, tot_429]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_430 : my_sum 430 = 352 := by
  rw [my_sum, my_sum_429, tot_430]
  have h : v3_fast 168 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_431 : my_sum 431 = 352 := by
  rw [my_sum, my_sum_430, tot_431]
  have h : v3_fast 430 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_432 : my_sum 432 = 354 := by
  rw [my_sum, my_sum_431, tot_432]
  have h : v3_fast 144 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_433 : my_sum 433 = 357 := by
  rw [my_sum, my_sum_432, tot_433]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_434 : my_sum 434 = 359 := by
  rw [my_sum, my_sum_433, tot_434]
  have h : v3_fast 180 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_435 : my_sum 435 = 359 := by
  rw [my_sum, my_sum_434, tot_435]
  have h : v3_fast 224 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_436 : my_sum 436 = 362 := by
  rw [my_sum, my_sum_435, tot_436]
  have h : v3_fast 216 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_437 : my_sum 437 = 364 := by
  rw [my_sum, my_sum_436, tot_437]
  have h : v3_fast 396 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_438 : my_sum 438 = 366 := by
  rw [my_sum, my_sum_437, tot_438]
  have h : v3_fast 144 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_439 : my_sum 439 = 367 := by
  rw [my_sum, my_sum_438, tot_439]
  have h : v3_fast 438 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_440 : my_sum 440 = 367 := by
  rw [my_sum, my_sum_439, tot_440]
  have h : v3_fast 160 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_441 : my_sum 441 = 369 := by
  rw [my_sum, my_sum_440, tot_441]
  have h : v3_fast 252 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_442 : my_sum 442 = 370 := by
  rw [my_sum, my_sum_441, tot_442]
  have h : v3_fast 192 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_443 : my_sum 443 = 370 := by
  rw [my_sum, my_sum_442, tot_443]
  have h : v3_fast 442 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_444 : my_sum 444 = 372 := by
  rw [my_sum, my_sum_443, tot_444]
  have h : v3_fast 144 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_445 : my_sum 445 = 372 := by
  rw [my_sum, my_sum_444, tot_445]
  have h : v3_fast 352 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_446 : my_sum 446 = 373 := by
  rw [my_sum, my_sum_445, tot_446]
  have h : v3_fast 222 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_447 : my_sum 447 = 373 := by
  rw [my_sum, my_sum_446, tot_447]
  have h : v3_fast 296 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_448 : my_sum 448 = 374 := by
  rw [my_sum, my_sum_447, tot_448]
  have h : v3_fast 192 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_449 : my_sum 449 = 374 := by
  rw [my_sum, my_sum_448, tot_449]
  have h : v3_fast 448 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_450 : my_sum 450 = 375 := by
  rw [my_sum, my_sum_449, tot_450]
  have h : v3_fast 120 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_451 : my_sum 451 = 375 := by
  rw [my_sum, my_sum_450, tot_451]
  have h : v3_fast 400 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_452 : my_sum 452 = 375 := by
  rw [my_sum, my_sum_451, tot_452]
  have h : v3_fast 224 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_453 : my_sum 453 = 376 := by
  rw [my_sum, my_sum_452, tot_453]
  have h : v3_fast 300 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_454 : my_sum 454 = 376 := by
  rw [my_sum, my_sum_453, tot_454]
  have h : v3_fast 226 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_455 : my_sum 455 = 378 := by
  rw [my_sum, my_sum_454, tot_455]
  have h : v3_fast 288 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_456 : my_sum 456 = 380 := by
  rw [my_sum, my_sum_455, tot_456]
  have h : v3_fast 144 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_457 : my_sum 457 = 381 := by
  rw [my_sum, my_sum_456, tot_457]
  have h : v3_fast 456 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_458 : my_sum 458 = 382 := by
  rw [my_sum, my_sum_457, tot_458]
  have h : v3_fast 228 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_459 : my_sum 459 = 384 := by
  rw [my_sum, my_sum_458, tot_459]
  have h : v3_fast 288 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_460 : my_sum 460 = 384 := by
  rw [my_sum, my_sum_459, tot_460]
  have h : v3_fast 176 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_461 : my_sum 461 = 384 := by
  rw [my_sum, my_sum_460, tot_461]
  have h : v3_fast 460 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_462 : my_sum 462 = 385 := by
  rw [my_sum, my_sum_461, tot_462]
  have h : v3_fast 120 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_463 : my_sum 463 = 386 := by
  rw [my_sum, my_sum_462, tot_463]
  have h : v3_fast 462 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_464 : my_sum 464 = 386 := by
  rw [my_sum, my_sum_463, tot_464]
  have h : v3_fast 224 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_465 : my_sum 465 = 387 := by
  rw [my_sum, my_sum_464, tot_465]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_466 : my_sum 466 = 387 := by
  rw [my_sum, my_sum_465, tot_466]
  have h : v3_fast 232 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_467 : my_sum 467 = 387 := by
  rw [my_sum, my_sum_466, tot_467]
  have h : v3_fast 466 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_468 : my_sum 468 = 389 := by
  rw [my_sum, my_sum_467, tot_468]
  have h : v3_fast 144 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_469 : my_sum 469 = 391 := by
  rw [my_sum, my_sum_468, tot_469]
  have h : v3_fast 396 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_470 : my_sum 470 = 391 := by
  rw [my_sum, my_sum_469, tot_470]
  have h : v3_fast 184 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_471 : my_sum 471 = 392 := by
  rw [my_sum, my_sum_470, tot_471]
  have h : v3_fast 312 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_472 : my_sum 472 = 392 := by
  rw [my_sum, my_sum_471, tot_472]
  have h : v3_fast 232 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_473 : my_sum 473 = 393 := by
  rw [my_sum, my_sum_472, tot_473]
  have h : v3_fast 420 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_474 : my_sum 474 = 394 := by
  rw [my_sum, my_sum_473, tot_474]
  have h : v3_fast 156 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_475 : my_sum 475 = 396 := by
  rw [my_sum, my_sum_474, tot_475]
  have h : v3_fast 360 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_476 : my_sum 476 = 397 := by
  rw [my_sum, my_sum_475, tot_476]
  have h : v3_fast 192 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_477 : my_sum 477 = 398 := by
  rw [my_sum, my_sum_476, tot_477]
  have h : v3_fast 312 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_478 : my_sum 478 = 398 := by
  rw [my_sum, my_sum_477, tot_478]
  have h : v3_fast 238 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_479 : my_sum 479 = 398 := by
  rw [my_sum, my_sum_478, tot_479]
  have h : v3_fast 478 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_480 : my_sum 480 = 398 := by
  rw [my_sum, my_sum_479, tot_480]
  have h : v3_fast 128 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_481 : my_sum 481 = 401 := by
  rw [my_sum, my_sum_480, tot_481]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_482 : my_sum 482 = 402 := by
  rw [my_sum, my_sum_481, tot_482]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_483 : my_sum 483 = 403 := by
  rw [my_sum, my_sum_482, tot_483]
  have h : v3_fast 264 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_484 : my_sum 484 = 403 := by
  rw [my_sum, my_sum_483, tot_484]
  have h : v3_fast 220 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_485 : my_sum 485 = 404 := by
  rw [my_sum, my_sum_484, tot_485]
  have h : v3_fast 384 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_486 : my_sum 486 = 408 := by
  rw [my_sum, my_sum_485, tot_486]
  have h : v3_fast 162 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_487 : my_sum 487 = 413 := by
  rw [my_sum, my_sum_486, tot_487]
  have h : v3_fast 486 100 = 5 := rfl
  rw [h] <;> decide

theorem my_sum_488 : my_sum 488 = 414 := by
  rw [my_sum, my_sum_487, tot_488]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_489 : my_sum 489 = 418 := by
  rw [my_sum, my_sum_488, tot_489]
  have h : v3_fast 324 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_490 : my_sum 490 = 419 := by
  rw [my_sum, my_sum_489, tot_490]
  have h : v3_fast 168 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_491 : my_sum 491 = 419 := by
  rw [my_sum, my_sum_490, tot_491]
  have h : v3_fast 490 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_492 : my_sum 492 = 419 := by
  rw [my_sum, my_sum_491, tot_492]
  have h : v3_fast 160 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_493 : my_sum 493 = 419 := by
  rw [my_sum, my_sum_492, tot_493]
  have h : v3_fast 448 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_494 : my_sum 494 = 422 := by
  rw [my_sum, my_sum_493, tot_494]
  have h : v3_fast 216 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_495 : my_sum 495 = 423 := by
  rw [my_sum, my_sum_494, tot_495]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_496 : my_sum 496 = 424 := by
  rw [my_sum, my_sum_495, tot_496]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_497 : my_sum 497 = 425 := by
  rw [my_sum, my_sum_496, tot_497]
  have h : v3_fast 420 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_498 : my_sum 498 = 425 := by
  rw [my_sum, my_sum_497, tot_498]
  have h : v3_fast 164 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_499 : my_sum 499 = 426 := by
  rw [my_sum, my_sum_498, tot_499]
  have h : v3_fast 498 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_500 : my_sum 500 = 426 := by
  rw [my_sum, my_sum_499, tot_500]
  have h : v3_fast 200 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_501 : my_sum 501 = 426 := by
  rw [my_sum, my_sum_500, tot_501]
  have h : v3_fast 332 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_502 : my_sum 502 = 426 := by
  rw [my_sum, my_sum_501, tot_502]
  have h : v3_fast 250 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_503 : my_sum 503 = 426 := by
  rw [my_sum, my_sum_502, tot_503]
  have h : v3_fast 502 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_504 : my_sum 504 = 428 := by
  rw [my_sum, my_sum_503, tot_504]
  have h : v3_fast 144 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_505 : my_sum 505 = 428 := by
  rw [my_sum, my_sum_504, tot_505]
  have h : v3_fast 400 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_506 : my_sum 506 = 428 := by
  rw [my_sum, my_sum_505, tot_506]
  have h : v3_fast 220 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_507 : my_sum 507 = 429 := by
  rw [my_sum, my_sum_506, tot_507]
  have h : v3_fast 312 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_508 : my_sum 508 = 431 := by
  rw [my_sum, my_sum_507, tot_508]
  have h : v3_fast 252 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_509 : my_sum 509 = 431 := by
  rw [my_sum, my_sum_508, tot_509]
  have h : v3_fast 508 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_510 : my_sum 510 = 431 := by
  rw [my_sum, my_sum_509, tot_510]
  have h : v3_fast 128 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_511 : my_sum 511 = 434 := by
  rw [my_sum, my_sum_510, tot_511]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_512 : my_sum 512 = 434 := by
  rw [my_sum, my_sum_511, tot_512]
  have h : v3_fast 256 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_513 : my_sum 513 = 438 := by
  rw [my_sum, my_sum_512, tot_513]
  have h : v3_fast 324 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_514 : my_sum 514 = 438 := by
  rw [my_sum, my_sum_513, tot_514]
  have h : v3_fast 256 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_515 : my_sum 515 = 439 := by
  rw [my_sum, my_sum_514, tot_515]
  have h : v3_fast 408 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_516 : my_sum 516 = 440 := by
  rw [my_sum, my_sum_515, tot_516]
  have h : v3_fast 168 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_517 : my_sum 517 = 440 := by
  rw [my_sum, my_sum_516, tot_517]
  have h : v3_fast 460 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_518 : my_sum 518 = 443 := by
  rw [my_sum, my_sum_517, tot_518]
  have h : v3_fast 216 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_519 : my_sum 519 = 443 := by
  rw [my_sum, my_sum_518, tot_519]
  have h : v3_fast 344 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_520 : my_sum 520 = 444 := by
  rw [my_sum, my_sum_519, tot_520]
  have h : v3_fast 192 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_521 : my_sum 521 = 444 := by
  rw [my_sum, my_sum_520, tot_521]
  have h : v3_fast 520 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_522 : my_sum 522 = 445 := by
  rw [my_sum, my_sum_521, tot_522]
  have h : v3_fast 168 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_523 : my_sum 523 = 447 := by
  rw [my_sum, my_sum_522, tot_523]
  have h : v3_fast 522 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_524 : my_sum 524 = 447 := by
  rw [my_sum, my_sum_523, tot_524]
  have h : v3_fast 260 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_525 : my_sum 525 = 448 := by
  rw [my_sum, my_sum_524, tot_525]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_526 : my_sum 526 = 448 := by
  rw [my_sum, my_sum_525, tot_526]
  have h : v3_fast 262 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_527 : my_sum 527 = 449 := by
  rw [my_sum, my_sum_526, tot_527]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_528 : my_sum 528 = 449 := by
  rw [my_sum, my_sum_527, tot_528]
  have h : v3_fast 160 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_529 : my_sum 529 = 449 := by
  rw [my_sum, my_sum_528, tot_529]
  have h : v3_fast 506 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_530 : my_sum 530 = 449 := by
  rw [my_sum, my_sum_529, tot_530]
  have h : v3_fast 208 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_531 : my_sum 531 = 450 := by
  rw [my_sum, my_sum_530, tot_531]
  have h : v3_fast 348 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_532 : my_sum 532 = 453 := by
  rw [my_sum, my_sum_531, tot_532]
  have h : v3_fast 216 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_533 : my_sum 533 = 454 := by
  rw [my_sum, my_sum_532, tot_533]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_534 : my_sum 534 = 454 := by
  rw [my_sum, my_sum_533, tot_534]
  have h : v3_fast 176 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_535 : my_sum 535 = 454 := by
  rw [my_sum, my_sum_534, tot_535]
  have h : v3_fast 424 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_536 : my_sum 536 = 455 := by
  rw [my_sum, my_sum_535, tot_536]
  have h : v3_fast 264 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_537 : my_sum 537 = 455 := by
  rw [my_sum, my_sum_536, tot_537]
  have h : v3_fast 356 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_538 : my_sum 538 = 455 := by
  rw [my_sum, my_sum_537, tot_538]
  have h : v3_fast 268 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_539 : my_sum 539 = 456 := by
  rw [my_sum, my_sum_538, tot_539]
  have h : v3_fast 420 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_540 : my_sum 540 = 458 := by
  rw [my_sum, my_sum_539, tot_540]
  have h : v3_fast 144 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_541 : my_sum 541 = 461 := by
  rw [my_sum, my_sum_540, tot_541]
  have h : v3_fast 540 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_542 : my_sum 542 = 464 := by
  rw [my_sum, my_sum_541, tot_542]
  have h : v3_fast 270 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_543 : my_sum 543 = 466 := by
  rw [my_sum, my_sum_542, tot_543]
  have h : v3_fast 360 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_544 : my_sum 544 = 466 := by
  rw [my_sum, my_sum_543, tot_544]
  have h : v3_fast 256 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_545 : my_sum 545 = 469 := by
  rw [my_sum, my_sum_544, tot_545]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_546 : my_sum 546 = 471 := by
  rw [my_sum, my_sum_545, tot_546]
  have h : v3_fast 144 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_547 : my_sum 547 = 472 := by
  rw [my_sum, my_sum_546, tot_547]
  have h : v3_fast 546 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_548 : my_sum 548 = 472 := by
  rw [my_sum, my_sum_547, tot_548]
  have h : v3_fast 272 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_549 : my_sum 549 = 474 := by
  rw [my_sum, my_sum_548, tot_549]
  have h : v3_fast 360 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_550 : my_sum 550 = 474 := by
  rw [my_sum, my_sum_549, tot_550]
  have h : v3_fast 200 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_551 : my_sum 551 = 476 := by
  rw [my_sum, my_sum_550, tot_551]
  have h : v3_fast 504 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_552 : my_sum 552 = 476 := by
  rw [my_sum, my_sum_551, tot_552]
  have h : v3_fast 176 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_553 : my_sum 553 = 478 := by
  rw [my_sum, my_sum_552, tot_553]
  have h : v3_fast 468 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_554 : my_sum 554 = 479 := by
  rw [my_sum, my_sum_553, tot_554]
  have h : v3_fast 276 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_555 : my_sum 555 = 481 := by
  rw [my_sum, my_sum_554, tot_555]
  have h : v3_fast 288 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_556 : my_sum 556 = 482 := by
  rw [my_sum, my_sum_555, tot_556]
  have h : v3_fast 276 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_557 : my_sum 557 = 482 := by
  rw [my_sum, my_sum_556, tot_557]
  have h : v3_fast 556 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_558 : my_sum 558 = 484 := by
  rw [my_sum, my_sum_557, tot_558]
  have h : v3_fast 180 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_559 : my_sum 559 = 486 := by
  rw [my_sum, my_sum_558, tot_559]
  have h : v3_fast 504 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_560 : my_sum 560 = 487 := by
  rw [my_sum, my_sum_559, tot_560]
  have h : v3_fast 192 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_561 : my_sum 561 = 487 := by
  rw [my_sum, my_sum_560, tot_561]
  have h : v3_fast 320 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_562 : my_sum 562 = 487 := by
  rw [my_sum, my_sum_561, tot_562]
  have h : v3_fast 280 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_563 : my_sum 563 = 487 := by
  rw [my_sum, my_sum_562, tot_563]
  have h : v3_fast 562 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_564 : my_sum 564 = 487 := by
  rw [my_sum, my_sum_563, tot_564]
  have h : v3_fast 184 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_565 : my_sum 565 = 487 := by
  rw [my_sum, my_sum_564, tot_565]
  have h : v3_fast 448 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_566 : my_sum 566 = 488 := by
  rw [my_sum, my_sum_565, tot_566]
  have h : v3_fast 282 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_567 : my_sum 567 = 492 := by
  rw [my_sum, my_sum_566, tot_567]
  have h : v3_fast 324 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_568 : my_sum 568 = 492 := by
  rw [my_sum, my_sum_567, tot_568]
  have h : v3_fast 280 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_569 : my_sum 569 = 492 := by
  rw [my_sum, my_sum_568, tot_569]
  have h : v3_fast 568 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_570 : my_sum 570 = 494 := by
  rw [my_sum, my_sum_569, tot_570]
  have h : v3_fast 144 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_571 : my_sum 571 = 495 := by
  rw [my_sum, my_sum_570, tot_571]
  have h : v3_fast 570 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_572 : my_sum 572 = 496 := by
  rw [my_sum, my_sum_571, tot_572]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_573 : my_sum 573 = 496 := by
  rw [my_sum, my_sum_572, tot_573]
  have h : v3_fast 380 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_574 : my_sum 574 = 497 := by
  rw [my_sum, my_sum_573, tot_574]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_575 : my_sum 575 = 497 := by
  rw [my_sum, my_sum_574, tot_575]
  have h : v3_fast 440 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_576 : my_sum 576 = 498 := by
  rw [my_sum, my_sum_575, tot_576]
  have h : v3_fast 192 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_577 : my_sum 577 = 500 := by
  rw [my_sum, my_sum_576, tot_577]
  have h : v3_fast 576 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_578 : my_sum 578 = 500 := by
  rw [my_sum, my_sum_577, tot_578]
  have h : v3_fast 272 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_579 : my_sum 579 = 501 := by
  rw [my_sum, my_sum_578, tot_579]
  have h : v3_fast 384 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_580 : my_sum 580 = 501 := by
  rw [my_sum, my_sum_579, tot_580]
  have h : v3_fast 224 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_581 : my_sum 581 = 502 := by
  rw [my_sum, my_sum_580, tot_581]
  have h : v3_fast 492 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_582 : my_sum 582 = 503 := by
  rw [my_sum, my_sum_581, tot_582]
  have h : v3_fast 192 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_583 : my_sum 583 = 503 := by
  rw [my_sum, my_sum_582, tot_583]
  have h : v3_fast 520 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_584 : my_sum 584 = 505 := by
  rw [my_sum, my_sum_583, tot_584]
  have h : v3_fast 288 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_585 : my_sum 585 = 507 := by
  rw [my_sum, my_sum_584, tot_585]
  have h : v3_fast 288 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_586 : my_sum 586 = 507 := by
  rw [my_sum, my_sum_585, tot_586]
  have h : v3_fast 292 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_587 : my_sum 587 = 507 := by
  rw [my_sum, my_sum_586, tot_587]
  have h : v3_fast 586 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_588 : my_sum 588 = 508 := by
  rw [my_sum, my_sum_587, tot_588]
  have h : v3_fast 168 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_589 : my_sum 589 = 511 := by
  rw [my_sum, my_sum_588, tot_589]
  have h : v3_fast 540 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_590 : my_sum 590 = 511 := by
  rw [my_sum, my_sum_589, tot_590]
  have h : v3_fast 232 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_591 : my_sum 591 = 511 := by
  rw [my_sum, my_sum_590, tot_591]
  have h : v3_fast 392 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_592 : my_sum 592 = 513 := by
  rw [my_sum, my_sum_591, tot_592]
  have h : v3_fast 288 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_593 : my_sum 593 = 513 := by
  rw [my_sum, my_sum_592, tot_593]
  have h : v3_fast 592 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_594 : my_sum 594 = 515 := by
  rw [my_sum, my_sum_593, tot_594]
  have h : v3_fast 180 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_595 : my_sum 595 = 516 := by
  rw [my_sum, my_sum_594, tot_595]
  have h : v3_fast 384 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_596 : my_sum 596 = 516 := by
  rw [my_sum, my_sum_595, tot_596]
  have h : v3_fast 296 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_597 : my_sum 597 = 518 := by
  rw [my_sum, my_sum_596, tot_597]
  have h : v3_fast 396 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_598 : my_sum 598 = 519 := by
  rw [my_sum, my_sum_597, tot_598]
  have h : v3_fast 264 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_599 : my_sum 599 = 519 := by
  rw [my_sum, my_sum_598, tot_599]
  have h : v3_fast 598 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_600 : my_sum 600 = 519 := by
  rw [my_sum, my_sum_599, tot_600]
  have h : v3_fast 160 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_601 : my_sum 601 = 520 := by
  rw [my_sum, my_sum_600, tot_601]
  have h : v3_fast 600 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_602 : my_sum 602 = 522 := by
  rw [my_sum, my_sum_601, tot_602]
  have h : v3_fast 252 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_603 : my_sum 603 = 524 := by
  rw [my_sum, my_sum_602, tot_603]
  have h : v3_fast 396 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_604 : my_sum 604 = 525 := by
  rw [my_sum, my_sum_603, tot_604]
  have h : v3_fast 300 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_605 : my_sum 605 = 525 := by
  rw [my_sum, my_sum_604, tot_605]
  have h : v3_fast 440 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_606 : my_sum 606 = 525 := by
  rw [my_sum, my_sum_605, tot_606]
  have h : v3_fast 200 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_607 : my_sum 607 = 526 := by
  rw [my_sum, my_sum_606, tot_607]
  have h : v3_fast 606 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_608 : my_sum 608 = 528 := by
  rw [my_sum, my_sum_607, tot_608]
  have h : v3_fast 288 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_609 : my_sum 609 = 529 := by
  rw [my_sum, my_sum_608, tot_609]
  have h : v3_fast 336 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_610 : my_sum 610 = 530 := by
  rw [my_sum, my_sum_609, tot_610]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_611 : my_sum 611 = 531 := by
  rw [my_sum, my_sum_610, tot_611]
  have h : v3_fast 552 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_612 : my_sum 612 = 532 := by
  rw [my_sum, my_sum_611, tot_612]
  have h : v3_fast 192 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_613 : my_sum 613 = 534 := by
  rw [my_sum, my_sum_612, tot_613]
  have h : v3_fast 612 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_614 : my_sum 614 = 536 := by
  rw [my_sum, my_sum_613, tot_614]
  have h : v3_fast 306 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_615 : my_sum 615 = 536 := by
  rw [my_sum, my_sum_614, tot_615]
  have h : v3_fast 320 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_616 : my_sum 616 = 537 := by
  rw [my_sum, my_sum_615, tot_616]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_617 : my_sum 617 = 537 := by
  rw [my_sum, my_sum_616, tot_617]
  have h : v3_fast 616 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_618 : my_sum 618 = 538 := by
  rw [my_sum, my_sum_617, tot_618]
  have h : v3_fast 204 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_619 : my_sum 619 = 539 := by
  rw [my_sum, my_sum_618, tot_619]
  have h : v3_fast 618 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_620 : my_sum 620 = 540 := by
  rw [my_sum, my_sum_619, tot_620]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_621 : my_sum 621 = 542 := by
  rw [my_sum, my_sum_620, tot_621]
  have h : v3_fast 396 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_622 : my_sum 622 = 542 := by
  rw [my_sum, my_sum_621, tot_622]
  have h : v3_fast 310 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_623 : my_sum 623 = 543 := by
  rw [my_sum, my_sum_622, tot_623]
  have h : v3_fast 528 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_624 : my_sum 624 = 544 := by
  rw [my_sum, my_sum_623, tot_624]
  have h : v3_fast 192 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_625 : my_sum 625 = 544 := by
  rw [my_sum, my_sum_624, tot_625]
  have h : v3_fast 500 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_626 : my_sum 626 = 545 := by
  rw [my_sum, my_sum_625, tot_626]
  have h : v3_fast 312 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_627 : my_sum 627 = 547 := by
  rw [my_sum, my_sum_626, tot_627]
  have h : v3_fast 360 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_628 : my_sum 628 = 548 := by
  rw [my_sum, my_sum_627, tot_628]
  have h : v3_fast 312 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_629 : my_sum 629 = 550 := by
  rw [my_sum, my_sum_628, tot_629]
  have h : v3_fast 576 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_630 : my_sum 630 = 552 := by
  rw [my_sum, my_sum_629, tot_630]
  have h : v3_fast 144 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_631 : my_sum 631 = 554 := by
  rw [my_sum, my_sum_630, tot_631]
  have h : v3_fast 630 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_632 : my_sum 632 = 555 := by
  rw [my_sum, my_sum_631, tot_632]
  have h : v3_fast 312 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_633 : my_sum 633 = 556 := by
  rw [my_sum, my_sum_632, tot_633]
  have h : v3_fast 420 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_634 : my_sum 634 = 556 := by
  rw [my_sum, my_sum_633, tot_634]
  have h : v3_fast 316 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_635 : my_sum 635 = 558 := by
  rw [my_sum, my_sum_634, tot_635]
  have h : v3_fast 504 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_636 : my_sum 636 = 558 := by
  rw [my_sum, my_sum_635, tot_636]
  have h : v3_fast 208 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_637 : my_sum 637 = 560 := by
  rw [my_sum, my_sum_636, tot_637]
  have h : v3_fast 504 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_638 : my_sum 638 = 560 := by
  rw [my_sum, my_sum_637, tot_638]
  have h : v3_fast 280 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_639 : my_sum 639 = 561 := by
  rw [my_sum, my_sum_638, tot_639]
  have h : v3_fast 420 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_640 : my_sum 640 = 561 := by
  rw [my_sum, my_sum_639, tot_640]
  have h : v3_fast 256 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_641 : my_sum 641 = 561 := by
  rw [my_sum, my_sum_640, tot_641]
  have h : v3_fast 640 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_642 : my_sum 642 = 561 := by
  rw [my_sum, my_sum_641, tot_642]
  have h : v3_fast 212 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_643 : my_sum 643 = 562 := by
  rw [my_sum, my_sum_642, tot_643]
  have h : v3_fast 642 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_644 : my_sum 644 = 563 := by
  rw [my_sum, my_sum_643, tot_644]
  have h : v3_fast 264 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_645 : my_sum 645 = 564 := by
  rw [my_sum, my_sum_644, tot_645]
  have h : v3_fast 336 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_646 : my_sum 646 = 566 := by
  rw [my_sum, my_sum_645, tot_646]
  have h : v3_fast 288 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_647 : my_sum 647 = 566 := by
  rw [my_sum, my_sum_646, tot_647]
  have h : v3_fast 646 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_648 : my_sum 648 = 569 := by
  rw [my_sum, my_sum_647, tot_648]
  have h : v3_fast 216 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_649 : my_sum 649 = 569 := by
  rw [my_sum, my_sum_648, tot_649]
  have h : v3_fast 580 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_650 : my_sum 650 = 570 := by
  rw [my_sum, my_sum_649, tot_650]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_651 : my_sum 651 = 572 := by
  rw [my_sum, my_sum_650, tot_651]
  have h : v3_fast 360 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_652 : my_sum 652 = 576 := by
  rw [my_sum, my_sum_651, tot_652]
  have h : v3_fast 324 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_653 : my_sum 653 = 576 := by
  rw [my_sum, my_sum_652, tot_653]
  have h : v3_fast 652 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_654 : my_sum 654 = 579 := by
  rw [my_sum, my_sum_653, tot_654]
  have h : v3_fast 216 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_655 : my_sum 655 = 579 := by
  rw [my_sum, my_sum_654, tot_655]
  have h : v3_fast 520 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_656 : my_sum 656 = 579 := by
  rw [my_sum, my_sum_655, tot_656]
  have h : v3_fast 320 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_657 : my_sum 657 = 582 := by
  rw [my_sum, my_sum_656, tot_657]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_658 : my_sum 658 = 583 := by
  rw [my_sum, my_sum_657, tot_658]
  have h : v3_fast 276 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_659 : my_sum 659 = 583 := by
  rw [my_sum, my_sum_658, tot_659]
  have h : v3_fast 658 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_660 : my_sum 660 = 583 := by
  rw [my_sum, my_sum_659, tot_660]
  have h : v3_fast 160 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_661 : my_sum 661 = 584 := by
  rw [my_sum, my_sum_660, tot_661]
  have h : v3_fast 660 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_662 : my_sum 662 = 585 := by
  rw [my_sum, my_sum_661, tot_662]
  have h : v3_fast 330 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_663 : my_sum 663 = 586 := by
  rw [my_sum, my_sum_662, tot_663]
  have h : v3_fast 384 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_664 : my_sum 664 = 586 := by
  rw [my_sum, my_sum_663, tot_664]
  have h : v3_fast 328 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_665 : my_sum 665 = 589 := by
  rw [my_sum, my_sum_664, tot_665]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_666 : my_sum 666 = 592 := by
  rw [my_sum, my_sum_665, tot_666]
  have h : v3_fast 216 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_667 : my_sum 667 = 592 := by
  rw [my_sum, my_sum_666, tot_667]
  have h : v3_fast 616 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_668 : my_sum 668 = 592 := by
  rw [my_sum, my_sum_667, tot_668]
  have h : v3_fast 332 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_669 : my_sum 669 = 593 := by
  rw [my_sum, my_sum_668, tot_669]
  have h : v3_fast 444 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_670 : my_sum 670 = 594 := by
  rw [my_sum, my_sum_669, tot_670]
  have h : v3_fast 264 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_671 : my_sum 671 = 595 := by
  rw [my_sum, my_sum_670, tot_671]
  have h : v3_fast 600 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_672 : my_sum 672 = 596 := by
  rw [my_sum, my_sum_671, tot_672]
  have h : v3_fast 192 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_673 : my_sum 673 = 597 := by
  rw [my_sum, my_sum_672, tot_673]
  have h : v3_fast 672 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_674 : my_sum 674 = 598 := by
  rw [my_sum, my_sum_673, tot_674]
  have h : v3_fast 336 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_675 : my_sum 675 = 600 := by
  rw [my_sum, my_sum_674, tot_675]
  have h : v3_fast 360 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_676 : my_sum 676 = 601 := by
  rw [my_sum, my_sum_675, tot_676]
  have h : v3_fast 312 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_677 : my_sum 677 = 601 := by
  rw [my_sum, my_sum_676, tot_677]
  have h : v3_fast 676 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_678 : my_sum 678 = 601 := by
  rw [my_sum, my_sum_677, tot_678]
  have h : v3_fast 224 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_679 : my_sum 679 = 603 := by
  rw [my_sum, my_sum_678, tot_679]
  have h : v3_fast 576 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_680 : my_sum 680 = 603 := by
  rw [my_sum, my_sum_679, tot_680]
  have h : v3_fast 256 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_681 : my_sum 681 = 603 := by
  rw [my_sum, my_sum_680, tot_681]
  have h : v3_fast 452 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_682 : my_sum 682 = 604 := by
  rw [my_sum, my_sum_681, tot_682]
  have h : v3_fast 300 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_683 : my_sum 683 = 604 := by
  rw [my_sum, my_sum_682, tot_683]
  have h : v3_fast 682 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_684 : my_sum 684 = 607 := by
  rw [my_sum, my_sum_683, tot_684]
  have h : v3_fast 216 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_685 : my_sum 685 = 607 := by
  rw [my_sum, my_sum_684, tot_685]
  have h : v3_fast 544 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_686 : my_sum 686 = 608 := by
  rw [my_sum, my_sum_685, tot_686]
  have h : v3_fast 294 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_687 : my_sum 687 = 609 := by
  rw [my_sum, my_sum_686, tot_687]
  have h : v3_fast 456 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_688 : my_sum 688 = 610 := by
  rw [my_sum, my_sum_687, tot_688]
  have h : v3_fast 336 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_689 : my_sum 689 = 611 := by
  rw [my_sum, my_sum_688, tot_689]
  have h : v3_fast 624 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_690 : my_sum 690 = 611 := by
  rw [my_sum, my_sum_689, tot_690]
  have h : v3_fast 176 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_691 : my_sum 691 = 612 := by
  rw [my_sum, my_sum_690, tot_691]
  have h : v3_fast 690 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_692 : my_sum 692 = 612 := by
  rw [my_sum, my_sum_691, tot_692]
  have h : v3_fast 344 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_693 : my_sum 693 = 614 := by
  rw [my_sum, my_sum_692, tot_693]
  have h : v3_fast 360 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_694 : my_sum 694 = 614 := by
  rw [my_sum, my_sum_693, tot_694]
  have h : v3_fast 346 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_695 : my_sum 695 = 615 := by
  rw [my_sum, my_sum_694, tot_695]
  have h : v3_fast 552 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_696 : my_sum 696 = 615 := by
  rw [my_sum, my_sum_695, tot_696]
  have h : v3_fast 224 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_697 : my_sum 697 = 615 := by
  rw [my_sum, my_sum_696, tot_697]
  have h : v3_fast 640 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_698 : my_sum 698 = 616 := by
  rw [my_sum, my_sum_697, tot_698]
  have h : v3_fast 348 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_699 : my_sum 699 = 616 := by
  rw [my_sum, my_sum_698, tot_699]
  have h : v3_fast 464 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_700 : my_sum 700 = 617 := by
  rw [my_sum, my_sum_699, tot_700]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_701 : my_sum 701 = 617 := by
  rw [my_sum, my_sum_700, tot_701]
  have h : v3_fast 700 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_702 : my_sum 702 = 620 := by
  rw [my_sum, my_sum_701, tot_702]
  have h : v3_fast 216 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_703 : my_sum 703 = 624 := by
  rw [my_sum, my_sum_702, tot_703]
  have h : v3_fast 648 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_704 : my_sum 704 = 624 := by
  rw [my_sum, my_sum_703, tot_704]
  have h : v3_fast 320 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_705 : my_sum 705 = 624 := by
  rw [my_sum, my_sum_704, tot_705]
  have h : v3_fast 368 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_706 : my_sum 706 = 624 := by
  rw [my_sum, my_sum_705, tot_706]
  have h : v3_fast 352 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_707 : my_sum 707 = 625 := by
  rw [my_sum, my_sum_706, tot_707]
  have h : v3_fast 600 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_708 : my_sum 708 = 625 := by
  rw [my_sum, my_sum_707, tot_708]
  have h : v3_fast 232 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_709 : my_sum 709 = 626 := by
  rw [my_sum, my_sum_708, tot_709]
  have h : v3_fast 708 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_710 : my_sum 710 = 626 := by
  rw [my_sum, my_sum_709, tot_710]
  have h : v3_fast 280 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_711 : my_sum 711 = 628 := by
  rw [my_sum, my_sum_710, tot_711]
  have h : v3_fast 468 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_712 : my_sum 712 = 628 := by
  rw [my_sum, my_sum_711, tot_712]
  have h : v3_fast 352 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_713 : my_sum 713 = 629 := by
  rw [my_sum, my_sum_712, tot_713]
  have h : v3_fast 660 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_714 : my_sum 714 = 630 := by
  rw [my_sum, my_sum_713, tot_714]
  have h : v3_fast 192 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_715 : my_sum 715 = 631 := by
  rw [my_sum, my_sum_714, tot_715]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_716 : my_sum 716 = 631 := by
  rw [my_sum, my_sum_715, tot_716]
  have h : v3_fast 356 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_717 : my_sum 717 = 631 := by
  rw [my_sum, my_sum_716, tot_717]
  have h : v3_fast 476 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_718 : my_sum 718 = 631 := by
  rw [my_sum, my_sum_717, tot_718]
  have h : v3_fast 358 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_719 : my_sum 719 = 631 := by
  rw [my_sum, my_sum_718, tot_719]
  have h : v3_fast 718 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_720 : my_sum 720 = 632 := by
  rw [my_sum, my_sum_719, tot_720]
  have h : v3_fast 192 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_721 : my_sum 721 = 634 := by
  rw [my_sum, my_sum_720, tot_721]
  have h : v3_fast 612 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_722 : my_sum 722 = 636 := by
  rw [my_sum, my_sum_721, tot_722]
  have h : v3_fast 342 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_723 : my_sum 723 = 637 := by
  rw [my_sum, my_sum_722, tot_723]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_724 : my_sum 724 = 639 := by
  rw [my_sum, my_sum_723, tot_724]
  have h : v3_fast 360 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_725 : my_sum 725 = 639 := by
  rw [my_sum, my_sum_724, tot_725]
  have h : v3_fast 560 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_726 : my_sum 726 = 639 := by
  rw [my_sum, my_sum_725, tot_726]
  have h : v3_fast 220 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_727 : my_sum 727 = 640 := by
  rw [my_sum, my_sum_726, tot_727]
  have h : v3_fast 726 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_728 : my_sum 728 = 642 := by
  rw [my_sum, my_sum_727, tot_728]
  have h : v3_fast 288 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_729 : my_sum 729 = 647 := by
  rw [my_sum, my_sum_728, tot_729]
  have h : v3_fast 486 100 = 5 := rfl
  rw [h] <;> decide

theorem my_sum_730 : my_sum 730 = 649 := by
  rw [my_sum, my_sum_729, tot_730]
  have h : v3_fast 288 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_731 : my_sum 731 = 650 := by
  rw [my_sum, my_sum_730, tot_731]
  have h : v3_fast 672 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_732 : my_sum 732 = 651 := by
  rw [my_sum, my_sum_731, tot_732]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_733 : my_sum 733 = 652 := by
  rw [my_sum, my_sum_732, tot_733]
  have h : v3_fast 732 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_734 : my_sum 734 = 653 := by
  rw [my_sum, my_sum_733, tot_734]
  have h : v3_fast 366 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_735 : my_sum 735 = 654 := by
  rw [my_sum, my_sum_734, tot_735]
  have h : v3_fast 336 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_736 : my_sum 736 = 654 := by
  rw [my_sum, my_sum_735, tot_736]
  have h : v3_fast 352 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_737 : my_sum 737 = 655 := by
  rw [my_sum, my_sum_736, tot_737]
  have h : v3_fast 660 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_738 : my_sum 738 = 656 := by
  rw [my_sum, my_sum_737, tot_738]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_739 : my_sum 739 = 658 := by
  rw [my_sum, my_sum_738, tot_739]
  have h : v3_fast 738 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_740 : my_sum 740 = 660 := by
  rw [my_sum, my_sum_739, tot_740]
  have h : v3_fast 288 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_741 : my_sum 741 = 663 := by
  rw [my_sum, my_sum_740, tot_741]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_742 : my_sum 742 = 664 := by
  rw [my_sum, my_sum_741, tot_742]
  have h : v3_fast 312 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_743 : my_sum 743 = 664 := by
  rw [my_sum, my_sum_742, tot_743]
  have h : v3_fast 742 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_744 : my_sum 744 = 665 := by
  rw [my_sum, my_sum_743, tot_744]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_745 : my_sum 745 = 665 := by
  rw [my_sum, my_sum_744, tot_745]
  have h : v3_fast 592 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_746 : my_sum 746 = 666 := by
  rw [my_sum, my_sum_745, tot_746]
  have h : v3_fast 372 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_747 : my_sum 747 = 667 := by
  rw [my_sum, my_sum_746, tot_747]
  have h : v3_fast 492 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_748 : my_sum 748 = 667 := by
  rw [my_sum, my_sum_747, tot_748]
  have h : v3_fast 320 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_749 : my_sum 749 = 668 := by
  rw [my_sum, my_sum_748, tot_749]
  have h : v3_fast 636 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_750 : my_sum 750 = 668 := by
  rw [my_sum, my_sum_749, tot_750]
  have h : v3_fast 200 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_751 : my_sum 751 = 669 := by
  rw [my_sum, my_sum_750, tot_751]
  have h : v3_fast 750 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_752 : my_sum 752 = 669 := by
  rw [my_sum, my_sum_751, tot_752]
  have h : v3_fast 368 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_753 : my_sum 753 = 669 := by
  rw [my_sum, my_sum_752, tot_753]
  have h : v3_fast 500 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_754 : my_sum 754 = 670 := by
  rw [my_sum, my_sum_753, tot_754]
  have h : v3_fast 336 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_755 : my_sum 755 = 671 := by
  rw [my_sum, my_sum_754, tot_755]
  have h : v3_fast 600 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_756 : my_sum 756 = 674 := by
  rw [my_sum, my_sum_755, tot_756]
  have h : v3_fast 216 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_757 : my_sum 757 = 677 := by
  rw [my_sum, my_sum_756, tot_757]
  have h : v3_fast 756 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_758 : my_sum 758 = 680 := by
  rw [my_sum, my_sum_757, tot_758]
  have h : v3_fast 378 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_759 : my_sum 759 = 680 := by
  rw [my_sum, my_sum_758, tot_759]
  have h : v3_fast 440 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_760 : my_sum 760 = 682 := by
  rw [my_sum, my_sum_759, tot_760]
  have h : v3_fast 288 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_761 : my_sum 761 = 682 := by
  rw [my_sum, my_sum_760, tot_761]
  have h : v3_fast 760 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_762 : my_sum 762 = 684 := by
  rw [my_sum, my_sum_761, tot_762]
  have h : v3_fast 252 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_763 : my_sum 763 = 688 := by
  rw [my_sum, my_sum_762, tot_763]
  have h : v3_fast 648 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_764 : my_sum 764 = 688 := by
  rw [my_sum, my_sum_763, tot_764]
  have h : v3_fast 380 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_765 : my_sum 765 = 689 := by
  rw [my_sum, my_sum_764, tot_765]
  have h : v3_fast 384 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_766 : my_sum 766 = 689 := by
  rw [my_sum, my_sum_765, tot_766]
  have h : v3_fast 382 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_767 : my_sum 767 = 690 := by
  rw [my_sum, my_sum_766, tot_767]
  have h : v3_fast 696 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_768 : my_sum 768 = 690 := by
  rw [my_sum, my_sum_767, tot_768]
  have h : v3_fast 256 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_769 : my_sum 769 = 691 := by
  rw [my_sum, my_sum_768, tot_769]
  have h : v3_fast 768 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_770 : my_sum 770 = 692 := by
  rw [my_sum, my_sum_769, tot_770]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_771 : my_sum 771 = 692 := by
  rw [my_sum, my_sum_770, tot_771]
  have h : v3_fast 512 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_772 : my_sum 772 = 693 := by
  rw [my_sum, my_sum_771, tot_772]
  have h : v3_fast 384 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_773 : my_sum 773 = 693 := by
  rw [my_sum, my_sum_772, tot_773]
  have h : v3_fast 772 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_774 : my_sum 774 = 695 := by
  rw [my_sum, my_sum_773, tot_774]
  have h : v3_fast 252 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_775 : my_sum 775 = 696 := by
  rw [my_sum, my_sum_774, tot_775]
  have h : v3_fast 600 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_776 : my_sum 776 = 697 := by
  rw [my_sum, my_sum_775, tot_776]
  have h : v3_fast 384 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_777 : my_sum 777 = 700 := by
  rw [my_sum, my_sum_776, tot_777]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_778 : my_sum 778 = 700 := by
  rw [my_sum, my_sum_777, tot_778]
  have h : v3_fast 388 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_779 : my_sum 779 = 702 := by
  rw [my_sum, my_sum_778, tot_779]
  have h : v3_fast 720 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_780 : my_sum 780 = 703 := by
  rw [my_sum, my_sum_779, tot_780]
  have h : v3_fast 192 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_781 : my_sum 781 = 703 := by
  rw [my_sum, my_sum_780, tot_781]
  have h : v3_fast 700 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_782 : my_sum 782 = 703 := by
  rw [my_sum, my_sum_781, tot_782]
  have h : v3_fast 352 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_783 : my_sum 783 = 705 := by
  rw [my_sum, my_sum_782, tot_783]
  have h : v3_fast 504 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_784 : my_sum 784 = 706 := by
  rw [my_sum, my_sum_783, tot_784]
  have h : v3_fast 336 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_785 : my_sum 785 = 707 := by
  rw [my_sum, my_sum_784, tot_785]
  have h : v3_fast 624 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_786 : my_sum 786 = 707 := by
  rw [my_sum, my_sum_785, tot_786]
  have h : v3_fast 260 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_787 : my_sum 787 = 708 := by
  rw [my_sum, my_sum_786, tot_787]
  have h : v3_fast 786 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_788 : my_sum 788 = 708 := by
  rw [my_sum, my_sum_787, tot_788]
  have h : v3_fast 392 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_789 : my_sum 789 = 708 := by
  rw [my_sum, my_sum_788, tot_789]
  have h : v3_fast 524 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_790 : my_sum 790 = 709 := by
  rw [my_sum, my_sum_789, tot_790]
  have h : v3_fast 312 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_791 : my_sum 791 = 710 := by
  rw [my_sum, my_sum_790, tot_791]
  have h : v3_fast 672 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_792 : my_sum 792 = 711 := by
  rw [my_sum, my_sum_791, tot_792]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_793 : my_sum 793 = 713 := by
  rw [my_sum, my_sum_792, tot_793]
  have h : v3_fast 720 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_794 : my_sum 794 = 715 := by
  rw [my_sum, my_sum_793, tot_794]
  have h : v3_fast 396 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_795 : my_sum 795 = 715 := by
  rw [my_sum, my_sum_794, tot_795]
  have h : v3_fast 416 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_796 : my_sum 796 = 717 := by
  rw [my_sum, my_sum_795, tot_796]
  have h : v3_fast 396 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_797 : my_sum 797 = 717 := by
  rw [my_sum, my_sum_796, tot_797]
  have h : v3_fast 796 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_798 : my_sum 798 = 720 := by
  rw [my_sum, my_sum_797, tot_798]
  have h : v3_fast 216 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_799 : my_sum 799 = 720 := by
  rw [my_sum, my_sum_798, tot_799]
  have h : v3_fast 736 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_800 : my_sum 800 = 720 := by
  rw [my_sum, my_sum_799, tot_800]
  have h : v3_fast 320 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_801 : my_sum 801 = 721 := by
  rw [my_sum, my_sum_800, tot_801]
  have h : v3_fast 528 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_802 : my_sum 802 = 721 := by
  rw [my_sum, my_sum_801, tot_802]
  have h : v3_fast 400 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_803 : my_sum 803 = 723 := by
  rw [my_sum, my_sum_802, tot_803]
  have h : v3_fast 720 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_804 : my_sum 804 = 724 := by
  rw [my_sum, my_sum_803, tot_804]
  have h : v3_fast 264 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_805 : my_sum 805 = 725 := by
  rw [my_sum, my_sum_804, tot_805]
  have h : v3_fast 528 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_806 : my_sum 806 = 727 := by
  rw [my_sum, my_sum_805, tot_806]
  have h : v3_fast 360 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_807 : my_sum 807 = 727 := by
  rw [my_sum, my_sum_806, tot_807]
  have h : v3_fast 536 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_808 : my_sum 808 = 727 := by
  rw [my_sum, my_sum_807, tot_808]
  have h : v3_fast 400 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_809 : my_sum 809 = 727 := by
  rw [my_sum, my_sum_808, tot_809]
  have h : v3_fast 808 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_810 : my_sum 810 = 730 := by
  rw [my_sum, my_sum_809, tot_810]
  have h : v3_fast 216 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_811 : my_sum 811 = 734 := by
  rw [my_sum, my_sum_810, tot_811]
  have h : v3_fast 810 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_812 : my_sum 812 = 735 := by
  rw [my_sum, my_sum_811, tot_812]
  have h : v3_fast 336 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_813 : my_sum 813 = 738 := by
  rw [my_sum, my_sum_812, tot_813]
  have h : v3_fast 540 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_814 : my_sum 814 = 740 := by
  rw [my_sum, my_sum_813, tot_814]
  have h : v3_fast 360 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_815 : my_sum 815 = 744 := by
  rw [my_sum, my_sum_814, tot_815]
  have h : v3_fast 648 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_816 : my_sum 816 = 744 := by
  rw [my_sum, my_sum_815, tot_816]
  have h : v3_fast 256 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_817 : my_sum 817 = 747 := by
  rw [my_sum, my_sum_816, tot_817]
  have h : v3_fast 756 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_818 : my_sum 818 = 748 := by
  rw [my_sum, my_sum_817, tot_818]
  have h : v3_fast 408 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_819 : my_sum 819 = 751 := by
  rw [my_sum, my_sum_818, tot_819]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_820 : my_sum 820 = 751 := by
  rw [my_sum, my_sum_819, tot_820]
  have h : v3_fast 320 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_821 : my_sum 821 = 751 := by
  rw [my_sum, my_sum_820, tot_821]
  have h : v3_fast 820 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_822 : my_sum 822 = 751 := by
  rw [my_sum, my_sum_821, tot_822]
  have h : v3_fast 272 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_823 : my_sum 823 = 752 := by
  rw [my_sum, my_sum_822, tot_823]
  have h : v3_fast 822 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_824 : my_sum 824 = 753 := by
  rw [my_sum, my_sum_823, tot_824]
  have h : v3_fast 408 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_825 : my_sum 825 = 753 := by
  rw [my_sum, my_sum_824, tot_825]
  have h : v3_fast 400 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_826 : my_sum 826 = 754 := by
  rw [my_sum, my_sum_825, tot_826]
  have h : v3_fast 348 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_827 : my_sum 827 = 754 := by
  rw [my_sum, my_sum_826, tot_827]
  have h : v3_fast 826 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_828 : my_sum 828 = 755 := by
  rw [my_sum, my_sum_827, tot_828]
  have h : v3_fast 264 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_829 : my_sum 829 = 757 := by
  rw [my_sum, my_sum_828, tot_829]
  have h : v3_fast 828 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_830 : my_sum 830 = 757 := by
  rw [my_sum, my_sum_829, tot_830]
  have h : v3_fast 328 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_831 : my_sum 831 = 758 := by
  rw [my_sum, my_sum_830, tot_831]
  have h : v3_fast 552 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_832 : my_sum 832 = 759 := by
  rw [my_sum, my_sum_831, tot_832]
  have h : v3_fast 384 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_833 : my_sum 833 = 760 := by
  rw [my_sum, my_sum_832, tot_833]
  have h : v3_fast 672 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_834 : my_sum 834 = 761 := by
  rw [my_sum, my_sum_833, tot_834]
  have h : v3_fast 276 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_835 : my_sum 835 = 761 := by
  rw [my_sum, my_sum_834, tot_835]
  have h : v3_fast 664 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_836 : my_sum 836 = 763 := by
  rw [my_sum, my_sum_835, tot_836]
  have h : v3_fast 360 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_837 : my_sum 837 = 766 := by
  rw [my_sum, my_sum_836, tot_837]
  have h : v3_fast 540 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_838 : my_sum 838 = 766 := by
  rw [my_sum, my_sum_837, tot_838]
  have h : v3_fast 418 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_839 : my_sum 839 = 766 := by
  rw [my_sum, my_sum_838, tot_839]
  have h : v3_fast 838 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_840 : my_sum 840 = 767 := by
  rw [my_sum, my_sum_839, tot_840]
  have h : v3_fast 192 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_841 : my_sum 841 = 767 := by
  rw [my_sum, my_sum_840, tot_841]
  have h : v3_fast 812 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_842 : my_sum 842 = 768 := by
  rw [my_sum, my_sum_841, tot_842]
  have h : v3_fast 420 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_843 : my_sum 843 = 768 := by
  rw [my_sum, my_sum_842, tot_843]
  have h : v3_fast 560 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_844 : my_sum 844 = 769 := by
  rw [my_sum, my_sum_843, tot_844]
  have h : v3_fast 420 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_845 : my_sum 845 = 770 := by
  rw [my_sum, my_sum_844, tot_845]
  have h : v3_fast 624 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_846 : my_sum 846 = 771 := by
  rw [my_sum, my_sum_845, tot_846]
  have h : v3_fast 276 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_847 : my_sum 847 = 772 := by
  rw [my_sum, my_sum_846, tot_847]
  have h : v3_fast 660 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_848 : my_sum 848 = 772 := by
  rw [my_sum, my_sum_847, tot_848]
  have h : v3_fast 416 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_849 : my_sum 849 = 773 := by
  rw [my_sum, my_sum_848, tot_849]
  have h : v3_fast 564 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_850 : my_sum 850 = 773 := by
  rw [my_sum, my_sum_849, tot_850]
  have h : v3_fast 320 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_851 : my_sum 851 = 775 := by
  rw [my_sum, my_sum_850, tot_851]
  have h : v3_fast 792 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_852 : my_sum 852 = 775 := by
  rw [my_sum, my_sum_851, tot_852]
  have h : v3_fast 280 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_853 : my_sum 853 = 776 := by
  rw [my_sum, my_sum_852, tot_853]
  have h : v3_fast 852 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_854 : my_sum 854 = 778 := by
  rw [my_sum, my_sum_853, tot_854]
  have h : v3_fast 360 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_855 : my_sum 855 = 781 := by
  rw [my_sum, my_sum_854, tot_855]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_856 : my_sum 856 = 781 := by
  rw [my_sum, my_sum_855, tot_856]
  have h : v3_fast 424 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_857 : my_sum 857 = 781 := by
  rw [my_sum, my_sum_856, tot_857]
  have h : v3_fast 856 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_858 : my_sum 858 = 782 := by
  rw [my_sum, my_sum_857, tot_858]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_859 : my_sum 859 = 783 := by
  rw [my_sum, my_sum_858, tot_859]
  have h : v3_fast 858 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_860 : my_sum 860 = 784 := by
  rw [my_sum, my_sum_859, tot_860]
  have h : v3_fast 336 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_861 : my_sum 861 = 785 := by
  rw [my_sum, my_sum_860, tot_861]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_862 : my_sum 862 = 785 := by
  rw [my_sum, my_sum_861, tot_862]
  have h : v3_fast 430 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_863 : my_sum 863 = 785 := by
  rw [my_sum, my_sum_862, tot_863]
  have h : v3_fast 862 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_864 : my_sum 864 = 787 := by
  rw [my_sum, my_sum_863, tot_864]
  have h : v3_fast 288 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_865 : my_sum 865 = 787 := by
  rw [my_sum, my_sum_864, tot_865]
  have h : v3_fast 688 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_866 : my_sum 866 = 790 := by
  rw [my_sum, my_sum_865, tot_866]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_867 : my_sum 867 = 790 := by
  rw [my_sum, my_sum_866, tot_867]
  have h : v3_fast 544 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_868 : my_sum 868 = 792 := by
  rw [my_sum, my_sum_867, tot_868]
  have h : v3_fast 360 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_869 : my_sum 869 = 793 := by
  rw [my_sum, my_sum_868, tot_869]
  have h : v3_fast 780 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_870 : my_sum 870 = 793 := by
  rw [my_sum, my_sum_869, tot_870]
  have h : v3_fast 224 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_871 : my_sum 871 = 795 := by
  rw [my_sum, my_sum_870, tot_871]
  have h : v3_fast 792 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_872 : my_sum 872 = 798 := by
  rw [my_sum, my_sum_871, tot_872]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_873 : my_sum 873 = 800 := by
  rw [my_sum, my_sum_872, tot_873]
  have h : v3_fast 576 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_874 : my_sum 874 = 802 := by
  rw [my_sum, my_sum_873, tot_874]
  have h : v3_fast 396 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_875 : my_sum 875 = 803 := by
  rw [my_sum, my_sum_874, tot_875]
  have h : v3_fast 600 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_876 : my_sum 876 = 805 := by
  rw [my_sum, my_sum_875, tot_876]
  have h : v3_fast 288 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_877 : my_sum 877 = 806 := by
  rw [my_sum, my_sum_876, tot_877]
  have h : v3_fast 876 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_878 : my_sum 878 = 807 := by
  rw [my_sum, my_sum_877, tot_878]
  have h : v3_fast 438 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_879 : my_sum 879 = 807 := by
  rw [my_sum, my_sum_878, tot_879]
  have h : v3_fast 584 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_880 : my_sum 880 = 807 := by
  rw [my_sum, my_sum_879, tot_880]
  have h : v3_fast 320 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_881 : my_sum 881 = 807 := by
  rw [my_sum, my_sum_880, tot_881]
  have h : v3_fast 880 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_882 : my_sum 882 = 809 := by
  rw [my_sum, my_sum_881, tot_882]
  have h : v3_fast 252 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_883 : my_sum 883 = 811 := by
  rw [my_sum, my_sum_882, tot_883]
  have h : v3_fast 882 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_884 : my_sum 884 = 812 := by
  rw [my_sum, my_sum_883, tot_884]
  have h : v3_fast 384 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_885 : my_sum 885 = 812 := by
  rw [my_sum, my_sum_884, tot_885]
  have h : v3_fast 464 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_886 : my_sum 886 = 812 := by
  rw [my_sum, my_sum_885, tot_886]
  have h : v3_fast 442 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_887 : my_sum 887 = 812 := by
  rw [my_sum, my_sum_886, tot_887]
  have h : v3_fast 886 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_888 : my_sum 888 = 814 := by
  rw [my_sum, my_sum_887, tot_888]
  have h : v3_fast 288 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_889 : my_sum 889 = 817 := by
  rw [my_sum, my_sum_888, tot_889]
  have h : v3_fast 756 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_890 : my_sum 890 = 817 := by
  rw [my_sum, my_sum_889, tot_890]
  have h : v3_fast 352 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_891 : my_sum 891 = 820 := by
  rw [my_sum, my_sum_890, tot_891]
  have h : v3_fast 540 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_892 : my_sum 892 = 821 := by
  rw [my_sum, my_sum_891, tot_892]
  have h : v3_fast 444 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_893 : my_sum 893 = 823 := by
  rw [my_sum, my_sum_892, tot_893]
  have h : v3_fast 828 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_894 : my_sum 894 = 823 := by
  rw [my_sum, my_sum_893, tot_894]
  have h : v3_fast 296 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_895 : my_sum 895 = 823 := by
  rw [my_sum, my_sum_894, tot_895]
  have h : v3_fast 712 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_896 : my_sum 896 = 824 := by
  rw [my_sum, my_sum_895, tot_896]
  have h : v3_fast 384 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_897 : my_sum 897 = 825 := by
  rw [my_sum, my_sum_896, tot_897]
  have h : v3_fast 528 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_898 : my_sum 898 = 825 := by
  rw [my_sum, my_sum_897, tot_898]
  have h : v3_fast 448 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_899 : my_sum 899 = 826 := by
  rw [my_sum, my_sum_898, tot_899]
  have h : v3_fast 840 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_900 : my_sum 900 = 827 := by
  rw [my_sum, my_sum_899, tot_900]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_901 : my_sum 901 = 827 := by
  rw [my_sum, my_sum_900, tot_901]
  have h : v3_fast 832 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_902 : my_sum 902 = 827 := by
  rw [my_sum, my_sum_901, tot_902]
  have h : v3_fast 400 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_903 : my_sum 903 = 829 := by
  rw [my_sum, my_sum_902, tot_903]
  have h : v3_fast 504 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_904 : my_sum 904 = 829 := by
  rw [my_sum, my_sum_903, tot_904]
  have h : v3_fast 448 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_905 : my_sum 905 = 831 := by
  rw [my_sum, my_sum_904, tot_905]
  have h : v3_fast 720 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_906 : my_sum 906 = 832 := by
  rw [my_sum, my_sum_905, tot_906]
  have h : v3_fast 300 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_907 : my_sum 907 = 833 := by
  rw [my_sum, my_sum_906, tot_907]
  have h : v3_fast 906 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_908 : my_sum 908 = 833 := by
  rw [my_sum, my_sum_907, tot_908]
  have h : v3_fast 452 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_909 : my_sum 909 = 834 := by
  rw [my_sum, my_sum_908, tot_909]
  have h : v3_fast 600 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_910 : my_sum 910 = 836 := by
  rw [my_sum, my_sum_909, tot_910]
  have h : v3_fast 288 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_911 : my_sum 911 = 836 := by
  rw [my_sum, my_sum_910, tot_911]
  have h : v3_fast 910 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_912 : my_sum 912 = 838 := by
  rw [my_sum, my_sum_911, tot_912]
  have h : v3_fast 288 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_913 : my_sum 913 = 838 := by
  rw [my_sum, my_sum_912, tot_913]
  have h : v3_fast 820 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_914 : my_sum 914 = 839 := by
  rw [my_sum, my_sum_913, tot_914]
  have h : v3_fast 456 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_915 : my_sum 915 = 840 := by
  rw [my_sum, my_sum_914, tot_915]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_916 : my_sum 916 = 841 := by
  rw [my_sum, my_sum_915, tot_916]
  have h : v3_fast 456 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_917 : my_sum 917 = 842 := by
  rw [my_sum, my_sum_916, tot_917]
  have h : v3_fast 780 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_918 : my_sum 918 = 844 := by
  rw [my_sum, my_sum_917, tot_918]
  have h : v3_fast 288 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_919 : my_sum 919 = 847 := by
  rw [my_sum, my_sum_918, tot_919]
  have h : v3_fast 918 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_920 : my_sum 920 = 847 := by
  rw [my_sum, my_sum_919, tot_920]
  have h : v3_fast 352 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_921 : my_sum 921 = 849 := by
  rw [my_sum, my_sum_920, tot_921]
  have h : v3_fast 612 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_922 : my_sum 922 = 849 := by
  rw [my_sum, my_sum_921, tot_922]
  have h : v3_fast 460 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_923 : my_sum 923 = 850 := by
  rw [my_sum, my_sum_922, tot_923]
  have h : v3_fast 840 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_924 : my_sum 924 = 851 := by
  rw [my_sum, my_sum_923, tot_924]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_925 : my_sum 925 = 853 := by
  rw [my_sum, my_sum_924, tot_925]
  have h : v3_fast 720 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_926 : my_sum 926 = 854 := by
  rw [my_sum, my_sum_925, tot_926]
  have h : v3_fast 462 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_927 : my_sum 927 = 856 := by
  rw [my_sum, my_sum_926, tot_927]
  have h : v3_fast 612 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_928 : my_sum 928 = 856 := by
  rw [my_sum, my_sum_927, tot_928]
  have h : v3_fast 448 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_929 : my_sum 929 = 856 := by
  rw [my_sum, my_sum_928, tot_929]
  have h : v3_fast 928 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_930 : my_sum 930 = 857 := by
  rw [my_sum, my_sum_929, tot_930]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_931 : my_sum 931 = 860 := by
  rw [my_sum, my_sum_930, tot_931]
  have h : v3_fast 756 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_932 : my_sum 932 = 860 := by
  rw [my_sum, my_sum_931, tot_932]
  have h : v3_fast 464 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_933 : my_sum 933 = 860 := by
  rw [my_sum, my_sum_932, tot_933]
  have h : v3_fast 620 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_934 : my_sum 934 = 860 := by
  rw [my_sum, my_sum_933, tot_934]
  have h : v3_fast 466 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_935 : my_sum 935 = 860 := by
  rw [my_sum, my_sum_934, tot_935]
  have h : v3_fast 640 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_936 : my_sum 936 = 862 := by
  rw [my_sum, my_sum_935, tot_936]
  have h : v3_fast 288 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_937 : my_sum 937 = 864 := by
  rw [my_sum, my_sum_936, tot_937]
  have h : v3_fast 936 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_938 : my_sum 938 = 866 := by
  rw [my_sum, my_sum_937, tot_938]
  have h : v3_fast 396 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_939 : my_sum 939 = 867 := by
  rw [my_sum, my_sum_938, tot_939]
  have h : v3_fast 624 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_940 : my_sum 940 = 867 := by
  rw [my_sum, my_sum_939, tot_940]
  have h : v3_fast 368 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_941 : my_sum 941 = 867 := by
  rw [my_sum, my_sum_940, tot_941]
  have h : v3_fast 940 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_942 : my_sum 942 = 868 := by
  rw [my_sum, my_sum_941, tot_942]
  have h : v3_fast 312 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_943 : my_sum 943 = 868 := by
  rw [my_sum, my_sum_942, tot_943]
  have h : v3_fast 880 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_944 : my_sum 944 = 868 := by
  rw [my_sum, my_sum_943, tot_944]
  have h : v3_fast 464 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_945 : my_sum 945 = 871 := by
  rw [my_sum, my_sum_944, tot_945]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_946 : my_sum 946 = 872 := by
  rw [my_sum, my_sum_945, tot_946]
  have h : v3_fast 420 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_947 : my_sum 947 = 872 := by
  rw [my_sum, my_sum_946, tot_947]
  have h : v3_fast 946 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_948 : my_sum 948 = 873 := by
  rw [my_sum, my_sum_947, tot_948]
  have h : v3_fast 312 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_949 : my_sum 949 = 876 := by
  rw [my_sum, my_sum_948, tot_949]
  have h : v3_fast 864 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_950 : my_sum 950 = 878 := by
  rw [my_sum, my_sum_949, tot_950]
  have h : v3_fast 360 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_951 : my_sum 951 = 878 := by
  rw [my_sum, my_sum_950, tot_951]
  have h : v3_fast 632 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_952 : my_sum 952 = 879 := by
  rw [my_sum, my_sum_951, tot_952]
  have h : v3_fast 384 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_953 : my_sum 953 = 879 := by
  rw [my_sum, my_sum_952, tot_953]
  have h : v3_fast 952 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_954 : my_sum 954 = 880 := by
  rw [my_sum, my_sum_953, tot_954]
  have h : v3_fast 312 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_955 : my_sum 955 = 880 := by
  rw [my_sum, my_sum_954, tot_955]
  have h : v3_fast 760 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_956 : my_sum 956 = 880 := by
  rw [my_sum, my_sum_955, tot_956]
  have h : v3_fast 476 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_957 : my_sum 957 = 880 := by
  rw [my_sum, my_sum_956, tot_957]
  have h : v3_fast 560 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_958 : my_sum 958 = 880 := by
  rw [my_sum, my_sum_957, tot_958]
  have h : v3_fast 478 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_959 : my_sum 959 = 881 := by
  rw [my_sum, my_sum_958, tot_959]
  have h : v3_fast 816 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_960 : my_sum 960 = 881 := by
  rw [my_sum, my_sum_959, tot_960]
  have h : v3_fast 256 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_961 : my_sum 961 = 882 := by
  rw [my_sum, my_sum_960, tot_961]
  have h : v3_fast 930 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_962 : my_sum 962 = 885 := by
  rw [my_sum, my_sum_961, tot_962]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_963 : my_sum 963 = 886 := by
  rw [my_sum, my_sum_962, tot_963]
  have h : v3_fast 636 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_964 : my_sum 964 = 887 := by
  rw [my_sum, my_sum_963, tot_964]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_965 : my_sum 965 = 888 := by
  rw [my_sum, my_sum_964, tot_965]
  have h : v3_fast 768 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_966 : my_sum 966 = 889 := by
  rw [my_sum, my_sum_965, tot_966]
  have h : v3_fast 264 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_967 : my_sum 967 = 890 := by
  rw [my_sum, my_sum_966, tot_967]
  have h : v3_fast 966 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_968 : my_sum 968 = 890 := by
  rw [my_sum, my_sum_967, tot_968]
  have h : v3_fast 440 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_969 : my_sum 969 = 892 := by
  rw [my_sum, my_sum_968, tot_969]
  have h : v3_fast 576 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_970 : my_sum 970 = 893 := by
  rw [my_sum, my_sum_969, tot_970]
  have h : v3_fast 384 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_971 : my_sum 971 = 893 := by
  rw [my_sum, my_sum_970, tot_971]
  have h : v3_fast 970 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_972 : my_sum 972 = 897 := by
  rw [my_sum, my_sum_971, tot_972]
  have h : v3_fast 324 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_973 : my_sum 973 = 899 := by
  rw [my_sum, my_sum_972, tot_973]
  have h : v3_fast 828 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_974 : my_sum 974 = 904 := by
  rw [my_sum, my_sum_973, tot_974]
  have h : v3_fast 486 100 = 5 := rfl
  rw [h] <;> decide

theorem my_sum_975 : my_sum 975 = 905 := by
  rw [my_sum, my_sum_974, tot_975]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_976 : my_sum 976 = 906 := by
  rw [my_sum, my_sum_975, tot_976]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_977 : my_sum 977 = 906 := by
  rw [my_sum, my_sum_976, tot_977]
  have h : v3_fast 976 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_978 : my_sum 978 = 910 := by
  rw [my_sum, my_sum_977, tot_978]
  have h : v3_fast 324 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_979 : my_sum 979 = 910 := by
  rw [my_sum, my_sum_978, tot_979]
  have h : v3_fast 880 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_980 : my_sum 980 = 911 := by
  rw [my_sum, my_sum_979, tot_980]
  have h : v3_fast 336 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_981 : my_sum 981 = 915 := by
  rw [my_sum, my_sum_980, tot_981]
  have h : v3_fast 648 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_982 : my_sum 982 = 915 := by
  rw [my_sum, my_sum_981, tot_982]
  have h : v3_fast 490 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_983 : my_sum 983 = 915 := by
  rw [my_sum, my_sum_982, tot_983]
  have h : v3_fast 982 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_984 : my_sum 984 = 915 := by
  rw [my_sum, my_sum_983, tot_984]
  have h : v3_fast 320 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_985 : my_sum 985 = 915 := by
  rw [my_sum, my_sum_984, tot_985]
  have h : v3_fast 784 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_986 : my_sum 986 = 915 := by
  rw [my_sum, my_sum_985, tot_986]
  have h : v3_fast 448 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_987 : my_sum 987 = 916 := by
  rw [my_sum, my_sum_986, tot_987]
  have h : v3_fast 552 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_988 : my_sum 988 = 919 := by
  rw [my_sum, my_sum_987, tot_988]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_989 : my_sum 989 = 920 := by
  rw [my_sum, my_sum_988, tot_989]
  have h : v3_fast 924 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_990 : my_sum 990 = 921 := by
  rw [my_sum, my_sum_989, tot_990]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_991 : my_sum 991 = 923 := by
  rw [my_sum, my_sum_990, tot_991]
  have h : v3_fast 990 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_992 : my_sum 992 = 924 := by
  rw [my_sum, my_sum_991, tot_992]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_993 : my_sum 993 = 925 := by
  rw [my_sum, my_sum_992, tot_993]
  have h : v3_fast 660 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_994 : my_sum 994 = 926 := by
  rw [my_sum, my_sum_993, tot_994]
  have h : v3_fast 420 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_995 : my_sum 995 = 928 := by
  rw [my_sum, my_sum_994, tot_995]
  have h : v3_fast 792 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_996 : my_sum 996 = 928 := by
  rw [my_sum, my_sum_995, tot_996]
  have h : v3_fast 328 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_997 : my_sum 997 = 929 := by
  rw [my_sum, my_sum_996, tot_997]
  have h : v3_fast 996 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_998 : my_sum 998 = 930 := by
  rw [my_sum, my_sum_997, tot_998]
  have h : v3_fast 498 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_999 : my_sum 999 = 934 := by
  rw [my_sum, my_sum_998, tot_999]
  have h : v3_fast 648 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_1000 : my_sum 1000 = 934 := by
  rw [my_sum, my_sum_999, tot_1000]
  have h : v3_fast 400 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1001 : my_sum 1001 = 936 := by
  rw [my_sum, my_sum_1000, tot_1001]
  have h : v3_fast 720 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1002 : my_sum 1002 = 936 := by
  rw [my_sum, my_sum_1001, tot_1002]
  have h : v3_fast 332 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1003 : my_sum 1003 = 936 := by
  rw [my_sum, my_sum_1002, tot_1003]
  have h : v3_fast 928 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1004 : my_sum 1004 = 936 := by
  rw [my_sum, my_sum_1003, tot_1004]
  have h : v3_fast 500 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1005 : my_sum 1005 = 937 := by
  rw [my_sum, my_sum_1004, tot_1005]
  have h : v3_fast 528 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1006 : my_sum 1006 = 937 := by
  rw [my_sum, my_sum_1005, tot_1006]
  have h : v3_fast 502 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1007 : my_sum 1007 = 939 := by
  rw [my_sum, my_sum_1006, tot_1007]
  have h : v3_fast 936 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1008 : my_sum 1008 = 941 := by
  rw [my_sum, my_sum_1007, tot_1008]
  have h : v3_fast 288 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1009 : my_sum 1009 = 943 := by
  rw [my_sum, my_sum_1008, tot_1009]
  have h : v3_fast 1008 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1010 : my_sum 1010 = 943 := by
  rw [my_sum, my_sum_1009, tot_1010]
  have h : v3_fast 400 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1011 : my_sum 1011 = 944 := by
  rw [my_sum, my_sum_1010, tot_1011]
  have h : v3_fast 672 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1012 : my_sum 1012 = 944 := by
  rw [my_sum, my_sum_1011, tot_1012]
  have h : v3_fast 440 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1013 : my_sum 1013 = 944 := by
  rw [my_sum, my_sum_1012, tot_1013]
  have h : v3_fast 1012 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1014 : my_sum 1014 = 945 := by
  rw [my_sum, my_sum_1013, tot_1014]
  have h : v3_fast 312 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1015 : my_sum 1015 = 946 := by
  rw [my_sum, my_sum_1014, tot_1015]
  have h : v3_fast 672 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1016 : my_sum 1016 = 948 := by
  rw [my_sum, my_sum_1015, tot_1016]
  have h : v3_fast 504 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1017 : my_sum 1017 = 949 := by
  rw [my_sum, my_sum_1016, tot_1017]
  have h : v3_fast 672 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1018 : my_sum 1018 = 949 := by
  rw [my_sum, my_sum_1017, tot_1018]
  have h : v3_fast 508 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1019 : my_sum 1019 = 949 := by
  rw [my_sum, my_sum_1018, tot_1019]
  have h : v3_fast 1018 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1020 : my_sum 1020 = 949 := by
  rw [my_sum, my_sum_1019, tot_1020]
  have h : v3_fast 256 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1021 : my_sum 1021 = 950 := by
  rw [my_sum, my_sum_1020, tot_1021]
  have h : v3_fast 1020 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1022 : my_sum 1022 = 953 := by
  rw [my_sum, my_sum_1021, tot_1022]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1023 : my_sum 1023 = 954 := by
  rw [my_sum, my_sum_1022, tot_1023]
  have h : v3_fast 600 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1024 : my_sum 1024 = 954 := by
  rw [my_sum, my_sum_1023, tot_1024]
  have h : v3_fast 512 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1025 : my_sum 1025 = 954 := by
  rw [my_sum, my_sum_1024, tot_1025]
  have h : v3_fast 800 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1026 : my_sum 1026 = 958 := by
  rw [my_sum, my_sum_1025, tot_1026]
  have h : v3_fast 324 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_1027 : my_sum 1027 = 960 := by
  rw [my_sum, my_sum_1026, tot_1027]
  have h : v3_fast 936 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1028 : my_sum 1028 = 960 := by
  rw [my_sum, my_sum_1027, tot_1028]
  have h : v3_fast 512 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1029 : my_sum 1029 = 961 := by
  rw [my_sum, my_sum_1028, tot_1029]
  have h : v3_fast 588 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1030 : my_sum 1030 = 962 := by
  rw [my_sum, my_sum_1029, tot_1030]
  have h : v3_fast 408 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1031 : my_sum 1031 = 962 := by
  rw [my_sum, my_sum_1030, tot_1031]
  have h : v3_fast 1030 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1032 : my_sum 1032 = 963 := by
  rw [my_sum, my_sum_1031, tot_1032]
  have h : v3_fast 336 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1033 : my_sum 1033 = 964 := by
  rw [my_sum, my_sum_1032, tot_1033]
  have h : v3_fast 1032 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1034 : my_sum 1034 = 964 := by
  rw [my_sum, my_sum_1033, tot_1034]
  have h : v3_fast 460 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1035 : my_sum 1035 = 965 := by
  rw [my_sum, my_sum_1034, tot_1035]
  have h : v3_fast 528 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1036 : my_sum 1036 = 968 := by
  rw [my_sum, my_sum_1035, tot_1036]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1037 : my_sum 1037 = 969 := by
  rw [my_sum, my_sum_1036, tot_1037]
  have h : v3_fast 960 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1038 : my_sum 1038 = 969 := by
  rw [my_sum, my_sum_1037, tot_1038]
  have h : v3_fast 344 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1039 : my_sum 1039 = 970 := by
  rw [my_sum, my_sum_1038, tot_1039]
  have h : v3_fast 1038 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1040 : my_sum 1040 = 971 := by
  rw [my_sum, my_sum_1039, tot_1040]
  have h : v3_fast 384 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1041 : my_sum 1041 = 971 := by
  rw [my_sum, my_sum_1040, tot_1041]
  have h : v3_fast 692 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1042 : my_sum 1042 = 971 := by
  rw [my_sum, my_sum_1041, tot_1042]
  have h : v3_fast 520 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1043 : my_sum 1043 = 972 := by
  rw [my_sum, my_sum_1042, tot_1043]
  have h : v3_fast 888 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1044 : my_sum 1044 = 973 := by
  rw [my_sum, my_sum_1043, tot_1044]
  have h : v3_fast 336 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1045 : my_sum 1045 = 975 := by
  rw [my_sum, my_sum_1044, tot_1045]
  have h : v3_fast 720 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1046 : my_sum 1046 = 977 := by
  rw [my_sum, my_sum_1045, tot_1046]
  have h : v3_fast 522 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1047 : my_sum 1047 = 978 := by
  rw [my_sum, my_sum_1046, tot_1047]
  have h : v3_fast 696 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1048 : my_sum 1048 = 978 := by
  rw [my_sum, my_sum_1047, tot_1048]
  have h : v3_fast 520 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1049 : my_sum 1049 = 978 := by
  rw [my_sum, my_sum_1048, tot_1049]
  have h : v3_fast 1048 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1050 : my_sum 1050 = 979 := by
  rw [my_sum, my_sum_1049, tot_1050]
  have h : v3_fast 240 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1051 : my_sum 1051 = 980 := by
  rw [my_sum, my_sum_1050, tot_1051]
  have h : v3_fast 1050 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1052 : my_sum 1052 = 980 := by
  rw [my_sum, my_sum_1051, tot_1052]
  have h : v3_fast 524 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1053 : my_sum 1053 = 984 := by
  rw [my_sum, my_sum_1052, tot_1053]
  have h : v3_fast 648 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_1054 : my_sum 1054 = 985 := by
  rw [my_sum, my_sum_1053, tot_1054]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1055 : my_sum 1055 = 986 := by
  rw [my_sum, my_sum_1054, tot_1055]
  have h : v3_fast 840 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1056 : my_sum 1056 = 986 := by
  rw [my_sum, my_sum_1055, tot_1056]
  have h : v3_fast 320 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1057 : my_sum 1057 = 988 := by
  rw [my_sum, my_sum_1056, tot_1057]
  have h : v3_fast 900 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1058 : my_sum 1058 = 988 := by
  rw [my_sum, my_sum_1057, tot_1058]
  have h : v3_fast 506 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1059 : my_sum 1059 = 988 := by
  rw [my_sum, my_sum_1058, tot_1059]
  have h : v3_fast 704 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1060 : my_sum 1060 = 988 := by
  rw [my_sum, my_sum_1059, tot_1060]
  have h : v3_fast 416 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1061 : my_sum 1061 = 988 := by
  rw [my_sum, my_sum_1060, tot_1061]
  have h : v3_fast 1060 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1062 : my_sum 1062 = 989 := by
  rw [my_sum, my_sum_1061, tot_1062]
  have h : v3_fast 348 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1063 : my_sum 1063 = 991 := by
  rw [my_sum, my_sum_1062, tot_1063]
  have h : v3_fast 1062 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1064 : my_sum 1064 = 994 := by
  rw [my_sum, my_sum_1063, tot_1064]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1065 : my_sum 1065 = 994 := by
  rw [my_sum, my_sum_1064, tot_1065]
  have h : v3_fast 560 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1066 : my_sum 1066 = 995 := by
  rw [my_sum, my_sum_1065, tot_1066]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1067 : my_sum 1067 = 996 := by
  rw [my_sum, my_sum_1066, tot_1067]
  have h : v3_fast 960 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1068 : my_sum 1068 = 996 := by
  rw [my_sum, my_sum_1067, tot_1068]
  have h : v3_fast 352 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1069 : my_sum 1069 = 997 := by
  rw [my_sum, my_sum_1068, tot_1069]
  have h : v3_fast 1068 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1070 : my_sum 1070 = 997 := by
  rw [my_sum, my_sum_1069, tot_1070]
  have h : v3_fast 424 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1071 : my_sum 1071 = 999 := by
  rw [my_sum, my_sum_1070, tot_1071]
  have h : v3_fast 576 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1072 : my_sum 1072 = 1000 := by
  rw [my_sum, my_sum_1071, tot_1072]
  have h : v3_fast 528 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1073 : my_sum 1073 = 1002 := by
  rw [my_sum, my_sum_1072, tot_1073]
  have h : v3_fast 1008 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1074 : my_sum 1074 = 1002 := by
  rw [my_sum, my_sum_1073, tot_1074]
  have h : v3_fast 356 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1075 : my_sum 1075 = 1003 := by
  rw [my_sum, my_sum_1074, tot_1075]
  have h : v3_fast 840 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1076 : my_sum 1076 = 1003 := by
  rw [my_sum, my_sum_1075, tot_1076]
  have h : v3_fast 536 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1077 : my_sum 1077 = 1003 := by
  rw [my_sum, my_sum_1076, tot_1077]
  have h : v3_fast 716 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1078 : my_sum 1078 = 1004 := by
  rw [my_sum, my_sum_1077, tot_1078]
  have h : v3_fast 420 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1079 : my_sum 1079 = 1005 := by
  rw [my_sum, my_sum_1078, tot_1079]
  have h : v3_fast 984 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1080 : my_sum 1080 = 1007 := by
  rw [my_sum, my_sum_1079, tot_1080]
  have h : v3_fast 288 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1081 : my_sum 1081 = 1007 := by
  rw [my_sum, my_sum_1080, tot_1081]
  have h : v3_fast 1012 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1082 : my_sum 1082 = 1010 := by
  rw [my_sum, my_sum_1081, tot_1082]
  have h : v3_fast 540 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1083 : my_sum 1083 = 1012 := by
  rw [my_sum, my_sum_1082, tot_1083]
  have h : v3_fast 684 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1084 : my_sum 1084 = 1015 := by
  rw [my_sum, my_sum_1083, tot_1084]
  have h : v3_fast 540 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1085 : my_sum 1085 = 1017 := by
  rw [my_sum, my_sum_1084, tot_1085]
  have h : v3_fast 720 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1086 : my_sum 1086 = 1019 := by
  rw [my_sum, my_sum_1085, tot_1086]
  have h : v3_fast 360 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1087 : my_sum 1087 = 1020 := by
  rw [my_sum, my_sum_1086, tot_1087]
  have h : v3_fast 1086 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1088 : my_sum 1088 = 1020 := by
  rw [my_sum, my_sum_1087, tot_1088]
  have h : v3_fast 512 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1089 : my_sum 1089 = 1021 := by
  rw [my_sum, my_sum_1088, tot_1089]
  have h : v3_fast 660 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1090 : my_sum 1090 = 1024 := by
  rw [my_sum, my_sum_1089, tot_1090]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1091 : my_sum 1091 = 1024 := by
  rw [my_sum, my_sum_1090, tot_1091]
  have h : v3_fast 1090 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1092 : my_sum 1092 = 1026 := by
  rw [my_sum, my_sum_1091, tot_1092]
  have h : v3_fast 288 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1093 : my_sum 1093 = 1027 := by
  rw [my_sum, my_sum_1092, tot_1093]
  have h : v3_fast 1092 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1094 : my_sum 1094 = 1028 := by
  rw [my_sum, my_sum_1093, tot_1094]
  have h : v3_fast 546 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1095 : my_sum 1095 = 1030 := by
  rw [my_sum, my_sum_1094, tot_1095]
  have h : v3_fast 576 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1096 : my_sum 1096 = 1030 := by
  rw [my_sum, my_sum_1095, tot_1096]
  have h : v3_fast 544 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1097 : my_sum 1097 = 1030 := by
  rw [my_sum, my_sum_1096, tot_1097]
  have h : v3_fast 1096 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1098 : my_sum 1098 = 1032 := by
  rw [my_sum, my_sum_1097, tot_1098]
  have h : v3_fast 360 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1099 : my_sum 1099 = 1034 := by
  rw [my_sum, my_sum_1098, tot_1099]
  have h : v3_fast 936 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1100 : my_sum 1100 = 1034 := by
  rw [my_sum, my_sum_1099, tot_1100]
  have h : v3_fast 400 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1101 : my_sum 1101 = 1035 := by
  rw [my_sum, my_sum_1100, tot_1101]
  have h : v3_fast 732 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1102 : my_sum 1102 = 1037 := by
  rw [my_sum, my_sum_1101, tot_1102]
  have h : v3_fast 504 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1103 : my_sum 1103 = 1037 := by
  rw [my_sum, my_sum_1102, tot_1103]
  have h : v3_fast 1102 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1104 : my_sum 1104 = 1037 := by
  rw [my_sum, my_sum_1103, tot_1104]
  have h : v3_fast 352 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1105 : my_sum 1105 = 1038 := by
  rw [my_sum, my_sum_1104, tot_1105]
  have h : v3_fast 768 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1106 : my_sum 1106 = 1040 := by
  rw [my_sum, my_sum_1105, tot_1106]
  have h : v3_fast 468 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1107 : my_sum 1107 = 1042 := by
  rw [my_sum, my_sum_1106, tot_1107]
  have h : v3_fast 720 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1108 : my_sum 1108 = 1043 := by
  rw [my_sum, my_sum_1107, tot_1108]
  have h : v3_fast 552 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1109 : my_sum 1109 = 1043 := by
  rw [my_sum, my_sum_1108, tot_1109]
  have h : v3_fast 1108 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1110 : my_sum 1110 = 1045 := by
  rw [my_sum, my_sum_1109, tot_1110]
  have h : v3_fast 288 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1111 : my_sum 1111 = 1045 := by
  rw [my_sum, my_sum_1110, tot_1111]
  have h : v3_fast 1000 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1112 : my_sum 1112 = 1046 := by
  rw [my_sum, my_sum_1111, tot_1112]
  have h : v3_fast 552 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1113 : my_sum 1113 = 1047 := by
  rw [my_sum, my_sum_1112, tot_1113]
  have h : v3_fast 624 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1114 : my_sum 1114 = 1047 := by
  rw [my_sum, my_sum_1113, tot_1114]
  have h : v3_fast 556 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1115 : my_sum 1115 = 1048 := by
  rw [my_sum, my_sum_1114, tot_1115]
  have h : v3_fast 888 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1116 : my_sum 1116 = 1050 := by
  rw [my_sum, my_sum_1115, tot_1116]
  have h : v3_fast 360 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1117 : my_sum 1117 = 1052 := by
  rw [my_sum, my_sum_1116, tot_1117]
  have h : v3_fast 1116 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1118 : my_sum 1118 = 1054 := by
  rw [my_sum, my_sum_1117, tot_1118]
  have h : v3_fast 504 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1119 : my_sum 1119 = 1055 := by
  rw [my_sum, my_sum_1118, tot_1119]
  have h : v3_fast 744 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1120 : my_sum 1120 = 1056 := by
  rw [my_sum, my_sum_1119, tot_1120]
  have h : v3_fast 384 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1121 : my_sum 1121 = 1058 := by
  rw [my_sum, my_sum_1120, tot_1121]
  have h : v3_fast 1044 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1122 : my_sum 1122 = 1058 := by
  rw [my_sum, my_sum_1121, tot_1122]
  have h : v3_fast 320 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1123 : my_sum 1123 = 1059 := by
  rw [my_sum, my_sum_1122, tot_1123]
  have h : v3_fast 1122 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1124 : my_sum 1124 = 1059 := by
  rw [my_sum, my_sum_1123, tot_1124]
  have h : v3_fast 560 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1125 : my_sum 1125 = 1060 := by
  rw [my_sum, my_sum_1124, tot_1125]
  have h : v3_fast 600 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1126 : my_sum 1126 = 1060 := by
  rw [my_sum, my_sum_1125, tot_1126]
  have h : v3_fast 562 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1127 : my_sum 1127 = 1061 := by
  rw [my_sum, my_sum_1126, tot_1127]
  have h : v3_fast 924 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1128 : my_sum 1128 = 1061 := by
  rw [my_sum, my_sum_1127, tot_1128]
  have h : v3_fast 368 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1129 : my_sum 1129 = 1062 := by
  rw [my_sum, my_sum_1128, tot_1129]
  have h : v3_fast 1128 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1130 : my_sum 1130 = 1062 := by
  rw [my_sum, my_sum_1129, tot_1130]
  have h : v3_fast 448 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1131 : my_sum 1131 = 1063 := by
  rw [my_sum, my_sum_1130, tot_1131]
  have h : v3_fast 672 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1132 : my_sum 1132 = 1064 := by
  rw [my_sum, my_sum_1131, tot_1132]
  have h : v3_fast 564 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1133 : my_sum 1133 = 1065 := by
  rw [my_sum, my_sum_1132, tot_1133]
  have h : v3_fast 1020 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1134 : my_sum 1134 = 1069 := by
  rw [my_sum, my_sum_1133, tot_1134]
  have h : v3_fast 324 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_1135 : my_sum 1135 = 1069 := by
  rw [my_sum, my_sum_1134, tot_1135]
  have h : v3_fast 904 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1136 : my_sum 1136 = 1069 := by
  rw [my_sum, my_sum_1135, tot_1136]
  have h : v3_fast 560 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1137 : my_sum 1137 = 1072 := by
  rw [my_sum, my_sum_1136, tot_1137]
  have h : v3_fast 756 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1138 : my_sum 1138 = 1072 := by
  rw [my_sum, my_sum_1137, tot_1138]
  have h : v3_fast 568 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1139 : my_sum 1139 = 1073 := by
  rw [my_sum, my_sum_1138, tot_1139]
  have h : v3_fast 1056 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1140 : my_sum 1140 = 1075 := by
  rw [my_sum, my_sum_1139, tot_1140]
  have h : v3_fast 288 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1141 : my_sum 1141 = 1080 := by
  rw [my_sum, my_sum_1140, tot_1141]
  have h : v3_fast 972 100 = 5 := rfl
  rw [h] <;> decide

theorem my_sum_1142 : my_sum 1142 = 1081 := by
  rw [my_sum, my_sum_1141, tot_1142]
  have h : v3_fast 570 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1143 : my_sum 1143 = 1084 := by
  rw [my_sum, my_sum_1142, tot_1143]
  have h : v3_fast 756 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1144 : my_sum 1144 = 1085 := by
  rw [my_sum, my_sum_1143, tot_1144]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1145 : my_sum 1145 = 1086 := by
  rw [my_sum, my_sum_1144, tot_1145]
  have h : v3_fast 912 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1146 : my_sum 1146 = 1086 := by
  rw [my_sum, my_sum_1145, tot_1146]
  have h : v3_fast 380 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1147 : my_sum 1147 = 1089 := by
  rw [my_sum, my_sum_1146, tot_1147]
  have h : v3_fast 1080 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1148 : my_sum 1148 = 1090 := by
  rw [my_sum, my_sum_1147, tot_1148]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1149 : my_sum 1149 = 1090 := by
  rw [my_sum, my_sum_1148, tot_1149]
  have h : v3_fast 764 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1150 : my_sum 1150 = 1090 := by
  rw [my_sum, my_sum_1149, tot_1150]
  have h : v3_fast 440 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1151 : my_sum 1151 = 1090 := by
  rw [my_sum, my_sum_1150, tot_1151]
  have h : v3_fast 1150 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1152 : my_sum 1152 = 1091 := by
  rw [my_sum, my_sum_1151, tot_1152]
  have h : v3_fast 384 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1153 : my_sum 1153 = 1093 := by
  rw [my_sum, my_sum_1152, tot_1153]
  have h : v3_fast 1152 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1154 : my_sum 1154 = 1095 := by
  rw [my_sum, my_sum_1153, tot_1154]
  have h : v3_fast 576 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1155 : my_sum 1155 = 1096 := by
  rw [my_sum, my_sum_1154, tot_1155]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1156 : my_sum 1156 = 1096 := by
  rw [my_sum, my_sum_1155, tot_1156]
  have h : v3_fast 544 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1157 : my_sum 1157 = 1097 := by
  rw [my_sum, my_sum_1156, tot_1157]
  have h : v3_fast 1056 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1158 : my_sum 1158 = 1098 := by
  rw [my_sum, my_sum_1157, tot_1158]
  have h : v3_fast 384 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1159 : my_sum 1159 = 1101 := by
  rw [my_sum, my_sum_1158, tot_1159]
  have h : v3_fast 1080 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1160 : my_sum 1160 = 1101 := by
  rw [my_sum, my_sum_1159, tot_1160]
  have h : v3_fast 448 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1161 : my_sum 1161 = 1104 := by
  rw [my_sum, my_sum_1160, tot_1161]
  have h : v3_fast 756 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1162 : my_sum 1162 = 1105 := by
  rw [my_sum, my_sum_1161, tot_1162]
  have h : v3_fast 492 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1163 : my_sum 1163 = 1105 := by
  rw [my_sum, my_sum_1162, tot_1163]
  have h : v3_fast 1162 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1164 : my_sum 1164 = 1106 := by
  rw [my_sum, my_sum_1163, tot_1164]
  have h : v3_fast 384 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1165 : my_sum 1165 = 1106 := by
  rw [my_sum, my_sum_1164, tot_1165]
  have h : v3_fast 928 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1166 : my_sum 1166 = 1106 := by
  rw [my_sum, my_sum_1165, tot_1166]
  have h : v3_fast 520 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1167 : my_sum 1167 = 1106 := by
  rw [my_sum, my_sum_1166, tot_1167]
  have h : v3_fast 776 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1168 : my_sum 1168 = 1108 := by
  rw [my_sum, my_sum_1167, tot_1168]
  have h : v3_fast 576 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1169 : my_sum 1169 = 1109 := by
  rw [my_sum, my_sum_1168, tot_1169]
  have h : v3_fast 996 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1170 : my_sum 1170 = 1111 := by
  rw [my_sum, my_sum_1169, tot_1170]
  have h : v3_fast 288 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1171 : my_sum 1171 = 1113 := by
  rw [my_sum, my_sum_1170, tot_1171]
  have h : v3_fast 1170 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1172 : my_sum 1172 = 1113 := by
  rw [my_sum, my_sum_1171, tot_1172]
  have h : v3_fast 584 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1173 : my_sum 1173 = 1113 := by
  rw [my_sum, my_sum_1172, tot_1173]
  have h : v3_fast 704 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1174 : my_sum 1174 = 1113 := by
  rw [my_sum, my_sum_1173, tot_1174]
  have h : v3_fast 586 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1175 : my_sum 1175 = 1113 := by
  rw [my_sum, my_sum_1174, tot_1175]
  have h : v3_fast 920 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1176 : my_sum 1176 = 1114 := by
  rw [my_sum, my_sum_1175, tot_1176]
  have h : v3_fast 336 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1177 : my_sum 1177 = 1114 := by
  rw [my_sum, my_sum_1176, tot_1177]
  have h : v3_fast 1060 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1178 : my_sum 1178 = 1117 := by
  rw [my_sum, my_sum_1177, tot_1178]
  have h : v3_fast 540 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1179 : my_sum 1179 = 1118 := by
  rw [my_sum, my_sum_1178, tot_1179]
  have h : v3_fast 780 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1180 : my_sum 1180 = 1118 := by
  rw [my_sum, my_sum_1179, tot_1180]
  have h : v3_fast 464 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1181 : my_sum 1181 = 1118 := by
  rw [my_sum, my_sum_1180, tot_1181]
  have h : v3_fast 1180 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1182 : my_sum 1182 = 1118 := by
  rw [my_sum, my_sum_1181, tot_1182]
  have h : v3_fast 392 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1183 : my_sum 1183 = 1120 := by
  rw [my_sum, my_sum_1182, tot_1183]
  have h : v3_fast 936 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1184 : my_sum 1184 = 1122 := by
  rw [my_sum, my_sum_1183, tot_1184]
  have h : v3_fast 576 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1185 : my_sum 1185 = 1123 := by
  rw [my_sum, my_sum_1184, tot_1185]
  have h : v3_fast 624 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1186 : my_sum 1186 = 1123 := by
  rw [my_sum, my_sum_1185, tot_1186]
  have h : v3_fast 592 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1187 : my_sum 1187 = 1123 := by
  rw [my_sum, my_sum_1186, tot_1187]
  have h : v3_fast 1186 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1188 : my_sum 1188 = 1125 := by
  rw [my_sum, my_sum_1187, tot_1188]
  have h : v3_fast 360 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1189 : my_sum 1189 = 1125 := by
  rw [my_sum, my_sum_1188, tot_1189]
  have h : v3_fast 1120 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1190 : my_sum 1190 = 1126 := by
  rw [my_sum, my_sum_1189, tot_1190]
  have h : v3_fast 384 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1191 : my_sum 1191 = 1128 := by
  rw [my_sum, my_sum_1190, tot_1191]
  have h : v3_fast 792 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1192 : my_sum 1192 = 1128 := by
  rw [my_sum, my_sum_1191, tot_1192]
  have h : v3_fast 592 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1193 : my_sum 1193 = 1128 := by
  rw [my_sum, my_sum_1192, tot_1193]
  have h : v3_fast 1192 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1194 : my_sum 1194 = 1130 := by
  rw [my_sum, my_sum_1193, tot_1194]
  have h : v3_fast 396 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1195 : my_sum 1195 = 1130 := by
  rw [my_sum, my_sum_1194, tot_1195]
  have h : v3_fast 952 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1196 : my_sum 1196 = 1131 := by
  rw [my_sum, my_sum_1195, tot_1196]
  have h : v3_fast 528 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1197 : my_sum 1197 = 1135 := by
  rw [my_sum, my_sum_1196, tot_1197]
  have h : v3_fast 648 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_1198 : my_sum 1198 = 1135 := by
  rw [my_sum, my_sum_1197, tot_1198]
  have h : v3_fast 598 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1199 : my_sum 1199 = 1138 := by
  rw [my_sum, my_sum_1198, tot_1199]
  have h : v3_fast 1080 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1200 : my_sum 1200 = 1138 := by
  rw [my_sum, my_sum_1199, tot_1200]
  have h : v3_fast 320 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1201 : my_sum 1201 = 1139 := by
  rw [my_sum, my_sum_1200, tot_1201]
  have h : v3_fast 1200 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1202 : my_sum 1202 = 1140 := by
  rw [my_sum, my_sum_1201, tot_1202]
  have h : v3_fast 600 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1203 : my_sum 1203 = 1140 := by
  rw [my_sum, my_sum_1202, tot_1203]
  have h : v3_fast 800 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1204 : my_sum 1204 = 1142 := by
  rw [my_sum, my_sum_1203, tot_1204]
  have h : v3_fast 504 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1205 : my_sum 1205 = 1143 := by
  rw [my_sum, my_sum_1204, tot_1205]
  have h : v3_fast 960 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1206 : my_sum 1206 = 1145 := by
  rw [my_sum, my_sum_1205, tot_1206]
  have h : v3_fast 396 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1207 : my_sum 1207 = 1145 := by
  rw [my_sum, my_sum_1206, tot_1207]
  have h : v3_fast 1120 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1208 : my_sum 1208 = 1146 := by
  rw [my_sum, my_sum_1207, tot_1208]
  have h : v3_fast 600 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1209 : my_sum 1209 = 1148 := by
  rw [my_sum, my_sum_1208, tot_1209]
  have h : v3_fast 720 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1210 : my_sum 1210 = 1148 := by
  rw [my_sum, my_sum_1209, tot_1210]
  have h : v3_fast 440 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1211 : my_sum 1211 = 1149 := by
  rw [my_sum, my_sum_1210, tot_1211]
  have h : v3_fast 1032 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1212 : my_sum 1212 = 1149 := by
  rw [my_sum, my_sum_1211, tot_1212]
  have h : v3_fast 400 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1213 : my_sum 1213 = 1150 := by
  rw [my_sum, my_sum_1212, tot_1213]
  have h : v3_fast 1212 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1214 : my_sum 1214 = 1151 := by
  rw [my_sum, my_sum_1213, tot_1214]
  have h : v3_fast 606 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1215 : my_sum 1215 = 1155 := by
  rw [my_sum, my_sum_1214, tot_1215]
  have h : v3_fast 648 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_1216 : my_sum 1216 = 1157 := by
  rw [my_sum, my_sum_1215, tot_1216]
  have h : v3_fast 576 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1217 : my_sum 1217 = 1157 := by
  rw [my_sum, my_sum_1216, tot_1217]
  have h : v3_fast 1216 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1218 : my_sum 1218 = 1158 := by
  rw [my_sum, my_sum_1217, tot_1218]
  have h : v3_fast 336 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1219 : my_sum 1219 = 1158 := by
  rw [my_sum, my_sum_1218, tot_1219]
  have h : v3_fast 1144 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1220 : my_sum 1220 = 1159 := by
  rw [my_sum, my_sum_1219, tot_1220]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1221 : my_sum 1221 = 1161 := by
  rw [my_sum, my_sum_1220, tot_1221]
  have h : v3_fast 720 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1222 : my_sum 1222 = 1162 := by
  rw [my_sum, my_sum_1221, tot_1222]
  have h : v3_fast 552 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1223 : my_sum 1223 = 1162 := by
  rw [my_sum, my_sum_1222, tot_1223]
  have h : v3_fast 1222 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1224 : my_sum 1224 = 1163 := by
  rw [my_sum, my_sum_1223, tot_1224]
  have h : v3_fast 384 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1225 : my_sum 1225 = 1164 := by
  rw [my_sum, my_sum_1224, tot_1225]
  have h : v3_fast 840 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1226 : my_sum 1226 = 1166 := by
  rw [my_sum, my_sum_1225, tot_1226]
  have h : v3_fast 612 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1227 : my_sum 1227 = 1167 := by
  rw [my_sum, my_sum_1226, tot_1227]
  have h : v3_fast 816 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1228 : my_sum 1228 = 1169 := by
  rw [my_sum, my_sum_1227, tot_1228]
  have h : v3_fast 612 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1229 : my_sum 1229 = 1169 := by
  rw [my_sum, my_sum_1228, tot_1229]
  have h : v3_fast 1228 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1230 : my_sum 1230 = 1169 := by
  rw [my_sum, my_sum_1229, tot_1230]
  have h : v3_fast 320 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1231 : my_sum 1231 = 1170 := by
  rw [my_sum, my_sum_1230, tot_1231]
  have h : v3_fast 1230 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1232 : my_sum 1232 = 1171 := by
  rw [my_sum, my_sum_1231, tot_1232]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1233 : my_sum 1233 = 1172 := by
  rw [my_sum, my_sum_1232, tot_1233]
  have h : v3_fast 816 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1234 : my_sum 1234 = 1172 := by
  rw [my_sum, my_sum_1233, tot_1234]
  have h : v3_fast 616 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1235 : my_sum 1235 = 1175 := by
  rw [my_sum, my_sum_1234, tot_1235]
  have h : v3_fast 864 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1236 : my_sum 1236 = 1176 := by
  rw [my_sum, my_sum_1235, tot_1236]
  have h : v3_fast 408 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1237 : my_sum 1237 = 1177 := by
  rw [my_sum, my_sum_1236, tot_1237]
  have h : v3_fast 1236 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1238 : my_sum 1238 = 1178 := by
  rw [my_sum, my_sum_1237, tot_1238]
  have h : v3_fast 618 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1239 : my_sum 1239 = 1179 := by
  rw [my_sum, my_sum_1238, tot_1239]
  have h : v3_fast 696 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1240 : my_sum 1240 = 1180 := by
  rw [my_sum, my_sum_1239, tot_1240]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1241 : my_sum 1241 = 1182 := by
  rw [my_sum, my_sum_1240, tot_1241]
  have h : v3_fast 1152 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1242 : my_sum 1242 = 1184 := by
  rw [my_sum, my_sum_1241, tot_1242]
  have h : v3_fast 396 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1243 : my_sum 1243 = 1184 := by
  rw [my_sum, my_sum_1242, tot_1243]
  have h : v3_fast 1120 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1244 : my_sum 1244 = 1184 := by
  rw [my_sum, my_sum_1243, tot_1244]
  have h : v3_fast 620 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1245 : my_sum 1245 = 1184 := by
  rw [my_sum, my_sum_1244, tot_1245]
  have h : v3_fast 656 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1246 : my_sum 1246 = 1185 := by
  rw [my_sum, my_sum_1245, tot_1246]
  have h : v3_fast 528 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1247 : my_sum 1247 = 1186 := by
  rw [my_sum, my_sum_1246, tot_1247]
  have h : v3_fast 1176 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1248 : my_sum 1248 = 1187 := by
  rw [my_sum, my_sum_1247, tot_1248]
  have h : v3_fast 384 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1249 : my_sum 1249 = 1188 := by
  rw [my_sum, my_sum_1248, tot_1249]
  have h : v3_fast 1248 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1250 : my_sum 1250 = 1188 := by
  rw [my_sum, my_sum_1249, tot_1250]
  have h : v3_fast 500 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1251 : my_sum 1251 = 1190 := by
  rw [my_sum, my_sum_1250, tot_1251]
  have h : v3_fast 828 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1252 : my_sum 1252 = 1191 := by
  rw [my_sum, my_sum_1251, tot_1252]
  have h : v3_fast 624 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1253 : my_sum 1253 = 1192 := by
  rw [my_sum, my_sum_1252, tot_1253]
  have h : v3_fast 1068 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1254 : my_sum 1254 = 1194 := by
  rw [my_sum, my_sum_1253, tot_1254]
  have h : v3_fast 360 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1255 : my_sum 1255 = 1194 := by
  rw [my_sum, my_sum_1254, tot_1255]
  have h : v3_fast 1000 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1256 : my_sum 1256 = 1195 := by
  rw [my_sum, my_sum_1255, tot_1256]
  have h : v3_fast 624 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1257 : my_sum 1257 = 1195 := by
  rw [my_sum, my_sum_1256, tot_1257]
  have h : v3_fast 836 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1258 : my_sum 1258 = 1197 := by
  rw [my_sum, my_sum_1257, tot_1258]
  have h : v3_fast 576 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1259 : my_sum 1259 = 1197 := by
  rw [my_sum, my_sum_1258, tot_1259]
  have h : v3_fast 1258 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1260 : my_sum 1260 = 1199 := by
  rw [my_sum, my_sum_1259, tot_1260]
  have h : v3_fast 288 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1261 : my_sum 1261 = 1201 := by
  rw [my_sum, my_sum_1260, tot_1261]
  have h : v3_fast 1152 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1262 : my_sum 1262 = 1203 := by
  rw [my_sum, my_sum_1261, tot_1262]
  have h : v3_fast 630 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1263 : my_sum 1263 = 1204 := by
  rw [my_sum, my_sum_1262, tot_1263]
  have h : v3_fast 840 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1264 : my_sum 1264 = 1205 := by
  rw [my_sum, my_sum_1263, tot_1264]
  have h : v3_fast 624 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1265 : my_sum 1265 = 1205 := by
  rw [my_sum, my_sum_1264, tot_1265]
  have h : v3_fast 880 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1266 : my_sum 1266 = 1206 := by
  rw [my_sum, my_sum_1265, tot_1266]
  have h : v3_fast 420 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1267 : my_sum 1267 = 1209 := by
  rw [my_sum, my_sum_1266, tot_1267]
  have h : v3_fast 1080 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1268 : my_sum 1268 = 1209 := by
  rw [my_sum, my_sum_1267, tot_1268]
  have h : v3_fast 632 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1269 : my_sum 1269 = 1211 := by
  rw [my_sum, my_sum_1268, tot_1269]
  have h : v3_fast 828 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1270 : my_sum 1270 = 1213 := by
  rw [my_sum, my_sum_1269, tot_1270]
  have h : v3_fast 504 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1271 : my_sum 1271 = 1214 := by
  rw [my_sum, my_sum_1270, tot_1271]
  have h : v3_fast 1200 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1272 : my_sum 1272 = 1214 := by
  rw [my_sum, my_sum_1271, tot_1272]
  have h : v3_fast 416 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1273 : my_sum 1273 = 1217 := by
  rw [my_sum, my_sum_1272, tot_1273]
  have h : v3_fast 1188 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1274 : my_sum 1274 = 1219 := by
  rw [my_sum, my_sum_1273, tot_1274]
  have h : v3_fast 504 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1275 : my_sum 1275 = 1219 := by
  rw [my_sum, my_sum_1274, tot_1275]
  have h : v3_fast 640 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1276 : my_sum 1276 = 1219 := by
  rw [my_sum, my_sum_1275, tot_1276]
  have h : v3_fast 560 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1277 : my_sum 1277 = 1219 := by
  rw [my_sum, my_sum_1276, tot_1277]
  have h : v3_fast 1276 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1278 : my_sum 1278 = 1220 := by
  rw [my_sum, my_sum_1277, tot_1278]
  have h : v3_fast 420 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1279 : my_sum 1279 = 1222 := by
  rw [my_sum, my_sum_1278, tot_1279]
  have h : v3_fast 1278 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1280 : my_sum 1280 = 1222 := by
  rw [my_sum, my_sum_1279, tot_1280]
  have h : v3_fast 512 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1281 : my_sum 1281 = 1224 := by
  rw [my_sum, my_sum_1280, tot_1281]
  have h : v3_fast 720 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1282 : my_sum 1282 = 1224 := by
  rw [my_sum, my_sum_1281, tot_1282]
  have h : v3_fast 640 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1283 : my_sum 1283 = 1224 := by
  rw [my_sum, my_sum_1282, tot_1283]
  have h : v3_fast 1282 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1284 : my_sum 1284 = 1224 := by
  rw [my_sum, my_sum_1283, tot_1284]
  have h : v3_fast 424 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1285 : my_sum 1285 = 1224 := by
  rw [my_sum, my_sum_1284, tot_1285]
  have h : v3_fast 1024 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1286 : my_sum 1286 = 1225 := by
  rw [my_sum, my_sum_1285, tot_1286]
  have h : v3_fast 642 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1287 : my_sum 1287 = 1227 := by
  rw [my_sum, my_sum_1286, tot_1287]
  have h : v3_fast 720 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1288 : my_sum 1288 = 1228 := by
  rw [my_sum, my_sum_1287, tot_1288]
  have h : v3_fast 528 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1289 : my_sum 1289 = 1228 := by
  rw [my_sum, my_sum_1288, tot_1289]
  have h : v3_fast 1288 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1290 : my_sum 1290 = 1229 := by
  rw [my_sum, my_sum_1289, tot_1290]
  have h : v3_fast 336 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1291 : my_sum 1291 = 1230 := by
  rw [my_sum, my_sum_1290, tot_1291]
  have h : v3_fast 1290 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1292 : my_sum 1292 = 1232 := by
  rw [my_sum, my_sum_1291, tot_1292]
  have h : v3_fast 576 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1293 : my_sum 1293 = 1232 := by
  rw [my_sum, my_sum_1292, tot_1293]
  have h : v3_fast 860 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1294 : my_sum 1294 = 1232 := by
  rw [my_sum, my_sum_1293, tot_1294]
  have h : v3_fast 646 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1295 : my_sum 1295 = 1235 := by
  rw [my_sum, my_sum_1294, tot_1295]
  have h : v3_fast 864 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1296 : my_sum 1296 = 1238 := by
  rw [my_sum, my_sum_1295, tot_1296]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1297 : my_sum 1297 = 1242 := by
  rw [my_sum, my_sum_1296, tot_1297]
  have h : v3_fast 1296 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_1298 : my_sum 1298 = 1242 := by
  rw [my_sum, my_sum_1297, tot_1298]
  have h : v3_fast 580 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1299 : my_sum 1299 = 1245 := by
  rw [my_sum, my_sum_1298, tot_1299]
  have h : v3_fast 864 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1300 : my_sum 1300 = 1246 := by
  rw [my_sum, my_sum_1299, tot_1300]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1301 : my_sum 1301 = 1246 := by
  rw [my_sum, my_sum_1300, tot_1301]
  have h : v3_fast 1300 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1302 : my_sum 1302 = 1248 := by
  rw [my_sum, my_sum_1301, tot_1302]
  have h : v3_fast 360 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1303 : my_sum 1303 = 1249 := by
  rw [my_sum, my_sum_1302, tot_1303]
  have h : v3_fast 1302 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1304 : my_sum 1304 = 1253 := by
  rw [my_sum, my_sum_1303, tot_1304]
  have h : v3_fast 648 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_1305 : my_sum 1305 = 1254 := by
  rw [my_sum, my_sum_1304, tot_1305]
  have h : v3_fast 672 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1306 : my_sum 1306 = 1254 := by
  rw [my_sum, my_sum_1305, tot_1306]
  have h : v3_fast 652 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1307 : my_sum 1307 = 1254 := by
  rw [my_sum, my_sum_1306, tot_1307]
  have h : v3_fast 1306 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1308 : my_sum 1308 = 1257 := by
  rw [my_sum, my_sum_1307, tot_1308]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1309 : my_sum 1309 = 1258 := by
  rw [my_sum, my_sum_1308, tot_1309]
  have h : v3_fast 960 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1310 : my_sum 1310 = 1258 := by
  rw [my_sum, my_sum_1309, tot_1310]
  have h : v3_fast 520 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1311 : my_sum 1311 = 1260 := by
  rw [my_sum, my_sum_1310, tot_1311]
  have h : v3_fast 792 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1312 : my_sum 1312 = 1260 := by
  rw [my_sum, my_sum_1311, tot_1312]
  have h : v3_fast 640 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1313 : my_sum 1313 = 1261 := by
  rw [my_sum, my_sum_1312, tot_1313]
  have h : v3_fast 1200 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1314 : my_sum 1314 = 1264 := by
  rw [my_sum, my_sum_1313, tot_1314]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1315 : my_sum 1315 = 1264 := by
  rw [my_sum, my_sum_1314, tot_1315]
  have h : v3_fast 1048 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1316 : my_sum 1316 = 1265 := by
  rw [my_sum, my_sum_1315, tot_1316]
  have h : v3_fast 552 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1317 : my_sum 1317 = 1266 := by
  rw [my_sum, my_sum_1316, tot_1317]
  have h : v3_fast 876 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1318 : my_sum 1318 = 1266 := by
  rw [my_sum, my_sum_1317, tot_1318]
  have h : v3_fast 658 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1319 : my_sum 1319 = 1266 := by
  rw [my_sum, my_sum_1318, tot_1319]
  have h : v3_fast 1318 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1320 : my_sum 1320 = 1266 := by
  rw [my_sum, my_sum_1319, tot_1320]
  have h : v3_fast 320 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1321 : my_sum 1321 = 1267 := by
  rw [my_sum, my_sum_1320, tot_1321]
  have h : v3_fast 1320 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1322 : my_sum 1322 = 1268 := by
  rw [my_sum, my_sum_1321, tot_1322]
  have h : v3_fast 660 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1323 : my_sum 1323 = 1271 := by
  rw [my_sum, my_sum_1322, tot_1323]
  have h : v3_fast 756 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1324 : my_sum 1324 = 1272 := by
  rw [my_sum, my_sum_1323, tot_1324]
  have h : v3_fast 660 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1325 : my_sum 1325 = 1272 := by
  rw [my_sum, my_sum_1324, tot_1325]
  have h : v3_fast 1040 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1326 : my_sum 1326 = 1273 := by
  rw [my_sum, my_sum_1325, tot_1326]
  have h : v3_fast 384 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1327 : my_sum 1327 = 1274 := by
  rw [my_sum, my_sum_1326, tot_1327]
  have h : v3_fast 1326 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1328 : my_sum 1328 = 1274 := by
  rw [my_sum, my_sum_1327, tot_1328]
  have h : v3_fast 656 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1329 : my_sum 1329 = 1274 := by
  rw [my_sum, my_sum_1328, tot_1329]
  have h : v3_fast 884 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1330 : my_sum 1330 = 1277 := by
  rw [my_sum, my_sum_1329, tot_1330]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1331 : my_sum 1331 = 1277 := by
  rw [my_sum, my_sum_1330, tot_1331]
  have h : v3_fast 1210 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1332 : my_sum 1332 = 1280 := by
  rw [my_sum, my_sum_1331, tot_1332]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1333 : my_sum 1333 = 1282 := by
  rw [my_sum, my_sum_1332, tot_1333]
  have h : v3_fast 1260 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1334 : my_sum 1334 = 1282 := by
  rw [my_sum, my_sum_1333, tot_1334]
  have h : v3_fast 616 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1335 : my_sum 1335 = 1282 := by
  rw [my_sum, my_sum_1334, tot_1335]
  have h : v3_fast 704 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1336 : my_sum 1336 = 1282 := by
  rw [my_sum, my_sum_1335, tot_1336]
  have h : v3_fast 664 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1337 : my_sum 1337 = 1283 := by
  rw [my_sum, my_sum_1336, tot_1337]
  have h : v3_fast 1140 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1338 : my_sum 1338 = 1284 := by
  rw [my_sum, my_sum_1337, tot_1338]
  have h : v3_fast 444 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1339 : my_sum 1339 = 1286 := by
  rw [my_sum, my_sum_1338, tot_1339]
  have h : v3_fast 1224 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1340 : my_sum 1340 = 1287 := by
  rw [my_sum, my_sum_1339, tot_1340]
  have h : v3_fast 528 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1341 : my_sum 1341 = 1288 := by
  rw [my_sum, my_sum_1340, tot_1341]
  have h : v3_fast 888 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1342 : my_sum 1342 = 1289 := by
  rw [my_sum, my_sum_1341, tot_1342]
  have h : v3_fast 600 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1343 : my_sum 1343 = 1290 := by
  rw [my_sum, my_sum_1342, tot_1343]
  have h : v3_fast 1248 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1344 : my_sum 1344 = 1291 := by
  rw [my_sum, my_sum_1343, tot_1344]
  have h : v3_fast 384 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1345 : my_sum 1345 = 1291 := by
  rw [my_sum, my_sum_1344, tot_1345]
  have h : v3_fast 1072 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1346 : my_sum 1346 = 1292 := by
  rw [my_sum, my_sum_1345, tot_1346]
  have h : v3_fast 672 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1347 : my_sum 1347 = 1292 := by
  rw [my_sum, my_sum_1346, tot_1347]
  have h : v3_fast 896 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1348 : my_sum 1348 = 1293 := by
  rw [my_sum, my_sum_1347, tot_1348]
  have h : v3_fast 672 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1349 : my_sum 1349 = 1295 := by
  rw [my_sum, my_sum_1348, tot_1349]
  have h : v3_fast 1260 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1350 : my_sum 1350 = 1297 := by
  rw [my_sum, my_sum_1349, tot_1350]
  have h : v3_fast 360 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1351 : my_sum 1351 = 1299 := by
  rw [my_sum, my_sum_1350, tot_1351]
  have h : v3_fast 1152 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1352 : my_sum 1352 = 1300 := by
  rw [my_sum, my_sum_1351, tot_1352]
  have h : v3_fast 624 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1353 : my_sum 1353 = 1300 := by
  rw [my_sum, my_sum_1352, tot_1353]
  have h : v3_fast 800 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1354 : my_sum 1354 = 1300 := by
  rw [my_sum, my_sum_1353, tot_1354]
  have h : v3_fast 676 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1355 : my_sum 1355 = 1303 := by
  rw [my_sum, my_sum_1354, tot_1355]
  have h : v3_fast 1080 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1356 : my_sum 1356 = 1303 := by
  rw [my_sum, my_sum_1355, tot_1356]
  have h : v3_fast 448 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1357 : my_sum 1357 = 1303 := by
  rw [my_sum, my_sum_1356, tot_1357]
  have h : v3_fast 1276 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1358 : my_sum 1358 = 1305 := by
  rw [my_sum, my_sum_1357, tot_1358]
  have h : v3_fast 576 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1359 : my_sum 1359 = 1307 := by
  rw [my_sum, my_sum_1358, tot_1359]
  have h : v3_fast 900 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1360 : my_sum 1360 = 1307 := by
  rw [my_sum, my_sum_1359, tot_1360]
  have h : v3_fast 512 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1361 : my_sum 1361 = 1307 := by
  rw [my_sum, my_sum_1360, tot_1361]
  have h : v3_fast 1360 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1362 : my_sum 1362 = 1307 := by
  rw [my_sum, my_sum_1361, tot_1362]
  have h : v3_fast 452 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1363 : my_sum 1363 = 1307 := by
  rw [my_sum, my_sum_1362, tot_1363]
  have h : v3_fast 1288 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1364 : my_sum 1364 = 1308 := by
  rw [my_sum, my_sum_1363, tot_1364]
  have h : v3_fast 600 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1365 : my_sum 1365 = 1310 := by
  rw [my_sum, my_sum_1364, tot_1365]
  have h : v3_fast 576 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1366 : my_sum 1366 = 1310 := by
  rw [my_sum, my_sum_1365, tot_1366]
  have h : v3_fast 682 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1367 : my_sum 1367 = 1310 := by
  rw [my_sum, my_sum_1366, tot_1367]
  have h : v3_fast 1366 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1368 : my_sum 1368 = 1313 := by
  rw [my_sum, my_sum_1367, tot_1368]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1369 : my_sum 1369 = 1315 := by
  rw [my_sum, my_sum_1368, tot_1369]
  have h : v3_fast 1332 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1370 : my_sum 1370 = 1315 := by
  rw [my_sum, my_sum_1369, tot_1370]
  have h : v3_fast 544 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1371 : my_sum 1371 = 1316 := by
  rw [my_sum, my_sum_1370, tot_1371]
  have h : v3_fast 912 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1372 : my_sum 1372 = 1317 := by
  rw [my_sum, my_sum_1371, tot_1372]
  have h : v3_fast 588 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1373 : my_sum 1373 = 1317 := by
  rw [my_sum, my_sum_1372, tot_1373]
  have h : v3_fast 1372 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1374 : my_sum 1374 = 1318 := by
  rw [my_sum, my_sum_1373, tot_1374]
  have h : v3_fast 456 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1375 : my_sum 1375 = 1318 := by
  rw [my_sum, my_sum_1374, tot_1375]
  have h : v3_fast 1000 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1376 : my_sum 1376 = 1319 := by
  rw [my_sum, my_sum_1375, tot_1376]
  have h : v3_fast 672 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1377 : my_sum 1377 = 1322 := by
  rw [my_sum, my_sum_1376, tot_1377]
  have h : v3_fast 864 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1378 : my_sum 1378 = 1323 := by
  rw [my_sum, my_sum_1377, tot_1378]
  have h : v3_fast 624 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1379 : my_sum 1379 = 1324 := by
  rw [my_sum, my_sum_1378, tot_1379]
  have h : v3_fast 1176 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1380 : my_sum 1380 = 1324 := by
  rw [my_sum, my_sum_1379, tot_1380]
  have h : v3_fast 352 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1381 : my_sum 1381 = 1325 := by
  rw [my_sum, my_sum_1380, tot_1381]
  have h : v3_fast 1380 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1382 : my_sum 1382 = 1326 := by
  rw [my_sum, my_sum_1381, tot_1382]
  have h : v3_fast 690 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1383 : my_sum 1383 = 1326 := by
  rw [my_sum, my_sum_1382, tot_1383]
  have h : v3_fast 920 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1384 : my_sum 1384 = 1326 := by
  rw [my_sum, my_sum_1383, tot_1384]
  have h : v3_fast 688 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1385 : my_sum 1385 = 1327 := by
  rw [my_sum, my_sum_1384, tot_1385]
  have h : v3_fast 1104 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1386 : my_sum 1386 = 1329 := by
  rw [my_sum, my_sum_1385, tot_1386]
  have h : v3_fast 360 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1387 : my_sum 1387 = 1333 := by
  rw [my_sum, my_sum_1386, tot_1387]
  have h : v3_fast 1296 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_1388 : my_sum 1388 = 1333 := by
  rw [my_sum, my_sum_1387, tot_1388]
  have h : v3_fast 692 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1389 : my_sum 1389 = 1334 := by
  rw [my_sum, my_sum_1388, tot_1389]
  have h : v3_fast 924 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1390 : my_sum 1390 = 1335 := by
  rw [my_sum, my_sum_1389, tot_1390]
  have h : v3_fast 552 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1391 : my_sum 1391 = 1336 := by
  rw [my_sum, my_sum_1390, tot_1391]
  have h : v3_fast 1272 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1392 : my_sum 1392 = 1336 := by
  rw [my_sum, my_sum_1391, tot_1392]
  have h : v3_fast 448 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1393 : my_sum 1393 = 1339 := by
  rw [my_sum, my_sum_1392, tot_1393]
  have h : v3_fast 1188 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1394 : my_sum 1394 = 1339 := by
  rw [my_sum, my_sum_1393, tot_1394]
  have h : v3_fast 640 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1395 : my_sum 1395 = 1341 := by
  rw [my_sum, my_sum_1394, tot_1395]
  have h : v3_fast 720 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1396 : my_sum 1396 = 1342 := by
  rw [my_sum, my_sum_1395, tot_1396]
  have h : v3_fast 696 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1397 : my_sum 1397 = 1344 := by
  rw [my_sum, my_sum_1396, tot_1397]
  have h : v3_fast 1260 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1398 : my_sum 1398 = 1344 := by
  rw [my_sum, my_sum_1397, tot_1398]
  have h : v3_fast 464 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1399 : my_sum 1399 = 1345 := by
  rw [my_sum, my_sum_1398, tot_1399]
  have h : v3_fast 1398 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1400 : my_sum 1400 = 1346 := by
  rw [my_sum, my_sum_1399, tot_1400]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1401 : my_sum 1401 = 1346 := by
  rw [my_sum, my_sum_1400, tot_1401]
  have h : v3_fast 932 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1402 : my_sum 1402 = 1346 := by
  rw [my_sum, my_sum_1401, tot_1402]
  have h : v3_fast 700 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1403 : my_sum 1403 = 1347 := by
  rw [my_sum, my_sum_1402, tot_1403]
  have h : v3_fast 1320 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1404 : my_sum 1404 = 1350 := by
  rw [my_sum, my_sum_1403, tot_1404]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1405 : my_sum 1405 = 1350 := by
  rw [my_sum, my_sum_1404, tot_1405]
  have h : v3_fast 1120 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1406 : my_sum 1406 = 1354 := by
  rw [my_sum, my_sum_1405, tot_1406]
  have h : v3_fast 648 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_1407 : my_sum 1407 = 1356 := by
  rw [my_sum, my_sum_1406, tot_1407]
  have h : v3_fast 792 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1408 : my_sum 1408 = 1356 := by
  rw [my_sum, my_sum_1407, tot_1408]
  have h : v3_fast 640 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1409 : my_sum 1409 = 1356 := by
  rw [my_sum, my_sum_1408, tot_1409]
  have h : v3_fast 1408 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1410 : my_sum 1410 = 1356 := by
  rw [my_sum, my_sum_1409, tot_1410]
  have h : v3_fast 368 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1411 : my_sum 1411 = 1356 := by
  rw [my_sum, my_sum_1410, tot_1411]
  have h : v3_fast 1312 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1412 : my_sum 1412 = 1356 := by
  rw [my_sum, my_sum_1411, tot_1412]
  have h : v3_fast 704 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1413 : my_sum 1413 = 1358 := by
  rw [my_sum, my_sum_1412, tot_1413]
  have h : v3_fast 936 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1414 : my_sum 1414 = 1359 := by
  rw [my_sum, my_sum_1413, tot_1414]
  have h : v3_fast 600 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1415 : my_sum 1415 = 1360 := by
  rw [my_sum, my_sum_1414, tot_1415]
  have h : v3_fast 1128 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1416 : my_sum 1416 = 1360 := by
  rw [my_sum, my_sum_1415, tot_1416]
  have h : v3_fast 464 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1417 : my_sum 1417 = 1364 := by
  rw [my_sum, my_sum_1416, tot_1417]
  have h : v3_fast 1296 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_1418 : my_sum 1418 = 1365 := by
  rw [my_sum, my_sum_1417, tot_1418]
  have h : v3_fast 708 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1419 : my_sum 1419 = 1366 := by
  rw [my_sum, my_sum_1418, tot_1419]
  have h : v3_fast 840 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1420 : my_sum 1420 = 1366 := by
  rw [my_sum, my_sum_1419, tot_1420]
  have h : v3_fast 560 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1421 : my_sum 1421 = 1367 := by
  rw [my_sum, my_sum_1420, tot_1421]
  have h : v3_fast 1176 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1422 : my_sum 1422 = 1369 := by
  rw [my_sum, my_sum_1421, tot_1422]
  have h : v3_fast 468 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1423 : my_sum 1423 = 1371 := by
  rw [my_sum, my_sum_1422, tot_1423]
  have h : v3_fast 1422 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1424 : my_sum 1424 = 1371 := by
  rw [my_sum, my_sum_1423, tot_1424]
  have h : v3_fast 704 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1425 : my_sum 1425 = 1373 := by
  rw [my_sum, my_sum_1424, tot_1425]
  have h : v3_fast 720 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1426 : my_sum 1426 = 1374 := by
  rw [my_sum, my_sum_1425, tot_1426]
  have h : v3_fast 660 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1427 : my_sum 1427 = 1374 := by
  rw [my_sum, my_sum_1426, tot_1427]
  have h : v3_fast 1426 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1428 : my_sum 1428 = 1375 := by
  rw [my_sum, my_sum_1427, tot_1428]
  have h : v3_fast 384 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1429 : my_sum 1429 = 1376 := by
  rw [my_sum, my_sum_1428, tot_1429]
  have h : v3_fast 1428 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1430 : my_sum 1430 = 1377 := by
  rw [my_sum, my_sum_1429, tot_1430]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1431 : my_sum 1431 = 1379 := by
  rw [my_sum, my_sum_1430, tot_1431]
  have h : v3_fast 936 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1432 : my_sum 1432 = 1379 := by
  rw [my_sum, my_sum_1431, tot_1432]
  have h : v3_fast 712 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1433 : my_sum 1433 = 1379 := by
  rw [my_sum, my_sum_1432, tot_1433]
  have h : v3_fast 1432 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1434 : my_sum 1434 = 1379 := by
  rw [my_sum, my_sum_1433, tot_1434]
  have h : v3_fast 476 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1435 : my_sum 1435 = 1380 := by
  rw [my_sum, my_sum_1434, tot_1435]
  have h : v3_fast 960 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1436 : my_sum 1436 = 1380 := by
  rw [my_sum, my_sum_1435, tot_1436]
  have h : v3_fast 716 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1437 : my_sum 1437 = 1380 := by
  rw [my_sum, my_sum_1436, tot_1437]
  have h : v3_fast 956 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1438 : my_sum 1438 = 1380 := by
  rw [my_sum, my_sum_1437, tot_1438]
  have h : v3_fast 718 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1439 : my_sum 1439 = 1380 := by
  rw [my_sum, my_sum_1438, tot_1439]
  have h : v3_fast 1438 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1440 : my_sum 1440 = 1381 := by
  rw [my_sum, my_sum_1439, tot_1440]
  have h : v3_fast 384 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1441 : my_sum 1441 = 1381 := by
  rw [my_sum, my_sum_1440, tot_1441]
  have h : v3_fast 1300 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1442 : my_sum 1442 = 1383 := by
  rw [my_sum, my_sum_1441, tot_1442]
  have h : v3_fast 612 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1443 : my_sum 1443 = 1386 := by
  rw [my_sum, my_sum_1442, tot_1443]
  have h : v3_fast 864 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1444 : my_sum 1444 = 1388 := by
  rw [my_sum, my_sum_1443, tot_1444]
  have h : v3_fast 684 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1445 : my_sum 1445 = 1388 := by
  rw [my_sum, my_sum_1444, tot_1445]
  have h : v3_fast 1088 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1446 : my_sum 1446 = 1389 := by
  rw [my_sum, my_sum_1445, tot_1446]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1447 : my_sum 1447 = 1390 := by
  rw [my_sum, my_sum_1446, tot_1447]
  have h : v3_fast 1446 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1448 : my_sum 1448 = 1392 := by
  rw [my_sum, my_sum_1447, tot_1448]
  have h : v3_fast 720 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1449 : my_sum 1449 = 1394 := by
  rw [my_sum, my_sum_1448, tot_1449]
  have h : v3_fast 792 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1450 : my_sum 1450 = 1394 := by
  rw [my_sum, my_sum_1449, tot_1450]
  have h : v3_fast 560 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1451 : my_sum 1451 = 1394 := by
  rw [my_sum, my_sum_1450, tot_1451]
  have h : v3_fast 1450 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1452 : my_sum 1452 = 1394 := by
  rw [my_sum, my_sum_1451, tot_1452]
  have h : v3_fast 440 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1453 : my_sum 1453 = 1395 := by
  rw [my_sum, my_sum_1452, tot_1453]
  have h : v3_fast 1452 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1454 : my_sum 1454 = 1396 := by
  rw [my_sum, my_sum_1453, tot_1454]
  have h : v3_fast 726 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1455 : my_sum 1455 = 1397 := by
  rw [my_sum, my_sum_1454, tot_1455]
  have h : v3_fast 768 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1456 : my_sum 1456 = 1399 := by
  rw [my_sum, my_sum_1455, tot_1456]
  have h : v3_fast 576 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1457 : my_sum 1457 = 1400 := by
  rw [my_sum, my_sum_1456, tot_1457]
  have h : v3_fast 1380 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1458 : my_sum 1458 = 1405 := by
  rw [my_sum, my_sum_1457, tot_1458]
  have h : v3_fast 486 100 = 5 := rfl
  rw [h] <;> decide

theorem my_sum_1459 : my_sum 1459 = 1411 := by
  rw [my_sum, my_sum_1458, tot_1459]
  have h : v3_fast 1458 100 = 6 := rfl
  rw [h] <;> decide

theorem my_sum_1460 : my_sum 1460 = 1413 := by
  rw [my_sum, my_sum_1459, tot_1460]
  have h : v3_fast 576 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1461 : my_sum 1461 = 1418 := by
  rw [my_sum, my_sum_1460, tot_1461]
  have h : v3_fast 972 100 = 5 := rfl
  rw [h] <;> decide

theorem my_sum_1462 : my_sum 1462 = 1419 := by
  rw [my_sum, my_sum_1461, tot_1462]
  have h : v3_fast 672 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1463 : my_sum 1463 = 1422 := by
  rw [my_sum, my_sum_1462, tot_1463]
  have h : v3_fast 1080 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1464 : my_sum 1464 = 1423 := by
  rw [my_sum, my_sum_1463, tot_1464]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1465 : my_sum 1465 = 1423 := by
  rw [my_sum, my_sum_1464, tot_1465]
  have h : v3_fast 1168 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1466 : my_sum 1466 = 1424 := by
  rw [my_sum, my_sum_1465, tot_1466]
  have h : v3_fast 732 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1467 : my_sum 1467 = 1429 := by
  rw [my_sum, my_sum_1466, tot_1467]
  have h : v3_fast 972 100 = 5 := rfl
  rw [h] <;> decide

theorem my_sum_1468 : my_sum 1468 = 1430 := by
  rw [my_sum, my_sum_1467, tot_1468]
  have h : v3_fast 732 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1469 : my_sum 1469 = 1431 := by
  rw [my_sum, my_sum_1468, tot_1469]
  have h : v3_fast 1344 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1470 : my_sum 1470 = 1432 := by
  rw [my_sum, my_sum_1469, tot_1470]
  have h : v3_fast 336 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1471 : my_sum 1471 = 1433 := by
  rw [my_sum, my_sum_1470, tot_1471]
  have h : v3_fast 1470 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1472 : my_sum 1472 = 1433 := by
  rw [my_sum, my_sum_1471, tot_1472]
  have h : v3_fast 704 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1473 : my_sum 1473 = 1433 := by
  rw [my_sum, my_sum_1472, tot_1473]
  have h : v3_fast 980 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1474 : my_sum 1474 = 1434 := by
  rw [my_sum, my_sum_1473, tot_1474]
  have h : v3_fast 660 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1475 : my_sum 1475 = 1434 := by
  rw [my_sum, my_sum_1474, tot_1475]
  have h : v3_fast 1160 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1476 : my_sum 1476 = 1435 := by
  rw [my_sum, my_sum_1475, tot_1476]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1477 : my_sum 1477 = 1437 := by
  rw [my_sum, my_sum_1476, tot_1477]
  have h : v3_fast 1260 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1478 : my_sum 1478 = 1439 := by
  rw [my_sum, my_sum_1477, tot_1478]
  have h : v3_fast 738 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1479 : my_sum 1479 = 1439 := by
  rw [my_sum, my_sum_1478, tot_1479]
  have h : v3_fast 896 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1480 : my_sum 1480 = 1441 := by
  rw [my_sum, my_sum_1479, tot_1480]
  have h : v3_fast 576 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1481 : my_sum 1481 = 1441 := by
  rw [my_sum, my_sum_1480, tot_1481]
  have h : v3_fast 1480 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1482 : my_sum 1482 = 1444 := by
  rw [my_sum, my_sum_1481, tot_1482]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1483 : my_sum 1483 = 1445 := by
  rw [my_sum, my_sum_1482, tot_1483]
  have h : v3_fast 1482 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1484 : my_sum 1484 = 1446 := by
  rw [my_sum, my_sum_1483, tot_1484]
  have h : v3_fast 624 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1485 : my_sum 1485 = 1448 := by
  rw [my_sum, my_sum_1484, tot_1485]
  have h : v3_fast 720 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1486 : my_sum 1486 = 1448 := by
  rw [my_sum, my_sum_1485, tot_1486]
  have h : v3_fast 742 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1487 : my_sum 1487 = 1448 := by
  rw [my_sum, my_sum_1486, tot_1487]
  have h : v3_fast 1486 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1488 : my_sum 1488 = 1449 := by
  rw [my_sum, my_sum_1487, tot_1488]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1489 : my_sum 1489 = 1450 := by
  rw [my_sum, my_sum_1488, tot_1489]
  have h : v3_fast 1488 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1490 : my_sum 1490 = 1450 := by
  rw [my_sum, my_sum_1489, tot_1490]
  have h : v3_fast 592 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1491 : my_sum 1491 = 1451 := by
  rw [my_sum, my_sum_1490, tot_1491]
  have h : v3_fast 840 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1492 : my_sum 1492 = 1452 := by
  rw [my_sum, my_sum_1491, tot_1492]
  have h : v3_fast 744 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1493 : my_sum 1493 = 1452 := by
  rw [my_sum, my_sum_1492, tot_1493]
  have h : v3_fast 1492 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1494 : my_sum 1494 = 1453 := by
  rw [my_sum, my_sum_1493, tot_1494]
  have h : v3_fast 492 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1495 : my_sum 1495 = 1454 := by
  rw [my_sum, my_sum_1494, tot_1495]
  have h : v3_fast 1056 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1496 : my_sum 1496 = 1454 := by
  rw [my_sum, my_sum_1495, tot_1496]
  have h : v3_fast 640 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1497 : my_sum 1497 = 1455 := by
  rw [my_sum, my_sum_1496, tot_1497]
  have h : v3_fast 996 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1498 : my_sum 1498 = 1456 := by
  rw [my_sum, my_sum_1497, tot_1498]
  have h : v3_fast 636 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1499 : my_sum 1499 = 1456 := by
  rw [my_sum, my_sum_1498, tot_1499]
  have h : v3_fast 1498 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1500 : my_sum 1500 = 1456 := by
  rw [my_sum, my_sum_1499, tot_1500]
  have h : v3_fast 400 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1501 : my_sum 1501 = 1459 := by
  rw [my_sum, my_sum_1500, tot_1501]
  have h : v3_fast 1404 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1502 : my_sum 1502 = 1460 := by
  rw [my_sum, my_sum_1501, tot_1502]
  have h : v3_fast 750 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1503 : my_sum 1503 = 1461 := by
  rw [my_sum, my_sum_1502, tot_1503]
  have h : v3_fast 996 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1504 : my_sum 1504 = 1461 := by
  rw [my_sum, my_sum_1503, tot_1504]
  have h : v3_fast 736 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1505 : my_sum 1505 = 1463 := by
  rw [my_sum, my_sum_1504, tot_1505]
  have h : v3_fast 1008 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1506 : my_sum 1506 = 1463 := by
  rw [my_sum, my_sum_1505, tot_1506]
  have h : v3_fast 500 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1507 : my_sum 1507 = 1463 := by
  rw [my_sum, my_sum_1506, tot_1507]
  have h : v3_fast 1360 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1508 : my_sum 1508 = 1464 := by
  rw [my_sum, my_sum_1507, tot_1508]
  have h : v3_fast 672 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1509 : my_sum 1509 = 1464 := by
  rw [my_sum, my_sum_1508, tot_1509]
  have h : v3_fast 1004 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1510 : my_sum 1510 = 1465 := by
  rw [my_sum, my_sum_1509, tot_1510]
  have h : v3_fast 600 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1511 : my_sum 1511 = 1465 := by
  rw [my_sum, my_sum_1510, tot_1511]
  have h : v3_fast 1510 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1512 : my_sum 1512 = 1468 := by
  rw [my_sum, my_sum_1511, tot_1512]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1513 : my_sum 1513 = 1468 := by
  rw [my_sum, my_sum_1512, tot_1513]
  have h : v3_fast 1408 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1514 : my_sum 1514 = 1471 := by
  rw [my_sum, my_sum_1513, tot_1514]
  have h : v3_fast 756 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1515 : my_sum 1515 = 1471 := by
  rw [my_sum, my_sum_1514, tot_1515]
  have h : v3_fast 800 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1516 : my_sum 1516 = 1474 := by
  rw [my_sum, my_sum_1515, tot_1516]
  have h : v3_fast 756 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1517 : my_sum 1517 = 1476 := by
  rw [my_sum, my_sum_1516, tot_1517]
  have h : v3_fast 1440 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1518 : my_sum 1518 = 1476 := by
  rw [my_sum, my_sum_1517, tot_1518]
  have h : v3_fast 440 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1519 : my_sum 1519 = 1478 := by
  rw [my_sum, my_sum_1518, tot_1519]
  have h : v3_fast 1260 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1520 : my_sum 1520 = 1480 := by
  rw [my_sum, my_sum_1519, tot_1520]
  have h : v3_fast 576 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1521 : my_sum 1521 = 1482 := by
  rw [my_sum, my_sum_1520, tot_1521]
  have h : v3_fast 936 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1522 : my_sum 1522 = 1482 := by
  rw [my_sum, my_sum_1521, tot_1522]
  have h : v3_fast 760 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1523 : my_sum 1523 = 1482 := by
  rw [my_sum, my_sum_1522, tot_1523]
  have h : v3_fast 1522 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1524 : my_sum 1524 = 1484 := by
  rw [my_sum, my_sum_1523, tot_1524]
  have h : v3_fast 504 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1525 : my_sum 1525 = 1485 := by
  rw [my_sum, my_sum_1524, tot_1525]
  have h : v3_fast 1200 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1526 : my_sum 1526 = 1489 := by
  rw [my_sum, my_sum_1525, tot_1526]
  have h : v3_fast 648 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_1527 : my_sum 1527 = 1489 := by
  rw [my_sum, my_sum_1526, tot_1527]
  have h : v3_fast 1016 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1528 : my_sum 1528 = 1489 := by
  rw [my_sum, my_sum_1527, tot_1528]
  have h : v3_fast 760 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1529 : my_sum 1529 = 1490 := by
  rw [my_sum, my_sum_1528, tot_1529]
  have h : v3_fast 1380 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1530 : my_sum 1530 = 1491 := by
  rw [my_sum, my_sum_1529, tot_1530]
  have h : v3_fast 384 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1531 : my_sum 1531 = 1493 := by
  rw [my_sum, my_sum_1530, tot_1531]
  have h : v3_fast 1530 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1532 : my_sum 1532 = 1493 := by
  rw [my_sum, my_sum_1531, tot_1532]
  have h : v3_fast 764 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1533 : my_sum 1533 = 1496 := by
  rw [my_sum, my_sum_1532, tot_1533]
  have h : v3_fast 864 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1534 : my_sum 1534 = 1497 := by
  rw [my_sum, my_sum_1533, tot_1534]
  have h : v3_fast 696 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1535 : my_sum 1535 = 1499 := by
  rw [my_sum, my_sum_1534, tot_1535]
  have h : v3_fast 1224 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1536 : my_sum 1536 = 1499 := by
  rw [my_sum, my_sum_1535, tot_1536]
  have h : v3_fast 512 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1537 : my_sum 1537 = 1499 := by
  rw [my_sum, my_sum_1536, tot_1537]
  have h : v3_fast 1456 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1538 : my_sum 1538 = 1500 := by
  rw [my_sum, my_sum_1537, tot_1538]
  have h : v3_fast 768 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1539 : my_sum 1539 = 1505 := by
  rw [my_sum, my_sum_1538, tot_1539]
  have h : v3_fast 972 100 = 5 := rfl
  rw [h] <;> decide

theorem my_sum_1540 : my_sum 1540 = 1506 := by
  rw [my_sum, my_sum_1539, tot_1540]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1541 : my_sum 1541 = 1507 := by
  rw [my_sum, my_sum_1540, tot_1541]
  have h : v3_fast 1452 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1542 : my_sum 1542 = 1507 := by
  rw [my_sum, my_sum_1541, tot_1542]
  have h : v3_fast 512 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1543 : my_sum 1543 = 1508 := by
  rw [my_sum, my_sum_1542, tot_1543]
  have h : v3_fast 1542 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1544 : my_sum 1544 = 1509 := by
  rw [my_sum, my_sum_1543, tot_1544]
  have h : v3_fast 768 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1545 : my_sum 1545 = 1510 := by
  rw [my_sum, my_sum_1544, tot_1545]
  have h : v3_fast 816 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1546 : my_sum 1546 = 1510 := by
  rw [my_sum, my_sum_1545, tot_1546]
  have h : v3_fast 772 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1547 : my_sum 1547 = 1512 := by
  rw [my_sum, my_sum_1546, tot_1547]
  have h : v3_fast 1152 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1548 : my_sum 1548 = 1514 := by
  rw [my_sum, my_sum_1547, tot_1548]
  have h : v3_fast 504 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1549 : my_sum 1549 = 1516 := by
  rw [my_sum, my_sum_1548, tot_1549]
  have h : v3_fast 1548 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1550 : my_sum 1550 = 1517 := by
  rw [my_sum, my_sum_1549, tot_1550]
  have h : v3_fast 600 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1551 : my_sum 1551 = 1517 := by
  rw [my_sum, my_sum_1550, tot_1551]
  have h : v3_fast 920 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1552 : my_sum 1552 = 1518 := by
  rw [my_sum, my_sum_1551, tot_1552]
  have h : v3_fast 768 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1553 : my_sum 1553 = 1518 := by
  rw [my_sum, my_sum_1552, tot_1553]
  have h : v3_fast 1552 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1554 : my_sum 1554 = 1521 := by
  rw [my_sum, my_sum_1553, tot_1554]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1555 : my_sum 1555 = 1521 := by
  rw [my_sum, my_sum_1554, tot_1555]
  have h : v3_fast 1240 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1556 : my_sum 1556 = 1521 := by
  rw [my_sum, my_sum_1555, tot_1556]
  have h : v3_fast 776 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1557 : my_sum 1557 = 1522 := by
  rw [my_sum, my_sum_1556, tot_1557]
  have h : v3_fast 1032 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1558 : my_sum 1558 = 1524 := by
  rw [my_sum, my_sum_1557, tot_1558]
  have h : v3_fast 720 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1559 : my_sum 1559 = 1524 := by
  rw [my_sum, my_sum_1558, tot_1559]
  have h : v3_fast 1558 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1560 : my_sum 1560 = 1525 := by
  rw [my_sum, my_sum_1559, tot_1560]
  have h : v3_fast 384 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1561 : my_sum 1561 = 1527 := by
  rw [my_sum, my_sum_1560, tot_1561]
  have h : v3_fast 1332 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1562 : my_sum 1562 = 1527 := by
  rw [my_sum, my_sum_1561, tot_1562]
  have h : v3_fast 700 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1563 : my_sum 1563 = 1527 := by
  rw [my_sum, my_sum_1562, tot_1563]
  have h : v3_fast 1040 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1564 : my_sum 1564 = 1527 := by
  rw [my_sum, my_sum_1563, tot_1564]
  have h : v3_fast 704 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1565 : my_sum 1565 = 1528 := by
  rw [my_sum, my_sum_1564, tot_1565]
  have h : v3_fast 1248 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1566 : my_sum 1566 = 1530 := by
  rw [my_sum, my_sum_1565, tot_1566]
  have h : v3_fast 504 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1567 : my_sum 1567 = 1533 := by
  rw [my_sum, my_sum_1566, tot_1567]
  have h : v3_fast 1566 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1568 : my_sum 1568 = 1534 := by
  rw [my_sum, my_sum_1567, tot_1568]
  have h : v3_fast 672 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1569 : my_sum 1569 = 1536 := by
  rw [my_sum, my_sum_1568, tot_1569]
  have h : v3_fast 1044 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1570 : my_sum 1570 = 1537 := by
  rw [my_sum, my_sum_1569, tot_1570]
  have h : v3_fast 624 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1571 : my_sum 1571 = 1537 := by
  rw [my_sum, my_sum_1570, tot_1571]
  have h : v3_fast 1570 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1572 : my_sum 1572 = 1537 := by
  rw [my_sum, my_sum_1571, tot_1572]
  have h : v3_fast 520 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1573 : my_sum 1573 = 1538 := by
  rw [my_sum, my_sum_1572, tot_1573]
  have h : v3_fast 1320 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1574 : my_sum 1574 = 1539 := by
  rw [my_sum, my_sum_1573, tot_1574]
  have h : v3_fast 786 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1575 : my_sum 1575 = 1541 := by
  rw [my_sum, my_sum_1574, tot_1575]
  have h : v3_fast 720 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1576 : my_sum 1576 = 1541 := by
  rw [my_sum, my_sum_1575, tot_1576]
  have h : v3_fast 784 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1577 : my_sum 1577 = 1543 := by
  rw [my_sum, my_sum_1576, tot_1577]
  have h : v3_fast 1476 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1578 : my_sum 1578 = 1543 := by
  rw [my_sum, my_sum_1577, tot_1578]
  have h : v3_fast 524 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1579 : my_sum 1579 = 1544 := by
  rw [my_sum, my_sum_1578, tot_1579]
  have h : v3_fast 1578 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1580 : my_sum 1580 = 1545 := by
  rw [my_sum, my_sum_1579, tot_1580]
  have h : v3_fast 624 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1581 : my_sum 1581 = 1546 := by
  rw [my_sum, my_sum_1580, tot_1581]
  have h : v3_fast 960 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1582 : my_sum 1582 = 1547 := by
  rw [my_sum, my_sum_1581, tot_1582]
  have h : v3_fast 672 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1583 : my_sum 1583 = 1547 := by
  rw [my_sum, my_sum_1582, tot_1583]
  have h : v3_fast 1582 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1584 : my_sum 1584 = 1548 := by
  rw [my_sum, my_sum_1583, tot_1584]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1585 : my_sum 1585 = 1548 := by
  rw [my_sum, my_sum_1584, tot_1585]
  have h : v3_fast 1264 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1586 : my_sum 1586 = 1550 := by
  rw [my_sum, my_sum_1585, tot_1586]
  have h : v3_fast 720 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1587 : my_sum 1587 = 1550 := by
  rw [my_sum, my_sum_1586, tot_1587]
  have h : v3_fast 1012 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1588 : my_sum 1588 = 1552 := by
  rw [my_sum, my_sum_1587, tot_1588]
  have h : v3_fast 792 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1589 : my_sum 1589 = 1553 := by
  rw [my_sum, my_sum_1588, tot_1589]
  have h : v3_fast 1356 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1590 : my_sum 1590 = 1553 := by
  rw [my_sum, my_sum_1589, tot_1590]
  have h : v3_fast 416 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1591 : my_sum 1591 = 1556 := by
  rw [my_sum, my_sum_1590, tot_1591]
  have h : v3_fast 1512 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1592 : my_sum 1592 = 1558 := by
  rw [my_sum, my_sum_1591, tot_1592]
  have h : v3_fast 792 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1593 : my_sum 1593 = 1560 := by
  rw [my_sum, my_sum_1592, tot_1593]
  have h : v3_fast 1044 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1594 : my_sum 1594 = 1560 := by
  rw [my_sum, my_sum_1593, tot_1594]
  have h : v3_fast 796 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1595 : my_sum 1595 = 1560 := by
  rw [my_sum, my_sum_1594, tot_1595]
  have h : v3_fast 1120 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1596 : my_sum 1596 = 1563 := by
  rw [my_sum, my_sum_1595, tot_1596]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1597 : my_sum 1597 = 1564 := by
  rw [my_sum, my_sum_1596, tot_1597]
  have h : v3_fast 1596 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1598 : my_sum 1598 = 1564 := by
  rw [my_sum, my_sum_1597, tot_1598]
  have h : v3_fast 736 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1599 : my_sum 1599 = 1565 := by
  rw [my_sum, my_sum_1598, tot_1599]
  have h : v3_fast 960 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1600 : my_sum 1600 = 1565 := by
  rw [my_sum, my_sum_1599, tot_1600]
  have h : v3_fast 640 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1601 : my_sum 1601 = 1565 := by
  rw [my_sum, my_sum_1600, tot_1601]
  have h : v3_fast 1600 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1602 : my_sum 1602 = 1566 := by
  rw [my_sum, my_sum_1601, tot_1602]
  have h : v3_fast 528 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1603 : my_sum 1603 = 1568 := by
  rw [my_sum, my_sum_1602, tot_1603]
  have h : v3_fast 1368 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1604 : my_sum 1604 = 1568 := by
  rw [my_sum, my_sum_1603, tot_1604]
  have h : v3_fast 800 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1605 : my_sum 1605 = 1568 := by
  rw [my_sum, my_sum_1604, tot_1605]
  have h : v3_fast 848 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1606 : my_sum 1606 = 1570 := by
  rw [my_sum, my_sum_1605, tot_1606]
  have h : v3_fast 720 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1607 : my_sum 1607 = 1570 := by
  rw [my_sum, my_sum_1606, tot_1607]
  have h : v3_fast 1606 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1608 : my_sum 1608 = 1571 := by
  rw [my_sum, my_sum_1607, tot_1608]
  have h : v3_fast 528 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1609 : my_sum 1609 = 1572 := by
  rw [my_sum, my_sum_1608, tot_1609]
  have h : v3_fast 1608 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1610 : my_sum 1610 = 1573 := by
  rw [my_sum, my_sum_1609, tot_1610]
  have h : v3_fast 528 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1611 : my_sum 1611 = 1574 := by
  rw [my_sum, my_sum_1610, tot_1611]
  have h : v3_fast 1068 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1612 : my_sum 1612 = 1576 := by
  rw [my_sum, my_sum_1611, tot_1612]
  have h : v3_fast 720 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1613 : my_sum 1613 = 1576 := by
  rw [my_sum, my_sum_1612, tot_1613]
  have h : v3_fast 1612 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1614 : my_sum 1614 = 1576 := by
  rw [my_sum, my_sum_1613, tot_1614]
  have h : v3_fast 536 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1615 : my_sum 1615 = 1578 := by
  rw [my_sum, my_sum_1614, tot_1615]
  have h : v3_fast 1152 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1616 : my_sum 1616 = 1578 := by
  rw [my_sum, my_sum_1615, tot_1616]
  have h : v3_fast 800 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1617 : my_sum 1617 = 1579 := by
  rw [my_sum, my_sum_1616, tot_1617]
  have h : v3_fast 840 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1618 : my_sum 1618 = 1579 := by
  rw [my_sum, my_sum_1617, tot_1618]
  have h : v3_fast 808 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1619 : my_sum 1619 = 1579 := by
  rw [my_sum, my_sum_1618, tot_1619]
  have h : v3_fast 1618 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1620 : my_sum 1620 = 1582 := by
  rw [my_sum, my_sum_1619, tot_1620]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1621 : my_sum 1621 = 1586 := by
  rw [my_sum, my_sum_1620, tot_1621]
  have h : v3_fast 1620 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_1622 : my_sum 1622 = 1590 := by
  rw [my_sum, my_sum_1621, tot_1622]
  have h : v3_fast 810 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_1623 : my_sum 1623 = 1593 := by
  rw [my_sum, my_sum_1622, tot_1623]
  have h : v3_fast 1080 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1624 : my_sum 1624 = 1594 := by
  rw [my_sum, my_sum_1623, tot_1624]
  have h : v3_fast 672 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1625 : my_sum 1625 = 1595 := by
  rw [my_sum, my_sum_1624, tot_1625]
  have h : v3_fast 1200 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1626 : my_sum 1626 = 1598 := by
  rw [my_sum, my_sum_1625, tot_1626]
  have h : v3_fast 540 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1627 : my_sum 1627 = 1599 := by
  rw [my_sum, my_sum_1626, tot_1627]
  have h : v3_fast 1626 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1628 : my_sum 1628 = 1601 := by
  rw [my_sum, my_sum_1627, tot_1628]
  have h : v3_fast 720 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1629 : my_sum 1629 = 1604 := by
  rw [my_sum, my_sum_1628, tot_1629]
  have h : v3_fast 1080 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1630 : my_sum 1630 = 1608 := by
  rw [my_sum, my_sum_1629, tot_1630]
  have h : v3_fast 648 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_1631 : my_sum 1631 = 1609 := by
  rw [my_sum, my_sum_1630, tot_1631]
  have h : v3_fast 1392 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1632 : my_sum 1632 = 1609 := by
  rw [my_sum, my_sum_1631, tot_1632]
  have h : v3_fast 512 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1633 : my_sum 1633 = 1609 := by
  rw [my_sum, my_sum_1632, tot_1633]
  have h : v3_fast 1540 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1634 : my_sum 1634 = 1612 := by
  rw [my_sum, my_sum_1633, tot_1634]
  have h : v3_fast 756 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1635 : my_sum 1635 = 1615 := by
  rw [my_sum, my_sum_1634, tot_1635]
  have h : v3_fast 864 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1636 : my_sum 1636 = 1616 := by
  rw [my_sum, my_sum_1635, tot_1636]
  have h : v3_fast 816 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1637 : my_sum 1637 = 1616 := by
  rw [my_sum, my_sum_1636, tot_1637]
  have h : v3_fast 1636 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1638 : my_sum 1638 = 1619 := by
  rw [my_sum, my_sum_1637, tot_1638]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1639 : my_sum 1639 = 1619 := by
  rw [my_sum, my_sum_1638, tot_1639]
  have h : v3_fast 1480 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1640 : my_sum 1640 = 1619 := by
  rw [my_sum, my_sum_1639, tot_1640]
  have h : v3_fast 640 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1641 : my_sum 1641 = 1620 := by
  rw [my_sum, my_sum_1640, tot_1641]
  have h : v3_fast 1092 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1642 : my_sum 1642 = 1620 := by
  rw [my_sum, my_sum_1641, tot_1642]
  have h : v3_fast 820 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1643 : my_sum 1643 = 1621 := by
  rw [my_sum, my_sum_1642, tot_1643]
  have h : v3_fast 1560 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1644 : my_sum 1644 = 1621 := by
  rw [my_sum, my_sum_1643, tot_1644]
  have h : v3_fast 544 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1645 : my_sum 1645 = 1622 := by
  rw [my_sum, my_sum_1644, tot_1645]
  have h : v3_fast 1104 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1646 : my_sum 1646 = 1623 := by
  rw [my_sum, my_sum_1645, tot_1646]
  have h : v3_fast 822 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1647 : my_sum 1647 = 1626 := by
  rw [my_sum, my_sum_1646, tot_1647]
  have h : v3_fast 1080 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1648 : my_sum 1648 = 1627 := by
  rw [my_sum, my_sum_1647, tot_1648]
  have h : v3_fast 816 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1649 : my_sum 1649 = 1628 := by
  rw [my_sum, my_sum_1648, tot_1649]
  have h : v3_fast 1536 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1650 : my_sum 1650 = 1628 := by
  rw [my_sum, my_sum_1649, tot_1650]
  have h : v3_fast 400 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1651 : my_sum 1651 = 1631 := by
  rw [my_sum, my_sum_1650, tot_1651]
  have h : v3_fast 1512 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1652 : my_sum 1652 = 1632 := by
  rw [my_sum, my_sum_1651, tot_1652]
  have h : v3_fast 696 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1653 : my_sum 1653 = 1634 := by
  rw [my_sum, my_sum_1652, tot_1653]
  have h : v3_fast 1008 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1654 : my_sum 1654 = 1634 := by
  rw [my_sum, my_sum_1653, tot_1654]
  have h : v3_fast 826 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1655 : my_sum 1655 = 1635 := by
  rw [my_sum, my_sum_1654, tot_1655]
  have h : v3_fast 1320 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1656 : my_sum 1656 = 1636 := by
  rw [my_sum, my_sum_1655, tot_1656]
  have h : v3_fast 528 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1657 : my_sum 1657 = 1638 := by
  rw [my_sum, my_sum_1656, tot_1657]
  have h : v3_fast 1656 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1658 : my_sum 1658 = 1640 := by
  rw [my_sum, my_sum_1657, tot_1658]
  have h : v3_fast 828 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1659 : my_sum 1659 = 1642 := by
  rw [my_sum, my_sum_1658, tot_1659]
  have h : v3_fast 936 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1660 : my_sum 1660 = 1642 := by
  rw [my_sum, my_sum_1659, tot_1660]
  have h : v3_fast 656 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1661 : my_sum 1661 = 1643 := by
  rw [my_sum, my_sum_1660, tot_1661]
  have h : v3_fast 1500 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1662 : my_sum 1662 = 1644 := by
  rw [my_sum, my_sum_1661, tot_1662]
  have h : v3_fast 552 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1663 : my_sum 1663 = 1645 := by
  rw [my_sum, my_sum_1662, tot_1663]
  have h : v3_fast 1662 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1664 : my_sum 1664 = 1646 := by
  rw [my_sum, my_sum_1663, tot_1664]
  have h : v3_fast 768 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1665 : my_sum 1665 = 1649 := by
  rw [my_sum, my_sum_1664, tot_1665]
  have h : v3_fast 864 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1666 : my_sum 1666 = 1650 := by
  rw [my_sum, my_sum_1665, tot_1666]
  have h : v3_fast 672 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1667 : my_sum 1667 = 1650 := by
  rw [my_sum, my_sum_1666, tot_1667]
  have h : v3_fast 1666 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1668 : my_sum 1668 = 1651 := by
  rw [my_sum, my_sum_1667, tot_1668]
  have h : v3_fast 552 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1669 : my_sum 1669 = 1652 := by
  rw [my_sum, my_sum_1668, tot_1669]
  have h : v3_fast 1668 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1670 : my_sum 1670 = 1652 := by
  rw [my_sum, my_sum_1669, tot_1670]
  have h : v3_fast 664 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1671 : my_sum 1671 = 1652 := by
  rw [my_sum, my_sum_1670, tot_1671]
  have h : v3_fast 1112 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1672 : my_sum 1672 = 1654 := by
  rw [my_sum, my_sum_1671, tot_1672]
  have h : v3_fast 720 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1673 : my_sum 1673 = 1655 := by
  rw [my_sum, my_sum_1672, tot_1673]
  have h : v3_fast 1428 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1674 : my_sum 1674 = 1658 := by
  rw [my_sum, my_sum_1673, tot_1674]
  have h : v3_fast 540 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1675 : my_sum 1675 = 1659 := by
  rw [my_sum, my_sum_1674, tot_1675]
  have h : v3_fast 1320 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1676 : my_sum 1676 = 1659 := by
  rw [my_sum, my_sum_1675, tot_1676]
  have h : v3_fast 836 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1677 : my_sum 1677 = 1661 := by
  rw [my_sum, my_sum_1676, tot_1677]
  have h : v3_fast 1008 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1678 : my_sum 1678 = 1661 := by
  rw [my_sum, my_sum_1677, tot_1678]
  have h : v3_fast 838 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1679 : my_sum 1679 = 1663 := by
  rw [my_sum, my_sum_1678, tot_1679]
  have h : v3_fast 1584 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1680 : my_sum 1680 = 1664 := by
  rw [my_sum, my_sum_1679, tot_1680]
  have h : v3_fast 384 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1681 : my_sum 1681 = 1664 := by
  rw [my_sum, my_sum_1680, tot_1681]
  have h : v3_fast 1640 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1682 : my_sum 1682 = 1664 := by
  rw [my_sum, my_sum_1681, tot_1682]
  have h : v3_fast 812 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1683 : my_sum 1683 = 1665 := by
  rw [my_sum, my_sum_1682, tot_1683]
  have h : v3_fast 960 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1684 : my_sum 1684 = 1666 := by
  rw [my_sum, my_sum_1683, tot_1684]
  have h : v3_fast 840 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1685 : my_sum 1685 = 1667 := by
  rw [my_sum, my_sum_1684, tot_1685]
  have h : v3_fast 1344 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1686 : my_sum 1686 = 1667 := by
  rw [my_sum, my_sum_1685, tot_1686]
  have h : v3_fast 560 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1687 : my_sum 1687 = 1669 := by
  rw [my_sum, my_sum_1686, tot_1687]
  have h : v3_fast 1440 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1688 : my_sum 1688 = 1670 := by
  rw [my_sum, my_sum_1687, tot_1688]
  have h : v3_fast 840 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1689 : my_sum 1689 = 1670 := by
  rw [my_sum, my_sum_1688, tot_1689]
  have h : v3_fast 1124 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1690 : my_sum 1690 = 1671 := by
  rw [my_sum, my_sum_1689, tot_1690]
  have h : v3_fast 624 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1691 : my_sum 1691 = 1673 := by
  rw [my_sum, my_sum_1690, tot_1691]
  have h : v3_fast 1584 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1692 : my_sum 1692 = 1674 := by
  rw [my_sum, my_sum_1691, tot_1692]
  have h : v3_fast 552 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1693 : my_sum 1693 = 1676 := by
  rw [my_sum, my_sum_1692, tot_1693]
  have h : v3_fast 1692 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1694 : my_sum 1694 = 1677 := by
  rw [my_sum, my_sum_1693, tot_1694]
  have h : v3_fast 660 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1695 : my_sum 1695 = 1677 := by
  rw [my_sum, my_sum_1694, tot_1695]
  have h : v3_fast 896 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1696 : my_sum 1696 = 1677 := by
  rw [my_sum, my_sum_1695, tot_1696]
  have h : v3_fast 832 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1697 : my_sum 1697 = 1677 := by
  rw [my_sum, my_sum_1696, tot_1697]
  have h : v3_fast 1696 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1698 : my_sum 1698 = 1678 := by
  rw [my_sum, my_sum_1697, tot_1698]
  have h : v3_fast 564 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1699 : my_sum 1699 = 1679 := by
  rw [my_sum, my_sum_1698, tot_1699]
  have h : v3_fast 1698 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1700 : my_sum 1700 = 1679 := by
  rw [my_sum, my_sum_1699, tot_1700]
  have h : v3_fast 640 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1701 : my_sum 1701 = 1684 := by
  rw [my_sum, my_sum_1700, tot_1701]
  have h : v3_fast 972 100 = 5 := rfl
  rw [h] <;> decide

theorem my_sum_1702 : my_sum 1702 = 1686 := by
  rw [my_sum, my_sum_1701, tot_1702]
  have h : v3_fast 792 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1703 : my_sum 1703 = 1687 := by
  rw [my_sum, my_sum_1702, tot_1703]
  have h : v3_fast 1560 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1704 : my_sum 1704 = 1687 := by
  rw [my_sum, my_sum_1703, tot_1704]
  have h : v3_fast 560 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1705 : my_sum 1705 = 1688 := by
  rw [my_sum, my_sum_1704, tot_1705]
  have h : v3_fast 1200 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1706 : my_sum 1706 = 1689 := by
  rw [my_sum, my_sum_1705, tot_1706]
  have h : v3_fast 852 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1707 : my_sum 1707 = 1689 := by
  rw [my_sum, my_sum_1706, tot_1707]
  have h : v3_fast 1136 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1708 : my_sum 1708 = 1691 := by
  rw [my_sum, my_sum_1707, tot_1708]
  have h : v3_fast 720 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1709 : my_sum 1709 = 1691 := by
  rw [my_sum, my_sum_1708, tot_1709]
  have h : v3_fast 1708 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1710 : my_sum 1710 = 1694 := by
  rw [my_sum, my_sum_1709, tot_1710]
  have h : v3_fast 432 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1711 : my_sum 1711 = 1694 := by
  rw [my_sum, my_sum_1710, tot_1711]
  have h : v3_fast 1624 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1712 : my_sum 1712 = 1694 := by
  rw [my_sum, my_sum_1711, tot_1712]
  have h : v3_fast 848 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1713 : my_sum 1713 = 1695 := by
  rw [my_sum, my_sum_1712, tot_1713]
  have h : v3_fast 1140 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1714 : my_sum 1714 = 1695 := by
  rw [my_sum, my_sum_1713, tot_1714]
  have h : v3_fast 856 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1715 : my_sum 1715 = 1696 := by
  rw [my_sum, my_sum_1714, tot_1715]
  have h : v3_fast 1176 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1716 : my_sum 1716 = 1697 := by
  rw [my_sum, my_sum_1715, tot_1716]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1717 : my_sum 1717 = 1697 := by
  rw [my_sum, my_sum_1716, tot_1717]
  have h : v3_fast 1600 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1718 : my_sum 1718 = 1698 := by
  rw [my_sum, my_sum_1717, tot_1718]
  have h : v3_fast 858 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1719 : my_sum 1719 = 1699 := by
  rw [my_sum, my_sum_1718, tot_1719]
  have h : v3_fast 1140 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1720 : my_sum 1720 = 1700 := by
  rw [my_sum, my_sum_1719, tot_1720]
  have h : v3_fast 672 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1721 : my_sum 1721 = 1700 := by
  rw [my_sum, my_sum_1720, tot_1721]
  have h : v3_fast 1720 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1722 : my_sum 1722 = 1701 := by
  rw [my_sum, my_sum_1721, tot_1722]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1723 : my_sum 1723 = 1702 := by
  rw [my_sum, my_sum_1722, tot_1723]
  have h : v3_fast 1722 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1724 : my_sum 1724 = 1702 := by
  rw [my_sum, my_sum_1723, tot_1724]
  have h : v3_fast 860 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1725 : my_sum 1725 = 1702 := by
  rw [my_sum, my_sum_1724, tot_1725]
  have h : v3_fast 880 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1726 : my_sum 1726 = 1702 := by
  rw [my_sum, my_sum_1725, tot_1726]
  have h : v3_fast 862 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1727 : my_sum 1727 = 1703 := by
  rw [my_sum, my_sum_1726, tot_1727]
  have h : v3_fast 1560 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1728 : my_sum 1728 = 1705 := by
  rw [my_sum, my_sum_1727, tot_1728]
  have h : v3_fast 576 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1729 : my_sum 1729 = 1709 := by
  rw [my_sum, my_sum_1728, tot_1729]
  have h : v3_fast 1296 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_1730 : my_sum 1730 = 1709 := by
  rw [my_sum, my_sum_1729, tot_1730]
  have h : v3_fast 688 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1731 : my_sum 1731 = 1711 := by
  rw [my_sum, my_sum_1730, tot_1731]
  have h : v3_fast 1152 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1732 : my_sum 1732 = 1714 := by
  rw [my_sum, my_sum_1731, tot_1732]
  have h : v3_fast 864 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1733 : my_sum 1733 = 1714 := by
  rw [my_sum, my_sum_1732, tot_1733]
  have h : v3_fast 1732 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1734 : my_sum 1734 = 1714 := by
  rw [my_sum, my_sum_1733, tot_1734]
  have h : v3_fast 544 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1735 : my_sum 1735 = 1714 := by
  rw [my_sum, my_sum_1734, tot_1735]
  have h : v3_fast 1384 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1736 : my_sum 1736 = 1716 := by
  rw [my_sum, my_sum_1735, tot_1736]
  have h : v3_fast 720 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1737 : my_sum 1737 = 1718 := by
  rw [my_sum, my_sum_1736, tot_1737]
  have h : v3_fast 1152 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1738 : my_sum 1738 = 1719 := by
  rw [my_sum, my_sum_1737, tot_1738]
  have h : v3_fast 780 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1739 : my_sum 1739 = 1721 := by
  rw [my_sum, my_sum_1738, tot_1739]
  have h : v3_fast 1656 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1740 : my_sum 1740 = 1721 := by
  rw [my_sum, my_sum_1739, tot_1740]
  have h : v3_fast 448 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1741 : my_sum 1741 = 1722 := by
  rw [my_sum, my_sum_1740, tot_1741]
  have h : v3_fast 1740 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1742 : my_sum 1742 = 1724 := by
  rw [my_sum, my_sum_1741, tot_1742]
  have h : v3_fast 792 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1743 : my_sum 1743 = 1725 := by
  rw [my_sum, my_sum_1742, tot_1743]
  have h : v3_fast 984 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1744 : my_sum 1744 = 1728 := by
  rw [my_sum, my_sum_1743, tot_1744]
  have h : v3_fast 864 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1745 : my_sum 1745 = 1729 := by
  rw [my_sum, my_sum_1744, tot_1745]
  have h : v3_fast 1392 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1746 : my_sum 1746 = 1731 := by
  rw [my_sum, my_sum_1745, tot_1746]
  have h : v3_fast 576 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1747 : my_sum 1747 = 1733 := by
  rw [my_sum, my_sum_1746, tot_1747]
  have h : v3_fast 1746 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1748 : my_sum 1748 = 1735 := by
  rw [my_sum, my_sum_1747, tot_1748]
  have h : v3_fast 792 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1749 : my_sum 1749 = 1735 := by
  rw [my_sum, my_sum_1748, tot_1749]
  have h : v3_fast 1040 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1750 : my_sum 1750 = 1736 := by
  rw [my_sum, my_sum_1749, tot_1750]
  have h : v3_fast 600 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1751 : my_sum 1751 = 1737 := by
  rw [my_sum, my_sum_1750, tot_1751]
  have h : v3_fast 1632 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1752 : my_sum 1752 = 1739 := by
  rw [my_sum, my_sum_1751, tot_1752]
  have h : v3_fast 576 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1753 : my_sum 1753 = 1740 := by
  rw [my_sum, my_sum_1752, tot_1753]
  have h : v3_fast 1752 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1754 : my_sum 1754 = 1741 := by
  rw [my_sum, my_sum_1753, tot_1754]
  have h : v3_fast 876 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1755 : my_sum 1755 = 1744 := by
  rw [my_sum, my_sum_1754, tot_1755]
  have h : v3_fast 864 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1756 : my_sum 1756 = 1745 := by
  rw [my_sum, my_sum_1755, tot_1756]
  have h : v3_fast 876 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1757 : my_sum 1757 = 1746 := by
  rw [my_sum, my_sum_1756, tot_1757]
  have h : v3_fast 1500 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1758 : my_sum 1758 = 1746 := by
  rw [my_sum, my_sum_1757, tot_1758]
  have h : v3_fast 584 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1759 : my_sum 1759 = 1747 := by
  rw [my_sum, my_sum_1758, tot_1759]
  have h : v3_fast 1758 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1760 : my_sum 1760 = 1747 := by
  rw [my_sum, my_sum_1759, tot_1760]
  have h : v3_fast 640 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1761 : my_sum 1761 = 1747 := by
  rw [my_sum, my_sum_1760, tot_1761]
  have h : v3_fast 1172 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1762 : my_sum 1762 = 1747 := by
  rw [my_sum, my_sum_1761, tot_1762]
  have h : v3_fast 880 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1763 : my_sum 1763 = 1748 := by
  rw [my_sum, my_sum_1762, tot_1763]
  have h : v3_fast 1680 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1764 : my_sum 1764 = 1750 := by
  rw [my_sum, my_sum_1763, tot_1764]
  have h : v3_fast 504 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1765 : my_sum 1765 = 1750 := by
  rw [my_sum, my_sum_1764, tot_1765]
  have h : v3_fast 1408 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1766 : my_sum 1766 = 1752 := by
  rw [my_sum, my_sum_1765, tot_1766]
  have h : v3_fast 882 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1767 : my_sum 1767 = 1755 := by
  rw [my_sum, my_sum_1766, tot_1767]
  have h : v3_fast 1080 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1768 : my_sum 1768 = 1756 := by
  rw [my_sum, my_sum_1767, tot_1768]
  have h : v3_fast 768 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1769 : my_sum 1769 = 1757 := by
  rw [my_sum, my_sum_1768, tot_1769]
  have h : v3_fast 1680 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1770 : my_sum 1770 = 1757 := by
  rw [my_sum, my_sum_1769, tot_1770]
  have h : v3_fast 464 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1771 : my_sum 1771 = 1758 := by
  rw [my_sum, my_sum_1770, tot_1771]
  have h : v3_fast 1320 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1772 : my_sum 1772 = 1758 := by
  rw [my_sum, my_sum_1771, tot_1772]
  have h : v3_fast 884 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1773 : my_sum 1773 = 1759 := by
  rw [my_sum, my_sum_1772, tot_1773]
  have h : v3_fast 1176 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1774 : my_sum 1774 = 1759 := by
  rw [my_sum, my_sum_1773, tot_1774]
  have h : v3_fast 886 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1775 : my_sum 1775 = 1759 := by
  rw [my_sum, my_sum_1774, tot_1775]
  have h : v3_fast 1400 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1776 : my_sum 1776 = 1761 := by
  rw [my_sum, my_sum_1775, tot_1776]
  have h : v3_fast 576 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1777 : my_sum 1777 = 1762 := by
  rw [my_sum, my_sum_1776, tot_1777]
  have h : v3_fast 1776 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1778 : my_sum 1778 = 1765 := by
  rw [my_sum, my_sum_1777, tot_1778]
  have h : v3_fast 756 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1779 : my_sum 1779 = 1765 := by
  rw [my_sum, my_sum_1778, tot_1779]
  have h : v3_fast 1184 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1780 : my_sum 1780 = 1765 := by
  rw [my_sum, my_sum_1779, tot_1780]
  have h : v3_fast 704 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1781 : my_sum 1781 = 1766 := by
  rw [my_sum, my_sum_1780, tot_1781]
  have h : v3_fast 1632 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1782 : my_sum 1782 = 1769 := by
  rw [my_sum, my_sum_1781, tot_1782]
  have h : v3_fast 540 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1783 : my_sum 1783 = 1773 := by
  rw [my_sum, my_sum_1782, tot_1783]
  have h : v3_fast 1782 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_1784 : my_sum 1784 = 1774 := by
  rw [my_sum, my_sum_1783, tot_1784]
  have h : v3_fast 888 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1785 : my_sum 1785 = 1775 := by
  rw [my_sum, my_sum_1784, tot_1785]
  have h : v3_fast 768 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1786 : my_sum 1786 = 1777 := by
  rw [my_sum, my_sum_1785, tot_1786]
  have h : v3_fast 828 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1787 : my_sum 1787 = 1777 := by
  rw [my_sum, my_sum_1786, tot_1787]
  have h : v3_fast 1786 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1788 : my_sum 1788 = 1777 := by
  rw [my_sum, my_sum_1787, tot_1788]
  have h : v3_fast 592 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1789 : my_sum 1789 = 1778 := by
  rw [my_sum, my_sum_1788, tot_1789]
  have h : v3_fast 1788 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1790 : my_sum 1790 = 1778 := by
  rw [my_sum, my_sum_1789, tot_1790]
  have h : v3_fast 712 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1791 : my_sum 1791 = 1781 := by
  rw [my_sum, my_sum_1790, tot_1791]
  have h : v3_fast 1188 100 = 3 := rfl
  rw [h] <;> decide

theorem my_sum_1792 : my_sum 1792 = 1782 := by
  rw [my_sum, my_sum_1791, tot_1792]
  have h : v3_fast 768 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1793 : my_sum 1793 = 1786 := by
  rw [my_sum, my_sum_1792, tot_1793]
  have h : v3_fast 1620 100 = 4 := rfl
  rw [h] <;> decide

theorem my_sum_1794 : my_sum 1794 = 1787 := by
  rw [my_sum, my_sum_1793, tot_1794]
  have h : v3_fast 528 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1795 : my_sum 1795 = 1787 := by
  rw [my_sum, my_sum_1794, tot_1795]
  have h : v3_fast 1432 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1796 : my_sum 1796 = 1787 := by
  rw [my_sum, my_sum_1795, tot_1796]
  have h : v3_fast 896 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1797 : my_sum 1797 = 1787 := by
  rw [my_sum, my_sum_1796, tot_1797]
  have h : v3_fast 1196 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1798 : my_sum 1798 = 1788 := by
  rw [my_sum, my_sum_1797, tot_1798]
  have h : v3_fast 840 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1799 : my_sum 1799 = 1789 := by
  rw [my_sum, my_sum_1798, tot_1799]
  have h : v3_fast 1536 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1800 : my_sum 1800 = 1790 := by
  rw [my_sum, my_sum_1799, tot_1800]
  have h : v3_fast 480 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1801 : my_sum 1801 = 1792 := by
  rw [my_sum, my_sum_1800, tot_1801]
  have h : v3_fast 1800 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1802 : my_sum 1802 = 1792 := by
  rw [my_sum, my_sum_1801, tot_1802]
  have h : v3_fast 832 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1803 : my_sum 1803 = 1793 := by
  rw [my_sum, my_sum_1802, tot_1803]
  have h : v3_fast 1200 100 = 1 := rfl
  rw [h] <;> decide

theorem my_sum_1804 : my_sum 1804 = 1793 := by
  rw [my_sum, my_sum_1803, tot_1804]
  have h : v3_fast 800 100 = 0 := rfl
  rw [h] <;> decide

theorem my_sum_1805 : my_sum 1805 = 1795 := by
  rw [my_sum, my_sum_1804, tot_1805]
  have h : v3_fast 1368 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1806 : my_sum 1806 = 1797 := by
  rw [my_sum, my_sum_1805, tot_1806]
  have h : v3_fast 504 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_1807 : my_sum 1807 = 1799 := by
  rw [my_sum, my_sum_1806, tot_1807]
  have h : v3_fast 1656 100 = 2 := rfl
  rw [h] <;> decide

theorem my_sum_eq_Icc (n : ℕ) : my_sum n = (Icc 1 n).sum (fun k => v3_fast k.totient 100) := by
  induction n with
  | zero => simp [my_sum]
  | succ k ih => rw [my_sum, ih, Icc_succ_sum]

